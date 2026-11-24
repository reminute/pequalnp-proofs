"""Rebuild the L-meta-1971 proof companion and audit the selected theorems."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent
SRC = ROOT / "src"
RELEASE = "leanprover/lean4:v4.36.0"
UPSTREAM = {
    "19b9ebcdbad73b4e7dc900df1e5c49dc7034a8eb",
    "2e67c7c8499e2e12d39c1f31c085c0e4e94b0391",
}
MATHLIB = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"
IDENT = r"[A-Za-z_][A-Za-z0-9_']*"
IMPORT = re.compile(r"^import\s+([\w.]+)\s*$", re.MULTILINE)
AXIOMS = re.compile(r"^#print axioms ([\w.]+)\s*$", re.MULTILINE)


def ordered_sources(targets, libraries, all_sources):
    files = {p.stem: p for p in SRC.glob("*.lean")}
    if len({name.casefold() for name in files}) != len(files):
        raise ValueError("Source module names collide on a case-insensitive filesystem")
    ordered = {}
    active = set()

    def visit(name):
        if name in ordered:
            return
        if name in active:
            raise ValueError(f"Cyclic import at {name}")
        if name not in files:
            raise ValueError(f"No companion source for {name}")
        if any((lib / f"{name}.olean").is_file() for lib in libraries):
            raise ValueError(f"Module {name} also exists in the upstream libraries")
        active.add(name)
        path = files[name]
        for dependency in IMPORT.findall(path.read_text(encoding="utf-8-sig")):
            if dependency in files:
                visit(dependency)
            elif dependency.split(".")[0] not in {"Mathlib", "PEqualNP", "Init", "Lean", "Std"}:
                raise ValueError(f"Missing companion dependency {dependency} for {name}")
        active.remove(name)
        ordered[name] = path

    names = sorted(files) if all_sources else dict(targets)
    for name in names:
        visit(name)
    return ordered


def environment(project, lean, output):
    revision = subprocess.check_output(["git", "-C", project, "rev-parse", "HEAD"], text=True).strip()
    if revision not in UPSTREAM:
        raise ValueError(f"The upstream checkout is at {revision}, expected one of {sorted(UPSTREAM)}")
    if (project / "lean-toolchain").read_text().strip() != RELEASE:
        raise ValueError(f"Expected {RELEASE} in the upstream lean-toolchain file")
    manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = manifest["packages"]
    if not any(p["name"] == "mathlib" and p["rev"] == MATHLIB for p in packages):
        raise ValueError("The upstream mathlib revision differs from the companion pin")
    roots = [project]
    for package in packages:
        roots.append(project / manifest["packagesDir"] / package["name"] / (package.get("subDir") or ""))
    libraries = [root / ".lake/build/lib/lean" for root in roots]
    for module in ("PEqualNP/Defs.olean", "Mathlib.olean"):
        if not any((lib / module).is_file() for lib in libraries):
            raise ValueError(f"Missing upstream build artifact {module}")
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, [output, *libraries]))
    env["LEAN_SYSROOT"] = str(lean.parent.parent)
    env["PATH"] = str(lean.parent) + os.pathsep + env.get("PATH", "")
    return env, libraries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True, help="upstream lean directory")
    parser.add_argument("--build-dir", type=Path, required=True, help="separate output directory")
    parser.add_argument("--lean", type=Path, help="actual Lean release binary if installed outside elan")
    parser.add_argument("--target", action="append", metavar="MODULE:THEOREM",
                        help="check this target and its dependencies (repeatable, replaces defaults)")
    args = parser.parse_args()
    project = args.upstream.resolve()
    output = args.build_dir.resolve()
    if output.is_relative_to(project) or output.is_relative_to(ROOT):
        parser.error("Choose a build directory separate from the upstream project and companion sources")
    elan = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    installed = elan / "toolchains" / "leanprover--lean4---v4.36.0" / "bin"
    lean = (args.lean or installed / ("lean.exe" if os.name == "nt" else "lean")).resolve()
    if not lean.is_file():
        parser.error("Supply --lean pointing to the installed Lean 4.36.0 release binary")
    if not re.search(r"\bversion 4\.36\.0\b", subprocess.check_output([lean, "--version"], text=True)):
        parser.error("Lean version 4.36.0 is required")
    targets = []
    source_targets = [
        f"{path.stem}:{decl}" for path in sorted(SRC.glob("*.lean"))
        for decl in AXIOMS.findall(path.read_text(encoding="utf-8-sig"))
    ]
    for target in args.target or source_targets:
        if not re.fullmatch(fr"{IDENT}:{IDENT}(?:\.{IDENT})*", target):
            parser.error(f"Expected MODULE:THEOREM, got {target}")
        targets.append(tuple(target.split(":")))
    env, libraries = environment(project, lean, output)
    ordered = ordered_sources(targets, [*libraries, lean.parent.parent / "lib/lean"],
                              all_sources=not args.target)
    output.mkdir(parents=True, exist_ok=True)
    for i, (name, source) in enumerate(ordered.items(), 1):
        print(f"[{i}/{len(ordered)}] {name}", flush=True)
        with tempfile.TemporaryDirectory(dir=output) as scratch:
            dest = Path(scratch) / f"{name}.olean"
            subprocess.run([lean, "-j", "1", "-R", source.parent, "-o", dest, source],
                           cwd=project, env=env, check=True)
            dest.replace(output / dest.name)
    probe = "\n".join([*(f"import {name}" for name in dict(targets)),
                       *(f"#print axioms {theorem}" for _, theorem in targets)]) + "\n"
    audit = subprocess.run([lean, "-j", "1", "--stdin"], cwd=project, env=env,
                           input=probe, encoding="utf-8", stdout=subprocess.PIPE, check=True)
    print(audit.stdout, end="")
    standard = {"propext", "Classical.choice", "Quot.sound"}
    for _, theorem in targets:
        pattern = rf"'{re.escape(theorem)}' depends on axioms: \[([^]]*)\]"
        match = re.search(pattern, audit.stdout)
        if match:
            dependencies = {a.strip() for a in match[1].split(",") if a.strip()}
            if not dependencies <= standard:
                raise ValueError(f"{theorem} depends on nonstandard axioms: {sorted(dependencies - standard)}")
        elif f"'{theorem}' does not depend on any axioms" not in audit.stdout:
            raise ValueError(f"Could not verify the axiom report for {theorem}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        sys.exit(str(exc))
