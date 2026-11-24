"""Check the uniform Fano star construction and its two-gate extension."""

VARIABLES = 14
TABLE_SIZE = 1 << VARIABLES


def star():
    gates = []

    def add(op, left, right):
        wire = VARIABLES + len(gates)
        assert left != right and max(left, right) < wire
        gates.append((op, left, right))
        return wire

    terms = []
    for line in range(7):
        pair = add("or", line, (line + 1) % 7)
        triple = add("or", pair, (line + 3) % 7)
        terms.append(add("and", triple, 7 + line))
    output = terms[0]
    for term in terms[1:]:
        output = add("or", output, term)
    return gates, output, terms[0]


def truth(gates, raw):
    wires = list(raw)
    for op, left, right in gates:
        wires.append(wires[left] & wires[right] if op == "and" else wires[left] | wires[right])
    return wires


def derivative(gates, anchor, direction):
    pure = truth(gates, [int(i == anchor) for i in range(VARIABLES)])
    d = [int(i == direction) for i in range(VARIABLES)]
    for op, a, b in gates:
        d.append((pure[a] & d[b]) | (d[a] & pure[b]) if op == "and" else d[a] | d[b])
    return d


def factor_at_zero():
    gates = []

    def add(op, a, b):
        gates.append((op, a, b))
        return VARIABLES + len(gates) - 1

    def pencil(p):
        lines = [7 + (p - d) % 7 for d in (0, 1, 3)]
        return add("or", add("or", lines[0], lines[1]), lines[2])

    other = [add("and", p, pencil(p)) for p in range(1, 7)]
    residual = other[0]
    for term in other[1:]:
        residual = add("or", residual, term)
    through_zero = pencil(0)
    return gates, add("and", add("or", residual, 0), add("or", residual, through_zero))


def main():
    edges = [(p, 7 + l) for l in range(7) for p in (l, (l + 1) % 7, (l + 3) % 7)]
    tab = [sum(1 << x for x in range(TABLE_SIZE) if (x >> i) & 1) for i in range(VARIABLES)]
    correct = 0
    for p, line in edges:
        correct |= tab[p] & tab[line]
    gates, output, one_term = star()
    # F or one of its own terms equals F, and is a distinct wire.
    extended = gates + [("or", output, one_term), ("and", output, VARIABLES + len(gates))]
    for circuit, out in [(gates, output), factor_at_zero(), (extended, VARIABLES + len(extended) - 1)]:
        assert all(a != b and max(a, b) < VARIABLES + j for j, (_, a, b) in enumerate(circuit))
        assert truth(circuit, tab)[out] == correct
        doubled = [(p, line) for p, line in edges if derivative(circuit, p, line)[out] == 0
                   and derivative(circuit, line, p)[out] == 0]
        print(f"{len(circuit)} gates: all {TABLE_SIZE} inputs agree; {len(doubled)}/21 double re-reads")


if __name__ == "__main__":
    main()
