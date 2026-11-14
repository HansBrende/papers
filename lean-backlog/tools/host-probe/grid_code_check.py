"""Integer identities for the explicit 21-symbol code on the 3x3 grid.

Rows are points (i, j); columns R_k and C_k read the rows with i = k and
j = k, respectively. Only the 36 nonincident cells occur here. Every
recovery and parameter-extraction identity is checked as an equality of
integer coefficient vectors, so it holds over every abelian group. For a
finite alphabet Z/qZ this gives exactly q**21 codewords, for every q >= 2.
This is an executable symbolic certificate, not a Lean formalization.
"""

from itertools import combinations


PAIRS = tuple(combinations(range(3), 2))
PARAMETERS = (
    tuple(("S", j, i, k) for j in range(3) for i, k in PAIRS)
    + tuple(("T", i, j, k) for i in range(3) for j, k in PAIRS)
    + tuple(("D", a, b) for a, b in PAIRS)
)
BASIS = {
    key: tuple(int(i == j) for i in range(len(PARAMETERS)))
    for j, key in enumerate(PARAMETERS)
}


def linear_combination(*terms):
    return tuple(sum(c * v[i] for c, v in terms) for i in range(len(PARAMETERS)))


def a_cell(j, i, k):
    return (i, j), ("R", k)


def b_cell(i, j, k):
    return (i, j), ("C", k)


def check():
    word = {}
    for j in range(3):
        for i, k in PAIRS:
            s, delta = BASIS["S", j, i, k], BASIS["D", i, k]
            word[a_cell(j, i, k)] = s
            word[a_cell(j, k, i)] = linear_combination((1, s), (-1, delta))
    for i in range(3):
        for j, k in PAIRS:
            t, delta = BASIS["T", i, j, k], BASIS["D", j, k]
            word[b_cell(i, j, k)] = t
            word[b_cell(i, k, j)] = linear_combination((1, t), (-1, delta))
    assert len(word) == 36 and len(PARAMETERS) == 21

    recovered = set()

    def recovery(target, terms):
        kind, k = target[1]
        axis = 0 if kind == "R" else 1
        assert target[0][axis] != k
        assert all(cell[0][axis] == k for _, cell in terms)
        assert word[target] == linear_combination(
            *((coefficient, word[cell]) for coefficient, cell in terms)
        )
        recovered.add(target)

    for k in range(3):
        for j in range(3):
            for i in range(3):
                if i != k:
                    a, b = sorted((i, k))
                    sign = 1 if i < k else -1
                    recovery(a_cell(j, i, k), (
                        (1, a_cell(j, k, i)),
                        (sign, b_cell(k, a, b)),
                        (-sign, b_cell(k, b, a)),
                    ))
        for i in range(3):
            for j in range(3):
                if j != k:
                    a, b = sorted((j, k))
                    sign = 1 if j < k else -1
                    recovery(b_cell(i, j, k), (
                        (1, b_cell(i, k, j)),
                        (sign, a_cell(k, a, b)),
                        (-sign, a_cell(k, b, a)),
                    ))
    assert recovered == word.keys()

    extracted = {}
    for j in range(3):
        for i, k in PAIRS:
            extracted["S", j, i, k] = word[a_cell(j, i, k)]
    for i in range(3):
        for j, k in PAIRS:
            extracted["T", i, j, k] = word[b_cell(i, j, k)]
    for a, b in PAIRS:
        extracted["D", a, b] = linear_combination(
            (1, word[a_cell(0, a, b)]), (-1, word[a_cell(0, b, a)])
        )
    assert extracted == BASIS
    print("PASS: 36 recovery identities, with helper-row support checked, "
          "and 21 parameter-extraction identities over the integers.")
    print("S and T are designated entries; D is recovered from entry differences. "
          "The encoder is injective over every abelian group, giving q^21 "
          "codewords on 36 nonincident cells over Z/qZ for every q >= 2.")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O: this certificate uses assertions.")
    check()
