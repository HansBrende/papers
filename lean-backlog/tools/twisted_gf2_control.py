"""Independent exact verification of the n=4,d=2,w=3 GF(2) witness.

Pure Python integer row elimination; no dependencies and no numerical tolerances.
"""


def matrix(bits):
    return [[(bits >> (4 * i + j)) & 1 for j in range(4)] for i in range(4)]


def add(a, b):
    return [[x ^ y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b))) % 2
             for j in range(len(b[0]))] for i in range(len(a))]


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def rref(a):
    a = [row[:] for row in a]
    pivots = []
    for j in range(len(a[0])):
        k = next((k for k in range(len(pivots), len(a)) if a[k][j]), None)
        if k is None:
            continue
        i = len(pivots)
        a[i], a[k] = a[k], a[i]
        for k in range(len(a)):
            if k != i and a[k][j]:
                a[k] = [x ^ y for x, y in zip(a[k], a[i])]
        pivots.append(j)
    return a, pivots


def rank(a):
    return len(rref(a)[1])


def kernel(a):
    reduced, pivots = rref(a)
    basis = []
    for j in range(len(a[0])):
        if j in pivots:
            continue
        v = [int(k == j) for k in range(len(a[0]))]
        for i, p in enumerate(pivots):
            v[p] = reduced[i][j]
        basis.append(v)
    return basis


def flatten(a):
    return sum(a, [])


def generated_algebra(a, b):
    basis = [eye(4)]
    for u in basis:
        for v in (a, b):
            z = mul(u, v)
            if rank([flatten(x) for x in basis] + [flatten(z)]) > len(basis):
                basis.append(z)
    return basis


def verify():
    # Fixed witness from an exact search with PRNG seed 20261113.
    a, b, u, ui = map(matrix, (52093, 6571, 31576, 7599))
    identity = eye(4)
    zero = [[0] * 4 for _ in range(4)]
    assert mul(u, ui) == identity == mul(ui, u)
    assert rank([flatten(identity), flatten(a), flatten(b)]) == 3
    algebra = generated_algebra(a, b)
    assert len(algebra) == 16
    # K00=K11=0, K01=I+A, K10=B.
    r01, r10 = add(u, add(identity, a)), add(ui, b)
    residual = [zero[i] + r01[i] for i in range(4)] + [r10[i] + zero[i] for i in range(4)]
    nullspace = kernel(residual)
    assert rank(r01) == 2 and rank(r10) == 1
    assert rank(residual) == 3 and len(nullspace) == 5
    assert all(mul(residual, [[x] for x in v]) == [[0]] * 8 for v in nullspace)
    power = identity
    order = None
    for k in range(1, 20161):
        power = mul(power, u)
        if power == identity:
            order = k
            break
    assert order == 7
    for name, m in [('A', a), ('B', b), ('U', u), ('U_inverse', ui),
                    ('R01', r01), ('R10', r10), ('residual', residual), ('kernel_basis', nullspace)]:
        print(name)
        for row in m:
            print(' '.join(map(str, row)))
    print('rank(residual)=3; nullity=5; dim algebra(W)=16')
    print(f'rank(U-I)={rank(add(u, identity))}; order(U)={order}')


if __name__ == '__main__':
    verify()
