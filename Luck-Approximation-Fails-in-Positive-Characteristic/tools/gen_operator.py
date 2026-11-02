"""gen_operator.py -- the generated Lean data: the ell = 11 Goren-Oort Tanner operator over F3 and its certificate.

Base graph X0 = Gamma+(lambda0)\\T at p = 3, ell = 11 (icosian_graph.py, 'tw' gluing): 11 even + 11 odd vertices,
110 edges, simple, 10-regular. F = pi_1(X0) is free on the 89 edges outside a BFS spanning tree. The operator
over F9[F] is
    A[(v0,c),(v1,r)] = sum_{e: v0 -- v1} m1[pos1(e)][r] * m0[pos0(e)][c] * gamma_e      (x -> x A, rows = unknowns)
with gamma_e the generator of e (1 on tree edges). Restriction of scalars along F9 = F3[i]/(i^2+1): a coefficient
c0 + c1 i becomes the block [[c0, c1], [-c1, c0]] (row-vector convention). The F3 index of (vertex, slot, comp)
is 10*vertex + 2*slot + comp.

The 3-cover: chi : F -> Z/3, generator g -> volt[g]. Level-1 matrix over F3[t]/(t^3-1) = F3[u]/(u^3), u = t - 1:
    B0 = sum_e M_e,  B1 = sum_e chi(gamma_e) M_e   (coefficient of u),  B2 = sum_e [chi(gamma_e) = 2] M_e.
Certificate (all over F3): b (42 x 110) basis of the left kernel of B0, y (42 x 110) basis of the right kernel,
C = b B1 y^T (42 x 42) and its inverse, and a 68 x 68 minor of B0 (rows R, cols S) with its inverse.

Output (each file is checked by Lean; none is trusted):
  lean/LuckApproximation/ConData.lean   the coset certificate: representatives of the even and odd vertices
                                        (matrices over F11), the ends and positions of each edge, and the
                                        icosians labelling the ten positions (indices into Luck.Con.icosians);
  lean/LuckApproximation/Data.lean      packed caches of the incidences and blocks (proved equal to the
                                        construction in ConCache.lean), the spanning tree with the generator
                                        numbering (checked to be a spanning tree), and the 3-cover voltage;
  lean/LuckApproximation/CertData.lean  the certificate for the 3-chain side.
Needs numpy. Run from the paper directory:  python3 tools/gen_operator.py
"""
from collections import deque
from pathlib import Path
import numpy as np

import icosian_graph as gt

F9 = gt.F9
ELL, SEED = 11, 1
LIB = Path(__file__).resolve().parents[1] / "lean" / "LuckApproximation"
OUT = LIB / "Data.lean"


# ---------------------------------------------------------------- F3 linear algebra (row reduction mod 3)
def rref3(M):
    M = np.array(M, dtype=np.int64) % 3
    rows, cols = M.shape
    piv, r = [], 0
    for c in range(cols):
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0:
            continue
        k = r + nz[0]
        M[[r, k]] = M[[k, r]]
        M[r] = (M[r] * (1 if M[r, c] == 1 else 2)) % 3      # 2 = 2^{-1} mod 3
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] = (M[i] - M[i, c] * M[r]) % 3
        piv.append(c)
        r += 1
        if r == rows:
            break
    return M, piv


def rank3(M):
    return len(rref3(M)[1])


def left_kernel3(M):
    """basis (rows) of {x : x M = 0}"""
    return right_kernel3(np.array(M).T)


def right_kernel3(M):
    """basis (rows) of {y : M y = 0}"""
    R, piv = rref3(M)
    n = R.shape[1]
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = np.zeros(n, dtype=np.int64)
        v[f] = 1
        for i, c in enumerate(piv):
            v[c] = (-R[i, f]) % 3
        basis.append(v)
    return np.array(basis, dtype=np.int64).reshape(len(basis), n)


def inv3(M):
    M = np.array(M, dtype=np.int64) % 3
    n = M.shape[0]
    R, piv = rref3(np.hstack([M, np.eye(n, dtype=np.int64)]))
    assert piv[:n] == list(range(n)), "singular"
    return R[:, n:] % 3


# ---------------------------------------------------------------- base structure
S = gt.build(ELL, verbose=False)
nV, nE = S["nV"], S["nE"]
assert (nV, nE) == (11, 110)
lab0, lab1 = S["lab0"], np.array([gt.frob(x) for x in S["lab1"]])        # 'tw' gluing
m0 = np.array([gt.monos(x) for x in lab0])     # even: form monomials at position j (10 x 5)
m1 = np.array([gt.monos(x) for x in lab1])     # odd: parity rows at position j (10 x 5)
ev, od = [int(x) for x in S["e_even"]], [int(x) for x in S["e_odd"]]
pos0, pos1 = [0] * nE, [0] * nE
for v in range(nV):
    for j in range(10):
        pos0[int(S["E0"][v, j])] = j
        pos1[int(S["E1"][v, j])] = j
edge_of = {}
for e in range(nE):
    assert (ev[e], od[e]) not in edge_of, "multi-edge"
    edge_of[(ev[e], od[e])] = e

# BFS spanning tree on 22 vertices (even v -> v, odd v -> 11 + v)
adj = [[] for _ in range(2 * nV)]
for e in range(nE):
    adj[ev[e]].append((nV + od[e], e))
    adj[nV + od[e]].append((ev[e], e))
seen, tree, q = {0}, set(), deque([0])
while q:
    x = q.popleft()
    for y, e in adj[x]:
        if y not in seen:
            seen.add(y); tree.add(e); q.append(y)
assert len(seen) == 22 and len(tree) == 21
gen = {}
for e in range(nE):
    if e not in tree:
        gen[e] = len(gen)
assert len(gen) == 89


def f9_to_f3(c):
    return int(c) % 3, int(c) // 3        # a + 3b encodes a + b i


def block(c):
    c0, c1 = f9_to_f3(c)
    return [[c0, c1], [(-c1) % 3, c0]]


# coupling[e] : 10 x 10 over F3, rows (c, comp) at the even end, cols (r, comp) at the odd end
coupling = []
for e in range(nE):
    Cb = [[0] * 10 for _ in range(10)]
    for c in range(5):
        for r in range(5):
            coef = F9.m(int(m1[pos1[e]][r]), int(m0[pos0[e]][c]))
            B = block(coef)
            for a in range(2):
                for b in range(2):
                    Cb[2 * c + a][2 * r + b] = B[a][b]
    coupling.append(Cb)


def M_e(e):
    M = np.zeros((110, 110), dtype=np.int64)
    M[10 * ev[e]:10 * ev[e] + 10, 10 * od[e]:10 * od[e] + 10] = np.array(coupling[e])
    return M


volt_gen = np.random.default_rng(SEED).integers(0, 3, size=89)
assert any(volt_gen)
volt = [0 if e in tree else int(volt_gen[gen[e]]) for e in range(nE)]
B0 = sum(M_e(e) for e in range(nE)) % 3
B1 = sum(volt[e] * M_e(e) for e in range(nE)) % 3
B2 = sum((1 if volt[e] == 2 else 0) * M_e(e) for e in range(nE)) % 3

# --------------------------------------------------------------- checks against the F9 computation
kerL = left_kernel3(B0)
kerR = right_kernel3(B0)
print("rank B0 =", rank3(B0), " dim left ker =", len(kerL), " dim right ker =", len(kerR))
assert len(kerL) == 42 and len(kerR) == 42          # = 2 x 21 (F9 dim 21 at ell = 11, 'tw')
# full level-1 map on row vectors (x0, x1, x2) -> (x0 B0, x0 B1 + x1 B0, x0 B2 + x1 B1 + x2 B0)
Z = np.zeros_like(B0)
T = np.block([[B0, B1, B2], [Z, B0, B1], [Z, Z, B0]]) % 3
print("level-1 (Z/3 cover) kernel dim over F3 =", 330 - rank3(T))
assert 330 - rank3(T) == 42
C = (kerL @ B1 @ kerR.T) % 3
Cinv = inv3(C)
assert np.all((C @ Cinv) % 3 == np.eye(42, dtype=np.int64))
assert np.all((kerL @ B0) % 3 == 0) and np.all((B0 @ kerR.T) % 3 == 0)
# 68 x 68 invertible minor of B0
R0, pivc = rref3(B0)
cols = pivc[:68]
Rt, pivr = rref3(B0[:, cols].T)
rows = pivr[:68]
minor = B0[np.ix_(rows, cols)]
Winv = inv3(minor)
assert np.all((minor @ Winv) % 3 == np.eye(68, dtype=np.int64))
print("certificate OK: C invertible, 68 x 68 minor invertible")


coupling_f9 = coupling

# --------------------------------------------------------------- Lean output (packed, for fast kernel checks)
def pack(digits, w):
    """little-endian digits, w bits each, as one natural number"""
    n = 0
    for d in reversed([int(x) for x in digits]):
        assert 0 <= d < (1 << w), (d, w)
        n = (n << w) | d
    return n


def hexlit(n):
    return hex(n) if n else "0"


EDGE_NONE, GEN_NONE = 127, 127
edge_digits = [edge_of.get((a, b), EDGE_NONE) for a in range(11) for b in range(11)]
gen_digits = [GEN_NONE if e in tree else gen[e] for e in range(nE)]
coup_digits = [coupling_f9[e][a][b] for e in range(nE) for a in range(10) for b in range(10)]

lines = []
lines.append("import Mathlib.Data.ZMod.Defs\n")
lines.append("/-!\n# Packed data for the ℓ = 11 Goren–Oort operator (generated by `tools/gen_operator.py`)\n")
lines.append("Do not edit by hand. Tables are packed into natural numbers (little-endian digits in base `2 ^ w`),")
lines.append("so that the kernel reads an entry with one division and one remainder on a literal.")
lines.append("* `edgeOfCode`: base `2⁷`, digit `11 a + b` is the edge joining even vertex `a` to odd vertex `b`")
lines.append("  (127: no edge). A cache: `ConCache.lean` proves it equal to the construction.")
lines.append("* `couplingCode`: base `2²`, digit `100 e + 10 a + b` is entry `(a, b)` of the 10 × 10 block of")
lines.append("  edge `e` over 𝔽₃. A cache: `ConCache.lean` proves it equal to the construction.")
lines.append("* `edgeGenCode`: base `2⁷`, digit `e` is the free generator of edge `e` (127: spanning-tree edge).")
lines.append("  A choice: `ConChecks.lean` checks that the tree edges form a spanning tree.")
lines.append("* `voltCode`: base `2²`, the 3-cover voltage of each generator (a choice).")
lines.append("The certificate data are in `CertData.lean`, checked in `CertB0.lean`, `CertB1.lean` and `CertRest.lean`.\n-/\n")
lines.append("namespace Luck.Data\n")
lines.append("/-- Digit `k` of `n` in base `2 ^ w`. -/\ndef digit (w n k : ℕ) : ℕ := n / 2 ^ (w * k) % 2 ^ w\n")
lines.append(f"def edgeOfCode : ℕ := {hexlit(pack(edge_digits, 7))}\n")
lines.append(f"def edgeGenCode : ℕ := {hexlit(pack(gen_digits, 7))}\n")
lines.append(f"def couplingCode : ℕ :=\n  {hexlit(pack(coup_digits, 2))}\n")
lines.append(f"def voltCode : ℕ := {hexlit(pack(volt_gen, 2))}\n")
lines.append("def edgeOfNat (a b : ℕ) : ℕ := digit 7 edgeOfCode (11 * a + b)\n")
lines.append("def edgeGenNat (e : ℕ) : ℕ := digit 7 edgeGenCode e\n")
lines.append("def couplingNat (e a b : ℕ) : ℕ := digit 2 couplingCode (100 * e + 10 * a + b)\n")
lines.append("def voltNat (g : ℕ) : ℕ := digit 2 voltCode g\n")
lines.append("/-- The free generator of an edge (`none` on the 21 spanning-tree edges). -/\n"
             "def edgeGen (e : Fin 110) : Option (Fin 89) :=\n"
             "  if h : edgeGenNat e < 89 then some ⟨_, h⟩ else none\n")
lines.append("/-- The 3-cover voltage of a generator. -/\n"
             "def volt (g : Fin 89) : ZMod 3 := (voltNat g : ZMod 3)\n")
lines.append("end Luck.Data\n")

# ---- certificate (CertData.lean): small matrices as digit lists, right factors packed in base 512
P = (kerL @ B1) % 3                      # 42 x 110
Cm = (P @ kerR.T) % 3                    # 42 x 42  (= C)
assert np.all(Cm == C % 3)


def pk512(row):
    return pack(row, 9)


def L1(v):
    return "[" + ", ".join(str(int(x)) for x in v) + "]"


def L2(M):
    return "[" + ",\n    ".join(L1(r) for r in M) + "]"


def LP(nums):
    return "[" + ",\n    ".join(hexlit(n) for n in nums) + "]"


cl = ["/-!\n# Certificate data (generated by `tools/gen_operator.py`; do not edit)\n",
      "Every matrix is a list of rows packed in base 512 (little-endian digits in `{0, 1, 2}`):",
      "* `kerLPk`: 42 rows of length 110, a basis of the left kernel of `B₀`;",
      "* `PPk = kerL · B₁` (42 × 110) and `CPk = P · kerRᵀ` (42 × 42);",
      "* `kerRTpk`: the 110 columns of `kerR` (length 42), a basis of the right kernel of `B₀`;",
      "* `CinvPk`: the rows of `C⁻¹`; `WPk`: the rows of the inverse of the 68 × 68 minor",
      "  `B₀[minorR, minorS]`.",
      "No imports: these are plain literals.\n-/\n", "namespace Luck.Cert\n"]
cl.append(f"def kerLPk : List Nat :=\n  {LP([pk512(r) for r in kerL])}\n")
cl.append(f"def PPk : List Nat :=\n  {LP([pk512(r) for r in P])}\n")
cl.append(f"def CPk : List Nat :=\n  {LP([pk512(r) for r in Cm])}\n")
cl.append(f"def kerRTpk : List Nat :=\n  {LP([pk512(c) for c in kerR.T])}\n")
cl.append(f"def CinvPk : List Nat :=\n  {LP([pk512(r) for r in Cinv])}\n")
cl.append(f"def WPk : List Nat :=\n  {LP([pk512(r) for r in Winv])}\n")
cl.append(f"def minorR : List Nat := {L1(rows)}\n")
cl.append(f"def minorS : List Nat := {L1(cols)}\n")
cl.append("end Luck.Cert\n")
(LIB / "CertData.lean").write_text("\n".join(cl))
print("wrote CertData.lean")
OUT.write_text("\n".join(lines))
print("wrote Data.lean")

# ---- the coset certificate (ConData.lean), in the icosian order of Luck.Con.icosians
import itertools
from fractions import Fraction as Fr
EVEN_PERMS = [p for p in itertools.permutations(range(4))
              if sum(1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j]) % 2 == 0]
LEAN_ICOS = []
for p_ in range(4):
    for s_ in (1, 2):
        LEAN_ICOS.append(tuple(s_ if k == p_ else 0 for k in range(4)))
for sg in itertools.product((3, 4), repeat=4):
    LEAN_ICOS.append(sg)
for perm in EVEN_PERMS:
    for s1, s2, s3 in itertools.product((0, 1), repeat=3):
        vals = [0, 3 + s1, 5 + s2, 7 + s3]
        q_ = [None] * 4
        for i_ in range(4):
            q_[perm[i_]] = vals[i_]
        LEAN_ICOS.append(tuple(q_))
SYM = {(Fr(0), Fr(0)): 0, (Fr(1), Fr(0)): 1, (Fr(-1), Fr(0)): 2, (Fr(1, 2), Fr(0)): 3, (Fr(-1, 2), Fr(0)): 4,
       (Fr(-1, 2), Fr(1, 2)): 5, (Fr(1, 2), Fr(-1, 2)): 6, (Fr(0), Fr(1, 2)): 7, (Fr(0), Fr(-1, 2)): 8}
lean_index = {q_: n_ for n_, q_ in enumerate(LEAN_ICOS)}
assert len(lean_index) == 120
U_ = S["U"]
posRep0 = [lean_index[tuple(SYM[(Fr(c[0]), Fr(c[1]))] for c in U_[r_])] for r_ in S["R0"]]
posRep1 = [lean_index[tuple(SYM[(Fr(c[0]), Fr(c[1]))] for c in U_[r_])] for r_ in S["R1"]]
mcode = lambda M_: sum(int(t) % 11 * 11 ** k_ for k_, t in enumerate(M_))
evenRep = [mcode(r_) for r_ in S["rep0"]]
oddRep = [mcode(r_) for r_ in S["rep1"]]
LL = lambda xs: "[" + ", ".join(str(int(x)) for x in xs) + "]"
cd = ["/-!", "# The coset certificate (generated by `tools/gen_operator.py`; do not edit)", "",
      "Checked in `ConChecks.lean`. Matrices over `𝔽₁₁` are coded `a + 11 b + 121 c + 1331 d` for `(a b; c d)`.",
      "* `evenRep`, `oddRep`: representatives of the cosets `G/H₀` and `G/H₁` of `G = PSL₂(𝔽₁₁)`;",
      "* `edgeEven`, `edgePos0`, `edgeOdd`, `edgePos1`: the ends of each edge and its positions there;",
      "* `posRep0`, `posRep1`: the icosians (indices into `Luck.Con.icosians`) labelling the ten positions.",
      "No imports: these are plain literals.", "-/", "", "namespace Luck.ConData", "",
      f"def evenRep : List Nat := {LL(evenRep)}", "", f"def oddRep : List Nat := {LL(oddRep)}", "",
      f"def edgeEven : List Nat := {LL(ev)}", "", f"def edgePos0 : List Nat := {LL(pos0)}", "",
      f"def edgeOdd : List Nat := {LL(od)}", "", f"def edgePos1 : List Nat := {LL(pos1)}", "",
      f"def posRep0 : List Nat := {LL(posRep0)}", "", f"def posRep1 : List Nat := {LL(posRep1)}", "",
      "end Luck.ConData", ""]
(LIB / "ConData.lean").write_text("\n".join(cd))
print("wrote ConData.lean")
