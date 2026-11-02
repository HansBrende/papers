import LuckApproximation.ConData
import Mathlib.Data.Nat.Notation

/-!
# The Goren–Oort operator, built from its definition

This file defines the labels and the blocks of the operator of the paper's Definition 3.4 from first principles, and
reads the incidences of the base graph from the certificate in `ConData.lean`. Everything is computable on natural
numbers, so that the kernel can evaluate it.

* **`𝔽₉`.** `𝔽₉ = 𝔽₃[i]/(i² + 1)`; the element `a + b i` (`a, b ∈ {0, 1, 2}`) has code `a + 3 b` (`add`, `mul`,
  `neg`, `frob`).
* **The icosians.** `icosians` lists the 120 norm-one units of the icosian ring by the standard formula, with each
  coordinate one of nine symbols (`symF9`, `symF11` give their images under `θ ↦ 2 + i` in `𝔽₉` and `θ ↦ 4` in
  `𝔽₁₁ = 𝒪_E/λ₀`, where `θ = (1 + √5)/2`). `red3` and `red11` are the two splittings of the quaternion algebra
  (`i, j ↦` explicit matrices).
* **The base graph.** The coset graph of `PSL₂(𝔽₁₁)` with respect to the images `H₀`, `H₁` of `2I` and
  `α 2I α⁻¹` (`α = 1 + i + j`). The certificate in `ConData.lean` enumerates its vertices and edges by coset
  representatives; `ConChecks.lean` checks that the enumeration is the coset graph.
* **Labels and blocks.** The edge at position `j` of an even vertex is labelled `red3 u_j · p₀`; at an odd vertex
  `Frob (red3 u'_j · k₀)`, where `p₀` and `k₀` span the image and the kernel of `red3 α`. The block of an edge is the
  restriction of scalars of `m₁(e)_r · m₀(e)_c` (quartic monomials at the two labels), `x + y i ↦ (x y; −y x)`.

Matrices over `𝔽₉` and over `𝔽₁₁` are lists `[a, b, c, d]` for `(a b; c d)`.
-/

namespace Luck.Con

open Luck.ConData

/-! ### `𝔽₉` -/

/-- Real and imaginary parts of the code of `a + b i`. -/
def re (x : ℕ) : ℕ := x % 3
def im (x : ℕ) : ℕ := x / 3 % 3
/-- The code of `a + b i`. -/
def mk (a b : ℕ) : ℕ := a % 3 + 3 * (b % 3)
def add (x y : ℕ) : ℕ := mk (re x + re y) (im x + im y)
/-- `(a + b i)(c + d i) = (a c − b d) + (a d + b c) i`. -/
def mul (x y : ℕ) : ℕ := mk (re x * re y + 2 * (im x * im y)) (re x * im y + im x * re y)
def neg (x : ℕ) : ℕ := mk (2 * re x) (2 * im x)
/-- The Frobenius `x ↦ x³`, which sends `a + b i` to `a − b i`. -/
def frob (x : ℕ) : ℕ := mk (re x) (2 * im x)
/-- `x ^ n` in `𝔽₉`. -/
def pow (x : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => mul (pow x n) x

/-! ### The icosians -/

/-- Images in `𝔽₉` of the coordinate symbols `0, 1, −1, 1/2, −1/2, θ⁻¹/2, −θ⁻¹/2, θ/2, −θ/2` under `θ ↦ 2 + i`. -/
def symF9 (s : ℕ) : ℕ := [0, 1, 2, 2, 1, 8, 4, 7, 5].getD s 0
/-- Images in `𝔽₁₁` of the same symbols under `θ ↦ 4`. -/
def symF11 (s : ℕ) : ℕ := [0, 1, 10, 6, 5, 7, 4, 2, 9].getD s 0

/-- The twelve even permutations of `{0, 1, 2, 3}`, as `[π 0, π 1, π 2, π 3]`. -/
def evenPerms : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2], [1, 0, 3, 2], [1, 2, 0, 3], [1, 3, 2, 0],
   [2, 0, 1, 3], [2, 1, 3, 0], [2, 3, 0, 1], [3, 0, 2, 1], [3, 1, 0, 2], [3, 2, 1, 0]]

/-- The quaternion with coordinate `vals.getD i` at position `π i`. -/
def place (π vals : List ℕ) : List ℕ := (List.range 4).map fun k => vals.getD (π.idxOf k) 0

/-- The 120 icosians of norm one, as coordinate symbols `[w, x, y, z]` for `w + x i + y j + z k`: the units
`±1, ±i, ±j, ±k`, the elements `(±1 ± i ± j ± k)/2`, and the elements whose coordinates are an even permutation of
`(0, ±1/2, ±θ⁻¹/2, ±θ/2)`. -/
def icosians : List (List ℕ) :=
  ((List.range 4).flatMap fun p => [1, 2].map fun s => (List.range 4).map fun k => if k = p then s else 0) ++
  ([3, 4].flatMap fun a => [3, 4].flatMap fun b => [3, 4].flatMap fun c => [3, 4].map fun d => [a, b, c, d]) ++
  (evenPerms.flatMap fun π => [3, 4].flatMap fun s₁ => [5, 6].flatMap fun s₂ => [7, 8].map fun s₃ =>
    place π [0, s₁, s₂, s₃])

/-- `α = 1 + i + j`, of reduced norm 3. -/
def alpha : List ℕ := [1, 1, 1, 0]

/-- The splitting modulo 3: `w + x i + y j + z k ↦ w + x I + y J + z I J` with `I = (1 1; 1 −1)`,
`J = (0 1; −1 0)` over `𝔽₉`. -/
def red3 (q : List ℕ) : List ℕ :=
  let w := symF9 (q.getD 0 0); let x := symF9 (q.getD 1 0)
  let y := symF9 (q.getD 2 0); let z := symF9 (q.getD 3 0)
  [add (add w x) (neg z), add (add x y) z, add (add x (neg y)) z, add (add w (neg x)) z]

/-- The splitting modulo `λ₀`: `w + x i + y j + z k ↦ w + x I + y J + z I J` with `I = (1 3; 3 −1)`,
`J = (0 1; −1 0)` over `𝔽₁₁`. -/
def red11 (q : List ℕ) : List ℕ :=
  let w := symF11 (q.getD 0 0); let x := symF11 (q.getD 1 0)
  let y := symF11 (q.getD 2 0); let z := symF11 (q.getD 3 0)
  [(w + x + 8 * z) % 11, (3 * x + y + z) % 11, (3 * x + 10 * y + z) % 11, (w + 10 * x + 3 * z) % 11]

/-! ### Labels and blocks -/

/-- `M v` for a matrix over `𝔽₉`. -/
def mv (M v : List ℕ) : List ℕ :=
  [add (mul (M.getD 0 0) (v.getD 0 0)) (mul (M.getD 1 0) (v.getD 1 0)),
   add (mul (M.getD 2 0) (v.getD 0 0)) (mul (M.getD 3 0) (v.getD 1 0))]

/-- `p₀` spans the image and `k₀` the kernel of `red3 α` (`labels_ok` in `ConChecks.lean`). -/
def p0 : List ℕ := [(red3 alpha).getD 0 0, (red3 alpha).getD 2 0]
def k0 : List ℕ := [(red3 alpha).getD 1 0, neg ((red3 alpha).getD 0 0)]

/-- The ends of an edge and its positions there (from the certificate). -/
def ev (e : ℕ) : ℕ := edgeEven.getD e 0
def pos0 (e : ℕ) : ℕ := edgePos0.getD e 0
def od (e : ℕ) : ℕ := edgeOdd.getD e 0
def pos1 (e : ℕ) : ℕ := edgePos1.getD e 0

/-- The icosians labelling position `j` at an even and at an odd vertex. -/
def ico0 (j : ℕ) : List ℕ := icosians.getD (posRep0.getD j 0) []
def ico1 (j : ℕ) : List ℕ := icosians.getD (posRep1.getD j 0) []

/-- The labels of an edge at its even end and, twisted by Frobenius, at its odd end. -/
def label0 (e : ℕ) : List ℕ := mv (red3 (ico0 (pos0 e))) p0
def label1 (e : ℕ) : List ℕ := (mv (red3 (ico1 (pos1 e))) k0).map frob

/-- The quartic monomials `x^(4−a) y^a`, `a = 0, …, 4`, at `(x, y)`. -/
def mono (v : List ℕ) : List ℕ := (List.range 5).map fun a => mul (pow (v.getD 0 0) (4 - a)) (pow (v.getD 1 0) a)

/-- Entry `(a, b)` of the 10 × 10 block of edge `e` over `𝔽₃`: row `2 c + s`, column `2 r + t`, from the
coefficient `z = m₁(e)_r · m₀(e)_c ∈ 𝔽₉` and its block `(re z, im z; −im z, re z)`. -/
def blockNat (e a b : ℕ) : ℕ :=
  let z := mul ((mono (label1 e)).getD (b / 2) 0) ((mono (label0 e)).getD (a / 2) 0)
  if a % 2 = 0 then (if b % 2 = 0 then re z else im z)
  else (if b % 2 = 0 then (3 - im z) % 3 else re z)

/-- The edge joining even vertex `v` to odd vertex `w` (127 if none). -/
def edgeOfNat (v w : ℕ) : ℕ := ((List.range 110).find? fun e => ev e == v && od e == w).getD 127

/-- The edge joining even vertex `v` to odd vertex `w`, if any. -/
def edgeOf (v w : Fin 11) : Option (Fin 110) :=
  if h : edgeOfNat v w < 110 then some ⟨_, h⟩ else none

end Luck.Con
