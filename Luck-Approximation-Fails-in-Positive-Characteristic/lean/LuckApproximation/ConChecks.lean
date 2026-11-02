import LuckApproximation.Construction
import LuckApproximation.Data
import Mathlib.Data.List.GetD

/-!
# Kernel checks of the construction: the coset graph, the tree and the labels

All checks are Boolean computations on natural numbers, evaluated by `decide +kernel`.

* **The splittings** (`splittings_ok`): `red3` and `red11` respect `i² = j² = −1` and `i j = −j i`.
* **The subgroups** (`subgroups_ok`): `±H₀` and `±H₁`, the images in `SL₂(𝔽₁₁)` of `2I` and `α 2I α⁻¹`, consist of
  matrices of determinant 1, and the product of any two of the 120 images lies in `±H₀` (resp. `±H₁`). The masks are
  closed under `negC` by construction, so `±H₀` and `±H₁` are subgroups.
* **The coset certificate** (`cosetGraph_ok`). With `±Hₑ = ±H₀ ∩ ±H₁`: the representatives lie in `SL₂(𝔽₁₁)`, and
  `α` is invertible modulo `λ₀` with the stated inverse; the cosets `g_v (±H₀)` are pairwise distinct and cover
  `SL₂(𝔽₁₁)`, and so do the cosets `h_w (±H₁)`; the ten position icosians at even vertices, and the conjugates by `α`
  of the ten position icosians at odd vertices, represent the ten cosets of `±Hₑ` in `±H₀` (resp. `±H₁`) once each;
  the ends and positions of the edges are in range, no two edges have the same ends, and the pairs (end, position)
  are distinct; and each edge is the same coset of `±Hₑ` seen from both ends:
  `(g_v u_j)⁻¹ (h_w α u'_{j'} α⁻¹) ∈ ±Hₑ`. With `subgroups_ok`, the enumeration is the coset graph.
* **The spanning tree** (`spanningTree_ok`): the 21 edges without a generator connect all 22 vertices, and the other
  89 edges carry distinct generators.
* **The labels** (`labels_ok`): `p₀ ≠ 0`, `k₀ ≠ 0` and `red3 α · k₀ = 0`; as `p₀` is a column of `red3 α`, it spans the
  image and `k₀` the kernel.
* The caches of `Data.lean` are checked against the construction in `ConCache.lean`.
-/

namespace Luck.Con

open Luck.ConData Luck.Data

/-! ### Matrices over `𝔽₁₁`, coded `a + 11 b + 121 c + 1331 d` for `(a b; c d)` -/

def e0 (X : ℕ) : ℕ := X % 11
def e1 (X : ℕ) : ℕ := X / 11 % 11
def e2 (X : ℕ) : ℕ := X / 121 % 11
def e3 (X : ℕ) : ℕ := X / 1331 % 11
def enc (a b c d : ℕ) : ℕ := a % 11 + 11 * (b % 11) + 121 * (c % 11) + 1331 * (d % 11)
def mulC (X Y : ℕ) : ℕ :=
  enc (e0 X * e0 Y + e1 X * e2 Y) (e0 X * e1 Y + e1 X * e3 Y) (e2 X * e0 Y + e3 X * e2 Y) (e2 X * e1 Y + e3 X * e3 Y)
/-- The adjugate, which is the inverse for determinant 1. -/
def adjC (X : ℕ) : ℕ := enc (e3 X) (11 - e1 X) (11 - e2 X) (e0 X)
def negC (X : ℕ) : ℕ := enc (11 - e0 X) (11 - e1 X) (11 - e2 X) (11 - e3 X)
def detC (X : ℕ) : ℕ := (e0 X * e3 X + 121 - e1 X * e2 X) % 11
/-- The identity matrix. -/
def idC : ℕ := enc 1 0 0 1
/-- A list `[a, b, c, d]` from `red11` as a code. -/
def ofList (M : List ℕ) : ℕ := enc (M.getD 0 0) (M.getD 1 0) (M.getD 2 0) (M.getD 3 0)

/-- `α` and `α⁻¹ = 3⁻¹ adj α` modulo `λ₀`, and conjugation by `α`. -/
def alphaL : ℕ := ofList (red11 alpha)
def alphaLinv : ℕ := enc (4 * e3 alphaL) (4 * (11 - e1 alphaL)) (4 * (11 - e2 alphaL)) (4 * e0 alphaL)
def conj (X : ℕ) : ℕ := mulC (mulC alphaL X) alphaLinv

/-- Subsets of `SL₂(𝔽₁₁)` as bit masks on codes: `±H₀`, `±H₁` and `±Hₑ = ±H₀ ∩ ±H₁`. -/
def H0mask : ℕ := icosians.foldl (fun acc q => acc ||| 2 ^ ofList (red11 q) ||| 2 ^ negC (ofList (red11 q))) 0
def H1mask : ℕ :=
  icosians.foldl (fun acc q => acc ||| 2 ^ conj (ofList (red11 q)) ||| 2 ^ negC (conj (ofList (red11 q)))) 0
def Hemask : ℕ := H0mask &&& H1mask
def mem (mask X : ℕ) : Bool := Nat.testBit mask X

/-- The coset representatives, and the images of the position icosians: `u_j` in `H₀` and `α u'_j α⁻¹` in `H₁`. -/
def g (v : ℕ) : ℕ := evenRep.getD v 0
def h (w : ℕ) : ℕ := oddRep.getD w 0
/-- The inverses of the representatives, computed once. -/
def gInvs : List ℕ := (List.range 11).map fun v => adjC (g v)
def hInvs : List ℕ := (List.range 11).map fun w => adjC (h w)
def gInv (v : ℕ) : ℕ := gInvs.getD v 0
def hInv (w : ℕ) : ℕ := hInvs.getD w 0
def u0 (j : ℕ) : ℕ := ofList (red11 (ico0 j))
def u1 (j : ℕ) : ℕ := conj (ofList (red11 (ico1 j)))

def allDistinct (xs : List ℕ) : Bool := xs.all fun x => xs.count x == 1

/-! ### The checks -/

/-- The splittings respect the quaternion relations: `I² = J² = −1` and `I J = −J I`, over `𝔽₉` and over `𝔽₁₁`. -/
def splittingsOK : Bool :=
  let I3 := red3 [0, 1, 0, 0]; let J3 := red3 [0, 0, 1, 0]
  let mm := fun (X Y : List ℕ) => [add (mul (X.getD 0 0) (Y.getD 0 0)) (mul (X.getD 1 0) (Y.getD 2 0)),
    add (mul (X.getD 0 0) (Y.getD 1 0)) (mul (X.getD 1 0) (Y.getD 3 0)),
    add (mul (X.getD 2 0) (Y.getD 0 0)) (mul (X.getD 3 0) (Y.getD 2 0)),
    add (mul (X.getD 2 0) (Y.getD 1 0)) (mul (X.getD 3 0) (Y.getD 3 0))]
  let I11 := ofList (red11 [0, 1, 0, 0]); let J11 := ofList (red11 [0, 0, 1, 0])
  mm I3 I3 == [2, 0, 0, 2] && mm J3 J3 == [2, 0, 0, 2] && mm I3 J3 == (mm J3 I3).map neg &&
  mulC I11 I11 == negC idC && mulC J11 J11 == negC idC && mulC I11 J11 == negC (mulC J11 I11)

theorem splittings_ok : splittingsOK = true := by decide +kernel

/-- The images of the 120 icosians in `SL₂(𝔽₁₁)`, and their conjugates by `α`. -/
def imgs0 : List ℕ := icosians.map fun q => ofList (red11 q)
def imgs1 : List ℕ := imgs0.map conj

/-- `±H₀` and `±H₁` consist of matrices of determinant `1` and contain the products of any two of the 120 images. -/
def subgroupsOK : Bool :=
  ((imgs0 ++ imgs1).all fun X => detC X == 1 && detC (negC X) == 1) &&
  (imgs0.all fun X => imgs0.all fun Y => mem H0mask (mulC X Y)) &&
  (imgs1.all fun X => imgs1.all fun Y => mem H1mask (mulC X Y))

theorem subgroups_ok : subgroupsOK = true := by decide +kernel

def cosetGraphOK : Bool :=
  -- representatives in `SL₂(𝔽₁₁)`, and `α` invertible with the stated inverse
  ((List.range 11).all fun v => detC (g v) == 1 && detC (h v) == 1) &&
  mulC alphaL alphaLinv == idC &&
  -- the cosets `g_v H₀` are pairwise distinct, and so are the cosets `h_w H₁`
  ((List.range 11).all fun v => (List.range 11).all fun w => v == w ||
    (!mem H0mask (mulC (gInv v) (g w)) && !mem H1mask (mulC (hInv v) (h w)))) &&
  -- every element of `SL₂(𝔽₁₁)` lies in some coset `g_v H₀` and in some coset `h_w H₁`
  ((List.range 14641).all fun M => detC M != 1 ||
    (((List.range 11).any fun v => mem H0mask (mulC (gInv v) M)) &&
     ((List.range 11).any fun w => mem H1mask (mulC (hInv w) M)))) &&
  -- the ten positions represent each coset of `Hₑ` in `H₀` (resp. `H₁`) exactly once
  (icosians.all fun q =>
    ((List.range 10).filter fun j => mem Hemask (mulC (adjC (u0 j)) (ofList (red11 q)))).length == 1 &&
    ((List.range 10).filter fun j => mem Hemask (mulC (adjC (u1 j)) (conj (ofList (red11 q))))).length == 1) &&
  -- the edges: ends and positions in range, the pairs (end, position) distinct, and both ends the same coset
  ((List.range 110).all fun e => ev e < 11 && pos0 e < 10 && od e < 11 && pos1 e < 10) &&
  allDistinct ((List.range 110).map fun e => 11 * ev e + od e) &&
  allDistinct ((List.range 110).map fun e => 10 * ev e + pos0 e) &&
  allDistinct ((List.range 110).map fun e => 10 * od e + pos1 e) &&
  ((List.range 110).all fun e => mem Hemask (mulC (adjC (mulC (g (ev e)) (u0 (pos0 e)))) (mulC (h (od e)) (u1 (pos1 e)))))

theorem cosetGraph_ok : cosetGraphOK = true := by decide +kernel

/-- One relaxation step of connectivity along the tree edges: every vertex takes the least label of its tree
neighbours. Vertices `0, …, 10` are even, `11, …, 21` odd. -/
def relax (lab : List ℕ) : List ℕ :=
  (List.range 110).foldl (fun l e =>
    if edgeGenNat e < 89 then l else
      let a := ev e; let b := 11 + od e; let m := min (l.getD a 0) (l.getD b 0)
      (l.set a m).set b m) lab

def spanningTreeOK : Bool :=
  ((List.range 110).filter fun e => 89 ≤ edgeGenNat e).length == 21 &&
  (Nat.iterate relax 22 (List.range 22)).all (· == 0) &&
  allDistinct (((List.range 110).filter fun e => edgeGenNat e < 89).map edgeGenNat)

theorem spanningTree_ok : spanningTreeOK = true := by decide +kernel

def labelsOK : Bool := p0 != [0, 0] && k0 != [0, 0] && mv (red3 alpha) k0 == [0, 0]

theorem labels_ok : labelsOK = true := by decide +kernel

end Luck.Con
