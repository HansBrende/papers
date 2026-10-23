import Mathlib

/-!
# Polymatroids with side information

A set function `h : Finset V → ℝ` is a polymatroid if it vanishes on `∅`, is
monotone, and is submodular. Side information is a map `N : V → Finset V`:
for a graph it sends a vertex to its neighbourhood, for a digraph to its
out-neighbourhood. A polymatroid is *valid* for `N` when adding `v` to `N v`
does not increase `h`. For the entropy of a storage code this says exactly that
the symbol at `v` is a function of the symbols on `N v`.

The *closure* lemmas below show that validity propagates: if every vertex of
`T \ S` has its side information inside `S`, then `h T = h S`.
-/

namespace MotionDepthCodes

open Finset
open scoped BigOperators
set_option autoImplicit false

variable {V : Type*} [DecidableEq V]

/-- A polymatroid on the ground set `V`, as a real set function. -/
structure IsPolymatroid (h : Finset V → ℝ) : Prop where
  empty : h ∅ = 0
  mono : Monotone h
  submod : ∀ A B, h (A ∪ B) + h (A ∩ B) ≤ h A + h B

/-- `h` is valid for the side information `N`: each `v` is determined by `N v`. -/
def IsValid (h : Finset V → ℝ) (N : V → Finset V) : Prop :=
  ∀ v, h (insert v (N v)) = h (N v)

namespace IsPolymatroid

variable {h : Finset V → ℝ}

theorem nonneg (hh : IsPolymatroid h) (A : Finset V) : 0 ≤ h A := by
  have h1 : h ∅ ≤ h A := hh.mono (Finset.empty_subset A)
  rwa [hh.empty] at h1

theorem union_le (hh : IsPolymatroid h) (A B : Finset V) : h (A ∪ B) ≤ h A + h B := by
  have h1 := hh.submod A B
  have h2 := hh.nonneg (A ∩ B)
  linarith

/-- Subadditivity over the elements of a finite set. -/
theorem le_sum_singleton (hh : IsPolymatroid h) (s : Finset V) :
    h s ≤ ∑ v ∈ s, h {v} := by
  induction s using Finset.induction_on with
  | empty => simp [hh.empty]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.insert_eq]
    have h1 := hh.union_le {a} s
    linarith

/-- The elemental Shannon inequality in the form used by certificates:
`h (A ∪ B) + h I ≤ h A + h B` whenever `I ⊆ A ∩ B`. -/
theorem elemental (hh : IsPolymatroid h) {A B U I : Finset V} (hU : A ∪ B = U)
    (hI : I ⊆ A ∩ B) : h U + h I ≤ h A + h B := by
  have h1 := hh.submod A B
  have h2 := hh.mono hI
  rw [hU] at h1
  linarith

/-- Diminishing returns: an element that adds nothing to `A` adds nothing to
any `B ⊇ A`. -/
theorem insert_eq_of_subset (hh : IsPolymatroid h) {A B : Finset V} {v : V}
    (hAB : A ⊆ B) (hA : h (insert v A) = h A) : h (insert v B) = h B := by
  apply le_antisymm
  · have h1 := hh.submod (insert v A) B
    rw [Finset.insert_union, Finset.union_eq_right.mpr hAB] at h1
    have h2 := hh.mono (Finset.subset_inter (Finset.subset_insert v A) hAB)
    linarith
  · exact hh.mono (Finset.subset_insert v B)

/-- One closure step: vertices of `T \ S` whose side information lies in `S`
add nothing. -/
theorem eq_of_closure (hh : IsPolymatroid h) {N : V → Finset V} (hv : IsValid h N)
    {S T : Finset V} (hST : S ⊆ T) (hcl : ∀ v ∈ T, v ∉ S → N v ⊆ S) : h T = h S := by
  have key : ∀ D : Finset V, (∀ v ∈ D, N v ⊆ S) → h (S ∪ D) = h S := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro _; simp
    | insert a D ha ih =>
      intro hD
      rw [Finset.union_insert]
      have hstep : h (insert a (S ∪ D)) = h (S ∪ D) :=
        hh.insert_eq_of_subset
          ((hD a (Finset.mem_insert_self a D)).trans Finset.subset_union_left) (hv a)
      rw [hstep]
      exact ih (fun v hvD => hD v (Finset.mem_insert_of_mem hvD))
  have h1 := key (T \ S) (by
    intro v hvTS
    rw [Finset.mem_sdiff] at hvTS
    exact hcl v hvTS.1 hvTS.2)
  rwa [Finset.union_sdiff_of_subset hST] at h1

end IsPolymatroid

/-! ## Rate bounds and homomorphisms (Theorem H) -/

variable [Fintype V]

/-- Every valid polymatroid satisfies `h V ≤ c · Σ_v h {v}`. For entropic
polymatroids of storage codes this bounds the rate by `c`. -/
def RateBound (N : V → Finset V) (c : ℝ) : Prop :=
  ∀ h : Finset V → ℝ, IsPolymatroid h → IsValid h N → h univ ≤ c * ∑ v, h {v}

/-- Rate bounds are monotone in the constant. -/
theorem RateBound.mono {N : V → Finset V} {c c' : ℝ} (h : RateBound N c) (hcc : c ≤ c') :
    RateBound N c' := by
  intro g hg hv
  have h1 := h g hg hv
  have h2 : 0 ≤ ∑ v, g {v} := Finset.sum_nonneg fun v _ => hg.nonneg {v}
  nlinarith

variable {W : Type*} [DecidableEq W]

/-- The push-forward of a set function along a vertex map:
`Z ↦ h (φ⁻¹ Z)`. -/
def pushRank (φ : V → W) (h : Finset V → ℝ) (Z : Finset W) : ℝ :=
  h (univ.filter fun v => φ v ∈ Z)

omit [DecidableEq V] in
theorem pushRank_univ [Fintype W] (φ : V → W) (h : Finset V → ℝ) :
    pushRank φ h univ = h univ := by
  simp [pushRank]

theorem IsPolymatroid.pushRank {h : Finset V → ℝ} (hh : IsPolymatroid h) (φ : V → W) :
    IsPolymatroid (MotionDepthCodes.pushRank φ h) where
  empty := by simp [MotionDepthCodes.pushRank, hh.empty]
  mono := by
    intro A B hAB
    apply hh.mono
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hAB hv
  submod := by
    intro A B
    have h1 := hh.submod (univ.filter fun v => φ v ∈ A) (univ.filter fun v => φ v ∈ B)
    have e1 : (univ.filter fun v => φ v ∈ A ∪ B) =
        (univ.filter fun v => φ v ∈ A) ∪ (univ.filter fun v => φ v ∈ B) := by
      ext v; simp
    have e2 : (univ.filter fun v => φ v ∈ A ∩ B) =
        (univ.filter fun v => φ v ∈ A) ∩ (univ.filter fun v => φ v ∈ B) := by
      ext v; simp
    simp only [MotionDepthCodes.pushRank, e1, e2]
    exact h1

/-- Validity is preserved by push-forward along a homomorphism of side
information. No looplessness or injectivity is needed. -/
theorem IsValid.pushRank {h : Finset V → ℝ} (hh : IsPolymatroid h)
    {NG : V → Finset V} {NT : W → Finset W} (hv : IsValid h NG) (φ : V → W)
    (hφ : ∀ u, ∀ w ∈ NG u, φ w ∈ NT (φ u)) :
    IsValid (MotionDepthCodes.pushRank φ h) NT := by
  intro t
  apply hh.eq_of_closure hv
  · intro v hv'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv' ⊢
    exact Finset.mem_insert_of_mem hv'
  · intro v hvT hvS w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hvT hvS ⊢
    rcases hvT with hvt | hvt
    · rw [← hvt]
      exact hφ v w hw
    · exact absurd hvt hvS

/-- The singleton values of the push-forward sum to at most those of `h`. -/
theorem sum_pushRank_singleton_le [Fintype W] {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (φ : V → W) : ∑ t, MotionDepthCodes.pushRank φ h {t} ≤ ∑ v, h {v} := by
  calc ∑ t, MotionDepthCodes.pushRank φ h {t}
      ≤ ∑ t, ∑ v ∈ univ.filter (fun v => φ v = t), h {v} := by
        apply Finset.sum_le_sum
        intro t _
        have e : (univ.filter fun v => φ v ∈ ({t} : Finset W)) =
            univ.filter (fun v => φ v = t) := by
          ext v; simp
        simp only [MotionDepthCodes.pushRank, e]
        exact hh.le_sum_singleton _
    _ = ∑ v, h {v} := Finset.sum_fiberwise univ φ (fun v => h {v})

/-- **Theorem H.** Rate bounds pull back along homomorphisms of side
information: if `φ` maps each `NG u` into `NT (φ u)`, every rate bound for
`NT` with `c ≥ 0` holds for `NG`. -/
theorem RateBound.of_hom [Fintype W] {NG : V → Finset V} {NT : W → Finset W} {c : ℝ}
    (hc : 0 ≤ c) (φ : V → W) (hφ : ∀ u, ∀ w ∈ NG u, φ w ∈ NT (φ u))
    (hT : RateBound NT c) : RateBound NG c := by
  intro h hh hv
  have h1 := hT (MotionDepthCodes.pushRank φ h) (hh.pushRank φ) (hv.pushRank hh φ hφ)
  rw [pushRank_univ] at h1
  have h2 := mul_le_mul_of_nonneg_left (sum_pushRank_singleton_le hh φ) hc
  linarith

/-! ## Graphs and digraphs -/

/-- The neighbourhood map of a simple graph. -/
def nbhd (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  univ.filter (G.Adj v)

/-- The out-neighbourhood map of a digraph. -/
def outNbhd (G : Digraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  univ.filter (G.Adj v)

/-- **Theorem H for graphs.** -/
theorem RateBound.of_graphHom [Fintype W] {G : SimpleGraph V} {T : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel T.Adj] {c : ℝ} (hc : 0 ≤ c) (φ : G →g T)
    (hT : RateBound (nbhd T) c) : RateBound (nbhd G) c := by
  apply RateBound.of_hom hc φ _ hT
  intro u w hw
  simp only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  exact φ.map_adj hw

/-- A graph is *good* if its neighbourhood map satisfies the rate bound `1/2`: every valid
polymatroid has `2 h(V) ≤ Σ_v h(v)`. -/
def IsGood (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  RateBound (nbhd G) (1 / 2)

/-- Goodness pulls back along homomorphisms (Theorem H with `c = 1/2`). -/
theorem IsGood.of_hom [Fintype W] {G : SimpleGraph V} {T : SimpleGraph W} [DecidableRel G.Adj]
    [DecidableRel T.Adj] (hT : IsGood T) (φ : G →g T) : IsGood G :=
  RateBound.of_graphHom (by norm_num) φ hT

/-- **Theorem H for digraphs** (index coding): `φ` maps arcs to arcs. -/
theorem RateBound.of_digraphHom [Fintype W] {G : Digraph V} {T : Digraph W}
    [DecidableRel G.Adj] [DecidableRel T.Adj] {c : ℝ} (hc : 0 ≤ c) (φ : V → W)
    (hφ : ∀ a b, G.Adj a b → T.Adj (φ a) (φ b))
    (hT : RateBound (outNbhd T) c) : RateBound (outNbhd G) c := by
  apply RateBound.of_hom hc φ _ hT
  intro u w hw
  simp only [outNbhd, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  exact hφ u w hw

end MotionDepthCodes
