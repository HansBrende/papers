import MergeDepth.Q91
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.ZMod.Basic

/-!
# Twisted quotients: descent of separated checks

The coordinates are a set `P` (in the paper, the edges of a tree) with an action of a group `Γ`. A
*check system* assigns to every coordinate `p` a finitely supported check `check p` with
`check p p = 1`, equivariantly, together with a *class* `cls : P → ZMod 2` that the group twists by
a character `χ`, such that every other coordinate in the support of `check p` lies in the other
class (*perfect separation*). A distance on the coordinates bounds the supports by a radius `R`.

For a subgroup `Γ'` the checks descend to the quotient `P/Γ'`, with recovery sets
`N(π p) = π (supp (check p) \ {p})` (`qrel`). Then:

* `isStorageCode_qrel`: every word annihilated by the descended checks is recovered, so such a code
  is a storage code for `qrel`;
* `card_qrel_le`, `card_in_qrel_le`: both incidence degrees are below the size of a ball of radius
  `R`;
* `le_mul_of_edist_le`: if the nontrivial elements of `Γ'` move every coordinate by at least `s`,
  every paired distance is at least `s / R`. A short paired path lifts to `P`, the class is constant
  along it in the signed sense, so its end differs from its start by an element of `Γ'` that swaps
  the classes, hence a nontrivial one, which moves coordinates by at least `s`;
* `symGraph`, `le_mul_of_odd_walk`, `degree_symGraph_le`, `isStorageCode_nbhd_symGraph`: the same
  argument for the symmetrized relation, a graph: every closed walk of odd length has length at least
  `s / R`, degrees are at most `2 (β - 1)`, and storage codes for `qrel` are storage codes for the
  neighbourhoods of the graph.
-/

namespace AboveHalf

open Finset DirectedRecovery MotionDepthCodes

set_option autoImplicit false

/-- A twisted check system on coordinates `P` with an action of `Γ`. -/
structure CheckSystem (P Γ 𝔽 : Type*) [Group Γ] [MulAction Γ P] [Field 𝔽] where
  /-- The check of each coordinate. -/
  check : P → P →₀ 𝔽
  /-- The class of each coordinate. -/
  cls : P → ZMod 2
  /-- The character by which the group twists the classes. -/
  χ : Γ → ZMod 2
  /-- A distance on coordinates. -/
  dist : P → P → ℕ
  /-- The radius of the checks. -/
  R : ℕ
  check_smul : ∀ (γ : Γ) (p x : P), check (γ • p) (γ • x) = check p x
  check_self : ∀ p, check p p = 1
  cls_smul : ∀ (γ : Γ) (p : P), cls (γ • p) = cls p + χ γ
  sep : ∀ p x, check p x ≠ 0 → x ≠ p → cls x ≠ cls p
  dist_self : ∀ x, dist x x = 0
  dist_comm : ∀ x y, dist x y = dist y x
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
  radius : ∀ p x, check p x ≠ 0 → dist p x ≤ R

variable {P Γ 𝔽 : Type*} [Group Γ] [MulAction Γ P] [Field 𝔽]

/-- The quotient of the coordinates by a subgroup. -/
abbrev Quo (Γ' : Subgroup Γ) (P : Type*) [MulAction Γ P] : Type _ :=
  MulAction.orbitRel.Quotient Γ' P

/-- The projection to the quotient. -/
abbrev proj (Γ' : Subgroup Γ) (p : P) : Quo Γ' P := Quotient.mk'' p

theorem proj_eq_iff {Γ' : Subgroup Γ} {x y : P} :
    proj Γ' x = proj Γ' y ↔ ∃ γ ∈ Γ', γ • y = x := by
  rw [Quotient.eq'']
  change x ∈ MulAction.orbit Γ' y ↔ _
  constructor
  · rintro ⟨γ, rfl⟩; exact ⟨γ, γ.2, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩; exact ⟨⟨γ, hγ⟩, rfl⟩

theorem proj_smul {Γ' : Subgroup Γ} {γ : Γ} (hγ : γ ∈ Γ') (x : P) :
    proj Γ' (γ • x) = proj Γ' x :=
  proj_eq_iff.2 ⟨γ, hγ, rfl⟩

namespace CheckSystem

variable (S : CheckSystem P Γ 𝔽)

theorem χ_one [Nonempty P] : S.χ 1 = 0 := by
  obtain ⟨p⟩ := ‹Nonempty P›
  have h := S.cls_smul 1 p
  rw [one_smul] at h
  have : S.cls p + S.χ 1 = S.cls p + 0 := by rw [← h, add_zero]
  exact add_left_cancel this

theorem check_smul_ne_zero_iff (γ : Γ) (p x : P) :
    S.check (γ • p) x ≠ 0 ↔ S.check p (γ⁻¹ • x) ≠ 0 := by
  rw [← S.check_smul γ p (γ⁻¹ • x), smul_inv_smul]

theorem mem_support_check_smul [DecidableEq P] (γ : Γ) (p x : P) :
    x ∈ (S.check (γ • p)).support ↔ γ⁻¹ • x ∈ (S.check p).support := by
  simp only [Finsupp.mem_support_iff]
  exact S.check_smul_ne_zero_iff γ p x

/-- In `ZMod 2`, two different classes differ by one. -/
theorem zmod_two_eq_add_one_of_ne {a b : ZMod 2} (h : a ≠ b) : a = b + 1 := by
  revert a b; decide

variable [DecidableEq P]

section Level

variable (Γ' : Subgroup Γ) [DecidableEq (Quo Γ' P)]

/-- The descended recovery relation: the recovery set of `π p` is the image of the other
coordinates in the support of `check p`. -/
noncomputable def qrel : Quo Γ' P → Finset (Quo Γ' P) :=
  Quotient.lift (fun p => ((S.check p).support.erase p).image (proj Γ'))
    (by
      rintro a b hab
      obtain ⟨γ, hγ, rfl⟩ := proj_eq_iff.1 (Quotient.sound hab : proj Γ' a = proj Γ' b)
      ext z
      simp only [Finset.mem_image, Finset.mem_erase]
      constructor
      · rintro ⟨y, ⟨hyne, hy⟩, rfl⟩
        refine ⟨γ⁻¹ • y, ⟨fun h => hyne (by rw [← h, smul_inv_smul]),
          (S.mem_support_check_smul γ b y).1 hy⟩, ?_⟩
        exact proj_smul (Subgroup.inv_mem _ hγ) y
      · rintro ⟨y, ⟨hyne, hy⟩, rfl⟩
        refine ⟨γ • y, ⟨fun h => hyne (smul_left_cancel γ h), ?_⟩, proj_smul hγ y⟩
        rw [S.mem_support_check_smul γ b, inv_smul_smul]
        exact hy)

theorem mem_qrel {p : P} {z : Quo Γ' P} :
    z ∈ S.qrel Γ' (proj Γ' p) ↔ ∃ y, S.check p y ≠ 0 ∧ y ≠ p ∧ proj Γ' y = z := by
  change z ∈ ((S.check p).support.erase p).image (proj Γ') ↔ _
  simp only [Finset.mem_image, Finset.mem_erase, Finsupp.mem_support_iff]
  constructor
  · rintro ⟨y, ⟨hne, hy⟩, rfl⟩; exact ⟨y, hy, hne, rfl⟩
  · rintro ⟨y, hy, hne, rfl⟩; exact ⟨y, ⟨hne, hy⟩, rfl⟩

variable {Γ'} {s : ℕ} (hdisp : ∀ γ ∈ Γ', γ ≠ 1 → ∀ p, s ≤ S.dist p (γ • p))
include hdisp

omit [DecidableEq (Quo Γ' P)] in
/-- Two coordinates with the same image and distance below the displacement are equal. -/
theorem eq_of_proj_eq_of_dist_lt {x y : P} (hxy : proj Γ' x = proj Γ' y)
    (hd : S.dist x y < s) : x = y := by
  obtain ⟨γ, hγ, rfl⟩ := proj_eq_iff.1 hxy
  by_contra hne
  have hγ1 : γ ≠ 1 := by rintro rfl; exact hne (one_smul _ _)
  have := hdisp γ hγ hγ1 y
  rw [S.dist_comm] at hd
  omega

/-- If the displacement exceeds the radius, the descended relation is irreflexive. -/
theorem proj_not_mem_qrel (hRs : S.R < s) (p : P) : proj Γ' p ∉ S.qrel Γ' (proj Γ' p) := by
  intro h
  obtain ⟨y, hy, hne, hyp⟩ := (S.mem_qrel Γ').1 h
  exact hne (S.eq_of_proj_eq_of_dist_lt hdisp hyp (lt_of_le_of_lt (by
    rw [S.dist_comm]; exact S.radius p y hy) hRs))

omit hdisp in
/-- **Storage.** Every word annihilated by all descended checks is a word of a storage code for
the descended relation: the symbol at `π p` is recovered from the symbols on its recovery set. -/
theorem isStorageCode_qrel (C : Finset (Quo Γ' P → 𝔽))
    (hC : ∀ c ∈ C, ∀ p, ∑ y ∈ (S.check p).support, S.check p y * c (proj Γ' y) = 0) :
    IsStorageCode (S.qrel Γ') C := by
  intro c₁ hc₁ c₂ hc₂ z hagree
  induction z using Quotient.inductionOn' with
  | h p =>
  have hp : p ∈ (S.check p).support := by
    rw [Finsupp.mem_support_iff, S.check_self]; exact one_ne_zero
  have e₁ := hC c₁ hc₁ p
  have e₂ := hC c₂ hc₂ p
  rw [← Finset.add_sum_erase _ _ hp, S.check_self, one_mul] at e₁ e₂
  have hrest : ∑ y ∈ (S.check p).support.erase p, S.check p y * c₁ (proj Γ' y) =
      ∑ y ∈ (S.check p).support.erase p, S.check p y * c₂ (proj Γ' y) := by
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨hne, hys⟩ := Finset.mem_erase.1 hy
    congr 1
    exact hagree _ ((S.mem_qrel Γ').2 ⟨y, Finsupp.mem_support_iff.1 hys, hne, rfl⟩)
  change c₁ (proj Γ' p) = c₂ (proj Γ' p)
  linear_combination e₁ - e₂ - hrest

omit hdisp in
/-- **Out-degree.** A recovery set is no larger than a ball of radius `R` minus its centre. -/
theorem card_qrel_le (ball : P → Finset P) (hball : ∀ p x, x ∈ ball p ↔ S.dist p x ≤ S.R)
    {β : ℕ} (hβ : ∀ p, (ball p).card ≤ β) (p : P) :
    (S.qrel Γ' (proj Γ' p)).card ≤ β - 1 := by
  change (((S.check p).support.erase p).image (proj Γ')).card ≤ β - 1
  refine Finset.card_image_le.trans ?_
  have hsub : (S.check p).support.erase p ⊆ (ball p).erase p := by
    intro x hx
    obtain ⟨hne, hxs⟩ := Finset.mem_erase.1 hx
    exact Finset.mem_erase.2 ⟨hne, (hball p x).2 (S.radius p x (Finsupp.mem_support_iff.1 hxs))⟩
  have hpb : p ∈ ball p := (hball p p).2 (by rw [S.dist_self]; exact Nat.zero_le _)
  calc ((S.check p).support.erase p).card ≤ ((ball p).erase p).card := Finset.card_le_card hsub
    _ = (ball p).card - 1 := Finset.card_erase_of_mem hpb
    _ ≤ β - 1 := Nat.sub_le_sub_right (hβ p) 1

omit hdisp in
/-- **In-degree.** A coordinate lies in at most `β - 1` recovery sets. -/
theorem card_in_qrel_le [Fintype (Quo Γ' P)] (ball : P → Finset P)
    (hball : ∀ p x, x ∈ ball p ↔ S.dist p x ≤ S.R)
    {β : ℕ} (hβ : ∀ p, (ball p).card ≤ β) (p : P) :
    (Finset.univ.filter (fun z => proj Γ' p ∈ S.qrel Γ' z)).card ≤ β - 1 := by
  classical
  -- every recovery set containing `π p` has a lift whose check involves `p`
  have hlift : ∀ z, ∃ q, proj Γ' p ∈ S.qrel Γ' z →
      proj Γ' q = z ∧ S.check q p ≠ 0 ∧ q ≠ p := by
    intro z
    by_cases hz : proj Γ' p ∈ S.qrel Γ' z
    swap
    · exact ⟨p, fun h => absurd h hz⟩
    suffices ∃ q, proj Γ' q = z ∧ S.check q p ≠ 0 ∧ q ≠ p by
      obtain ⟨q, hq⟩ := this; exact ⟨q, fun _ => hq⟩
    induction z using Quotient.inductionOn' with
    | h q₀ =>
    obtain ⟨y₀, hy₀, hne, hy₀p⟩ := (S.mem_qrel Γ').1 hz
    obtain ⟨γ, hγ, hγy⟩ := proj_eq_iff.1 hy₀p.symm
    refine ⟨γ • q₀, proj_smul hγ q₀, ?_, ?_⟩
    · rw [← hγy, S.check_smul]; exact hy₀
    · intro h; apply hne; rw [← hγy] at h; exact (smul_left_cancel γ h).symm
  choose f hf using hlift
  have hfproj : ∀ z, proj Γ' p ∈ S.qrel Γ' z → proj Γ' (f z) = z := fun z hz => (hf z hz).1
  have hfcheck : ∀ z, proj Γ' p ∈ S.qrel Γ' z → S.check (f z) p ≠ 0 := fun z hz => (hf z hz).2.1
  have hfne : ∀ z, proj Γ' p ∈ S.qrel Γ' z → f z ≠ p := fun z hz => (hf z hz).2.2
  have hinj : Set.InjOn f
      (↑(Finset.univ.filter (fun z => proj Γ' p ∈ S.qrel Γ' z)) : Set (Quo Γ' P)) := by
    intro z₁ hz₁ z₂ hz₂ h
    have h₁ := hfproj z₁ (Finset.mem_filter.1 hz₁).2
    have h₂ := hfproj z₂ (Finset.mem_filter.1 hz₂).2
    rw [← h₁, ← h₂, h]
  have hmaps : ∀ z ∈ Finset.univ.filter (fun z => proj Γ' p ∈ S.qrel Γ' z),
      f z ∈ (ball p).erase p := by
    intro z hz
    have hz' := (Finset.mem_filter.1 hz).2
    refine Finset.mem_erase.2 ⟨hfne z hz', (hball p _).2 ?_⟩
    rw [S.dist_comm]
    exact S.radius _ _ (hfcheck z hz')
  have hpb : p ∈ ball p := (hball p p).2 (by rw [S.dist_self]; exact Nat.zero_le _)
  calc (Finset.univ.filter (fun z => proj Γ' p ∈ S.qrel Γ' z)).card
      ≤ ((ball p).erase p).card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = (ball p).card - 1 := Finset.card_erase_of_mem hpb
    _ ≤ β - 1 := Nat.sub_le_sub_right (hβ p) 1

omit hdisp in
/-- Lifting one incidence step: a port over the start of an incidence edge of the descended relation
has a neighbour over its end, in the same signed class and within distance `R`. -/
theorem lift_step {u u' : Quo Γ' P ⊕ Quo Γ' P}
    (hadj : (pairedIncidenceGraph (S.qrel Γ')).Adj u u') (ut : P ⊕ P)
    (hut : Sum.map (proj Γ') (proj Γ') ut = u) :
    ∃ ut' : P ⊕ P, Sum.map (proj Γ') (proj Γ') ut' = u' ∧
      Sum.elim S.cls (fun q => S.cls q + 1) ut' = Sum.elim S.cls (fun q => S.cls q + 1) ut ∧
      S.dist (Sum.elim id id ut) (Sum.elim id id ut') ≤ S.R := by
  rcases ut with a | q <;> rcases u' with z' | z' <;> simp only [Sum.map_inl, Sum.map_inr] at hut <;>
    subst hut
  · exact absurd hadj (pairedIncidenceGraph_not_adj_left_left _ _ _)
  · -- from `inl a` to `inr z'`, with `π a ∈ N z'`
    induction z' using Quotient.inductionOn' with
    | h q₀ =>
    obtain ⟨y₀, hy₀, hne, hy₀a⟩ := (S.mem_qrel Γ').1 hadj
    obtain ⟨γ, hγ, hγy⟩ := proj_eq_iff.1 hy₀a.symm
    have hcheck : S.check (γ • q₀) a ≠ 0 := by rw [← hγy, S.check_smul]; exact hy₀
    have hne' : a ≠ γ • q₀ := by
      intro h; apply hne; rw [← hγy] at h; exact smul_left_cancel γ h
    refine ⟨Sum.inr (γ • q₀), by simp [proj_smul hγ], ?_, ?_⟩
    · simp only [Sum.elim_inl, Sum.elim_inr]
      exact (zmod_two_eq_add_one_of_ne (S.sep _ _ hcheck hne')).symm
    · simp only [Sum.elim_inl, Sum.elim_inr, id]
      rw [S.dist_comm]; exact S.radius _ _ hcheck
  · -- from `inr q` to `inl z'`, with `z' ∈ N (π q)`
    obtain ⟨y, hy, hne, rfl⟩ := (S.mem_qrel Γ').1 hadj
    refine ⟨Sum.inl y, rfl, ?_, ?_⟩
    · simp only [Sum.elim_inl, Sum.elim_inr]
      exact zmod_two_eq_add_one_of_ne (S.sep _ _ hy hne)
    · simp only [Sum.elim_inl, Sum.elim_inr, id]
      exact S.radius _ _ hy
  · exact absurd hadj (pairedIncidenceGraph_not_adj_right_right _ _ _)

omit hdisp in
/-- Lifting a walk of the descended incidence graph. -/
theorem lift_walk {u v : Quo Γ' P ⊕ Quo Γ' P}
    (w : (pairedIncidenceGraph (S.qrel Γ')).Walk u v) (ut : P ⊕ P)
    (hut : Sum.map (proj Γ') (proj Γ') ut = u) :
    ∃ vt : P ⊕ P, Sum.map (proj Γ') (proj Γ') vt = v ∧
      Sum.elim S.cls (fun q => S.cls q + 1) vt = Sum.elim S.cls (fun q => S.cls q + 1) ut ∧
      S.dist (Sum.elim id id ut) (Sum.elim id id vt) ≤ S.R * w.length := by
  induction w generalizing ut with
  | nil => exact ⟨ut, hut, rfl, by rw [S.dist_self]; exact Nat.zero_le _⟩
  | cons hadj w ih =>
    obtain ⟨ut', hut', hcls', hd'⟩ := S.lift_step hadj ut hut
    obtain ⟨vt, hvt, hcls, hd⟩ := ih ut' hut'
    refine ⟨vt, hvt, hcls.trans hcls', ?_⟩
    rw [SimpleGraph.Walk.length_cons]
    calc S.dist (Sum.elim id id ut) (Sum.elim id id vt)
        ≤ S.dist (Sum.elim id id ut) (Sum.elim id id ut') +
          S.dist (Sum.elim id id ut') (Sum.elim id id vt) := S.dist_triangle _ _ _
      _ ≤ S.R + S.R * w.length := add_le_add hd' hd
      _ = S.R * (w.length + 1) := by ring

/-- **Paired distances.** If the two ports of a coordinate of the descended relation are within
distance `K` in its paired incidence graph, then `s ≤ R K`. So every paired distance is at least
`s / R`, and no coordinate is short at a radius `K` with `R K < s`. -/
theorem le_mul_of_edist_le (z : Quo Γ' P) {K : ℕ}
    (hK : (pairedIncidenceGraph (S.qrel Γ')).edist (Sum.inl z) (Sum.inr z) ≤ K) :
    s ≤ S.R * K := by
  obtain ⟨n, hn, hnK⟩ := ENat.le_natCast_iff.1 hK
  obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hn
  induction z using Quotient.inductionOn' with
  | h a =>
  have : Nonempty P := ⟨a⟩
  obtain ⟨vt, hvt, hcls, hd⟩ := S.lift_walk w (Sum.inl a) rfl
  rcases vt with b | b
  · simp at hvt
  · simp only [Sum.map_inr, Sum.inr.injEq] at hvt
    obtain ⟨γ, hγ, hγa⟩ := proj_eq_iff.1 hvt
    simp only [Sum.elim_inl, Sum.elim_inr, id] at hcls hd
    rw [← hγa, S.cls_smul] at hcls
    have hχ : S.χ γ = 1 := by
      have key : ∀ x y : ZMod 2, x + y + 1 = x → y = 1 := by decide
      exact key _ _ hcls
    have hγ1 : γ ≠ 1 := by
      rintro rfl; rw [S.χ_one] at hχ; exact absurd hχ (by decide)
    have h1 := hdisp γ hγ hγ1 a
    rw [hγa] at h1
    calc s ≤ S.dist a b := h1
      _ ≤ S.R * w.length := hd
      _ ≤ S.R * K := Nat.mul_le_mul_left _ (hw ▸ hnK)

/-! ### The symmetrized relation -/

omit hdisp in
/-- In `ZMod 2`, `a = b + 1` if and only if `b = a + 1`. -/
theorem zmod_two_add_one_symm {a b : ZMod 2} (h : a = b + 1) : b = a + 1 := by
  revert a b; decide

variable (Γ')

/-- The symmetrized descended relation, as a simple graph: two different coordinates are adjacent
when one of them lies in the recovery set of the other. -/
def symGraph : SimpleGraph (Quo Γ' P) where
  Adj x y := x ≠ y ∧ (x ∈ S.qrel Γ' y ∨ y ∈ S.qrel Γ' x)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {Γ'}

omit hdisp in
/-- Lifting one step of the symmetrized relation flips the class and moves by at most `R`. -/
theorem lift_step_sym {x y : Quo Γ' P} (hxy : x ∈ S.qrel Γ' y ∨ y ∈ S.qrel Γ' x) (a : P)
    (ha : proj Γ' a = x) :
    ∃ b : P, proj Γ' b = y ∧ S.cls b = S.cls a + 1 ∧ S.dist a b ≤ S.R := by
  subst ha
  rcases hxy with h | h
  · induction y using Quotient.inductionOn' with
    | h q₀ =>
    obtain ⟨y₀, hy₀, hne, hy₀a⟩ := (S.mem_qrel Γ').1 h
    obtain ⟨γ, hγ, hγy⟩ := proj_eq_iff.1 hy₀a.symm
    have hcheck : S.check (γ • q₀) a ≠ 0 := by rw [← hγy, S.check_smul]; exact hy₀
    have hne' : a ≠ γ • q₀ := by
      intro h'; apply hne; rw [← hγy] at h'; exact smul_left_cancel γ h'
    refine ⟨γ • q₀, proj_smul hγ q₀, ?_, ?_⟩
    · exact zmod_two_add_one_symm (zmod_two_eq_add_one_of_ne (S.sep _ _ hcheck hne'))
    · rw [S.dist_comm]; exact S.radius _ _ hcheck
  · obtain ⟨b, hb, hne, rfl⟩ := (S.mem_qrel Γ').1 h
    exact ⟨b, rfl, zmod_two_eq_add_one_of_ne (S.sep _ _ hb hne), S.radius _ _ hb⟩

omit hdisp in
/-- Lifting a walk of the symmetrized graph: the class changes by the length of the walk. -/
theorem lift_walk_sym {x y : Quo Γ' P} (w : (S.symGraph Γ').Walk x y) (a : P)
    (ha : proj Γ' a = x) :
    ∃ b : P, proj Γ' b = y ∧ S.cls b = S.cls a + (w.length : ZMod 2) ∧
      S.dist a b ≤ S.R * w.length := by
  induction w generalizing a with
  | nil => exact ⟨a, ha, by simp, by rw [S.dist_self]; exact Nat.zero_le _⟩
  | cons hadj w ih =>
    obtain ⟨b', hb', hcls', hd'⟩ := S.lift_step_sym hadj.2 a ha
    obtain ⟨b, hb, hcls, hd⟩ := ih b' hb'
    refine ⟨b, hb, ?_, ?_⟩
    · rw [hcls, hcls', SimpleGraph.Walk.length_cons]
      push_cast
      ring
    · rw [SimpleGraph.Walk.length_cons]
      calc S.dist a b ≤ S.dist a b' + S.dist b' b := S.dist_triangle _ _ _
        _ ≤ S.R + S.R * w.length := add_le_add hd' hd
        _ = S.R * (w.length + 1) := by ring

/-- **Odd girth.** If the nontrivial elements of `Γ'` move every coordinate by at least `s`, every
closed walk of odd length in the symmetrized graph has length at least `s / R`. -/
theorem le_mul_of_odd_walk {x : Quo Γ' P} (w : (S.symGraph Γ').Walk x x) (hodd : Odd w.length) :
    s ≤ S.R * w.length := by
  induction x using Quotient.inductionOn' with
  | h a =>
  have : Nonempty P := ⟨a⟩
  obtain ⟨b, hb, hcls, hd⟩ := S.lift_walk_sym w a rfl
  obtain ⟨γ, hγ, hγa⟩ := proj_eq_iff.1 hb
  rw [← hγa, S.cls_smul, ZMod.natCast_eq_one_iff_odd.2 hodd] at hcls
  have hχ : S.χ γ = 1 := by
    have key : ∀ x y : ZMod 2, x + y = x + 1 → y = 1 := by decide
    exact key _ _ hcls
  have hγ1 : γ ≠ 1 := by
    rintro rfl; rw [S.χ_one] at hχ; exact absurd hχ (by decide)
  have h1 := hdisp γ hγ hγ1 a
  rw [hγa] at h1
  exact h1.trans hd

omit hdisp in
/-- Recovery-set sizes at every coordinate of the quotient. -/
theorem card_qrel_le_all (ball : P → Finset P) (hball : ∀ p x, x ∈ ball p ↔ S.dist p x ≤ S.R)
    {β : ℕ} (hβ : ∀ p, (ball p).card ≤ β) (x : Quo Γ' P) : (S.qrel Γ' x).card ≤ β - 1 := by
  induction x using Quotient.inductionOn' with
  | h p => exact S.card_qrel_le ball hball hβ p

omit hdisp in
/-- Reuse counts at every coordinate of the quotient. -/
theorem card_in_qrel_le_all [Fintype (Quo Γ' P)] (ball : P → Finset P)
    (hball : ∀ p x, x ∈ ball p ↔ S.dist p x ≤ S.R) {β : ℕ} (hβ : ∀ p, (ball p).card ≤ β)
    (x : Quo Γ' P) : (Finset.univ.filter (fun y => x ∈ S.qrel Γ' y)).card ≤ β - 1 := by
  induction x using Quotient.inductionOn' with
  | h p => exact S.card_in_qrel_le ball hball hβ p

omit hdisp in
/-- **Degrees of the symmetrized graph** are at most `2 (β - 1)`. -/
theorem degree_symGraph_le [Fintype (Quo Γ' P)] (ball : P → Finset P)
    (hball : ∀ p x, x ∈ ball p ↔ S.dist p x ≤ S.R) {β : ℕ} (hβ : ∀ p, (ball p).card ≤ β)
    (x : Quo Γ' P) [Fintype ((S.symGraph Γ').neighborSet x)] :
    (S.symGraph Γ').degree x ≤ 2 * (β - 1) := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : (S.symGraph Γ').neighborFinset x ⊆
      S.qrel Γ' x ∪ Finset.univ.filter (fun y => x ∈ S.qrel Γ' y) := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    rcases hy.2 with h | h
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_left _ h
  calc ((S.symGraph Γ').neighborFinset x).card
      ≤ (S.qrel Γ' x ∪ Finset.univ.filter (fun y => x ∈ S.qrel Γ' y)).card :=
        Finset.card_le_card hsub
    _ ≤ (S.qrel Γ' x).card + (Finset.univ.filter (fun y => x ∈ S.qrel Γ' y)).card :=
        Finset.card_union_le _ _
    _ ≤ (β - 1) + (β - 1) :=
        add_le_add (S.card_qrel_le_all ball hball hβ x) (S.card_in_qrel_le_all ball hball hβ x)
    _ = 2 * (β - 1) := (two_mul _).symm

/-- **Storage on the symmetrized graph.** If the displacement exceeds the radius, every storage
code for the descended relation is a storage code for the neighbourhoods of the symmetrized graph
(in the sense of the fourth paper's `MotionDepthCodes.nbhd`). -/
theorem isStorageCode_nbhd_symGraph [Fintype (Quo Γ' P)] [DecidableRel (S.symGraph Γ').Adj]
    (hRs : S.R < s) {α : Type*} {C : Finset (Quo Γ' P → α)} (hC : IsStorageCode (S.qrel Γ') C) :
    IsStorageCode (MotionDepthCodes.nbhd (S.symGraph Γ')) C := by
  intro c₁ h₁ c₂ h₂ x hagree
  refine hC c₁ h₁ c₂ h₂ x fun y hy => hagree y ?_
  simp only [MotionDepthCodes.nbhd, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, Or.inr hy⟩
  rintro rfl
  induction x using Quotient.inductionOn' with
  | h p => exact S.proj_not_mem_qrel hdisp hRs p hy

end Level

end CheckSystem

end AboveHalf
