import Transpose.Tape.MStarExcess

/-! Deleting visits from a finite ordered level set costs at most two pairs
per omitted visit. Successor uniqueness is reused from the original paper;
all finite-cardinality operations are from mathlib. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Transpose.Tape
open scoped ENNReal
set_option autoImplicit false

theorem consecIn_fst_unique {Λ : Set ℝ} {u v w : ℝ}
    (hu : ConsecIn Λ u w) (hv : ConsecIn Λ v w) : u=v := by
  rcases lt_trichotomy u v with h | h | h
  · exact False.elim (hu.2.2.2 v hv.1 ⟨h,hv.2.2.1⟩)
  · exact h
  · exact False.elim (hv.2.2.2 u hu.1 ⟨h,hu.2.2.1⟩)

theorem consecIn_restrict {Λ R : Set ℝ} {u v : ℝ}
    (h : ConsecIn Λ u v) (hu : u ∈ R) (hv : v ∈ R) :
    ConsecIn (Λ ∩ R) u v :=
  ⟨⟨h.1,hu⟩,⟨h.2.1,hv⟩,h.2.2.1,fun x hx => h.2.2.2 x hx.1⟩

theorem consecutive_pairs_delete_le {Λ : Set ℝ} (hΛ : Λ.Finite)
    (C : Set (ℝ × ℝ)) (hC : ∀ q ∈ C, ConsecIn Λ q.1 q.2) (R : Set ℝ) :
    C.ncard ≤ {q ∈ C | q.1 ∈ R ∧ q.2 ∈ R}.ncard + 2*(Λ \ R).ncard := by
  have hCf : C.Finite := (hΛ.prod hΛ).subset (fun q hq => ⟨(hC q hq).1,(hC q hq).2.1⟩)
  let G : Set (ℝ × ℝ) := {q ∈ C | q.1 ∈ R ∧ q.2 ∈ R}
  let A : Set (ℝ × ℝ) := {q ∈ C | q.1 ∉ R}
  let B : Set (ℝ × ℝ) := {q ∈ C | q.2 ∉ R}
  have hGf : G.Finite := hCf.subset (fun _ h => h.1)
  have hAf : A.Finite := hCf.subset (fun _ h => h.1)
  have hBf : B.Finite := hCf.subset (fun _ h => h.1)
  have hA : A.ncard ≤ (Λ \ R).ncard := by
    have hi : Set.InjOn Prod.fst A := by
      intro q hq q' hq' he
      exact Prod.ext he (Impl.consecIn_snd_unique (hC q hq.1) (he ▸ hC q' hq'.1))
    rw [← hi.ncard_image]
    apply Set.ncard_le_ncard _ (hΛ.subset Set.sdiff_subset)
    rintro _ ⟨q,hq,rfl⟩
    exact ⟨(hC q hq.1).1,hq.2⟩
  have hB : B.ncard ≤ (Λ \ R).ncard := by
    have hi : Set.InjOn Prod.snd B := by
      intro q hq q' hq' he
      exact Prod.ext (consecIn_fst_unique (hC q hq.1) (he ▸ hC q' hq'.1)) he
    rw [← hi.ncard_image]
    apply Set.ncard_le_ncard _ (hΛ.subset Set.sdiff_subset)
    rintro _ ⟨q,hq,rfl⟩
    exact ⟨(hC q hq.1).2.1,hq.2⟩
  have hcover : C ⊆ G ∪ (A ∪ B) := by
    intro q hq
    by_cases h1 : q.1 ∈ R
    · by_cases h2 : q.2 ∈ R
      · exact Or.inl ⟨hq,h1,h2⟩
      · exact Or.inr (Or.inr ⟨hq,h2⟩)
    · exact Or.inr (Or.inl ⟨hq,h1⟩)
  have hn := (Set.ncard_le_ncard hcover (hGf.union (hAf.union hBf))).trans
    ((Set.ncard_union_le G (A ∪ B)).trans (Nat.add_le_add_left (Set.ncard_union_le A B) G.ncard))
  change C.ncard ≤ G.ncard+2*(Λ \ R).ncard
  omega

theorem levelCross_delete_le (P : ℝ → ℝ) (β : ℝ → ℕ) (c₀ p : ℝ) (R : Set ℝ) :
    levelCross P ∅ β c₀ p ≤
      ({q ∈ crossPairs P ∅ β c₀ p | q.1 ∈ R ∧ q.2 ∈ R}.ncard : ℝ≥0∞) +
        2*((levelSet P c₀ p \ R).ncard : ℝ≥0∞) := by
  unfold levelCross
  split_ifs with hfin
  · exact_mod_cast consecutive_pairs_delete_le hfin (crossPairs P ∅ β c₀ p)
      (fun q hq => hq.1) R
  · exact zero_le

end TransposeFollowup.AffineMotion
