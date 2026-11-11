import AdaptiveTransfer.NativeSlabCutEvent
import AdaptiveTransfer.UnrestrictedSlabClasses
import AdaptiveTransfer.LocalClassCounting

/-! Finite localized counting on original adaptive executions. Input-dependent
chunks are grouped only by their computed bounded slab metadata; each local
cut and its complete value are charged once by the exact local menu. -/

namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting NativeRelations Finset LeanMachine
open scoped BigOperators

theorem localCutMenu_pos (k β P T N r : ℕ) : 0 < localCutMenu k β P T N r := by
  have hh : localGeometryMenuSize k P T N 0 * 2 ^ (β * 0) ≤
      ∑ s ∈ range (min r T + 1), localGeometryMenuSize k P T N s * 2 ^ (β * s) :=
    single_le_sum (f := fun s => localGeometryMenuSize k P T N s * 2 ^ (β * s))
      (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.succ_pos _))
  have hp : 0 < localGeometryMenuSize k P T N 0 := by
    simp only [localGeometryMenuSize, Nat.choose_zero_right, pow_zero, mul_one]
    apply Nat.mul_pos
    · apply Nat.mul_pos
      · apply Nat.mul_pos
        · exact Nat.succ_pos _
        · exact Nat.choose_pos (by omega)
      · positivity
    · exact Nat.choose_pos (by omega)
  simp only [mul_zero, pow_zero, mul_one] at hh
  exact hp.trans_le hh

/-- Exact finite bound for an arbitrary set of timely correct native inputs,
each with any valid computed slab and an actual small original separator. -/
theorem native_slab_cut_union_bound {M : TM} {d b a q H r : ℕ} {c : ℝ}
    (hq : M.q + 1 ≤ 2 ^ q) (hA : M.g + 1 ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, TransposesInput M d b c X.val)
    (witness : ∀ X : D, NativeSlabCutWitness M d b a c H X.val)
    (hcut : ∀ X, (witness X).cut.card ≤ r) :
    (D.card : ℝ) ≤
      (replayMetadataSize M.k (returnTime (d * d * b) c)
        (slabWidth (d * d * b) a c) (slabRunCap a c) : ℝ) *
      ((2 : ℝ) ^ ((d * d * b : ℕ) - slabSaving d b a c +
          (slabRunCap a c : ℝ) * q + (a : ℝ) * (M.k - 1 : ℕ) *
            (slabRunCap a c : ℝ) * (2 * H + 1)) *
        (localCutMenu M.k (q + M.k * a + 2) (d * d * b)
          (returnTime (d * d * b) c) (slabRunCap a c) r : ℝ)) := by
  classical
  rcases D.eq_empty_or_nonempty with hD | hD
  · rw [hD, card_empty, Nat.cast_zero]
    positivity
  let P := d * d * b
  let T := returnTime P c
  let W := slabWidth P a c
  let N := slabRunCap a c
  let obs (X : D) := (witness X).slab.obs
  let X₀ : D := ⟨hD.choose, hD.choose_spec⟩
  let encoding (X : Fin P → Bool) : ReplayMetadata M.k T W N :=
    if hX : X ∈ D then (obs ⟨X, hX⟩).encode else (obs X₀).encode
  have henc (X : D) : encoding X.val = (obs X).encode := by
    simp only [encoding, dite_eq_left X.property]
  let cost : ℝ := (2 : ℝ) ^ ((P : ℝ) - slabSaving d b a c + (N : ℝ) * q +
    (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1)) *
      (localCutMenu M.k (q + M.k * a + 2) P T N r : ℝ)
  have hfibre (σ : ReplayMetadata M.k T W N) :
      ((D.filter fun X => encoding X = σ).card : ℝ) ≤ cost := by
    let F := D.filter fun X => encoding X = σ
    rcases F.eq_empty_or_nonempty with hF | hF
    · change (F.card : ℝ) ≤ cost
      rw [hF, card_empty, Nat.cast_zero]
      dsimp [cost]
      positivity
    let lift (X : F) : D := ⟨X.val, (mem_filter.mp X.property).1⟩
    let X₁ : F := ⟨hF.choose, hF.choose_spec⟩
    have hsame (X : F) : (obs (lift X)).encode = (obs (lift X₁)).encode := by
      rw [← henc (lift X), ← henc (lift X₁)]
      exact (mem_filter.mp X.property).2.trans (mem_filter.mp X₁.property).2.symm
    let G := unrestrictedSlabClass (H := H) F (fun X => correct (lift X)) (fun X => obs (lift X))
      (fun X => (witness (lift X)).slab.finish_le) X₁ hsame
    have hcompletion : G.Completion := unrestrictedSlabCompletion F (fun X => correct (lift X))
      (fun X => obs (lift X)) (fun X => (witness (lift X)).slab.finish_le) X₁ hsame
      (fun X => (timely_native_data (correct (lift X))).1)
    have hN : (runStarts G.times).card ≤ N := (obs (lift X₁)).run_cap
    let cuts (X : G.inputs) : G.LocalCut X := {
      cut := (witness (lift X)).cut
      cut_lt := (witness (lift X)).cut_lt
      separates := by
        have ho := unrestrictedSlabClass_omitted (H := H) F (fun X => correct (lift X))
          (fun X => obs (lift X)) (fun X => (witness (lift X)).slab.finish_le) X₁ hsame X
        have hf : G.free = (obs (lift X)).free :=
          (SlabObservation.free_eq_of_encode_eq (hsame X)).symm
        change IsMengerVertexCut _ _ (nativeDemandedOutputSteps _ _ _ _ G.omitted)
          (offCarrierLowerEndpoints _ G.free _ H) _
        rw [ho, hf]
        exact (witness (lift X)).separates }
    have hsave : slabSaving d b a c ≤ (G.omitted.card : ℝ) -
        (a : ℝ) * (if G.start = 0 then 0 else (G.cells.card : ℝ)) := by
      have ho := unrestrictedSlabClass_omitted (H := H) F (fun X => correct (lift X))
        (fun X => obs (lift X)) (fun X => (witness (lift X)).slab.finish_le) X₁ hsame X₁
      rw [ho]
      simpa only [G, unrestrictedSlabClass, constantSlabClass, integerSlab_card]
        using (witness (lift X₁)).slab.margin
    exact G.local_saving_card_bound hcompletion N r hN cuts (fun X => hcut (lift X)) q a hq hA _ hsave
  have hcard : D.card = ∑ σ : ReplayMetadata M.k T W N, (D.filter fun X => encoding X = σ).card :=
    card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  have hsum : (D.card : ℝ) ≤ (replayMetadataSize M.k T W N : ℝ) * cost := by
    rw [hcard, Nat.cast_sum]
    calc
      _ ≤ ∑ _σ : ReplayMetadata M.k T W N, cost := sum_le_sum (fun σ _ => hfibre σ)
      _ = _ := by simp only [sum_const, card_univ, replayMetadata_card, nsmul_eq_mul]
  exact hsum

/-- The actual bad event includes every input-dependent valid slab and cut.
No head, chunk, target set, or detailed trace is fixed across inputs. -/
theorem native_bad_slab_cut_bound {M : TM} {d b a q H r : ℕ} {c : ℝ}
    (hq : M.q + 1 ≤ 2 ^ q) (hA : M.g + 1 ≤ 2 ^ a) :
    ((nativeBadSlabCuts M d b a c H r).card : ℝ) ≤
      (replayMetadataSize M.k (returnTime (d * d * b) c)
        (slabWidth (d * d * b) a c) (slabRunCap a c) : ℝ) *
      ((2 : ℝ) ^ ((d * d * b : ℕ) - slabSaving d b a c +
          (slabRunCap a c : ℝ) * q + (a : ℝ) * (M.k - 1 : ℕ) *
            (slabRunCap a c : ℝ) * (2 * H + 1)) *
        (localCutMenu M.k (q + M.k * a + 2) (d * d * b)
          (returnTime (d * d * b) c) (slabRunCap a c) r : ℝ)) := by
  classical
  let D := nativeBadSlabCuts M d b a c H r
  have hD (X : D) : TransposesInput M d b c X.val ∧
      ∃ w : NativeSlabCutWitness M d b a c H X.val, w.cut.card ≤ r :=
    (mem_filter.mp X.property).2
  exact native_slab_cut_union_bound hq hA D (fun X => (hD X).1)
    (fun X => (hD X).2.choose) (fun X => (hD X).2.choose_spec)

end AdaptiveTransfer
