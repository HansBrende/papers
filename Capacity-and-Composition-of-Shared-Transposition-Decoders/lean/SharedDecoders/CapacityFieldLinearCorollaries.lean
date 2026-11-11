import SharedDecoders.CapacityFieldLinearResidual

/-! # One- and two-class bounds for the actual extension-linear residual -/

namespace SharedDecoders.CapacityFieldLinear

open Module CapacityIntervals

variable {d : ℕ} [NeZero d]

theorem representative_not_active {κ : Type*}
    (p : ZMod d → κ) (r : κ → ZMod d) (hr : ∀ j, p (r j)=j)
    (C : Submodule Bit (State d Bit))
    (hH : ScalarResidual (C ⊓ LinearMap.ker (classProjection (F := Bit) p r))) (j : κ) :
    r j ∉ activeRows (encodedResidual _ hH) := by
  rw [mem_activeRows]
  rintro ⟨X,hX,hn⟩
  have hz := (mem_classProjection_ker hr).mp hX.2 j
  have he := congrArg (rowEncode d) hz
  change scalarEncode (scalarEncode.symm X) (r j)=rowEncode d 0 at he
  rw [LinearEquiv.apply_symm_apply, map_zero] at he
  exact hn he

/-- In the one-class case the actual extension-linear residual vanishes,
not just its contribution to the source dimension bound. -/
theorem one_class_residual_eq_bot (C : Submodule Bit (State d Bit))
    (hC : IsLinearSharedCode (fun _ => ()) C) (r : Unit → ZMod d)
    (hH : ScalarResidual (C ⊓ LinearMap.ker (classProjection (F := Bit) (fun _ => ()) r))) :
    encodedResidual (C ⊓ LinearMap.ker (classProjection (F := Bit) (fun _ => ()) r)) hH = ⊥ := by
  obtain ⟨f, hf⟩ := hC
  have h := active_class_residual_bound (fun _ => ()) r (by intro j; cases j; rfl)
    _ hH inf_le_right ⟨f, fun X hX c => hf X hX.1 c⟩ ()
  simp only [Finset.filter_true] at h
  apply Submodule.finrank_eq_zero.mp
  omega

theorem one_class_original_bound (C : Submodule Bit (State d Bit))
    (hC : IsLinearSharedCode (fun _ => ()) C) (r : Unit → ZMod d)
    (hH : ScalarResidual (C ⊓ LinearMap.ker (classProjection (F := Bit) (fun _ => ()) r))) :
    finrank Bit C ≤ d := by
  have h := original_source_class_bound (fun _ => ()) r (by intro j; cases j; rfl) C hC hH ()
  simp only [Finset.filter_true, Fintype.card_unit, one_mul] at h
  omega

omit [NeZero d] in
theorem bool_filter_card_add (S : Finset (ZMod d)) (p : ZMod d → Bool) (j : Bool) :
    (S.filter (fun c => p c=j)).card + (S.filter (fun c => p c=(!j))).card = S.card := by
  simp only [Bool.eq_not_iff]
  exact Finset.card_filter_add_card_filter_not _

theorem two_class_original_bound (p : ZMod d → Bool) (r : Bool → ZMod d)
    (hr : ∀ j, p (r j)=j) (C : Submodule Bit (State d Bit))
    (hC : IsLinearSharedCode p C)
    (hH : ScalarResidual (C ⊓ LinearMap.ker (classProjection (F := Bit) p r))) (j : Bool) :
    finrank Bit C ≤ d * (1 + (Finset.univ.filter (fun c => p c=j)).card) := by
  classical
  let S := activeRows (encodedResidual _ hH)
  have hbound := original_source_class_bound p r hr C hC hH (!j)
  simp only [Fintype.card_bool] at hbound
  have hsum := bool_filter_card_add S p (!j)
  simp only [Bool.not_not] at hsum
  have hsub : S.filter (fun c => p c=j) ⊂ Finset.univ.filter (fun c => p c=j) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro c hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, (Finset.mem_filter.mp hc).2⟩
    · intro he
      have hin : r j ∈ S.filter (fun c => p c=j) := by
        rw [he]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr j⟩
      exact representative_not_active p r hr C hH j (Finset.mem_filter.mp hin).1
  have hcard := Finset.card_lt_card hsub
  have hmul := Nat.mul_le_mul_left d (show (S.filter (fun c => p c=j)).card+1 ≤
    (Finset.univ.filter (fun c => p c=j)).card by omega)
  dsimp [S] at hsum hmul
  nlinarith only [hbound, hsum, hmul]

theorem two_class_half_bound (p : ZMod d → Bool) (r : Bool → ZMod d)
    (hr : ∀ j, p (r j)=j) (C : Submodule Bit (State d Bit))
    (hC : IsLinearSharedCode p C)
    (hH : ScalarResidual (C ⊓ LinearMap.ker (classProjection (F := Bit) p r))) :
    2 * finrank Bit C ≤ d*d + 2*d := by
  have h₀ := two_class_original_bound p r hr C hC hH false
  have h₁ := two_class_original_bound p r hr C hC hH true
  have hsum := bool_filter_card_add Finset.univ p false
  simp only [Bool.not_false, Finset.card_univ, ZMod.card] at hsum
  nlinarith only [h₀,h₁,hsum]

end SharedDecoders.CapacityFieldLinear
