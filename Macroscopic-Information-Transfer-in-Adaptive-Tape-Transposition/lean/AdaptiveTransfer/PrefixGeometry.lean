import AdaptiveTransfer.EnlargedGeometry

/-! Ordinary one-port, radius-zero geometry for prefix-assisted rules.
This retains the original 80/160 constants and adds no metadata field.
-/

namespace AdaptiveTransfer.Enlarged
open Transpose MergeDepth BoundedNesting NativeRelations Finset Getter

theorem one_port_bits_eq {P S : ℕ} (xs : Fin 1 → ℕ → ℤ) (hx : IsWalk (xs 0))
    {C : Finset ℕ} (hCS : ∀ t ∈ C, t < S) :
    portBits P xs C S 0 = inCells P (xs 0) C := by
  ext q
  rw [mem_portBits_iff]
  simp only [inCells, mem_filter, mem_univ, true_and]
  have he := rawExtent_eq_visited hx hCS
  change (q.val : ℤ) ∈ portExtent C _ _ 0 ↔
    (q.val : ℤ) ∈ {z | ∃ t ∈ C, xs 0 t = z}
  rw [← he]
  simp only [portExtent, rawExtent, Set.mem_ofPred_eq, Nat.cast_zero, sub_zero, add_zero]
  constructor
  · rintro ⟨r, hr, j, hj⟩
    have hzero : j = 0 := Subsingleton.elim _ _
    subst j
    exact ⟨r, hr, hj⟩
  · rintro ⟨r, hr, hj⟩
    exact ⟨r, hr, 0, hj⟩

theorem one_port_omitted_eq {d b S : ℕ} (xs : Fin 1 → ℕ → ℤ) (hx : IsWalk (xs 0))
    (ot : Fin (d * d * b) → ℕ) {C : Finset ℕ} (hCS : ∀ t ∈ C, t < S) :
    omittedPortBits xs ot C S 0 = omittedSlabBits d b (xs 0) ot C := by
  rw [omittedPortBits, omittedSlabBits, one_port_bits_eq xs hx hCS]

namespace System
variable {Q Γ : Type*} (M : System Q Γ Unit 1 1 0)

/-- The stronger prefix-assisted transition still has the original one-head
slab saving, obtained from its actual raw port and physical work walk. -/
theorem prefix_observation {d b a : ℕ} {c : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (ha : 1 ≤ a) (hP : 2 ≤ d * d * b) (hc : 1 ≤ c)
    {X : Fin (d * d * b) → Bool} {F : ℕ}
    (hF : F ≤ returnTime (d * d * b) c)
    (hout : (M.run () (List.ofFn X) F).outRev.reverse = List.ofFn (fun j => X (tposOf d b j)))
    (hsaving : 0 < slabSaving d b a c) :
    ∃ g : SlabObservation (M.motionTrace () (List.ofFn X)) (returnTime (d * d * b) c)
      (slabWidth (d * d * b) a c) (slabRunCap a c),
      g.finish ≤ F ∧ slabSaving d b a c ≤
        ((omittedPortBits (d := d) (b := b) (M.portPaths () (List.ofFn X))
          (fun j => appendTime (M.motionTrace () (List.ofFn X)) F j.val)
          g.times g.finish 0).card : ℝ) -
        (a : ℝ) * (if g.start = 0 then 0 else (slabWidth (d * d * b) a c : ℝ)) := by
  classical
  let τ := M.motionTrace () (List.ofFn X)
  let xs := M.portPaths () (List.ofFn X)
  have happ : (appendList τ F).length = d * d * b := by
    rw [M.trace_output_count, ← List.length_reverse, hout, List.length_ofFn]
  have htime : (F : ℝ) ≤ 2 * c * (d * d * b : ℕ) := by
    have hh : (returnTime (d * d * b) c : ℝ) ≤ c * ((d * d * b : ℕ) + 1) := Nat.floor_le (by positivity)
    have hf : (F : ℝ) ≤ returnTime (d * d * b) c := by exact_mod_cast hF
    have hp' : (1 : ℝ) ≤ (d * d * b : ℕ) := by exact_mod_cast (by omega : 1 ≤ d * d * b)
    nlinarith
  have hot : StrictMono (fun j : Fin (d * d * b) => appendTime τ F j.val) := by
    intro i j hij
    exact appendTime_strictMonoOn τ F
      (by simpa only [Set.mem_Iio, happ] using i.isLt)
      (by simpa only [Set.mem_Iio, happ] using j.isLt) hij
  obtain ⟨ell, s, e, hse, he, _, hruns, hmargin⟩ := exists_slab_geometry (a := (a : ℝ))
    hd hb hP (by exact_mod_cast ha) hc (M.portPaths_walk () (List.ofFn X) 0) (τ.work_isWalk 0) hot
    (fun j => appendTime_lt τ F (by simpa only [happ] using j.isLt)) htime
  let C := selectedSlab (τ.work 0) (slabWidth (d * d * b) a c) ell s e
  have hne : C.Nonempty := by
    by_contra hn
    have hemp := not_nonempty_iff_eq_empty.mp hn
    have hU : omittedSlabBits d b (xs 0) (fun j => appendTime τ F j.val) C = ∅ := by
      simp [omittedSlabBits, outIn, hemp]
    change slabSaving d b a c ≤ ((omittedSlabBits d b (xs 0) _ C).card : ℝ) - _ at hmargin
    rw [hU, card_empty, Nat.cast_zero] at hmargin
    have hcost : 0 ≤ (a : ℝ) * (if s = 0 then 0 else (slabWidth (d * d * b) a c : ℝ)) := by
      split_ifs <;> positivity
    linarith
  let g : SlabObservation τ (returnTime (d * d * b) c)
      (slabWidth (d * d * b) a c) (slabRunCap a c) := ⟨0, ell, s, e, hse, he.trans hF, hne, hruns⟩
  refine ⟨g, he, ?_⟩
  rw [one_port_omitted_eq _ (M.portPaths_walk () (List.ofFn X) 0) _ (fun _t ht => g.time_finish ht)]
  exact hmargin

end System
end AdaptiveTransfer.Enlarged
