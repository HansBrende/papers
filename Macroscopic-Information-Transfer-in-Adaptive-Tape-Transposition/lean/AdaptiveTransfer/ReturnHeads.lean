import AdaptiveTransfer.ReturnTail

/-! The headwise consequences of the original-run off-carrier tail.
Return counts are the literal completed native hop/excursion records. -/

namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting Finset
open scoped BigOperators

noncomputable def headReturns {k : ℕ} (y : Fin k → ℕ → ℤ) (h : Fin k) (T H : ℕ) :
    Finset (Fin k × ℕ × ℕ) := by
  classical
  exact (allHops y T).filter fun e => e.1 = h ∧
    ∃ u ∈ Ioo e.2.1 e.2.2, H < (y e.1 u - y e.1 e.2.1).natAbs

theorem offCarrierReturns_card_eq_sum {k : ℕ} (y : Fin k → ℕ → ℤ) (f : Fin k) (T H : ℕ) :
    (offCarrierReturns y f T H).card =
      ∑ h ∈ univ.erase f, (headReturns y h T H).card := by
  classical
  have hh := card_eq_sum_card_fiberwise (s := offCarrierReturns y f T H)
    (t := univ.erase f) (f := fun e => e.1) (fun _e he =>
      mem_erase.mpr ⟨(mem_filter.mp he).2.1, mem_univ _⟩)
  rw [hh]
  apply sum_congr rfl
  intro h hh
  congr 1
  ext e
  simp only [mem_filter, offCarrierReturns, headReturns]
  have hhf := (mem_erase.mp hh).1
  constructor
  · rintro ⟨⟨he, _hfree, hfar⟩, hhead⟩
    exact ⟨he, hhead, hfar⟩
  · rintro ⟨he, hhead, hfar⟩
    exact ⟨⟨he, hhead ▸ hhf, hfar⟩, hhead⟩

/-- If deleting any one head still leaves more than R returns, two distinct
heads each have more than R/(k-1) returns. -/
theorem two_large_head_counts {k : ℕ} (hk : 2 ≤ k) (count : Fin k → ℕ) (R : ℝ)
    (hoff : ∀ f : Fin k, R < ((∑ h ∈ univ.erase f, count h : ℕ) : ℝ)) :
    ∃ f g : Fin k, f ≠ g ∧ R / (k - 1 : ℕ) < (count f : ℝ) ∧
      R / (k - 1 : ℕ) < (count g : ℝ) := by
  classical
  have hne : (univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  obtain ⟨f, _hf, hmax⟩ := exists_max_image univ count hne
  have hex : ∃ g ∈ univ.erase f, R / (k - 1 : ℕ) < (count g : ℝ) := by
    by_contra h
    push Not at h
    have hsum : ((∑ g ∈ univ.erase f, count g : ℕ) : ℝ) ≤
        ((univ.erase f : Finset (Fin k)).card : ℝ) * (R / (k - 1 : ℕ)) := by
      rw [Nat.cast_sum]
      calc
        _ ≤ ∑ _g ∈ univ.erase f, R / (k - 1 : ℕ) := sum_le_sum fun g hg => h g hg
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    have hcard : (univ.erase f : Finset (Fin k)).card = k - 1 := by simp
    rw [hcard, mul_div_cancel₀ _ (by exact_mod_cast (show k - 1 ≠ 0 by omega))] at hsum
    exact (not_lt_of_ge hsum) (hoff f)
  obtain ⟨g, hg, hlarge⟩ := hex
  exact ⟨f, g, (mem_erase.mp hg).1.symm,
    hlarge.trans_le (by exact_mod_cast hmax g (mem_univ _)), hlarge⟩

theorem offCarrierReturns_eq_empty_of_one {k : ℕ} (hk : k = 1)
    (y : Fin k → ℕ → ℤ) (f : Fin k) (T H : ℕ) : offCarrierReturns y f T H = ∅ := by
  subst k
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  exact (mem_filter.mp he).2.1 (Subsingleton.elim _ _)

/-- Every timely correct input outside the bad set has two busy original
heads. Passing from the floor cutoff back to the real density is checked. -/
theorem native_two_return_heads {M : TM} {d b H : ℕ} {c γ : ℝ}
    (hk : 2 ≤ M.k) {X : Fin (d * d * b) → Bool}
    (hcorrect : TransposesInput M d b c X)
    (hgood : X ∉ nativeBadInputs M d b c H ⌊γ * (d * d * b : ℕ)⌋₊) :
    let y := (trace M (List.ofFn X)).work
    let T := (trace M (List.ofFn X)).haltTime
    ∃ f g : Fin M.k, f ≠ g ∧
      γ * (d * d * b : ℕ) / (M.k - 1 : ℕ) < ((headReturns y f T H).card : ℝ) ∧
      γ * (d * d * b : ℕ) / (M.k - 1 : ℕ) < ((headReturns y g T H).card : ℝ) := by
  classical
  apply two_large_head_counts hk (fun h => (headReturns (trace M (List.ofFn X)).work h
    (trace M (List.ofFn X)).haltTime H).card)
  intro f
  rw [← offCarrierReturns_card_eq_sum]
  have hnot : ¬ (offCarrierReturns (trace M (List.ofFn X)).work f
      (trace M (List.ofFn X)).haltTime H).card ≤ ⌊γ * (d * d * b : ℕ)⌋₊ := by
    intro h
    apply hgood
    exact mem_filter.mpr ⟨mem_univ _, hcorrect, f, h⟩
  have hh := Nat.lt_floor_add_one (γ * (d * d * b : ℕ))
  exact hh.trans_le (by exact_mod_cast (show ⌊γ * (d * d * b : ℕ)⌋₊ + 1 ≤
    (offCarrierReturns (trace M (List.ofFn X)).work f (trace M (List.ofFn X)).haltTime H).card by omega))

/-- With one work head, the bad set is the entire timely success set. -/
theorem native_one_head_bad {M : TM} {d b H J : ℕ} {c : ℝ} (hk : M.k = 1)
    {X : Fin (d * d * b) → Bool} (hcorrect : TransposesInput M d b c X) :
    X ∈ nativeBadInputs M d b c H J := by
  classical
  let f : Fin M.k := ⟨0, by omega⟩
  refine mem_filter.mpr ⟨mem_univ _, hcorrect, f, ?_⟩
  rw [offCarrierReturns_eq_empty_of_one hk, card_empty]
  exact Nat.zero_le _

end AdaptiveTransfer
