import AdaptiveTransfer.FragmentPrefixes
import AdaptiveTransfer.SlabGeometryAdapters

/-! Joint raw-extremum offsets for actual retained prefixes. Their total is
bounded by the total retained length, so the exact 2(s+1)-tuple menu applies. -/

namespace AdaptiveTransfer
open Finset BoundedNesting LeanMachine
open scoped BigOperators

noncomputable def intervalLo (x : ℕ → ℤ) (a n : ℕ) : ℤ :=
  if hn : 0 < n then ((Ico a (a + n)).image x).min'
    ⟨x a, mem_image.mpr ⟨a, mem_Ico.mpr ⟨le_rfl, by omega⟩, rfl⟩⟩ else x a

noncomputable def intervalHi (x : ℕ → ℤ) (a n : ℕ) : ℤ :=
  if hn : 0 < n then ((Ico a (a + n)).image x).max'
    ⟨x a, mem_image.mpr ⟨a, mem_Ico.mpr ⟨le_rfl, by omega⟩, rfl⟩⟩ else x a

noncomputable def intervalLeft (x : ℕ → ℤ) (a n : ℕ) : ℕ := (x a - intervalLo x a n).toNat
noncomputable def intervalRight (x : ℕ → ℤ) (a n : ℕ) : ℕ := (intervalHi x a n - x a).toNat

theorem intervalLo_le_entry (x : ℕ → ℤ) (a n : ℕ) : intervalLo x a n ≤ x a := by
  unfold intervalLo
  split_ifs with hn
  · exact min'_le _ _ (mem_image.mpr ⟨a, mem_Ico.mpr ⟨le_rfl, by omega⟩, rfl⟩)
  · exact le_rfl

theorem entry_le_intervalHi (x : ℕ → ℤ) (a n : ℕ) : x a ≤ intervalHi x a n := by
  unfold intervalHi
  split_ifs with hn
  · exact le_max' _ _ (mem_image.mpr ⟨a, mem_Ico.mpr ⟨le_rfl, by omega⟩, rfl⟩)
  · exact le_rfl

theorem intervalLo_from_offset (x : ℕ → ℤ) (a n : ℕ) :
    intervalLo x a n = x a - (intervalLeft x a n : ℤ) := by
  rw [intervalLeft, Int.toNat_of_nonneg (sub_nonneg.mpr (intervalLo_le_entry x a n))]
  ring

theorem intervalHi_from_offset (x : ℕ → ℤ) (a n : ℕ) :
    intervalHi x a n = x a + (intervalRight x a n : ℤ) := by
  rw [intervalRight, Int.toNat_of_nonneg (sub_nonneg.mpr (entry_le_intervalHi x a n))]
  ring

theorem interval_offset_budget {x : ℕ → ℤ} (hx : IsWalk x) (a n : ℕ) :
    intervalLeft x a n + intervalRight x a n ≤ n := by
  by_cases hn : 0 < n
  · have hlo : intervalLo x a n ∈ (Ico a (a + n)).image x := by
      simp only [intervalLo, dite_eq_left hn]
      exact min'_mem _ _
    have hhi : intervalHi x a n ∈ (Ico a (a + n)).image x := by
      simp only [intervalHi, dite_eq_left hn]
      exact max'_mem _ _
    obtain ⟨u, hu, heu⟩ := mem_image.mp hlo
    obtain ⟨v, hv, hev⟩ := mem_image.mp hhi
    have hspan : intervalHi x a n - intervalLo x a n ≤ (n : ℤ) := by
      rw [← heu, ← hev]
      rcases le_total u v with huv | hvu
      · have hh := (hx.lip huv).1
        have h₁ := mem_Ico.mp hu
        have h₂ := mem_Ico.mp hv
        omega
      · have hh := (hx.lip hvu).2
        have h₁ := mem_Ico.mp hu
        have h₂ := mem_Ico.mp hv
        omega
    have hl := intervalLo_from_offset x a n
    have hr := intervalHi_from_offset x a n
    omega
  · have hn0 : n = 0 := by omega
    simp [intervalLeft, intervalRight, intervalLo, intervalHi, hn0]

theorem interval_image_eq_extrema {x : ℕ → ℤ} (hx : IsWalk x) {a n : ℕ} (hn : 0 < n) :
    (Ico a (a + n)).image x = Icc (intervalLo x a n) (intervalHi x a n) := by
  simpa only [intervalLo, intervalHi, dite_eq_left hn] using
    walk_image_Ico_eq_Icc hx (show a < a + n by omega)

noncomputable def prefixOffset (B K : Finset ℕ) (x : ℕ → ℤ)
    (i : Fin 2 × cutGapStarts B) : ℕ :=
  if i.1.val = 0 then intervalLeft x i.2.val (gapPrefix B K i.2.val).card
    else intervalRight x i.2.val (gapPrefix B K i.2.val).card

theorem sum_prefixOffset_le (B K : Finset ℕ) {x : ℕ → ℤ} (hx : IsWalk x) :
    ∑ i : Fin 2 × cutGapStarts B, prefixOffset B K x i ≤ K.card := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [prefixOffset, Fin.val_zero, ite_true, Fin.val_one, one_ne_zero, ite_false]
  rw [← sum_add_distrib]
  calc
    _ ≤ ∑ a : cutGapStarts B, (gapPrefix B K a.val).card :=
      sum_le_sum fun a _ => interval_offset_budget hx a.val _
    _ = K.card := (sum_coe_sort (cutGapStarts B) _).trans (sum_gapPrefix_card B K)

noncomputable def prefixOffsetEquiv (B : Finset ℕ) :
    (Fin 2 × cutGapStarts B) ≃ Fin (2 * (B.card + 1)) :=
  Fintype.equivFinOfCardEq (by simp)

noncomputable def prefixExtremaDescription (B K : Finset ℕ) (T : ℕ)
    (hKT : ∀ t ∈ K, t < T) (x : ℕ → ℤ) (hx : IsWalk x) :
    BoundedTuple (2 * (B.card + 1)) T := by
  refine ⟨fun i => prefixOffset B K x ((prefixOffsetEquiv B).symm i), ?_⟩
  rw [(prefixOffsetEquiv B).symm.sum_comp]
  exact (sum_prefixOffset_le B K hx).trans
    ((card_le_card (fun t ht => mem_range.mpr (hKT t ht))).trans (card_range T).le)

theorem prefixExtrema_offsets_eq {B K : Finset ℕ} {T : ℕ}
    (hKT : ∀ t ∈ K, t < T) {x y : ℕ → ℤ} (hx : IsWalk x) (hy : IsWalk y)
    (he : prefixExtremaDescription B K T hKT x hx = prefixExtremaDescription B K T hKT y hy)
    (a : cutGapStarts B) :
    intervalLeft x a.val (gapPrefix B K a.val).card = intervalLeft y a.val (gapPrefix B K a.val).card ∧
    intervalRight x a.val (gapPrefix B K a.val).card = intervalRight y a.val (gapPrefix B K a.val).card := by
  have hh (i : Fin 2) := congrFun (congrArg Subtype.val he) (prefixOffsetEquiv B (i, a))
  constructor
  · simpa only [prefixExtremaDescription, Equiv.symm_apply_apply, prefixOffset,
      Fin.val_zero, ite_true] using hh 0
  · simpa only [prefixExtremaDescription, Equiv.symm_apply_apply, prefixOffset,
      Fin.val_one, one_ne_zero, ite_false] using hh 1

/-- Equal paid entry coordinates and the joint offset tuple recover the exact
raw cells visited in all retained prefixes. -/
theorem prefixExtrema_recovers_image {B K : Finset ℕ} {T : ℕ}
    (hclosed : StateClosedExcept K B) (hKT : ∀ t ∈ K, t < T)
    {x y : ℕ → ℤ} (hx : IsWalk x) (hy : IsWalk y)
    (hentry : ∀ a ∈ cutGapStarts B, x a = y a)
    (he : prefixExtremaDescription B K T hKT x hx = prefixExtremaDescription B K T hKT y hy) :
    K.image x = K.image y := by
  have hgap (a : cutGapStarts B) : (gapPrefix B K a.val).image x = (gapPrefix B K a.val).image y := by
    rcases (gapPrefix B K a.val).eq_empty_or_nonempty with hemp | hne
    · simp only [hemp, image_empty]
    · have hn : 0 < (gapPrefix B K a.val).card := hne.card_pos
      rw [gapPrefix_eq_Ico hclosed, interval_image_eq_extrema hx hn, interval_image_eq_extrema hy hn]
      have hoff := prefixExtrema_offsets_eq hKT hx hy he a
      rw [intervalLo_from_offset x, intervalLo_from_offset y,
        intervalHi_from_offset x, intervalHi_from_offset y, hentry a.val a.property, hoff.1, hoff.2]
  ext z
  constructor
  · intro hz
    obtain ⟨t, ht, hxt⟩ := mem_image.mp hz
    have hh : z ∈ (gapPrefix B K (cutGapStart B t)).image x :=
      mem_image.mpr ⟨t, mem_filter.mpr ⟨ht, rfl⟩, hxt⟩
    rw [hgap ⟨cutGapStart B t, cutGapStart_mem B t⟩] at hh
    obtain ⟨u, hu, hyu⟩ := mem_image.mp hh
    exact mem_image.mpr ⟨u, (mem_filter.mp hu).1, hyu⟩
  · intro hz
    obtain ⟨t, ht, hyt⟩ := mem_image.mp hz
    have hh : z ∈ (gapPrefix B K (cutGapStart B t)).image y :=
      mem_image.mpr ⟨t, mem_filter.mpr ⟨ht, rfl⟩, hyt⟩
    rw [← hgap ⟨cutGapStart B t, cutGapStart_mem B t⟩] at hh
    obtain ⟨u, hu, hxu⟩ := mem_image.mp hh
    exact mem_image.mpr ⟨u, (mem_filter.mp hu).1, hxu⟩

end AdaptiveTransfer
