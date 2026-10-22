import TransposeFollowup.EntropyFibers
import TransposeFollowup.RefinedPrefix

/-! The two mass bounds in leaf aggregation: disjoint fibers and prefix codes.
Labels are distinct helper/code pairs. No independence is required. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

theorem sum_fiberCard_le {Ω L A : Type*} [Fintype Ω] [Fintype L]
    (f : Ω → A) (code : L → A) (hinj : Function.Injective code) :
    (∑ l, fiberCard f (code l)) ≤ Fintype.card Ω := by
  classical
  have hsum : (∑ l, fiberCard f (code l)) =
      ∑ a ∈ Finset.univ.image code, fiberCard f a := by
    symm
    apply Finset.sum_image
    intro x _ y _ h
    exact hinj h
  rw [hsum]
  exact (Finset.sum_card_fiberwise_eq_card_filter Finset.univ (Finset.univ.image code) f).trans_le
    (Finset.card_filter_le _ _)

open Classical in
noncomputable def keyFiber {L H A : Type*} [Fintype L]
    (key : L → H × A) (h : H) : Finset L :=
  Finset.univ.filter (fun l => (key l).1 = h)

theorem keyFiber_second_injective {L H A : Type*} [Fintype L]
    (key : L → H × A) (hinj : Function.Injective key) (h : H) :
    Function.Injective (fun l : keyFiber key h => (key l.val).2) := by
  classical
  intro x y hxy
  apply Subtype.ext
  apply hinj
  apply Prod.ext
  · exact ((Finset.mem_filter.mp x.property).2).trans ((Finset.mem_filter.mp y.property).2).symm
  · exact hxy

theorem pushforward_key_fst {L H A : Type*} [Fintype L]
    (key : L → H × A) (q : L → ℝ) (h : H) :
    pushforward q (fun l => (key l).1) h = ∑ l : keyFiber key h, q l.val := by
  classical
  unfold pushforward
  rw [← Finset.sum_filter]
  exact (Finset.sum_coe_sort (keyFiber key h) q).symm

/-- Full virtual fibers indexed by distinct helper/code labels have total
volume at most the whole input space, separately for each helper. -/
theorem conditional_fiber_budget {Ω L H A : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype L]
    (key : L → H × A) (hinj : Function.Injective key) (f : H → Ω → A) (h : H) :
    pushforward (fun l => (fiberCard (f (key l).1) (key l).2 : ℝ) / Fintype.card Ω)
      (fun l => (key l).1) h ≤ 1 := by
  classical
  have hN : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [pushforward_key_fst key, ← Finset.sum_div]
  apply (div_le_one hN).mpr
  have hsum : (∑ l : keyFiber key h, (fiberCard (f (key l.val).1) (key l.val).2 : ℝ)) =
      ∑ l : keyFiber key h, (fiberCard (f h) (key l.val).2 : ℝ) := by
    apply Finset.sum_congr rfl
    intro l _
    rw [(Finset.mem_filter.mp l.property).2]
  rw [hsum]
  exact_mod_cast sum_fiberCard_le (f h) _ (keyFiber_second_injective key hinj h)

/-- Distinct helper/code labels inherit a conditional Kraft budget from
the virtual code, including zero-length transcripts. -/
theorem conditional_prefix_budget {Ω L H : Type*} [Fintype L]
    (key : L → H × List Bool) (hinj : Function.Injective key)
    (code : H → Ω → List Bool)
    (hprefix : ∀ h, InformationTheory.IsPrefixFree (Set.range (code h)))
    (hreal : ∀ l, (key l).2 ∈ Set.range (code (key l).1)) (h : H) :
    pushforward (fun l => (1 / 2 : ℝ) ^ (key l).2.length) (fun l => (key l).1) h ≤ 1 := by
  classical
  rw [pushforward_key_fst key]
  apply kraft_indexed (fun l : keyFiber key h => (key l.val).2)
    (keyFiber_second_injective key hinj h)
  apply (hprefix h).anti
  rintro w ⟨l, rfl⟩
  have hmem := hreal l.val
  rwa [(Finset.mem_filter.mp l.property).2] at hmem

end TransposeFollowup
