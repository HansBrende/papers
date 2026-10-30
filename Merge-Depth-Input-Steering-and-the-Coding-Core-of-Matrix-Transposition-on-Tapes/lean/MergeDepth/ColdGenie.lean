import MergeDepth.Paths
import BoundedNesting.OwnerLoad

/-!
# The cold genie (Lemma 3.1)

The dependency DAG of work-head walks `xs` on `[0, T)` has the state edges `a → a - 1` and an edge
`a → b` for every long hop `(b, a)` of a head (`DepStep`). A step is *deep* if it is a long hop, of some
head, at a pair entered more than `V` times (`DeepStep`: a hop of `allHops` outside the eighth paper's
`lightHops`).

`cold_genie`: for `ε > 0` and `P ≥ 1` there is a set `Γ` of at most `εT + T/P` steps such that every
`Γ`-free path of the dependency DAG without deep steps has at most `DF k (2V - 1) ε ⋅ P` vertices. The
genie reveals the heads of the edges of Theorem F's cut of the light hops (the eighth paper's
`theoremF_owner`, at owner-load `2V - 1`), and every step `≡ P - 1 (mod P)`; a path then has fewer than
`DF k (2V - 1) ε` hop steps, and runs of state steps of fewer than `P` steps between them.

`card_allHops_le`: there are at most `kT` long hops, since a hop of a head is determined by its end.
-/

namespace MergeDepth

open Finset BoundedNesting

variable {k : ℕ}

/-- A step of the dependency DAG: a state edge `a → a - 1` below `T`, or a long hop `(b, a)`. -/
def DepStep (xs : Fin k → ℕ → ℤ) (T : ℕ) (a b : ℕ) : Prop :=
  (b + 1 = a ∧ a < T) ∨ (b, a) ∈ hopPairs (allHops xs T)

/-- A deep step: a long hop of some head at a pair entered more than `V` times. -/
def DeepStep (xs : Fin k → ℕ → ℤ) (T V : ℕ) (a b : ℕ) : Prop :=
  ∃ η ∈ allHops xs T, η.2 = (b, a) ∧ η ∉ lightHops xs T V

/-- Paths of the dependency DAG, as lists of steps. -/
def IsDepPath (xs : Fin k → ℕ → ℤ) (T : ℕ) : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: π => DepStep xs T a b ∧ IsDepPath xs T (b :: π)

/-- A hop of a head is determined by its end, so there are at most `kT` long hops. -/
theorem card_allHops_le (xs : Fin k → ℕ → ℤ) (T : ℕ) : (allHops xs T).card ≤ k * T := by
  classical
  have hinj : Set.InjOn (fun η : Fin k × ℕ × ℕ => (η.1, η.2.2)) (allHops xs T) := by
    intro η hη η' hη' he
    simp only [Prod.mk.injEq] at he
    obtain ⟨hh, hu⟩ := he
    have h1 := mem_allHops.mp hη
    have h2 := mem_allHops.mp hη'
    rw [hh] at h1
    have hc : xs η'.1 η.2.1 = xs η'.1 η'.2.1 := by rw [← h1.2.2.1, ← h2.2.2.1, hu]
    obtain ⟨hp, -⟩ := hop_unique h1 h2 hc ⟨by have := h1.1; omega, le_rfl⟩
      ⟨by have := h2.1; omega, by rw [hu]⟩
    exact Prod.ext hh (Prod.ext hp hu)
  calc (allHops xs T).card = ((allHops xs T).image fun η => (η.1, η.2.2)).card :=
        (card_image_of_injOn hinj).symm
    _ ≤ (univ ×ˢ range T).card := card_le_card fun e he => by
        obtain ⟨η, hη, rfl⟩ := mem_image.mp he
        exact mem_product.mpr ⟨mem_univ _, mem_range.mpr (mem_allHops.mp hη).2.1⟩
    _ = k * T := by simp

/-- The number of hop steps of a path. -/
def hopCount : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: π => (if b + 1 = a then 0 else 1) + hopCount (b :: π)

/-- The periodic reveals: the steps below `T` that are `≡ P - 1 (mod P)`. -/
def periodic (T P : ℕ) : Finset ℕ := (range T).filter fun t => t % P = P - 1

theorem card_periodic_le (T P : ℕ) (hP : 1 ≤ P) : P * (periodic T P).card ≤ T := by
  classical
  -- the map `t ↦ t / P` is injective on the periodic steps, into `range (T / P)`
  have hinj : Set.InjOn (fun t => t / P) (periodic T P) := by
    intro t ht t' ht' he
    have h1 := (mem_filter.mp ht).2
    have h2 := (mem_filter.mp ht').2
    simp only at he
    rw [← Nat.div_add_mod t P, ← Nat.div_add_mod t' P, he, h1, h2]
  have hsub : (periodic T P).image (fun t => t / P) ⊆ range (T / P) := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
    obtain ⟨htT, hmod⟩ := mem_filter.mp ht
    rw [mem_range] at htT ⊢
    have h1 := Nat.div_add_mod t P
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega)]
    calc (t / P + 1) * P = P * (t / P) + P := by ring
      _ ≤ T := by omega
  calc P * (periodic T P).card = P * ((periodic T P).image fun t => t / P).card := by
        rw [card_image_of_injOn hinj]
    _ ≤ P * (T / P) := Nat.mul_le_mul_left _ ((card_le_card hsub).trans (by simp))
    _ ≤ T := Nat.mul_div_le T P

/-- Among `P` consecutive numbers one is `≡ P - 1 (mod P)`. -/
theorem exists_periodic (a P : ℕ) (hP : 1 ≤ P) : ∃ i < P, (a + i) % P = P - 1 := by
  refine ⟨(P - 1 + P - a % P) % P, Nat.mod_lt _ (by omega), ?_⟩
  have ha := Nat.mod_lt a (show 0 < P by omega)
  have e : a % P + (P - 1 + P - a % P) = P - 1 + P := by omega
  rw [Nat.add_mod_mod, ← Nat.mod_add_mod, e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- A path of state steps descends one step at a time. -/
theorem state_path_eq (xs : Fin k → ℕ → ℤ) (T : ℕ) :
    ∀ (π : List ℕ) (t : ℕ), IsDepPath xs T (t :: π) → hopCount (t :: π) = 0 →
      π.length ≤ t ∧ ∀ i, 1 ≤ i → i ≤ π.length → t - i ∈ π ∧ (π ≠ [] → t < T)
  | [], t, _, _ => ⟨Nat.zero_le _, fun i h1 h2 => by simp at h2; omega⟩
  | b :: π, t, hp, hc => by
    obtain ⟨hstep, hp'⟩ := hp
    have hb : b + 1 = t := by
      by_contra hne
      simp [hopCount, hne] at hc
    have hc' : hopCount (b :: π) = 0 := by simpa [hopCount, hb] using hc
    have hT : t < T := by
      rcases hstep with ⟨-, h⟩ | h
      · exact h
      · obtain ⟨η, hη, he⟩ := mem_image.mp h
        have := (mem_allHops.mp hη).2.1
        simp only [Prod.mk.injEq] at he
        omega
    obtain ⟨hlen, hmem⟩ := state_path_eq xs T π b hp' hc'
    refine ⟨by simp; omega, fun i h1 h2 => ⟨?_, fun _ => hT⟩⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rw [show t - 1 = b by omega]; exact List.mem_cons_self ..
    · have := (hmem (i - 1) (by omega) (by simp at h2; omega)).1
      rw [show t - i = b - (i - 1) by omega]
      exact List.mem_cons_of_mem _ this

/-- **Runs of state steps.** A path of state steps whose vertices after the first avoid the periodic
reveals has at most `P` vertices. -/
theorem state_run_le (xs : Fin k → ℕ → ℤ) (T : ℕ) {P : ℕ} (hP : 1 ≤ P) (π : List ℕ) (t : ℕ)
    (hp : IsDepPath xs T (t :: π)) (hc : hopCount (t :: π) = 0)
    (hfree : ∀ v ∈ π, v ∉ periodic T P) : (t :: π).length ≤ P := by
  obtain ⟨hlen, hmem⟩ := state_path_eq xs T π t hp hc
  by_contra hcon
  push Not at hcon
  simp only [List.length_cons] at hcon
  have hne : π ≠ [] := by rintro rfl; simp at hcon; omega
  obtain ⟨i, hi, hmod⟩ := exists_periodic (t - P) P hP
  have hv := hmem (P - i) (by omega) (by omega)
  have heq : t - (P - i) = t - P + i := by omega
  rw [heq] at hv
  exact hfree _ hv.1 (mem_filter.mpr ⟨mem_range.mpr (by have := hv.2 hne; omega), hmod⟩)

/-- Paths with `h` hop steps whose vertices after the first avoid the periodic reveals have at most
`(h + 1) P` vertices; `a` counts the state steps already taken before the first vertex. -/
theorem length_le_hops_aux (xs : Fin k → ℕ → ℤ) (T : ℕ) {P : ℕ} (hP : 1 ≤ P) :
    ∀ (π : List ℕ) (t a : ℕ), IsDepPath xs T (t :: π) → (∀ v ∈ π, v ∉ periodic T P) →
      (∀ ρ, IsDepPath xs T (t :: ρ) → hopCount (t :: ρ) = 0 → (∀ v ∈ ρ, v ∉ periodic T P) →
        a + (t :: ρ).length ≤ P) →
      a + (t :: π).length ≤ (hopCount (t :: π) + 1) * P
  | [], t, a, _, _, hpre => by
    have := hpre [] trivial rfl (by simp)
    simpa [hopCount] using this
  | b :: π, t, a, hp, hfree, hpre => by
    obtain ⟨hstep, hp'⟩ := hp
    have hbP : b ∉ periodic T P := hfree b (List.mem_cons_self ..)
    have hfree' : ∀ v ∈ π, v ∉ periodic T P := fun v hv => hfree v (List.mem_cons_of_mem _ hv)
    by_cases hb : b + 1 = t
    · -- a state step: the run grows
      have ih := length_le_hops_aux xs T hP π b (a + 1) hp' hfree' (fun ρ hρ hρc hρf => by
        have := hpre (b :: ρ) ⟨hstep, hρ⟩ (by simpa [hopCount, hb] using hρc) (by
          intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hbP
          · exact hρf v hv)
        simp only [List.length_cons] at this ⊢
        omega)
      simp only [hopCount, hb, ↓reduceIte, zero_add, List.length_cons] at ih ⊢
      omega
    · -- a hop step: a new run starts at `b`
      have h1 := hpre [] trivial rfl (by simp)
      have ih := length_le_hops_aux xs T hP π b 0 hp' hfree' (fun ρ hρ hρc hρf => by
        simpa using state_run_le xs T hP ρ b hρ hρc hρf)
      simp only [hopCount, hb, ↓reduceIte, List.length_cons, zero_add] at ih h1 ⊢
      nlinarith

/-! ### From lists to the sequences of Theorem F -/

theorem depStep_getD (xs : Fin k → ℕ → ℤ) (T : ℕ) :
    ∀ (π : List ℕ), IsDepPath xs T π → ∀ i, i + 1 < π.length →
      DepStep xs T (π.getD i 0) (π.getD (i + 1) 0)
  | [], _, i, h => by simp at h
  | [_], _, i, h => by simp at h
  | a :: b :: π, hp, i, h => by
    obtain ⟨hs, hp'⟩ := hp
    cases i with
    | zero => simpa using hs
    | succ i =>
      have := depStep_getD xs T (b :: π) hp' i (by simp at h ⊢; omega)
      simpa using this

theorem not_rel_getD (R : ℕ → ℕ → Prop) [DecidableRel R] :
    ∀ (π : List ℕ), rCount R π = 0 → ∀ i, i + 1 < π.length → ¬ R (π.getD i 0) (π.getD (i + 1) 0)
  | [], _, i, h => by simp at h
  | [_], _, i, h => by simp at h
  | a :: b :: π, hc, i, h => by
    simp only [rCount] at hc
    have h1 : ¬ R a b := fun hR => by simp [hR] at hc
    have h2 : rCount R (b :: π) = 0 := by omega
    cases i with
    | zero => simpa using h1
    | succ i =>
      have := not_rel_getD R (b :: π) h2 i (by simp at h ⊢; omega)
      simpa using this

theorem getD_mem_tail : ∀ (π : List ℕ) (i : ℕ), i + 1 < π.length → π.getD (i + 1) 0 ∈ π.tail
  | [], i, h => by simp at h
  | a :: π, i, h => by
    simp only [List.getD_cons_succ, List.tail_cons]
    rw [List.getD_eq_getElem _ _ (by simp at h; omega)]
    exact List.getElem_mem _

theorem hopCount_eq : ∀ π : List ℕ, hopCount π =
    ((range (π.length - 1)).filter fun i => π.getD (i + 1) 0 + 1 ≠ π.getD i 0).card
  | [] => by simp [hopCount]
  | [_] => by simp [hopCount]
  | a :: b :: π => by
    rw [hopCount, hopCount_eq (b :: π)]
    simp only [List.length_cons, Nat.add_sub_cancel]
    rw [card_filter, card_filter, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]
    congr 1
    split_ifs <;> simp_all

open Classical in
/-- **Lemma 3.1: the cold genie.** For `ε > 0` and `P ≥ 1` there is a set `Γ` of at most `εT + T/P`
steps such that every `Γ`-free path of the dependency DAG without deep steps has at most
`DF k (2V - 1) ε ⋅ P` vertices. -/
theorem cold_genie (hk : 1 ≤ k) {V : ℕ} (hV : 1 ≤ V) {ε : ℝ} (hε : 0 < ε) {P : ℕ} (hP : 1 ≤ P)
    (xs : Fin k → ℕ → ℤ) (hx : ∀ h, IsWalk (xs h)) (T : ℕ) :
    ∃ Γ : Finset ℕ, (P * Γ.card : ℝ) ≤ P * ε * T + T ∧
      ∀ π, IsDepPath xs T π → LinNet.GFree Γ π → rCount (DeepStep xs T V) π = 0 →
        π.length ≤ DF k (2 * V - 1) ε * P := by
  have hH : ∀ η ∈ lightHops xs T V, IsHop (xs η.1) T η.2.1 η.2.2 :=
    fun η hη => mem_allHops.mp (mem_filter.mp hη).1
  obtain ⟨cutS, cutH, -, -, hcard, hF⟩ := theoremF_owner hk (by omega) hε xs hx _ hH
    (ownerLoad_le_of_entries hx hH fun η hη => entries_le_of_lightHops hη)
  set Γ := cutS.image (· - 1) ∪ cutH.image Prod.fst ∪ periodic T P
  refine ⟨Γ, ?_, ?_⟩
  · have h1 : Γ.card ≤ cutS.card + cutH.card + (periodic T P).card :=
      (card_union_le _ _).trans (Nat.add_le_add_right
        ((card_union_le _ _).trans (Nat.add_le_add card_image_le card_image_le)) _)
    have h2 := card_periodic_le T P hP
    have h1' : (Γ.card : ℝ) ≤ cutS.card + cutH.card + (periodic T P).card := by exact_mod_cast h1
    have h2' : (P * (periodic T P).card : ℝ) ≤ T := by exact_mod_cast h2
    have hcard' : ((cutS.card : ℝ) + cutH.card) ≤ ε * T := by exact_mod_cast hcard
    have hP' : (0 : ℝ) ≤ P := by positivity
    nlinarith
  · intro π hp hfree hdeep
    rcases π with _ | ⟨t, ρ⟩
    · simp
    set π := t :: ρ with hπ
    -- the steps of `π` are steps of Theorem F's sub-DAG of light hops, outside the cut
    set f : ℕ → ℕ := fun i => π.getD i 0
    have hnotΓ : ∀ i, i + 1 < π.length → f (i + 1) ∉ Γ := fun i hi =>
      hfree _ (getD_mem_tail π i hi)
    have hsteps : ∀ i < π.length - 1,
        (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T ∧ f i ∉ cutS) ∨
          ((f (i + 1), f i) ∈ hopPairs (lightHops xs T V) ∧ (f (i + 1), f i) ∉ cutH) := by
      intro i hi
      have hi' : i + 1 < π.length := by omega
      have hs := depStep_getD xs T π hp i hi'
      have hnd := not_rel_getD (DeepStep xs T V) π hdeep i hi'
      have hΓ := hnotΓ i hi'
      by_cases hst : f (i + 1) + 1 = f i
      · left
        rcases hs with ⟨-, hT⟩ | hhop
        · refine ⟨hst, by omega, hT, fun hS => hΓ ?_⟩
          exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨_, hS, by
            show f i - 1 = f (i + 1)
            omega⟩))
        · obtain ⟨η, hη, he⟩ := mem_image.mp hhop
          have := (mem_allHops.mp hη)
          simp only [Prod.mk.injEq] at he
          exfalso
          have := this.1
          simp only [f] at hst
          omega
      · right
        rcases hs with ⟨hb, -⟩ | hhop
        · exact absurd hb hst
        · obtain ⟨η, hη, he⟩ := mem_image.mp hhop
          have hlight : η ∈ lightHops xs T V := by
            by_contra hl
            exact hnd ⟨η, hη, by rw [← he], hl⟩
          refine ⟨mem_image.mpr ⟨η, hlight, he⟩, fun hc => hΓ ?_⟩
          exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨_, hc, rfl⟩))
    have hFcount := hF f (π.length - 1) hsteps
    -- the hop steps of `π` are light hop steps
    have hhops : hopCount π < DF k (2 * V - 1) ε := by
      rw [hopCount_eq]
      refine lt_of_le_of_lt (card_le_card fun i hi => ?_) hFcount
      obtain ⟨hi, hne⟩ := mem_filter.mp hi
      refine mem_filter.mpr ⟨hi, ?_⟩
      rcases hsteps i (mem_range.mp hi) with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hne
      · exact h
    -- runs of state steps have fewer than `P` steps
    have hlen := length_le_hops_aux xs T hP ρ t 0 hp (fun v hv hvP =>
        hfree v (by simpa [hπ] using hv) (mem_union_right _ hvP))
      (fun ρ' hρ' hρc hρf => by simpa using state_run_le xs T hP ρ' t hρ' hρc hρf)
    rw [zero_add] at hlen
    calc π.length ≤ (hopCount π + 1) * P := hlen
      _ ≤ DF k (2 * V - 1) ε * P := Nat.mul_le_mul_right _ hhops

end MergeDepth
