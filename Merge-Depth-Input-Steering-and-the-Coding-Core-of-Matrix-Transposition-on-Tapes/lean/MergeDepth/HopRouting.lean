import MergeDepth.HopMachine
import MergeDepth.HopFields
import MergeDepth.Capacity

/-!
# Routing through deep hops is hop-limited (Proposition 3.17)

* `length_le_of_coldDep`: under a cold genie of depth `D`, a `Γ_F`-free dependency path with `h'`
  deep edges has at most `(h' + 1) D` vertices (it splits at its deep edges into `h' + 1` paths
  without deep edges).
* `hop_routing_a`: if position `tpos ℓ` is not in the ball of radius `D''` around the output step
  `tout ℓ`, every `Γ_F`-free dependency path from `tout ℓ` to a step that reads `tpos ℓ` has at
  least `⌈(D'' + 2 - D)/D⌉` deep edges.
* `routing_count`: double counting. If every path of a position outside `X` carries at least `h`
  edges of a set `E`, weights of total at most one per position and load at most `c₀` on every edge
  of `E` give total weight at most `|X| + c₀ |E| / h`.
* `hop_routing_b`: Proposition 3.17(b) with the positions in the balls of radius `D''` as the
  exceptional set: total weight at most `|X| + c₀ N_R / h ≤ |X| + c₀ k C (L + 1) / h`.
-/

namespace MergeDepth

open Finset BoundedNesting

variable {k : ℕ}

open Classical in
/-- The cold-depth bound along dependency paths, with a prefix of `a` vertices already used. -/
theorem length_le_of_coldDep_aux (xs : Fin k → ℕ → ℤ) (T V : ℕ) (Γ : Finset ℕ) (D : ℕ)
    (hcold : ∀ π, IsDepPath xs T π → LinNet.GFree Γ π → rCount (DeepStep xs T V) π = 0 →
      π.length ≤ D) :
    ∀ (π : List ℕ) (u a : ℕ), IsDepPath xs T (u :: π) → (∀ v ∈ π, v ∉ Γ) →
      (∀ ρ, IsDepPath xs T (u :: ρ) → (∀ v ∈ ρ, v ∉ Γ) → rCount (DeepStep xs T V) (u :: ρ) = 0 →
        a + (u :: ρ).length ≤ D) →
      a + (u :: π).length ≤ (rCount (DeepStep xs T V) (u :: π) + 1) * D
  | [], u, a, _, _, hpre => by
    have := hpre [] trivial (by simp) rfl
    simpa [rCount] using this
  | s :: π, u, a, hp, hfree, hpre => by
    obtain ⟨hstep, hp'⟩ := hp
    have hsΓ : s ∉ Γ := hfree s (List.mem_cons_self ..)
    have hfree' : ∀ v ∈ π, v ∉ Γ := fun v hv => hfree v (List.mem_cons_of_mem _ hv)
    by_cases hR : DeepStep xs T V u s
    · -- a deep edge: the prefix ends at `u` and a new one starts at `s`
      have h1 := hpre [] trivial (by simp) rfl
      have h2 := length_le_of_coldDep_aux xs T V Γ D hcold π s 0 hp' hfree'
        (fun ρ hρ hρΓ hρR => by
          simpa using hcold (s :: ρ) hρ (fun v hv => hρΓ v (by simpa using hv)) hρR)
      simp only [rCount, hR, ↓reduceIte, List.length_cons] at h1 h2 ⊢
      nlinarith
    · -- no deep edge: the prefix grows by one vertex
      have h2 := length_le_of_coldDep_aux xs T V Γ D hcold π s (a + 1) hp' hfree'
        (fun ρ hρ hρΓ hρR => by
          have := hpre (s :: ρ) ⟨hstep, hρ⟩
            (fun v hv => by
              rcases List.mem_cons.mp hv with rfl | hv
              · exact hsΓ
              · exact hρΓ v hv)
            (by simp [rCount, hR, hρR])
          simp only [List.length_cons] at this ⊢
          omega)
      simp only [rCount, hR, ↓reduceIte, zero_add, List.length_cons] at h2 ⊢
      omega

open Classical in
/-- **Cold depth along dependency paths.** Under a cold genie of depth `D`, a `Γ`-free dependency
path with `h'` deep edges has at most `(h' + 1) D` vertices. -/
theorem length_le_of_coldDep (xs : Fin k → ℕ → ℤ) (T V : ℕ) (Γ : Finset ℕ) (D : ℕ)
    (hcold : ∀ π, IsDepPath xs T π → LinNet.GFree Γ π → rCount (DeepStep xs T V) π = 0 →
      π.length ≤ D) {π : List ℕ} (hπ : IsDepPath xs T π) (hfree : LinNet.GFree Γ π) :
    π.length ≤ (rCount (DeepStep xs T V) π + 1) * D := by
  cases π with
  | nil => simp
  | cons u π =>
    simpa using length_le_of_coldDep_aux xs T V Γ D hcold π u 0 hπ (fun v hv => hfree v hv)
      (fun ρ hρ hρΓ hρR => by simpa using hcold (u :: ρ) hρ (fun v hv => hρΓ v hv) hρR)

open Classical in
/-- **Proposition 3.17(a), per position.** If `tpos ℓ` is not in the ball of radius `D''` around
`t`, every `Γ_F`-free dependency path from `t` to a step that reads `tpos ℓ` has at least
`⌈(D'' + 2 - D)/D⌉` deep edges. -/
theorem hop_routing_a {L : ℕ} (xs : Fin k → ℕ → ℤ) {T V β : ℕ} {ε : ℝ} {D : ℕ} {ΓF : Finset ℕ}
    (hcold : IsColdGenie (L := L) xs T V β ε D ΓF) (hD : 1 ≤ D) (rdStep : ℕ → Option (Fin L))
    {D'' t : ℕ} {p : Fin L} (hfar : p ∉ stepBall xs T rdStep D'' t) {π : List ℕ}
    (hπ : IsDepPath xs T (t :: π)) (hfree : LinNet.GFree ΓF (t :: π))
    (hrd : rdStep ((t :: π).getLastD t) = some p) :
    ⌈((D'' + 2 - D : ℕ) : ℝ) / D⌉₊ ≤ rCount (DeepStep xs T V) (t :: π) := by
  have hlong : D'' + 1 ≤ π.length := by
    by_contra hlt
    push Not at hlt
    exact hfar (by
      simp only [stepBall, mem_filter, mem_univ, true_and]
      exact ⟨π, hπ, by omega, hrd⟩)
  have hlen := length_le_of_coldDep xs T V ΓF D hcold.2 hπ hfree
  simp only [List.length_cons] at hlen
  set h' := rCount (DeepStep xs T V) (t :: π)
  have hmul : D'' + 2 - D ≤ h' * D := by
    have : D'' + 2 ≤ (h' + 1) * D := by omega
    rw [add_mul, one_mul] at this
    omega
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [Nat.ceil_le, div_le_iff₀ hD']
  exact_mod_cast hmul

/-- The edges of a path, as pairs `(u, v)` of consecutive vertices. -/
def edgesOf : List ℕ → Finset (ℕ × ℕ)
  | [] => ∅
  | [_] => ∅
  | u :: v :: π => insert (u, v) (edgesOf (v :: π))

theorem fst_le_of_mem_edgesOf : ∀ {π : List ℕ} {u : ℕ} {e : ℕ × ℕ}, IsDepPath xs T (u :: π) →
    e ∈ edgesOf (u :: π) → e.1 ≤ u
  | [], _, _, _, he => by simp [edgesOf] at he
  | v :: π, u, e, hp, he => by
    obtain ⟨hstep, hp'⟩ := hp
    have hvu := (depStep_lt hstep).1
    rcases mem_insert.mp he with rfl | he
    · exact le_rfl
    · exact (fst_le_of_mem_edgesOf hp' he).trans hvu.le

open Classical in
/-- Along a dependency path, the `R`-edges are distinct: their number is at most the number of
edges of the path in any set `E` that contains every `R`-edge. -/
theorem rCount_le_card_edgesOf (R : ℕ → ℕ → Prop) [DecidableRel R] (E : Finset (ℕ × ℕ))
    (hE : ∀ a b, R a b → (a, b) ∈ E) :
    ∀ π : List ℕ, IsDepPath xs T π → rCount R π ≤ (edgesOf π ∩ E).card
  | [], _ => by simp [rCount]
  | [_], _ => by simp [rCount]
  | u :: v :: π, hp => by
    obtain ⟨hstep, hp'⟩ := hp
    have ih := rCount_le_card_edgesOf R E hE (v :: π) hp'
    have hnot : (u, v) ∉ edgesOf (v :: π) := fun h => by
      have := fst_le_of_mem_edgesOf hp' h
      have := (depStep_lt hstep).1
      simp only at *
      omega
    simp only [rCount, edgesOf]
    by_cases hR : R u v
    · have hmem : (u, v) ∈ E := hE u v hR
      rw [insert_inter_of_mem hmem, card_insert_of_notMem (fun h => hnot (mem_inter.mp h).1)]
      simp only [hR, ↓reduceIte]
      omega
    · simp only [hR, ↓reduceIte, zero_add]
      exact ih.trans (card_le_card (inter_subset_inter_right (subset_insert _ _)))

/-- **Double counting.** If every path of a position outside `X` has at least `h ≥ 1` edges in
`E`, weights of total at most one per position with load at most `c₀` on every edge of `E` have
total weight at most `|X| + c₀ |E| / h`. -/
theorem routing_count {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Finset (List ℕ))
    (f : ι → List ℕ → ℝ) (hf0 : ∀ ℓ π, 0 ≤ f ℓ π) (hf1 : ∀ ℓ, ∑ π ∈ P ℓ, f ℓ π ≤ 1)
    (E : Finset (ℕ × ℕ)) (c₀ : ℝ)
    (hload : ∀ e ∈ E, ∑ ℓ, ∑ π ∈ (P ℓ).filter (e ∈ edgesOf ·), f ℓ π ≤ c₀)
    (X : Finset ι) {h : ℕ} (hh : 1 ≤ h) (hdeep : ∀ ℓ ∉ X, ∀ π ∈ P ℓ, h ≤ (edgesOf π ∩ E).card) :
    ∑ ℓ, ∑ π ∈ P ℓ, f ℓ π ≤ X.card + c₀ * E.card / h := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  -- the positions in `X` contribute at most one each
  have hX : ∑ ℓ ∈ X, ∑ π ∈ P ℓ, f ℓ π ≤ X.card := by
    calc ∑ ℓ ∈ X, ∑ π ∈ P ℓ, f ℓ π ≤ ∑ _ℓ ∈ X, (1 : ℝ) := sum_le_sum fun ℓ _ => hf1 ℓ
      _ = X.card := by simp
  -- the others carry at least `h` edges of `E` on every path
  have hrest : h * ∑ ℓ ∈ univ \ X, ∑ π ∈ P ℓ, f ℓ π ≤ c₀ * E.card := by
    calc (h : ℝ) * ∑ ℓ ∈ univ \ X, ∑ π ∈ P ℓ, f ℓ π
        = ∑ ℓ ∈ univ \ X, ∑ π ∈ P ℓ, (h : ℝ) * f ℓ π := by
          rw [mul_sum]; exact sum_congr rfl fun ℓ _ => by rw [mul_sum]
      _ ≤ ∑ ℓ ∈ univ \ X, ∑ π ∈ P ℓ, ((edgesOf π ∩ E).card : ℝ) * f ℓ π := by
          refine sum_le_sum fun ℓ hℓ => sum_le_sum fun π hπ => ?_
          have := hdeep ℓ (mem_sdiff.mp hℓ).2 π hπ
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) (hf0 ℓ π)
      _ ≤ ∑ ℓ, ∑ π ∈ P ℓ, ((edgesOf π ∩ E).card : ℝ) * f ℓ π :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun ℓ _ _ =>
            sum_nonneg fun π _ => mul_nonneg (by positivity) (hf0 ℓ π)
      _ = ∑ ℓ, ∑ π ∈ P ℓ, ∑ e ∈ E, if e ∈ edgesOf π then f ℓ π else 0 := by
          refine sum_congr rfl fun ℓ _ => sum_congr rfl fun π _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul, filter_mem_eq_inter, inter_comm]
      _ = ∑ e ∈ E, ∑ ℓ, ∑ π ∈ (P ℓ).filter (e ∈ edgesOf ·), f ℓ π := by
          rw [sum_comm]
          refine sum_congr rfl fun ℓ _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun e _ => ?_
          rw [sum_filter]
      _ ≤ ∑ _e ∈ E, c₀ := sum_le_sum hload
      _ = c₀ * E.card := by rw [sum_const, nsmul_eq_mul, mul_comm]
  have hsplit : ∑ ℓ, ∑ π ∈ P ℓ, f ℓ π =
      ∑ ℓ ∈ X, ∑ π ∈ P ℓ, f ℓ π + ∑ ℓ ∈ univ \ X, ∑ π ∈ P ℓ, f ℓ π := by
    rw [add_comm, sum_sdiff (subset_univ X)]
  have hrest' : ∑ ℓ ∈ univ \ X, ∑ π ∈ P ℓ, f ℓ π ≤ c₀ * E.card / h := by
    rw [le_div_iff₀ hh']; linarith
  linarith

open Classical in
/-- **Proposition 3.17(b).** Let `P ℓ` be any finite set of `Γ_F`-free dependency paths from `tout ℓ`
to steps that read `tpos ℓ`, with nonnegative weights of total at most one per position and load
at most `c₀` on every deep edge. With `X` the positions `ℓ` such that `tpos ℓ` lies in the ball of
radius `D''` around `tout ℓ`, the total weight is at most `|X| + c₀ N_R / h ≤ |X| + c₀ k T / h`,
where `N_R` is the number of deep hops and `h = ⌈(D'' + 2 - D)/D⌉ ≥ 1`. -/
theorem hop_routing_b {L : ℕ} (xs : Fin k → ℕ → ℤ) {T V β : ℕ} {ε : ℝ} {D : ℕ}
    {ΓF : Finset ℕ} (hcold : IsColdGenie (L := L) xs T V β ε D ΓF) (hD : 1 ≤ D)
    (rdStep : ℕ → Option (Fin L)) (D'' : ℕ) (hD'' : D ≤ D'') (tout : Fin L → ℕ)
    (tpos : Fin L → Fin L) (P : Fin L → Finset (List ℕ))
    (hP : ∀ ℓ, ∀ π ∈ P ℓ, ∃ π', π = tout ℓ :: π' ∧ IsDepPath xs T π ∧ LinNet.GFree ΓF π ∧
      rdStep (π.getLastD (tout ℓ)) = some (tpos ℓ))
    (f : Fin L → List ℕ → ℝ) (hf0 : ∀ ℓ π, 0 ≤ f ℓ π) (hf1 : ∀ ℓ, ∑ π ∈ P ℓ, f ℓ π ≤ 1)
    (c₀ : ℝ) (hc₀ : 0 ≤ c₀)
    (hload : ∀ a b, DeepStep xs T V a b →
      ∑ ℓ, ∑ π ∈ (P ℓ).filter ((a, b) ∈ edgesOf ·), f ℓ π ≤ c₀) :
    ∑ ℓ, ∑ π ∈ P ℓ, f ℓ π ≤
        ((univ : Finset (Fin L)).filter fun ℓ => tpos ℓ ∈ stepBall xs T rdStep D'' (tout ℓ)).card +
          c₀ * (deepHops xs T V).card / ⌈((D'' + 2 - D : ℕ) : ℝ) / D⌉₊ ∧
      (deepHops xs T V).card ≤ k * T := by
  set h := ⌈((D'' + 2 - D : ℕ) : ℝ) / D⌉₊
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hh : 1 ≤ h := by
    rw [Nat.one_le_ceil_iff]
    have : (0 : ℝ) < (D'' + 2 - D : ℕ) := by exact_mod_cast (by omega : 0 < D'' + 2 - D)
    positivity
  let E : Finset (ℕ × ℕ) := (deepHops xs T V).image fun η => (η.2.2, η.2.1)
  have hE : ∀ a b, DeepStep xs T V a b → (a, b) ∈ E := by
    rintro a b ⟨η, hη, he, hl⟩
    refine mem_image.mpr ⟨η, mem_sdiff.mpr ⟨hη, hl⟩, ?_⟩
    rw [he]
  have hEcard : E.card ≤ (deepHops xs T V).card := card_image_le
  have hload' : ∀ e ∈ E, ∑ ℓ, ∑ π ∈ (P ℓ).filter (e ∈ edgesOf ·), f ℓ π ≤ c₀ := by
    intro e he
    obtain ⟨η, hη, rfl⟩ := mem_image.mp he
    exact hload _ _ ⟨η, (mem_sdiff.mp hη).1, rfl, (mem_sdiff.mp hη).2⟩
  have hdeep : ∀ ℓ ∉ (univ : Finset (Fin L)).filter
      (fun ℓ => tpos ℓ ∈ stepBall xs T rdStep D'' (tout ℓ)), ∀ π ∈ P ℓ,
      h ≤ (edgesOf π ∩ E).card := by
    intro ℓ hℓ π hπ
    have hfar : tpos ℓ ∉ stepBall xs T rdStep D'' (tout ℓ) := fun h' =>
      hℓ (mem_filter.mpr ⟨mem_univ _, h'⟩)
    obtain ⟨π', rfl, hdep, hfree, hrd⟩ := hP ℓ π hπ
    exact (hop_routing_a xs hcold hD rdStep hfar hdep hfree hrd).trans
      (rCount_le_card_edgesOf _ E hE _ hdep)
  have hmain := routing_count P f hf0 hf1 E c₀ hload' _ hh hdeep
  refine ⟨hmain.trans ?_, card_deepHops_le xs T V⟩
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  gcongr

end MergeDepth
