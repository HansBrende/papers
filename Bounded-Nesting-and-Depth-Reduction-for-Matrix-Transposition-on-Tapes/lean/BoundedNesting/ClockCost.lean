import BoundedNesting.Clock

/-!
# The cost of the family clock

Summed over all offsets `r < a` and all `ω ∈ [0, K)^N`, the cut of the family clock has at most
`K^N · 4N²T + a · K^(N-1) · 2^(a+1) N²T` elements (`Fam.Valid.cost_sum_le`), so some `(r, ω)`
has a cut of at most `4N²T/a + 2^(a+1) N²T/K` elements (`Fam.Valid.exists_cheap`).

The violated hops split into (α) the inconsistent hops (`Fam.incons`), (β) the consistent hops
whose higher groups differ (`Fam.higher`), and (γ) the violated hops among the rest
(`Fam.calm`); the descents into those at which some virtual head changes group (ε,
`Fam.gchange`) and the rest (δ, `Fam.still`). The bounds (α) and (ε) both count the jumps that
change a group (`Fam.gjumps`); (γ) and (δ) count the offsets `ω` at which a digit wraps.
-/

namespace BoundedNesting

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-! ### General counting lemmas -/

/-- Exchange of summation for counts. -/
theorem sum_card_filter_comm {α β : Type*} (s : Finset α) (t : Finset β) (p : α → β → Prop)
    [∀ x y, Decidable (p x y)] :
    ∑ x ∈ s, (t.filter (p x)).card = ∑ y ∈ t, (s.filter (fun x => p x y)).card := by
  simp only [card_filter]
  exact sum_comm

/-- A function that differs at `p ≤ u`, with a value above `g` at one of them, changes at some
step in `(p, u]` between two values one of which is above `g`. -/
theorem exists_change (f : ℕ → ℕ) (g p : ℕ) : ∀ u, p ≤ u → f p ≠ f u → g < max (f p) (f u) →
    ∃ τ, p < τ ∧ τ ≤ u ∧ f (τ - 1) ≠ f τ ∧ g < max (f (τ - 1)) (f τ) := by
  intro u hpu
  induction u, hpu using Nat.le_induction with
  | base => intro h; exact absurd rfl h
  | succ u hpu ih =>
    intro hne hg
    by_cases h : f u ≠ f (u + 1) ∧ g < max (f u) (f (u + 1))
    · exact ⟨u + 1, by omega, le_rfl, by simpa using h.1, by simpa using h.2⟩
    · have : f p ≠ f u ∧ g < max (f p) (f u) := by
        by_cases he : f u = f (u + 1)
        · rw [he]; exact ⟨hne, hg⟩
        · have h2 : max (f u) (f (u + 1)) ≤ g := by
            by_contra h3; exact h ⟨he, not_le.mp h3⟩
          simp only [max_le_iff, lt_max_iff] at h2 hg ⊢
          omega
      obtain ⟨τ, h1, h2, h3, h4⟩ := ih this.1 this.2
      exact ⟨τ, h1, by omega, h3, h4⟩

/-! ### Groups and floors -/

theorem grp_mono (a r : ℕ) : Monotone (grp a r) := fun _ _ h => Nat.div_le_div_right (by omega)

theorem flr_grp_le (a r b : ℕ) : flr a r (grp a r b) ≤ b := by
  unfold flr grp
  have := Nat.mul_div_le (b + r) a
  omega

theorem lt_flr_of_grp_lt {a r b g : ℕ} (ha : 0 < a) (h : grp a r b < g) : b < flr a r g := by
  unfold grp at h; unfold flr
  have h1 := (Nat.div_lt_iff_lt_mul ha).mp h
  rw [Nat.mul_comm] at h1
  omega

theorem lt_flr_add {a r b g : ℕ} (ha : 0 < a) (h : grp a r b ≤ g) : b < flr a r g + a := by
  unfold grp at h; unfold flr
  have h1 : b + r < (g + 1) * a := (Nat.div_lt_iff_lt_mul ha).mp (by omega)
  have h2 : (g + 1) * a = a * g + a := by ring
  omega

theorem flr_strictMono {a r : ℕ} (hr : r < a) {g g' : ℕ} (h : g < g') :
    flr a r g < flr a r g' := by
  unfold flr
  have : a * g + a ≤ a * g' := by
    calc a * g + a = a * (g + 1) := by ring
      _ ≤ a * g' := Nat.mul_le_mul_left a h
  omega

theorem flr_injective {a r : ℕ} (hr : r < a) : Function.Injective (flr a r) := by
  intro g g' h
  rcases lt_trichotomy g g' with hlt | heq | hgt
  · exact absurd h (flr_strictMono hr hlt).ne
  · exact heq
  · exact absurd h (flr_strictMono hr hgt).ne'

theorem le_of_flr_le {a r g s : ℕ} (hr : r < a) (h : flr a r g ≤ s) : g ≤ s := by
  unfold flr at h
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · omega
  · have h1 : a * (g - 1) + a = a * g := by
      rw [← Nat.mul_succ]; congr 1; omega
    have h2 : g - 1 ≤ a * (g - 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- At most `b + b'` offsets put `b` and `b'` in different groups. -/
theorem card_grp_ne_le {a : ℕ} (ha : 0 < a) (b b' : ℕ) :
    ((range a).filter (fun r => grp a r b ≠ grp a r b')).card ≤ b + b' := by
  unfold grp
  rcases le_total b b' with h | h
  · exact (Fam.card_wrap_le ha h).trans (by omega)
  · have he : (range a).filter (fun r => (b + r) / a ≠ (b' + r) / a) =
        (range a).filter (fun r => (b' + r) / a ≠ (b + r) / a) :=
      filter_congr fun r _ => ne_comm
    rw [he]
    exact (Fam.card_wrap_le ha h).trans (by omega)

/-- **Floors of a group change.** Over the offsets at which `b` and `b'` lie in different groups,
the floors of the larger group are distinct integers in `(min b b', max b b']`, so the sum of
`2^floor` is less than `2^(max b b' + 1) ≤ 2 (2^b + 2^b')`. -/
theorem sum_floor_pow_le {a : ℕ} (b b' : ℕ) :
    ∑ r ∈ (range a).filter (fun r => grp a r b ≠ grp a r b'),
      2 ^ flr a r (max (grp a r b) (grp a r b')) ≤ 2 * (2 ^ b + 2 ^ b') := by
  set M := max b b'
  set S := (range a).filter (fun r => grp a r b ≠ grp a r b')
  have hmax : ∀ r, max (grp a r b) (grp a r b') = grp a r M :=
    fun r => ((grp_mono a r).map_max).symm
  simp only [hmax]
  -- the floor `θ r` of the larger group, with `θ r + r = a · grp a r M`
  have hpos : ∀ r ∈ S, 1 ≤ grp a r M := by
    intro r hr
    have hne := (mem_filter.mp hr).2
    have h1 : grp a r b ≤ grp a r M := grp_mono a r (le_max_left b b')
    have h2 : grp a r b' ≤ grp a r M := grp_mono a r (le_max_right b b')
    omega
  have hsum : ∀ r ∈ S, flr a r (grp a r M) + r = a * grp a r M := by
    intro r hr
    have hr' := mem_range.mp (mem_filter.mp hr).1
    have h1 := hpos r hr
    have : a ≤ a * grp a r M := Nat.le_mul_of_pos_right a h1
    unfold flr; omega
  have hinj : Set.InjOn (fun r => flr a r (grp a r M)) S := by
    intro r hr r' hr' h
    simp only at h
    have hr1 := mem_range.mp (mem_filter.mp hr).1
    have hr1' := mem_range.mp (mem_filter.mp hr').1
    have e1 := hsum r hr
    have e2 := hsum r' hr'
    have m1 : (flr a r (grp a r M) + r) % a = 0 := by rw [e1, Nat.mul_mod_right]
    have m2 : (flr a r (grp a r M) + r') % a = 0 := by rw [h, e2, Nat.mul_mod_right]
    have hmod : r ≡ r' [MOD a] := Nat.ModEq.add_left_cancel' (flr a r (grp a r M)) (m1.trans m2.symm)
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hr1, Nat.mod_eq_of_lt hr1'] at hmod
  calc ∑ r ∈ S, 2 ^ flr a r (grp a r M) = ∑ x ∈ S.image (fun r => flr a r (grp a r M)), 2 ^ x :=
        (sum_image hinj).symm
    _ ≤ ∑ x ∈ range (M + 1), 2 ^ x := by
        refine sum_le_sum_of_subset fun x hx => ?_
        obtain ⟨r, -, rfl⟩ := mem_image.mp hx
        exact mem_range.mpr (Nat.lt_succ_of_le (flr_grp_le a r M))
    _ ≤ 2 ^ (M + 1) := (Fam.sum_pow_two_lt _).le
    _ ≤ 2 * (2 ^ b + 2 ^ b') := by
        rw [pow_succ, mul_comm]
        apply Nat.mul_le_mul_left
        rcases le_total b b' with h | h
        · rw [show M = b' from max_eq_right h]; exact Nat.le_add_left _ _
        · rw [show M = b from max_eq_left h]; exact Nat.le_add_right _ _

namespace Fam

variable {A : Fam ι N} {T : ℕ}

/-! ### Bands and jumps -/

omit [DecidableEq ι] in
/-- The band is `0` before the first family starts, and otherwise that of the family that started
last. -/
theorem band_cases (v : Fin N) (t : ℕ) :
    (A.started v t = ∅ ∧ A.band v t = 0) ∨
      ∃ F ∈ A.started v t, (∀ F' ∈ A.started v t, A.P F' ≤ A.P F) ∧ A.band v t = lam (A.d F) := by
  by_cases hne : (A.started v t).Nonempty
  · right
    obtain ⟨h1, h2⟩ := Classical.choose_spec ((A.started v t).exists_max_image A.P hne)
    refine ⟨_, h1, h2, ?_⟩
    unfold band
    simp only [hne, ↓reduceDIte]
  · left
    refine ⟨not_nonempty_iff_eq_empty.mp hne, ?_⟩
    unfold band
    simp only [hne, ↓reduceDIte]

variable (A) in
/-- The families that start at a positive time; their starts are the *jumps*. -/
def jumps : Finset ι := univ.filter (fun F => 1 ≤ A.P F)

variable (A) in
/-- The band of the virtual head of `F` just before `F` starts. -/
noncomputable def oldBand (F : ι) : ℕ := A.band (A.vh F) (A.P F - 1)

omit [DecidableEq ι] in
theorem mem_jumps {F : ι} : F ∈ A.jumps ↔ 1 ≤ A.P F := by simp [jumps]

/-- **Old bands.** Over the jumps of a virtual head, the old bands are `0` at most once and
otherwise the bands of distinct families: the previous family of each jump. -/
theorem Valid.sum_old_le (hA : A.Valid T) (f : ℕ → ℕ) (v : Fin N) :
    ∑ F ∈ A.jumps.filter (fun F => A.vh F = v), f (A.oldBand F) ≤
      f 0 + ∑ G ∈ univ.filter (fun G => A.vh G = v), f (lam (A.d G)) := by
  set S := A.jumps.filter (fun F => A.vh F = v)
  have hS : ∀ F ∈ S, A.vh F = v ∧ 1 ≤ A.P F := by
    intro F hF
    obtain ⟨h1, h2⟩ := mem_filter.mp hF
    exact ⟨h2, mem_jumps.mp h1⟩
  rw [← sum_filter_add_sum_filter_not S (fun F => A.started v (A.P F - 1) = ∅)]
  apply add_le_add
  · -- at most one jump of `v` has no family started before it
    have hone : (S.filter (fun F => A.started v (A.P F - 1) = ∅)).card ≤ 1 := by
      refine card_le_one.mpr fun F₁ h₁ F₂ h₂ => ?_
      obtain ⟨h₁S, h₁e⟩ := mem_filter.mp h₁
      obtain ⟨h₂S, h₂e⟩ := mem_filter.mp h₂
      obtain ⟨hv₁, hp₁⟩ := hS F₁ h₁S
      obtain ⟨hv₂, hp₂⟩ := hS F₂ h₂S
      by_contra hne
      have hP := hA.P_ne hne (hv₁.trans hv₂.symm)
      rcases lt_or_gt_of_ne hP with hlt | hlt
      · have : F₁ ∈ A.started v (A.P F₂ - 1) := mem_started.mpr ⟨hv₁, by omega⟩
        rw [h₂e] at this; exact absurd this (notMem_empty _)
      · have : F₂ ∈ A.started v (A.P F₁ - 1) := mem_started.mpr ⟨hv₂, by omega⟩
        rw [h₁e] at this; exact absurd this (notMem_empty _)
    calc ∑ F ∈ S.filter (fun F => A.started v (A.P F - 1) = ∅), f (A.oldBand F)
        = ∑ F ∈ S.filter (fun F => A.started v (A.P F - 1) = ∅), f 0 := by
          refine sum_congr rfl fun F hF => ?_
          obtain ⟨hFS, he⟩ := mem_filter.mp hF
          have hv := (hS F hFS).1
          unfold oldBand
          rw [hv]
          rcases band_cases (A := A) v (A.P F - 1) with ⟨-, h⟩ | ⟨G, hG, -, -⟩
          · rw [h]
          · rw [he] at hG; exact absurd hG (notMem_empty _)
      _ = (S.filter (fun F => A.started v (A.P F - 1) = ∅)).card * f 0 := by
          rw [sum_const, smul_eq_mul]
      _ ≤ 1 * f 0 := Nat.mul_le_mul_right _ hone
      _ = f 0 := one_mul _
  · -- otherwise the old band is that of the previous family, an injective choice
    set S₁ := S.filter (fun F => ¬ A.started v (A.P F - 1) = ∅)
    have hex : ∀ F, ∃ G, F ∈ S₁ → G ∈ A.started v (A.P F - 1) ∧
        (∀ G' ∈ A.started v (A.P F - 1), A.P G' ≤ A.P G) ∧ A.oldBand F = lam (A.d G) := by
      intro F
      by_cases hF : F ∈ S₁
      · obtain ⟨hFS, hne⟩ := mem_filter.mp hF
        have hv := (hS F hFS).1
        rcases band_cases (A := A) v (A.P F - 1) with ⟨he, -⟩ | ⟨G, hG, hmax, hb⟩
        · exact absurd he hne
        · exact ⟨G, fun _ => ⟨hG, hmax, by unfold oldBand; rw [hv]; exact hb⟩⟩
      · exact ⟨F, fun h => absurd h hF⟩
    choose g hg using hex
    have hinj : Set.InjOn g S₁ := by
      intro F₁ h₁ F₂ h₂ heq
      obtain ⟨hG₁, hmax₁, -⟩ := hg F₁ h₁
      obtain ⟨hG₂, hmax₂, -⟩ := hg F₂ h₂
      obtain ⟨hv₁, hp₁⟩ := hS F₁ (mem_filter.mp h₁).1
      obtain ⟨hv₂, hp₂⟩ := hS F₂ (mem_filter.mp h₂).1
      by_contra hne
      have hP := hA.P_ne hne (hv₁.trans hv₂.symm)
      rcases lt_or_gt_of_ne hP with hlt | hlt
      · have h1 := hmax₂ F₁ (mem_started.mpr ⟨hv₁, by omega⟩)
        have h2 := (mem_started.mp hG₁).2
        rw [heq] at h2
        omega
      · have h1 := hmax₁ F₂ (mem_started.mpr ⟨hv₂, by omega⟩)
        have h2 := (mem_started.mp hG₂).2
        rw [← heq] at h2
        omega
    calc ∑ F ∈ S₁, f (A.oldBand F) = ∑ F ∈ S₁, f (lam (A.d (g F))) :=
          sum_congr rfl fun F hF => by rw [(hg F hF).2.2]
      _ = ∑ G ∈ S₁.image g, f (lam (A.d G)) := (sum_image (f := fun G => f (lam (A.d G))) hinj).symm
      _ ≤ ∑ G ∈ univ.filter (fun G => A.vh G = v), f (lam (A.d G)) := by
          refine sum_le_sum_of_subset fun G hG => ?_
          obtain ⟨F, hF, rfl⟩ := mem_image.mp hG
          exact mem_filter.mpr ⟨mem_univ _, (mem_started.mp (hg F hF).1).1⟩

/-- Over the jumps of a virtual head, `∑ (2^b + 2^b') ≤ T` for the old and new bands. -/
theorem Valid.sum_jumps_pow (hA : A.Valid T) (v : Fin N) :
    ∑ F ∈ A.jumps.filter (fun F => A.vh F = v), (2 ^ A.oldBand F + 2 ^ lam (A.d F)) ≤ T := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · refine le_trans (le_of_eq (sum_eq_zero fun F _ => ?_)) (Nat.zero_le T)
    exact absurd (hA.lt_T F) (by omega)
  · have h1 := hA.sum_old_le (fun b => 2 ^ b) v
    have h2 : ∑ F ∈ A.jumps.filter (fun F => A.vh F = v), 2 ^ lam (A.d F) ≤
        ∑ G ∈ univ.filter (fun G => A.vh G = v), 2 ^ lam (A.d G) :=
      sum_le_sum_of_subset fun F hF => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hF).2⟩
    have h3 : ∑ G ∈ univ.filter (fun G => A.vh G = v), 2 ^ lam (A.d G) ≤
        ∑ G ∈ univ.filter (fun G => A.vh G = v), A.d G :=
      sum_le_sum fun G _ => Nat.pow_log_le_self 2 (by have := hA.d_pos G; omega)
    have h4 := hA.sum_d_le v
    rw [sum_add_distrib]
    simp only [pow_zero] at h1
    omega

/-- Over the jumps of a virtual head, `∑ (b + b') ≤ T` for the old and new bands. -/
theorem Valid.sum_jumps_lam (hA : A.Valid T) (v : Fin N) :
    ∑ F ∈ A.jumps.filter (fun F => A.vh F = v), (A.oldBand F + lam (A.d F)) ≤ T := by
  have h1 := hA.sum_old_le (fun b => b) v
  have h2 : ∑ F ∈ A.jumps.filter (fun F => A.vh F = v), lam (A.d F) ≤
      ∑ G ∈ univ.filter (fun G => A.vh G = v), lam (A.d G) :=
    sum_le_sum_of_subset fun F hF => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hF).2⟩
  have h3 : ∑ G ∈ univ.filter (fun G => A.vh G = v), lam (A.d G) ≤
      ∑ G ∈ univ.filter (fun G => A.vh G = v), A.d G :=
    sum_le_sum fun G _ => Nat.log_le_self 2 _
  have h4 := hA.sum_d_le v
  rw [sum_add_distrib]
  omega

variable (A) in
/-- The jumps that change the group of their virtual head, for the offset `r`. -/
noncomputable def gjumps (a r : ℕ) : Finset ι :=
  A.jumps.filter (fun F => grp a r (A.oldBand F) ≠ grp a r (lam (A.d F)))

/-- Summed over the offsets, at most `N T` jumps change a group. -/
theorem Valid.sum_gjumps (hA : A.Valid T) {a : ℕ} (ha : 0 < a) :
    ∑ r ∈ range a, (A.gjumps a r).card ≤ N * T := by
  unfold gjumps
  calc ∑ r ∈ range a,
        (A.jumps.filter (fun F => grp a r (A.oldBand F) ≠ grp a r (lam (A.d F)))).card
      = ∑ F ∈ A.jumps,
          ((range a).filter (fun r => grp a r (A.oldBand F) ≠ grp a r (lam (A.d F)))).card :=
        sum_card_filter_comm _ _ (fun r F => grp a r (A.oldBand F) ≠ grp a r (lam (A.d F)))
    _ ≤ ∑ F ∈ A.jumps, (A.oldBand F + lam (A.d F)) :=
        sum_le_sum fun F _ => card_grp_ne_le ha _ _
    _ = ∑ v, ∑ F ∈ A.jumps.filter (fun F => A.vh F = v), (A.oldBand F + lam (A.d F)) :=
        (sum_fiberwise _ _ _).symm
    _ ≤ ∑ _v : Fin N, T := sum_le_sum fun v _ => hA.sum_jumps_lam v
    _ = N * T := by simp

/-! ### (α) Inconsistent hops and (ε) group changes -/

variable (A) in
/-- (α) The inconsistent hops: at the end of the hop, the group of the virtual head is not that of
the band of the family. -/
noncomputable def incons (a r : ℕ) : Finset (ι × ℕ × ℕ) :=
  A.H.filter (fun η => A.group a r (A.vh η.1) η.2.2 ≠ grp a r (lam (A.d η.1)))

/-- An inconsistent hop is the span of its family, and a jump that changes the group occurs at its
end. Distinct inconsistent hops give distinct jumps. -/
theorem Valid.card_incons_le (hA : A.Valid T) (a r : ℕ) :
    (A.incons a r).card ≤ (A.gjumps a r).card := by
  have key : ∀ η ∈ A.incons a r, η.2.2 = A.U η.1 ∧ η.2.1 = A.P η.1 ∧
      ∃ F' ∈ A.gjumps a r, A.vh F' = A.vh η.1 ∧ A.P F' = A.U η.1 := by
    intro η hη
    obtain ⟨hηH, hne⟩ := mem_filter.mp hη
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hA.hop_in η hηH
    have hu : η.2.2 = A.U η.1 := by
      by_contra hlt
      apply hne
      unfold group
      rw [hA.band_of_mem (by omega) (by omega)]
    refine ⟨hu, hA.span_end η hηH hu, ?_⟩
    have hex : ∃ F', F' ≠ η.1 ∧ A.vh F' = A.vh η.1 ∧ A.P F' = A.U η.1 := by
      by_contra hno
      push Not at hno
      apply hne
      unfold group
      rw [hu, hA.band_at_end hno]
    obtain ⟨F', -, hv, hP⟩ := hex
    refine ⟨F', mem_filter.mpr ⟨mem_jumps.mpr (by have := hA.P_lt_U η.1; omega), ?_⟩, hv, hP⟩
    have hold : A.oldBand F' = lam (A.d η.1) := by
      unfold oldBand
      rw [hv, hP]
      exact hA.band_of_mem (by have := hA.P_lt_U η.1; omega) (by have := hA.P_lt_U η.1; omega)
    have hnew : A.group a r (A.vh η.1) η.2.2 = grp a r (lam (A.d F')) := by
      unfold group
      rw [hu, ← hP, ← hv]
      rw [hA.band_of_mem le_rfl (by have := hA.P_lt_U F'; omega)]
    rw [hold]
    rw [hnew] at hne
    exact fun h => hne h.symm
  calc (A.incons a r).card = ((A.incons a r).image (fun η => (A.vh η.1, A.U η.1))).card := by
        refine (card_image_of_injOn fun η₁ h₁ η₂ h₂ heq => ?_).symm
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hu₁, hp₁, -⟩ := key η₁ h₁
        obtain ⟨hu₂, hp₂, -⟩ := key η₂ h₂
        have hF : η₁.1 = η₂.1 := by
          by_contra hne
          have h1 := hA.P_lt_U η₁.1
          have h2 := hA.P_lt_U η₂.1
          rcases hA.disj η₁.1 η₂.1 hne heq.1 with h | h <;> omega
        refine Prod.ext hF (Prod.ext ?_ ?_)
        · rw [hp₁, hp₂, hF]
        · rw [hu₁, hu₂, hF]
    _ ≤ ((A.gjumps a r).image (fun F => (A.vh F, A.P F))).card := by
        refine card_le_card fun x hx => ?_
        obtain ⟨η, hη, rfl⟩ := mem_image.mp hx
        obtain ⟨-, -, F', hF', hv, hP⟩ := key η hη
        exact mem_image.mpr ⟨F', hF', by rw [hv, hP]⟩
    _ ≤ (A.gjumps a r).card := card_image_le

variable (A) in
/-- (ε) The times at which some virtual head changes group. -/
noncomputable def gchange (a r T : ℕ) : Finset ℕ :=
  (Ico 1 T).filter (fun t => ∃ v, A.group a r v (t - 1) ≠ A.group a r v t)

/-- A group change happens at a jump that changes the group. -/
theorem Valid.exists_gjump (hA : A.Valid T) {a r : ℕ} {v : Fin N} {t : ℕ} (ht : 1 ≤ t)
    (hne : A.group a r v (t - 1) ≠ A.group a r v t) :
    ∃ F ∈ A.gjumps a r, A.vh F = v ∧ A.P F = t := by
  have hex : ∃ F, A.vh F = v ∧ A.P F = t := by
    by_contra hno
    push Not at hno
    apply hne
    unfold group
    rw [band_eq_prev ht hno]
  obtain ⟨F, hv, hP⟩ := hex
  refine ⟨F, mem_filter.mpr ⟨mem_jumps.mpr (by omega), ?_⟩, hv, hP⟩
  have hnew : A.band v t = lam (A.d F) := by
    rw [← hv, ← hP]
    exact hA.band_of_mem le_rfl (by have := hA.P_lt_U F; omega)
  unfold group at hne
  unfold oldBand
  rw [hv, hP, ← hnew]
  exact hne

theorem Valid.card_gchange_le (hA : A.Valid T) (a r : ℕ) :
    (A.gchange a r T).card ≤ (A.gjumps a r).card := by
  calc (A.gchange a r T).card ≤ ((A.gjumps a r).image A.P).card := by
        refine card_le_card fun t ht => ?_
        obtain ⟨ht1, v, hne⟩ := mem_filter.mp ht
        obtain ⟨F, hF, -, hP⟩ := hA.exists_gjump (mem_Ico.mp ht1).1 hne
        exact mem_image.mpr ⟨F, hF, hP⟩
    _ ≤ (A.gjumps a r).card := card_image_le

/-! ### (β) Consistent hops whose higher groups differ -/

variable (A) in
/-- The group of the band of the family of a hop. -/
def hgrp (a r : ℕ) (η : ι × ℕ × ℕ) : ℕ := grp a r (lam (A.d η.1))

variable (A) in
/-- The occupied groups above `g` at `t`. -/
noncomputable def above (a r t g : ℕ) : Finset ℕ := (A.occ a r t).filter (fun g' => g < g')

variable (A) in
/-- (β) The consistent hops whose higher occupied groups differ at the two ends. -/
noncomputable def higher (a r : ℕ) : Finset (ι × ℕ × ℕ) :=
  A.H.filter (fun η => A.group a r (A.vh η.1) η.2.2 = A.hgrp a r η ∧
    A.above a r η.2.1 (A.hgrp a r η) ≠ A.above a r η.2.2 (A.hgrp a r η))

variable (A) in
/-- The floor of the larger of the two groups at the jump of `F`. -/
noncomputable def jfloor (a r : ℕ) (F : ι) : ℕ :=
  flr a r (max (grp a r (A.oldBand F)) (grp a r (lam (A.d F))))

/-- **Charging.** A hop of (β) spans a jump that moves some virtual head between two groups, the
larger of which is above the group of the hop; so the band of its family is less than the floor
of that group. -/
theorem Valid.exists_charge (hA : A.Valid T) {a r : ℕ} (ha : 0 < a) {η : ι × ℕ × ℕ}
    (hη : η ∈ A.higher a r) :
    ∃ F ∈ A.gjumps a r, η.2.1 < A.P F ∧ A.P F ≤ η.2.2 ∧ lam (A.d η.1) < A.jfloor a r F := by
  obtain ⟨hηH, -, hab⟩ := mem_filter.mp hη
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hA.hop_in η hηH
  -- some virtual head is in a higher group at exactly one end
  have hv : ∃ v, A.group a r v η.2.1 ≠ A.group a r v η.2.2 ∧
      A.hgrp a r η < max (A.group a r v η.2.1) (A.group a r v η.2.2) := by
    have : ∃ g, ¬ (g ∈ A.above a r η.2.1 (A.hgrp a r η) ↔ g ∈ A.above a r η.2.2 (A.hgrp a r η)) := by
      by_contra h
      push Not at h
      exact hab (Finset.ext h)
    obtain ⟨g, hg⟩ := this
    simp only [above, occ, mem_filter, mem_image, mem_univ, true_and] at hg
    have hG : A.hgrp a r η < g := by
      by_contra hlt
      exact hg ⟨fun h => absurd h.2 hlt, fun h => absurd h.2 hlt⟩
    by_cases hgp : ∃ v, A.group a r v η.2.1 = g
    · obtain ⟨v, hv⟩ := hgp
      have hgu : ¬ ∃ v', A.group a r v' η.2.2 = g :=
        fun h => hg ⟨fun _ => ⟨h, hG⟩, fun _ => ⟨⟨v, hv⟩, hG⟩⟩
      refine ⟨v, fun he => hgu ⟨v, he.symm.trans hv⟩, ?_⟩
      rw [hv]; exact lt_max_of_lt_left hG
    · have hgu : ∃ v', A.group a r v' η.2.2 = g := by
        by_contra h
        exact hg ⟨fun h' => absurd h'.1 hgp, fun h' => absurd h'.1 h⟩
      obtain ⟨v, hv⟩ := hgu
      refine ⟨v, fun he => hgp ⟨v, he.trans hv⟩, ?_⟩
      rw [hv]; exact lt_max_of_lt_right hG
  obtain ⟨v, hne, hlt⟩ := hv
  obtain ⟨τ, hτ1, hτ2, hτne, hτlt⟩ :=
    exists_change (fun t => A.group a r v t) (A.hgrp a r η) η.2.1 η.2.2 (by omega) hne hlt
  obtain ⟨F, hF, hvF, hPF⟩ := hA.exists_gjump (by omega) hτne
  refine ⟨F, hF, by omega, by omega, ?_⟩
  -- the groups at the jump are those of the old and of the new band
  have hold : A.group a r v (τ - 1) = grp a r (A.oldBand F) := by
    unfold group oldBand; rw [hvF, hPF]
  have hnew : A.group a r v τ = grp a r (lam (A.d F)) := by
    unfold group
    rw [← hvF, ← hPF, hA.band_of_mem le_rfl (by have := hA.P_lt_U F; omega)]
  unfold jfloor
  rw [← hold, ← hnew]
  exact lt_flr_of_grp_lt ha hτlt

/-- (β) for one offset: the hops charged to a jump number at most `N 2^floor`, by the overlap
bound. -/
theorem Valid.card_higher_le (hA : A.Valid T) {a : ℕ} (ha : 0 < a) (r : ℕ) :
    (A.higher a r).card ≤ ∑ F ∈ A.gjumps a r, N * 2 ^ A.jfloor a r F := by
  calc (A.higher a r).card ≤ ((A.gjumps a r).biUnion (fun F => A.H.filter (fun η =>
        η.2.1 < A.P F ∧ A.P F ≤ η.2.2 ∧ lam (A.d η.1) < A.jfloor a r F))).card := by
        refine card_le_card fun η hη => ?_
        obtain ⟨F, hF, h1, h2, h3⟩ := hA.exists_charge ha hη
        exact mem_biUnion.mpr ⟨F, hF, mem_filter.mpr ⟨(mem_filter.mp hη).1, h1, h2, h3⟩⟩
    _ ≤ ∑ F ∈ A.gjumps a r, (A.H.filter (fun η =>
        η.2.1 < A.P F ∧ A.P F ≤ η.2.2 ∧ lam (A.d η.1) < A.jfloor a r F)).card := card_biUnion_le
    _ ≤ ∑ F ∈ A.gjumps a r, N * 2 ^ A.jfloor a r F := by
        refine sum_le_sum fun F _ => (hA.overlap _ _).trans ?_
        exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-- (β) summed over the offsets: at most `2N · NT`. -/
theorem Valid.sum_higher_le (hA : A.Valid T) {a : ℕ} (ha : 0 < a) :
    ∑ r ∈ range a, (A.higher a r).card ≤ 2 * N * (N * T) := by
  calc ∑ r ∈ range a, (A.higher a r).card
      ≤ ∑ r ∈ range a, ∑ F ∈ A.gjumps a r, N * 2 ^ A.jfloor a r F :=
        sum_le_sum fun r _ => hA.card_higher_le ha r
    _ = ∑ F ∈ A.jumps, N * ∑ r ∈ (range a).filter
          (fun r => grp a r (A.oldBand F) ≠ grp a r (lam (A.d F))), 2 ^ A.jfloor a r F := by
        unfold gjumps
        simp only [sum_filter]
        rw [sum_comm]
        refine sum_congr rfl fun F _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun r _ => ?_
        split_ifs <;> simp
    _ ≤ ∑ F ∈ A.jumps, N * (2 * (2 ^ A.oldBand F + 2 ^ lam (A.d F))) := by
        refine sum_le_sum fun F _ => Nat.mul_le_mul_left _ ?_
        unfold jfloor
        exact sum_floor_pow_le _ _
    _ = 2 * N * ∑ v, ∑ F ∈ A.jumps.filter (fun F => A.vh F = v),
          (2 ^ A.oldBand F + 2 ^ lam (A.d F)) := by
        rw [sum_fiberwise, mul_sum]
        exact sum_congr rfl fun F _ => by ring
    _ ≤ 2 * N * ∑ _v : Fin N, T :=
        Nat.mul_le_mul_left _ (sum_le_sum fun v _ => hA.sum_jumps_pow v)
    _ = 2 * N * (N * T) := by simp

/-! ### (γ) The remaining hops -/

variable (A) in
/-- The consistent hops whose higher occupied groups agree at the two ends. -/
noncomputable def calm (a r : ℕ) : Finset (ι × ℕ × ℕ) :=
  A.H.filter (fun η => A.group a r (A.vh η.1) η.2.2 = A.hgrp a r η ∧
    A.above a r η.2.1 (A.hgrp a r η) = A.above a r η.2.2 (A.hgrp a r η))

omit [DecidableEq ι] in
/-- The growth of a count is at most the number of events in between. -/
theorem cnt_sub_le (A : Fam ι N) (a r : ℕ) {t t' : ℕ} (g : ℕ) :
    A.cnt a r t' g - A.cnt a r t g ≤
      (univ.filter (fun F => t < A.o F ∧ A.o F ≤ t' ∧ flr a r g ≤ lam (A.d F))).card := by
  classical
  unfold cnt
  have : univ.filter (fun F => A.o F ≤ t' ∧ flr a r g ≤ lam (A.d F)) ⊆
      univ.filter (fun F => A.o F ≤ t ∧ flr a r g ≤ lam (A.d F)) ∪
        univ.filter (fun F => t < A.o F ∧ A.o F ≤ t' ∧ flr a r g ≤ lam (A.d F)) := by
    intro F hF
    obtain ⟨-, h1, h2⟩ := mem_filter.mp hF
    rcases le_or_gt (A.o F) t with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h, h2⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h, h1, h2⟩)
  have := (card_le_card this).trans (card_union_le _ _)
  omega

omit [DecidableEq ι] in
/-- **Wraps.** The offsets `ω` at which some digit of a group of `S` wraps between `t` and `t'`
number at most `K^(N-1)` times the total growth of the counts of `S`. -/
theorem card_wrap_union (A : Fam ι N) {K : ℕ} (hK : 0 < K) (a r t t' : ℕ) (htt : t ≤ t')
    (S : Finset ℕ) :
    ((Fintype.piFinset (fun _ : Fin N => range K)).filter (fun ω => ∃ g ∈ S, ∃ i : Fin N,
      i.val = A.rk a r t g ∧ (A.cnt a r t g + ω i) / K ≠ (A.cnt a r t' g + ω i) / K)).card ≤
      K ^ (N - 1) * ∑ g ∈ S, (A.cnt a r t' g - A.cnt a r t g) := by
  classical
  set Ω := Fintype.piFinset (fun _ : Fin N => range K)
  calc _ ≤ (S.biUnion (fun g => (univ.filter (fun i : Fin N => i.val = A.rk a r t g)).biUnion
          (fun i => Ω.filter (fun ω => (A.cnt a r t g + ω i) / K ≠ (A.cnt a r t' g + ω i) / K)))).card := by
        refine card_le_card fun ω hω => ?_
        obtain ⟨hωΩ, g, hg, i, hi, hw⟩ := mem_filter.mp hω
        exact mem_biUnion.mpr ⟨g, hg, mem_biUnion.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩,
          mem_filter.mpr ⟨hωΩ, hw⟩⟩⟩
    _ ≤ ∑ g ∈ S, ((univ.filter (fun i : Fin N => i.val = A.rk a r t g)).biUnion
          (fun i => Ω.filter (fun ω => (A.cnt a r t g + ω i) / K ≠ (A.cnt a r t' g + ω i) / K))).card :=
        card_biUnion_le
    _ ≤ ∑ g ∈ S, K ^ (N - 1) * (A.cnt a r t' g - A.cnt a r t g) := by
        refine sum_le_sum fun g _ => card_biUnion_le.trans ?_
        have hone : (univ.filter (fun i : Fin N => i.val = A.rk a r t g)).card ≤ 1 :=
          card_le_one.mpr fun i hi j hj =>
            Fin.ext ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
        calc ∑ i ∈ univ.filter (fun i : Fin N => i.val = A.rk a r t g),
              (Ω.filter (fun ω => (A.cnt a r t g + ω i) / K ≠ (A.cnt a r t' g + ω i) / K)).card
            ≤ ∑ i ∈ univ.filter (fun i : Fin N => i.val = A.rk a r t g),
                K ^ (N - 1) * (A.cnt a r t' g - A.cnt a r t g) := by
              refine sum_le_sum fun i _ => ?_
              have hc := Fam.card_piFinset_coord (N := N) (K := K) i
                (fun c => (A.cnt a r t g + c) / K ≠ (A.cnt a r t' g + c) / K)
              rw [hc, mul_comm]
              exact Nat.mul_le_mul_left _ (Fam.card_wrap_le hK (A.cnt_mono a r htt g))
          _ = (univ.filter (fun i : Fin N => i.val = A.rk a r t g)).card *
                (K ^ (N - 1) * (A.cnt a r t' g - A.cnt a r t g)) := by rw [sum_const, smul_eq_mul]
          _ ≤ 1 * (K ^ (N - 1) * (A.cnt a r t' g - A.cnt a r t g)) := Nat.mul_le_mul_right _ hone
          _ = K ^ (N - 1) * (A.cnt a r t' g - A.cnt a r t g) := one_mul _
    _ = K ^ (N - 1) * ∑ g ∈ S, (A.cnt a r t' g - A.cnt a r t g) := by rw [mul_sum]

/-- A violated hop of (γ) needs a wrap of a digit at or above its group. -/
theorem Valid.card_viol_calm_le (hA : A.Valid T) {a K r : ℕ} (hK : 0 < K) {η : ι × ℕ × ℕ}
    (hη : η ∈ A.calm a r) :
    ((Fintype.piFinset (fun _ : Fin N => range K)).filter
        (fun ω => η ∈ A.violated a K r ω)).card ≤
      K ^ (N - 1) * ∑ g ∈ (A.occ a r η.2.1).filter (fun g => A.hgrp a r η ≤ g),
        (A.cnt a r η.2.2 g - A.cnt a r η.2.1 g) := by
  obtain ⟨hηH, hcons, habove⟩ := mem_filter.mp hη
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hA.hop_in η hηH
  refine le_trans (card_le_card fun ω hω => ?_)
    (card_wrap_union A hK a r η.2.1 η.2.2 (by omega) _)
  obtain ⟨hωΩ, hviol⟩ := mem_filter.mp hω
  have hviol := (mem_filter.mp hviol).2
  refine mem_filter.mpr ⟨hωΩ, ?_⟩
  by_contra hno
  push Not at hno
  have hp : A.hgrp a r η ∈ A.occ a r η.2.1 := by
    refine mem_image.mpr ⟨A.vh η.1, mem_univ _, ?_⟩
    unfold group hgrp
    rw [hA.band_of_mem hp1 (by omega)]
  have hu : A.hgrp a r η ∈ A.occ a r η.2.2 := mem_image.mpr ⟨A.vh η.1, mem_univ _, hcons⟩
  have hΔ : A.cnt a r η.2.1 (A.hgrp a r η) < A.cnt a r η.2.2 (A.hgrp a r η) := by
    unfold cnt
    refine card_lt_card ⟨fun F hF => ?_, fun hsub => ?_⟩
    · obtain ⟨-, h1, h2⟩ := mem_filter.mp hF
      exact mem_filter.mpr ⟨mem_univ _, by omega, h2⟩
    · have := mem_filter.mp (hsub (mem_filter.mpr ⟨mem_univ η.1, by omega, flr_grp_le a r _⟩))
      omega
  have hlt := A.clock_lt_of_no_wrap a K r ω (by omega) hp hu habove hΔ
    (fun g hg hg0 i hi => hno g (mem_filter.mpr ⟨hg, hg0⟩) i hi)
  exact absurd hviol (not_le.mpr hlt)

/-- **Exchange of summation.** Over the hops of (γ), the total growth of the counts at or above
their groups is at most `N 2^(a+1) ∑ d`: an event of scale `s` is counted by pairs `(η, g)` with
`η` spanning it and `g` a group of floor at most `s`, at most `N 2^(floor + a)` of them per floor
by the overlap bound. -/
theorem Valid.sum_calm_growth_le (hA : A.Valid T) {a r : ℕ} (ha : 0 < a) (hr : r < a) :
    ∑ η ∈ A.calm a r, ∑ g ∈ (A.occ a r η.2.1).filter (fun g => A.hgrp a r η ≤ g),
        (A.cnt a r η.2.2 g - A.cnt a r η.2.1 g) ≤ N * 2 ^ (a + 1) * ∑ F, A.d F := by
  calc ∑ η ∈ A.calm a r, ∑ g ∈ (A.occ a r η.2.1).filter (fun g => A.hgrp a r η ≤ g),
        (A.cnt a r η.2.2 g - A.cnt a r η.2.1 g)
      ≤ ∑ η ∈ A.calm a r, ∑ g ∈ (A.occ a r η.2.1).filter (fun g => A.hgrp a r η ≤ g),
          (univ.filter (fun F => η.2.1 < A.o F ∧ A.o F ≤ η.2.2 ∧
            flr a r g ≤ lam (A.d F))).card :=
        sum_le_sum fun η _ => sum_le_sum fun g _ => A.cnt_sub_le a r g
    _ = ∑ η ∈ A.calm a r, ∑ F, (((A.occ a r η.2.1).filter (fun g => A.hgrp a r η ≤ g)).filter
          (fun g => η.2.1 < A.o F ∧ A.o F ≤ η.2.2 ∧ flr a r g ≤ lam (A.d F))).card :=
        sum_congr rfl fun η _ => sum_card_filter_comm _ _
          (fun g F => η.2.1 < A.o F ∧ A.o F ≤ η.2.2 ∧ flr a r g ≤ lam (A.d F))
    _ = ∑ F, ∑ η ∈ A.calm a r, (((A.occ a r η.2.1).filter (fun g => A.hgrp a r η ≤ g)).filter
          (fun g => η.2.1 < A.o F ∧ A.o F ≤ η.2.2 ∧ flr a r g ≤ lam (A.d F))).card := sum_comm
    _ ≤ ∑ F, ∑ η ∈ A.calm a r, (((range (lam (A.d F) + 1)).filter
          (fun g => flr a r g ≤ lam (A.d F))).filter
          (fun g => A.hgrp a r η ≤ g ∧ η.2.1 < A.o F ∧ A.o F ≤ η.2.2)).card := by
        refine sum_le_sum fun F _ => sum_le_sum fun η _ => card_le_card fun g hg => ?_
        obtain ⟨hgS, h1, h2, h3⟩ := mem_filter.mp hg
        obtain ⟨-, hg0⟩ := mem_filter.mp hgS
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (le_of_flr_le hr h3)),
          h3⟩, hg0, h1, h2⟩
    _ = ∑ F, ∑ g ∈ (range (lam (A.d F) + 1)).filter (fun g => flr a r g ≤ lam (A.d F)),
          ((A.calm a r).filter (fun η => A.hgrp a r η ≤ g ∧ η.2.1 < A.o F ∧
            A.o F ≤ η.2.2)).card :=
        sum_congr rfl fun F _ => sum_card_filter_comm _ _
          (fun η g => A.hgrp a r η ≤ g ∧ η.2.1 < A.o F ∧ A.o F ≤ η.2.2)
    _ ≤ ∑ F, ∑ g ∈ (range (lam (A.d F) + 1)).filter (fun g => flr a r g ≤ lam (A.d F)),
          N * 2 ^ a * 2 ^ flr a r g := by
        refine sum_le_sum fun F _ => sum_le_sum fun g _ => ?_
        calc ((A.calm a r).filter (fun η => A.hgrp a r η ≤ g ∧ η.2.1 < A.o F ∧
              A.o F ≤ η.2.2)).card
            ≤ (A.H.filter (fun η => η.2.1 < A.o F ∧ A.o F ≤ η.2.2 ∧
                lam (A.d η.1) < flr a r g + a)).card := by
              refine card_le_card fun η hη => ?_
              obtain ⟨hηC, h1, h2, h3⟩ := mem_filter.mp hη
              exact mem_filter.mpr ⟨(mem_filter.mp hηC).1, h2, h3, lt_flr_add ha h1⟩
          _ ≤ N * (2 ^ (flr a r g + a) - 1) := hA.overlap _ _
          _ ≤ N * 2 ^ a * 2 ^ flr a r g := by
              rw [mul_assoc, ← pow_add, add_comm a]
              exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤ ∑ F, N * 2 ^ (a + 1) * A.d F := by
        refine sum_le_sum fun F _ => ?_
        rw [← mul_sum]
        set R := (range (lam (A.d F) + 1)).filter (fun g => flr a r g ≤ lam (A.d F))
        have hinj : Set.InjOn (flr a r) R := fun g _ g' _ h => flr_injective hr h
        have h1 : ∑ g ∈ R, 2 ^ flr a r g ≤ 2 ^ (lam (A.d F) + 1) := by
          calc ∑ g ∈ R, 2 ^ flr a r g = ∑ x ∈ R.image (flr a r), 2 ^ x :=
                (sum_image (f := fun x => 2 ^ x) hinj).symm
            _ ≤ ∑ x ∈ range (lam (A.d F) + 1), 2 ^ x := by
                refine sum_le_sum_of_subset fun x hx => ?_
                obtain ⟨g, hg, rfl⟩ := mem_image.mp hx
                exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hg).2)
            _ ≤ 2 ^ (lam (A.d F) + 1) := (Fam.sum_pow_two_lt _).le
        have h2 : 2 ^ lam (A.d F) ≤ A.d F :=
          Nat.pow_log_le_self 2 (by have := hA.d_pos F; omega)
        calc N * 2 ^ a * ∑ g ∈ R, 2 ^ flr a r g ≤ N * 2 ^ a * 2 ^ (lam (A.d F) + 1) :=
              Nat.mul_le_mul_left _ h1
          _ = N * 2 ^ (a + 1) * 2 ^ lam (A.d F) := by ring
          _ ≤ N * 2 ^ (a + 1) * A.d F := Nat.mul_le_mul_left _ h2
    _ = N * 2 ^ (a + 1) * ∑ F, A.d F := by rw [mul_sum]

/-- (γ) for one offset, summed over `ω`. -/
theorem Valid.sum_viol_calm_le (hA : A.Valid T) {a K r : ℕ} (ha : 0 < a) (hK : 0 < K)
    (hr : r < a) :
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin N => range K),
      ((A.calm a r).filter (fun η => η ∈ A.violated a K r ω)).card ≤
    K ^ (N - 1) * (N * 2 ^ (a + 1) * ∑ F, A.d F) := by
  calc ∑ ω ∈ Fintype.piFinset (fun _ : Fin N => range K),
        ((A.calm a r).filter (fun η => η ∈ A.violated a K r ω)).card
      = ∑ η ∈ A.calm a r, ((Fintype.piFinset (fun _ : Fin N => range K)).filter
          (fun ω => η ∈ A.violated a K r ω)).card :=
        sum_card_filter_comm _ _ (fun ω η => η ∈ A.violated a K r ω)
    _ ≤ ∑ η ∈ A.calm a r, K ^ (N - 1) * ∑ g ∈ (A.occ a r η.2.1).filter
          (fun g => A.hgrp a r η ≤ g), (A.cnt a r η.2.2 g - A.cnt a r η.2.1 g) :=
        sum_le_sum fun η hη => hA.card_viol_calm_le hK hη
    _ = K ^ (N - 1) * ∑ η ∈ A.calm a r, ∑ g ∈ (A.occ a r η.2.1).filter
          (fun g => A.hgrp a r η ≤ g), (A.cnt a r η.2.2 g - A.cnt a r η.2.1 g) := by
        rw [mul_sum]
    _ ≤ K ^ (N - 1) * (N * 2 ^ (a + 1) * ∑ F, A.d F) :=
        Nat.mul_le_mul_left _ (hA.sum_calm_growth_le ha hr)

/-! ### (δ) Descents without group changes -/

variable (A) in
/-- (δ) The times at which no virtual head changes group. -/
noncomputable def still (a r T : ℕ) : Finset ℕ :=
  (Ico 1 T).filter (fun t => ∀ v, A.group a r v (t - 1) = A.group a r v t)

omit [DecidableEq ι] in
/-- A descent without a group change needs a wrap. -/
theorem card_desc_still_le (A : Fam ι N) {a K r : ℕ} (hK : 0 < K) {t : ℕ}
    (ht : t ∈ A.still a r T) :
    ((Fintype.piFinset (fun _ : Fin N => range K)).filter
        (fun ω => t ∈ A.descents a K r ω T)).card ≤
      K ^ (N - 1) * (N * (univ.filter (fun F => A.o F = t)).card) := by
  classical
  obtain ⟨ht1, hall⟩ := mem_filter.mp ht
  have ht1' := mem_Ico.mp ht1
  have hocc : A.occ a r (t - 1) = A.occ a r t := by
    unfold occ
    exact image_congr fun v _ => hall v
  refine le_trans (card_le_card fun ω hω => ?_)
    ((card_wrap_union A hK a r (t - 1) t (by omega) (A.occ a r (t - 1))).trans ?_)
  · obtain ⟨hωΩ, hdesc⟩ := mem_filter.mp hω
    have hdesc := (mem_filter.mp hdesc).2
    refine mem_filter.mpr ⟨hωΩ, ?_⟩
    by_contra hno
    push Not at hno
    exact absurd hdesc (not_lt.mpr (A.clock_le_of_no_wrap a K r ω (by omega) hocc hno))
  · refine Nat.mul_le_mul_left _ ?_
    calc ∑ g ∈ A.occ a r (t - 1), (A.cnt a r t g - A.cnt a r (t - 1) g)
        ≤ ∑ g ∈ A.occ a r (t - 1), (univ.filter (fun F => A.o F = t)).card := by
          refine sum_le_sum fun g _ => (A.cnt_sub_le a r g).trans (card_le_card fun F hF => ?_)
          obtain ⟨-, h1, h2, -⟩ := mem_filter.mp hF
          exact mem_filter.mpr ⟨mem_univ _, by omega⟩
      _ = (A.occ a r (t - 1)).card * (univ.filter (fun F => A.o F = t)).card := by
          rw [sum_const, smul_eq_mul]
      _ ≤ N * (univ.filter (fun F => A.o F = t)).card :=
          Nat.mul_le_mul_right _ (A.card_occ_le a r _)

omit [DecidableEq ι] in
/-- (δ) for one offset, summed over `ω`: at most `K^(N-1) N` per event. -/
theorem sum_desc_still_le (A : Fam ι N) {a K r : ℕ} (hK : 0 < K) :
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin N => range K),
      ((A.still a r T).filter (fun t => t ∈ A.descents a K r ω T)).card ≤
    K ^ (N - 1) * (N * Fintype.card ι) := by
  classical
  calc ∑ ω ∈ Fintype.piFinset (fun _ : Fin N => range K),
        ((A.still a r T).filter (fun t => t ∈ A.descents a K r ω T)).card
      = ∑ t ∈ A.still a r T, ((Fintype.piFinset (fun _ : Fin N => range K)).filter
          (fun ω => t ∈ A.descents a K r ω T)).card :=
        sum_card_filter_comm _ _ (fun ω t => t ∈ A.descents a K r ω T)
    _ ≤ ∑ t ∈ A.still a r T, K ^ (N - 1) * (N * (univ.filter (fun F => A.o F = t)).card) :=
        sum_le_sum fun t ht => A.card_desc_still_le hK ht
    _ = K ^ (N - 1) * (N * ∑ t ∈ A.still a r T, (univ.filter (fun F => A.o F = t)).card) := by
        rw [mul_sum, mul_sum]
    _ ≤ K ^ (N - 1) * (N * Fintype.card ι) := by
        refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)
        calc ∑ t ∈ A.still a r T, (univ.filter (fun F => A.o F = t)).card
            = ∑ F, ((A.still a r T).filter (fun t => A.o F = t)).card :=
              sum_card_filter_comm _ _ (fun t F => A.o F = t)
          _ ≤ ∑ _F : ι, 1 := sum_le_sum fun F _ => card_le_one.mpr fun x hx y hy =>
              (mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2
          _ = Fintype.card ι := by simp

/-! ### The total cost -/

omit [DecidableEq ι] in
/-- The digits lie in `[0, K)`. -/
theorem digit_lt (A : Fam ι N) {a K r : ℕ} (hK : 0 < K) (ω : Fin N → ℕ) (t : ℕ) (i : Fin N) :
    A.digit a K r ω t i < K := by
  rw [digit_eq_filter]
  rcases ((A.occ a r t).filter (fun g => A.rk a r t g = i.val)).eq_empty_or_nonempty with
    he | ⟨g, hg⟩
  · rw [he, sum_empty]; exact hK
  · have : (A.occ a r t).filter (fun g => A.rk a r t g = i.val) = {g} := by
      refine eq_singleton_iff_unique_mem.mpr ⟨hg, fun g' hg' => ?_⟩
      obtain ⟨h1, h2⟩ := mem_filter.mp hg
      obtain ⟨h1', h2'⟩ := mem_filter.mp hg'
      exact A.rk_inj a r h1' h1 (h2'.trans h2.symm)
    rw [this, sum_singleton]
    exact Nat.mod_lt _ hK

theorem violated_subset (A : Fam ι N) (a K r : ℕ) (ω : Fin N → ℕ) :
    A.violated a K r ω ⊆ A.incons a r ∪ A.higher a r ∪
      (A.calm a r).filter (fun η => η ∈ A.violated a K r ω) := by
  intro η hη
  obtain ⟨hηH, -⟩ := mem_filter.mp hη
  by_cases hc : A.group a r (A.vh η.1) η.2.2 = A.hgrp a r η
  · by_cases hab : A.above a r η.2.1 (A.hgrp a r η) = A.above a r η.2.2 (A.hgrp a r η)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hηH, hc, hab⟩, hη⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hηH, hc, hab⟩))
  · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hηH, hc⟩))

omit [DecidableEq ι] in
theorem descents_subset (A : Fam ι N) (a K r : ℕ) (ω : Fin N → ℕ) (T : ℕ) :
    A.descents a K r ω T ⊆ A.gchange a r T ∪
      (A.still a r T).filter (fun t => t ∈ A.descents a K r ω T) := by
  classical
  intro t ht
  obtain ⟨ht1, -⟩ := mem_filter.mp ht
  by_cases hall : ∀ v, A.group a r v (t - 1) = A.group a r v t
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨ht1, hall⟩, ht⟩)
  · push Not at hall
    exact mem_union_left _ (mem_filter.mpr ⟨ht1, hall⟩)

/-- **The total cost.** Summed over all offsets `r < a` and all `ω ∈ [0, K)^N`, the violated
hops and the descents number at most `K^N · 4N²T + a · K^(N-1) · 2^(a+1) N²T`. -/
theorem Valid.cost_sum_le (hA : A.Valid T) {a K : ℕ} (ha : 0 < a) (hK : 0 < K) :
    ∑ r ∈ range a, ∑ ω ∈ Fintype.piFinset (fun _ : Fin N => range K),
      ((A.violated a K r ω).card + (A.descents a K r ω T).card) ≤
    K ^ N * (4 * N ^ 2 * T) + a * (K ^ (N - 1) * (2 ^ (a + 1) * N ^ 2 * T)) := by
  set Ω := Fintype.piFinset (fun _ : Fin N => range K)
  set D := ∑ F, A.d F
  have hD : 2 * D ≤ N * T := hA.sum_d_all
  have hcard : Fintype.card ι ≤ D := by
    calc Fintype.card ι = ∑ _F : ι, 1 := by simp
      _ ≤ D := sum_le_sum fun F _ => hA.d_pos F
  set X : ℕ → ℕ := fun r => (A.incons a r).card + (A.higher a r).card + (A.gchange a r T).card
  set Y : ℕ → (Fin N → ℕ) → ℕ := fun r ω =>
    ((A.calm a r).filter (fun η => η ∈ A.violated a K r ω)).card +
      ((A.still a r T).filter (fun t => t ∈ A.descents a K r ω T)).card
  have hpt : ∀ r ω, (A.violated a K r ω).card + (A.descents a K r ω T).card ≤ X r + Y r ω := by
    intro r ω
    have h1 := (card_le_card (A.violated_subset a K r ω)).trans
      ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    have h2 := (card_le_card (A.descents_subset a K r ω T)).trans (card_union_le _ _)
    simp only [X, Y]
    omega
  have hY : ∀ r ∈ range a, ∑ ω ∈ Ω, Y r ω ≤ K ^ (N - 1) * (2 ^ (a + 1) * N ^ 2 * T) := by
    intro r hr
    simp only [Y]
    rw [sum_add_distrib]
    have h1 := hA.sum_viol_calm_le (K := K) ha hK (mem_range.mp hr)
    have h2 := A.sum_desc_still_le (a := a) (r := r) (T := T) hK
    have h4 : N * Fintype.card ι ≤ N * 2 ^ (a + 1) * D := by
      calc N * Fintype.card ι ≤ N * D := Nat.mul_le_mul_left _ hcard
        _ = N * 1 * D := by ring
        _ ≤ N * 2 ^ (a + 1) * D :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ Nat.one_le_two_pow)
    have h3 : N * 2 ^ (a + 1) * D + N * Fintype.card ι ≤ 2 ^ (a + 1) * N ^ 2 * T := by
      calc N * 2 ^ (a + 1) * D + N * Fintype.card ι
          ≤ N * 2 ^ (a + 1) * D + N * 2 ^ (a + 1) * D := Nat.add_le_add_left h4 _
        _ = 2 ^ (a + 1) * N * (2 * D) := by ring
        _ ≤ 2 ^ (a + 1) * N * (N * T) := Nat.mul_le_mul_left _ hD
        _ = 2 ^ (a + 1) * N ^ 2 * T := by ring
    calc _ ≤ K ^ (N - 1) * (N * 2 ^ (a + 1) * D) + K ^ (N - 1) * (N * Fintype.card ι) :=
          Nat.add_le_add h1 h2
      _ = K ^ (N - 1) * (N * 2 ^ (a + 1) * D + N * Fintype.card ι) := by ring
      _ ≤ K ^ (N - 1) * (2 ^ (a + 1) * N ^ 2 * T) := Nat.mul_le_mul_left _ h3
  have hX : ∑ r ∈ range a, X r ≤ 4 * N ^ 2 * T := by
    simp only [X]
    rw [sum_add_distrib, sum_add_distrib]
    have h1 : ∑ r ∈ range a, (A.incons a r).card ≤ N * T :=
      (sum_le_sum fun r _ => hA.card_incons_le a r).trans (hA.sum_gjumps ha)
    have h2 := hA.sum_higher_le ha
    have h3 : ∑ r ∈ range a, (A.gchange a r T).card ≤ N * T :=
      (sum_le_sum fun r _ => hA.card_gchange_le a r).trans (hA.sum_gjumps ha)
    have h4 : N * T ≤ N ^ 2 * T := Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) N)
    have e1 : 2 * N * (N * T) = 2 * (N ^ 2 * T) := by ring
    have e2 : 4 * N ^ 2 * T = 4 * (N ^ 2 * T) := by ring
    omega
  calc ∑ r ∈ range a, ∑ ω ∈ Ω, ((A.violated a K r ω).card + (A.descents a K r ω T).card)
      ≤ ∑ r ∈ range a, ∑ ω ∈ Ω, (X r + Y r ω) :=
        sum_le_sum fun r _ => sum_le_sum fun ω _ => hpt r ω
    _ = ∑ r ∈ range a, (K ^ N * X r + ∑ ω ∈ Ω, Y r ω) := by
        refine sum_congr rfl fun r _ => ?_
        rw [sum_add_distrib, sum_const, Fam.card_piFinset_range, smul_eq_mul]
    _ ≤ ∑ r ∈ range a, (K ^ N * X r + K ^ (N - 1) * (2 ^ (a + 1) * N ^ 2 * T)) :=
        sum_le_sum fun r hr => Nat.add_le_add_left (hY r hr) _
    _ = K ^ N * ∑ r ∈ range a, X r + a * (K ^ (N - 1) * (2 ^ (a + 1) * N ^ 2 * T)) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, card_range, smul_eq_mul]
    _ ≤ K ^ N * (4 * N ^ 2 * T) + a * (K ^ (N - 1) * (2 ^ (a + 1) * N ^ 2 * T)) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hX) _

/-- **Averaging.** Some offset `r < a` and some `ω ∈ [0, K)^N` give a cut of at most
`4N²T/a + 2^(a+1) N²T/K` elements. -/
theorem Valid.exists_cheap (hA : A.Valid T) {a K : ℕ} (ha : 0 < a) (hK : 0 < K) :
    ∃ r < a, ∃ ω ∈ Fintype.piFinset (fun _ : Fin N => range K),
      a * K ^ N * ((A.violated a K r ω).card + (A.descents a K r ω T).card) ≤
        K ^ N * (4 * N ^ 2 * T) + a * (K ^ (N - 1) * (2 ^ (a + 1) * N ^ 2 * T)) := by
  set Ω := Fintype.piFinset (fun _ : Fin N => range K)
  set B := K ^ N * (4 * N ^ 2 * T) + a * (K ^ (N - 1) * (2 ^ (a + 1) * N ^ 2 * T))
  have hne : ((range a) ×ˢ Ω).Nonempty :=
    ⟨(0, fun _ => 0), mem_product.mpr ⟨mem_range.mpr ha,
      Fintype.mem_piFinset.mpr fun _ => mem_range.mpr hK⟩⟩
  have hsum : ∑ x ∈ (range a) ×ˢ Ω,
      a * K ^ N * ((A.violated a K x.1 x.2).card + (A.descents a K x.1 x.2 T).card) ≤
      ∑ _x ∈ (range a) ×ˢ Ω, B := by
    rw [sum_const, card_product, card_range, Fam.card_piFinset_range, smul_eq_mul, ← mul_sum,
      sum_product]
    exact Nat.mul_le_mul_left _ (hA.cost_sum_le ha hK)
  obtain ⟨⟨r, ω⟩, hx, hle⟩ := exists_le_of_sum_le hne hsum
  obtain ⟨hr, hω⟩ := mem_product.mp hx
  exact ⟨r, mem_range.mp hr, ω, hω, hle⟩

end Fam

end BoundedNesting
