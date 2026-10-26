import BoundedNesting.Families

/-!
# Theorem F: depth reduction at bounded owner-load

Let `xs h`, `h < k`, be walks (pauses allowed, coupled arbitrarily), `H'` a set of their long
hops before `T`, and `own` an assignment of owners strictly inside the hops such that `H'` has
owner-load at most `ℓ` (`OwnerLoadLE`). The DAG `G(H')` has the vertices `[0, T)`, the state
edges `t → t - 1` and the hop edges `u → p` for `(p, u) ∈ hopPairs H'`.

`theoremF`: for every `ε > 0`, `G(H')` has a cut of at most `ε T` edges (state edges at the times
of `cutS`, hop edges in `cutH`) such that every path avoiding the cut carries fewer than
`DF k ℓ ε = 2^(2kℓ (⌈64k²ℓ²/ε⌉ + 5 + ⌈log₂(k²ℓ²/ε)⌉))` hop edges. The cut is that of the family
clock with `a = ⌈64k²ℓ²/ε⌉` and `K = 2^(a+4) ⌈k²ℓ²/ε⌉` at a cheap offset (`Fam.Valid.exists_cheap`).

`theoremF_owner`: the same for the owners of the paper, the first time strictly inside a hop at
which the distance from its cell is largest (`hopOwner`).
-/

namespace BoundedNesting

open Finset

variable {k : ℕ}

/-- The hop edges `u → p` of a set of hops, as pairs `(p, u)`. -/
def hopPairs (H' : Finset (Fin k × ℕ × ℕ)) : Finset (ℕ × ℕ) := H'.image (fun η => (η.2.1, η.2.2))

/-- `H'` has owner-load at most `ℓ` for the owners `own`: for every time `t`, head `h` and side
`σ`, the hops of `H'` of head `h` on side `σ` whose open intervals contain `t` have at most `ℓ`
distinct owners. -/
def OwnerLoadLE (xs : Fin k → ℕ → ℤ) (H' : Finset (Fin k × ℕ × ℕ)) (own : Fin k × ℕ × ℕ → ℕ)
    (ℓ : ℕ) : Prop :=
  ∀ (h : Fin k) (σ : Bool) (t : ℕ),
    ((H'.filter (fun η => η.1 = h ∧ side xs η = σ ∧ η.2.1 < t ∧ t < η.2.2)).image own).card ≤ ℓ

/-- The depth bound `D_F(k, ℓ, ε)` of Theorem F. -/
noncomputable def DF (k ℓ : ℕ) (ε : ℝ) : ℕ :=
  2 ^ (2 * k * ℓ * (⌈64 * (k : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / ε⌉₊ + 5 +
    ⌈Real.logb 2 ((k : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / ε)⌉₊))

/-- The arithmetic of the parameters. -/
theorem cost_le_eps {a c N T cost kl ε : ℝ} (ha : 0 < a) (hc : 0 < c) (hT : 0 ≤ T)
    (hε : 0 < ε) (hN : N ^ 2 = 4 * kl) (ha' : 64 * kl ≤ a * ε)
    (hc' : kl ≤ c * ε) (h : 8 * a * c * cost ≤ 32 * c * N ^ 2 * T + a * N ^ 2 * T) :
    cost ≤ ε * T := by
  have h1 : 32 * c * N ^ 2 * T + a * N ^ 2 * T ≤ 8 * a * c * (ε * T) := by
    rw [hN]
    have e1 : 2 * c * T * (64 * kl) ≤ 2 * c * T * (a * ε) :=
      mul_le_mul_of_nonneg_left ha' (by positivity)
    have e2 : 4 * a * T * kl ≤ 4 * a * T * (c * ε) := mul_le_mul_of_nonneg_left hc' (by positivity)
    have e3 : 0 ≤ a * c * ε * T := by positivity
    nlinarith
  exact le_of_mul_le_mul_left (h.trans h1) (by positivity)

/-- `⌈x⌉ ≤ 2^⌈log₂ x⌉` for `x > 0`. -/
theorem ceil_le_two_pow_clog {x : ℝ} (hx : 0 < x) : ⌈x⌉₊ ≤ 2 ^ ⌈Real.logb 2 x⌉₊ := by
  refine Nat.ceil_le.mpr ?_
  calc x = (2 : ℝ) ^ Real.logb 2 x := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
    _ ≤ (2 : ℝ) ^ (⌈Real.logb 2 x⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ = ((2 ^ ⌈Real.logb 2 x⌉₊ : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl

/-- **Theorem F** (for any owners strictly inside the hops). -/
theorem theoremF {ℓ T : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) {ε : ℝ} (hε : 0 < ε)
    (xs : Fin k → ℕ → ℤ) (hx : ∀ h, IsWalk (xs h))
    (H' : Finset (Fin k × ℕ × ℕ)) (hH : ∀ η ∈ H', IsHop (xs η.1) T η.2.1 η.2.2)
    (own : Fin k × ℕ × ℕ → ℕ) (hown : ∀ η ∈ H', η.2.1 < own η ∧ own η < η.2.2)
    (hload : OwnerLoadLE xs H' own ℓ) :
    ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 T ∧ cutH ⊆ hopPairs H' ∧
      ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * T ∧
      ∀ (f : ℕ → ℕ) (n : ℕ),
        (∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T ∧ f i ∉ cutS) ∨
          ((f (i + 1), f i) ∈ hopPairs H' ∧ (f (i + 1), f i) ∉ cutH)) →
        ((range n).filter (fun i => (f (i + 1), f i) ∈ hopPairs H')).card < DF k ℓ ε := by
  classical
  set N := 2 * k * ℓ with hN
  set a := ⌈64 * (k : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / ε⌉₊ with ha_def
  set m := ⌈Real.logb 2 ((k : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / ε)⌉₊ with hm_def
  set c := ⌈(k : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / ε⌉₊ with hc_def
  set K := 2 ^ (a + 4) * c with hK_def
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hkl : (0 : ℝ) < (k : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 := by positivity
  have ha_ge : 64 * (k : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / ε ≤ a := Nat.le_ceil _
  have hc_ge : (k : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / ε ≤ c := Nat.le_ceil _
  have ha : 0 < a := Nat.ceil_pos.mpr (by positivity)
  have hc : 0 < c := Nat.ceil_pos.mpr (by positivity)
  have hK : 0 < K := by positivity
  have hN1 : 1 ≤ N := by
    have : 1 ≤ k * ℓ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    rw [hN, mul_assoc]; omega
  set A := famData xs H' own ℓ (by omega)
  have hA : A.Valid T := famData_valid hx hH hown (by omega) hload
  obtain ⟨r, -, ω, -, hcost⟩ := hA.exists_cheap ha hK
  set cutH := (hopPairs H').filter (fun e => A.clock a K r ω e.2 ≤ A.clock a K r ω e.1)
  refine ⟨A.descents a K r ω T, cutH, filter_subset _ _, filter_subset _ _, ?_, ?_⟩
  · -- the size of the cut
    have hcH : cutH.card ≤ (A.violated a K r ω).card := by
      calc cutH.card ≤ ((A.violated a K r ω).image (fun x => x.2)).card := by
            refine card_le_card fun e he => ?_
            obtain ⟨he1, he2⟩ := mem_filter.mp he
            obtain ⟨η, hη, rfl⟩ := mem_image.mp he1
            have hq : key xs own η ∈ keys xs H' own := mem_image_of_mem _ hη
            refine mem_image.mpr ⟨(⟨key xs own η, hq⟩, η.2.1, η.2.2), ?_, rfl⟩
            refine mem_filter.mpr ⟨mem_famData_H.mpr ⟨η, mem_filter.mpr ⟨hη, rfl⟩, rfl, rfl⟩, ?_⟩
            exact he2
        _ ≤ (A.violated a K r ω).card := card_image_le
    set cost := (A.violated a K r ω).card + (A.descents a K r ω T).card
    have hle : (A.descents a K r ω T).card + cutH.card ≤ cost := by omega
    have hKp : (0 : ℝ) < (K : ℝ) ^ (N - 1) := by positivity
    have hKN : (K : ℝ) ^ N = (K : ℝ) ^ (N - 1) * K := by
      rw [← pow_succ, Nat.sub_add_cancel hN1]
    have hcostR : (a : ℝ) * (K : ℝ) ^ N * cost ≤
        (K : ℝ) ^ N * (4 * (N : ℝ) ^ 2 * T) +
          a * ((K : ℝ) ^ (N - 1) * (2 ^ (a + 1) * (N : ℝ) ^ 2 * T)) := by
      exact_mod_cast hcost
    have h1 : (K : ℝ) ^ (N - 1) * (a * K * cost) ≤
        (K : ℝ) ^ (N - 1) * (4 * K * (N : ℝ) ^ 2 * T + a * 2 ^ (a + 1) * (N : ℝ) ^ 2 * T) := by
      calc (K : ℝ) ^ (N - 1) * (a * K * cost) = a * ((K : ℝ) ^ (N - 1) * K) * cost := by ring
        _ ≤ ((K : ℝ) ^ (N - 1) * K) * (4 * (N : ℝ) ^ 2 * T) +
              a * ((K : ℝ) ^ (N - 1) * (2 ^ (a + 1) * (N : ℝ) ^ 2 * T)) := by
            rw [← hKN]; exact hcostR
        _ = (K : ℝ) ^ (N - 1) * (4 * K * (N : ℝ) ^ 2 * T + a * 2 ^ (a + 1) * (N : ℝ) ^ 2 * T) := by
            ring
    have h2 := le_of_mul_le_mul_left h1 hKp
    have hKR : (K : ℝ) = 2 ^ (a + 1) * (8 * c) := by
      rw [hK_def]; push_cast; ring
    have h3 : (2 : ℝ) ^ (a + 1) * (8 * a * c * cost) ≤
        (2 : ℝ) ^ (a + 1) * (32 * c * (N : ℝ) ^ 2 * T + a * (N : ℝ) ^ 2 * T) := by
      rw [hKR] at h2; linarith
    have h4 := le_of_mul_le_mul_left h3 (by positivity)
    have hcost' : (cost : ℝ) ≤ ε * T := by
      refine cost_le_eps (a := a) (c := c) (N := N) (kl := (k : ℝ) ^ 2 * (ℓ : ℝ) ^ 2)
        (by exact_mod_cast ha) (by exact_mod_cast hc) (by positivity) hε ?_ ?_ ?_ h4
      · rw [hN]; push_cast; ring
      · have := (div_le_iff₀ hε).mp ha_ge; linarith
      · exact (div_le_iff₀ hε).mp hc_ge
    calc (((A.descents a K r ω T).card + cutH.card : ℕ) : ℝ) ≤ cost := by exact_mod_cast hle
      _ ≤ ε * T := hcost'
  · -- the depth of the cut
    intro f n hpath
    have hdl := Fam.depth_le_of_lex (N := N) (K := K) (fun t => A.digit a K r ω t)
      (fun t i => Fam.digit_lt A hK ω t i) f n (fun i => (f (i + 1), f i) ∈ hopPairs H')
      (fun i hi => ?_) (fun i hi hm => ?_)
    · have hc2 : c ≤ 2 ^ m := ceil_le_two_pow_clog (by positivity)
      have hKle : K ≤ 2 ^ (a + 4 + m) := by
        calc K = 2 ^ (a + 4) * c := hK_def
          _ ≤ 2 ^ (a + 4) * 2 ^ m := Nat.mul_le_mul_left _ hc2
          _ = 2 ^ (a + 4 + m) := (pow_add _ _ _).symm
      calc ((range n).filter (fun i => (f (i + 1), f i) ∈ hopPairs H')).card ≤ K ^ N - 1 := hdl
        _ < K ^ N := Nat.sub_lt (pow_pos hK _) one_pos
        _ ≤ (2 ^ (a + 4 + m)) ^ N := Nat.pow_le_pow_left hKle _
        _ = 2 ^ ((a + 4 + m) * N) := (pow_mul _ _ _).symm
        _ ≤ DF k ℓ ε := by
            unfold DF
            rw [← ha_def, ← hm_def, ← hN]
            exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    · rcases hpath i hi with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
      · have hnd : ¬ (A.clock a K r ω (f i) < A.clock a K r ω (f i - 1)) :=
          fun hlt => h4 (mem_filter.mpr ⟨mem_Ico.mpr ⟨h2, h3⟩, hlt⟩)
        rw [show f (i + 1) = f i - 1 by omega]
        exact not_lt.mp hnd
      · have hnv : ¬ (A.clock a K r ω (f i) ≤ A.clock a K r ω (f (i + 1))) :=
          fun hle => h2 (mem_filter.mpr ⟨h1, hle⟩)
        exact (not_le.mp hnv).le
    · rcases hpath i hi with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
      · exfalso
        obtain ⟨η, hη, he⟩ := mem_image.mp hm
        have := (hH η hη).1
        simp only [Prod.mk.injEq] at he
        omega
      · have hnv : ¬ (A.clock a K r ω (f i) ≤ A.clock a K r ω (f (i + 1))) :=
          fun hle => h2 (mem_filter.mpr ⟨h1, hle⟩)
        exact not_le.mp hnv

open Classical in
/-- The owner of a long hop `(p, u)` of `x`: the first time strictly inside at which the distance
`|x t - x p|` from its cell is largest. -/
noncomputable def hopOwner (x : ℕ → ℤ) (p u : ℕ) : ℕ :=
  if h : ∃ o, p < o ∧ o < u ∧ ∀ t, p < t → t < u → |x t - x p| ≤ |x o - x p| then Nat.find h
  else p + 1

/-- The owner lies strictly inside the hop, at the largest distance from its cell, and earlier
times inside are strictly closer. -/
theorem hopOwner_spec (x : ℕ → ℤ) {p u : ℕ} (h : p + 2 ≤ u) :
    p < hopOwner x p u ∧ hopOwner x p u < u ∧
      (∀ t, p < t → t < u → |x t - x p| ≤ |x (hopOwner x p u) - x p|) ∧
      ∀ t, p < t → t < hopOwner x p u → |x t - x p| < |x (hopOwner x p u) - x p| := by
  classical
  have hex : ∃ o, p < o ∧ o < u ∧ ∀ t, p < t → t < u → |x t - x p| ≤ |x o - x p| := by
    obtain ⟨o, ho, hmax⟩ := (Ioo p u).exists_max_image (fun t => |x t - x p|)
      ⟨p + 1, mem_Ioo.mpr ⟨by omega, by omega⟩⟩
    obtain ⟨h1, h2⟩ := mem_Ioo.mp ho
    exact ⟨o, h1, h2, fun t ht1 ht2 => hmax t (mem_Ioo.mpr ⟨ht1, ht2⟩)⟩
  have he : hopOwner x p u = Nat.find hex := by
    unfold hopOwner; simp only [hex, ↓reduceDIte]
  obtain ⟨h1, h2, h3⟩ := Nat.find_spec hex
  rw [he]
  refine ⟨h1, h2, h3, fun t ht1 ht2 => ?_⟩
  have hmin := Nat.find_min hex ht2
  push Not at hmin
  obtain ⟨s, hs1, hs2, hs3⟩ := hmin ht1 (by omega)
  exact lt_of_lt_of_le hs3 (h3 s hs1 hs2)

/-- **Theorem F**, for the owners of the paper. -/
theorem theoremF_owner {ℓ T : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) {ε : ℝ} (hε : 0 < ε)
    (xs : Fin k → ℕ → ℤ) (hx : ∀ h, IsWalk (xs h))
    (H' : Finset (Fin k × ℕ × ℕ)) (hH : ∀ η ∈ H', IsHop (xs η.1) T η.2.1 η.2.2)
    (hload : OwnerLoadLE xs H' (fun η => hopOwner (xs η.1) η.2.1 η.2.2) ℓ) :
    ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 T ∧ cutH ⊆ hopPairs H' ∧
      ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * T ∧
      ∀ (f : ℕ → ℕ) (n : ℕ),
        (∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T ∧ f i ∉ cutS) ∨
          ((f (i + 1), f i) ∈ hopPairs H' ∧ (f (i + 1), f i) ∉ cutH)) →
        ((range n).filter (fun i => (f (i + 1), f i) ∈ hopPairs H')).card < DF k ℓ ε :=
  theoremF hk hℓ hε xs hx H' hH _
    (fun η hη => ⟨(hopOwner_spec _ (hH η hη).1).1, (hopOwner_spec _ (hH η hη).1).2.1⟩) hload

end BoundedNesting
