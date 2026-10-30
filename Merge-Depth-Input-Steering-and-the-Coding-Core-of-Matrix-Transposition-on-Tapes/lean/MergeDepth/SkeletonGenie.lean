import MergeDepth.ColdGenie
import MergeDepth.SkeletonWalk

/-!
# A genie for a skeleton class (Lemma 4.6)

The dependency DAG of a skeleton class is that of its coarse work walks `skel w (xs j)`: state edges
and the long hops of the coarse walks (Lemma 4.5(a)). If one member of the class has work walks
`xs` that start at `0` and enter every cell at most `V` times, its coarse walks enter every block
at most `2V` times (Lemma 4.2), so none of their hops is deep at `2V`, and the cold genie of
Lemma 3.1, built from the eighth paper's Theorem F at owner-load `4V - 1` and periodic reveals,
has bounded full depth.

`skel_genie`: for `ε > 0` and `P ≥ 1` there is a set `Γ` with `P |Γ| ≤ P ε T + T` such that every
`Γ`-free path of the dependency DAG of the coarse work walks has at most `DF k (4V - 1) ε ⋅ P`
vertices. `skel_genie_cost` is Lemma 4.6 with its constants: cost `β_w |Γ| ≤ ε L` and full depth at
most `D₁ P - 1`.
-/

namespace MergeDepth

open Finset BoundedNesting

variable {k : ℕ}

open Classical in
/-- Coarse walks of bounded-entry walks have no deep steps at twice the entry bound. -/
theorem rCount_deep_coarse_eq_zero {w : ℤ} (hw : 0 < w) {xs : Fin k → ℕ → ℤ}
    (hx : ∀ j, IsWalk (xs j)) (h0 : ∀ j, xs j 0 = 0) {V T : ℕ}
    (hV : ∀ j c, (entries (xs j) c (T - 1)).card ≤ V) (π : List ℕ) :
    rCount (DeepStep (fun j => skel w (xs j)) T (2 * V)) π = 0 := by
  -- no long hop of a coarse walk lies at a pair entered more than `2V` times
  have hnone : ∀ a b, ¬ DeepStep (fun j => skel w (xs j)) T (2 * V) a b := by
    rintro a b ⟨η, hη, -, hl⟩
    apply hl
    refine mem_filter.mpr ⟨hη, fun hheavy => ?_⟩
    obtain ⟨-, hgt⟩ := mem_heavyPairs.mp hheavy
    have := card_entries_skel_le hw (hx η.1) (h0 η.1) (hV η.1) (skel w (xs η.1) η.2.1)
    simp only at hgt
    omega
  induction π with
  | nil => rfl
  | cons a π ih =>
    cases π with
    | nil => rfl
    | cons b π =>
      simp only [rCount, hnone a b, ↓reduceIte, zero_add]
      exact ih

open Classical in
/-- **Lemma 4.6, the path bound.** -/
theorem skel_genie (hk : 1 ≤ k) {V : ℕ} (hV : 1 ≤ V) {ε : ℝ} (hε : 0 < ε) {P : ℕ} (hP : 1 ≤ P)
    {w : ℤ} (hw : 0 < w) (xs : Fin k → ℕ → ℤ) (hx : ∀ j, IsWalk (xs j)) (h0 : ∀ j, xs j 0 = 0)
    (T : ℕ) (hentry : ∀ j c, (entries (xs j) c (T - 1)).card ≤ V) :
    ∃ Γ : Finset ℕ, (P * Γ.card : ℝ) ≤ P * ε * T + T ∧
      ∀ π, IsDepPath (fun j => skel w (xs j)) T π → LinNet.GFree Γ π →
        π.length ≤ DF k (4 * V - 1) ε * P := by
  have hV2 : 1 ≤ 2 * V := by omega
  obtain ⟨Γ, hcard, hpath⟩ := cold_genie hk hV2 hε hP (fun j => skel w (xs j))
    (fun j => isWalk_skel hw (hx j)) T
  refine ⟨Γ, hcard, fun π hπ hfree => ?_⟩
  have := hpath π hπ hfree (rCount_deep_coarse_eq_zero hw hx h0 hentry π)
  rwa [show 2 * (2 * V) - 1 = 4 * V - 1 by omega] at this

open Classical in
/-- **Lemma 4.6.** With `C = max(c, 1)`, `ε'' = ε/(4 β_w C)`, `P = ⌈4 β_w C/ε⌉` and `T ≤ c (L + 1)`,
for coarse work walks `s` of a member whose work walks start at `0` and enter every cell at most `V`
times, there is a genie, chosen from `s` and `T` alone, of cost `β_w |Γ| ≤ ε L`, all of whose
`Γ`-free paths in the dependency DAG of `s` have at most `DF k (4V - 1) ε'' ⋅ P` vertices. -/
theorem skel_genie_cost (hk : 1 ≤ k) {V β L T : ℕ} (hV : 1 ≤ V) (hβ : 1 ≤ β) (hL : 1 ≤ L)
    {c ε : ℝ} (hε : 0 < ε) (hT : (T : ℝ) ≤ c * (L + 1)) {w : ℤ} (hw : 0 < w)
    (s : Fin k → ℕ → ℤ)
    (hs : ∃ xs : Fin k → ℕ → ℤ, (∀ j, IsWalk (xs j)) ∧ (∀ j, xs j 0 = 0) ∧
      (∀ j c, (entries (xs j) c (T - 1)).card ≤ V) ∧ ∀ j, s j = skel w (xs j)) :
    ∃ Γ : Finset ℕ, (β * Γ.card : ℝ) ≤ ε * L ∧
      ∀ π, IsDepPath s T π → LinNet.GFree Γ π →
        π.length ≤ DF k (4 * V - 1) (ε / (4 * β * max c 1)) * ⌈4 * β * max c 1 / ε⌉₊ := by
  obtain ⟨xs, hx, h0, hentry, hsx⟩ := hs
  have hseq : s = fun j => skel w (xs j) := funext hsx
  subst hseq
  set C := max c 1
  have hC : 1 ≤ C := le_max_right c 1
  have hβC : (0 : ℝ) < 4 * β * C := by
    have : (1 : ℝ) ≤ β := by exact_mod_cast hβ
    positivity
  set P := ⌈4 * β * C / ε⌉₊
  have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  obtain ⟨Γ, hcard, hpath⟩ := skel_genie hk hV (div_pos hε hβC) hP hw xs hx h0 T hentry
  refine ⟨Γ, ?_, hpath⟩
  have hPge : 4 * β * C / ε ≤ (P : ℝ) := Nat.le_ceil _
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hT' : (T : ℝ) ≤ C * (L + 1) := hT.trans (by
    have : (0 : ℝ) ≤ L + 1 := by positivity
    exact mul_le_mul_of_nonneg_right (le_max_left c 1) this)
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hβ' : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have h1 : (Γ.card : ℝ) ≤ ε / (4 * β * C) * T + T / P := by
    have : (P : ℝ) * Γ.card ≤ P * (ε / (4 * β * C)) * T + T := hcard
    calc (Γ.card : ℝ) = (P * Γ.card) / P := by field_simp
      _ ≤ (P * (ε / (4 * β * C)) * T + T) / P := by gcongr
      _ = ε / (4 * β * C) * T + T / P := by field_simp
  have h2 : (T : ℝ) / P ≤ ε / (4 * β * C) * T := by
    rw [div_le_iff₀ hPpos]
    have : ε / (4 * β * C) * P ≥ 1 := by
      rw [ge_iff_le, ← div_le_iff₀' (div_pos hε hβC), one_div_div]
      exact hPge
    have hT0 : (0 : ℝ) ≤ T := by positivity
    nlinarith
  have h3 : (β : ℝ) * Γ.card ≤ ε * T / (2 * C) := by
    have : (β : ℝ) * Γ.card ≤ β * (2 * (ε / (4 * β * C) * T)) := by
      gcongr
      linarith
    calc (β : ℝ) * Γ.card ≤ β * (2 * (ε / (4 * β * C) * T)) := this
      _ = ε * T / (2 * C) := by field_simp; ring
  have hC0 : (0 : ℝ) < C := by linarith
  calc (β : ℝ) * Γ.card ≤ ε * T / (2 * C) := h3
    _ ≤ ε * (C * (L + 1)) / (2 * C) := by gcongr
    _ = ε * (L + 1) / 2 := by field_simp
    _ ≤ ε * L := by nlinarith

end MergeDepth
