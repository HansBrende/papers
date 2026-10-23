import TransposeFollowup.EntropyObservation
import MotionDepthCodes.Polymatroid

/-!
# Storage codes and their entropic polymatroids

A storage code for side information `N` is a set `C` of words `x : V → α` in
which each symbol `x v` is determined by the symbols on `N v`. For a random word
`X` with this recoverability property, `S ↦ H(X_S)` is a valid polymatroid. So a
rate bound for `N` (`RateBound`) bounds every storage code, linear or not, over
every alphabet.

Entropy is the finite Shannon entropy of a deterministic observation
(`observationEntropy`) from the preceding paper, imported through a relative
path dependency. Its strong subadditivity gives submodularity here.
-/

namespace MotionDepthCodes

open Finset TransposeFollowup
open scoped BigOperators
set_option autoImplicit false

variable {V α : Type*} [DecidableEq V]

/-- The symbols of `x` on `S`, with `none` elsewhere. -/
def view (S : Finset V) (x : V → α) : V → Option α :=
  fun v => if v ∈ S then some (x v) else none

theorem view_eq_iff (S : Finset V) (x y : V → α) :
    view S x = view S y ↔ ∀ v ∈ S, x v = y v := by
  constructor
  · intro h v hv
    simpa [view, hv] using congrFun h v
  · intro h
    funext v
    by_cases hv : v ∈ S
    · simp [view, hv, h v hv]
    · simp [view, hv]

theorem view_factorsThrough {Ω : Type*} (X : Ω → V → α) {S T : Finset V} (hST : S ⊆ T) :
    (fun ω => view S (X ω)).FactorsThrough (fun ω => view T (X ω)) := by
  intro ω ω' h
  rw [view_eq_iff] at h ⊢
  exact fun v hv => h v (hST hv)

/-- The random word `X` is supported on a storage code for `N`: the symbol at
`v` is a function of the symbols on `N v`. -/
def IsRecoverable {Ω : Type*} (N : V → Finset V) (X : Ω → V → α) : Prop :=
  ∀ v ω ω', (∀ u ∈ N v, X ω u = X ω' u) → X ω v = X ω' v

/-- A storage code for `N`. -/
def IsStorageCode (N : V → Finset V) (C : Finset (V → α)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ v, (∀ u ∈ N v, x u = y u) → x v = y v

variable [Fintype V] [Fintype α]

/-- `H(X_S)`: the entropy of the symbols on `S` under the law `p`. -/
noncomputable def codeEntropy {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → V → α)
    (S : Finset V) : ℝ :=
  observationEntropy p (fun ω => view S (X ω))

section Law

variable {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → V → α)

theorem codeEntropy_empty (hp1 : ∑ ω, p ω = 1) : codeEntropy p X ∅ = 0 := by
  have heq : (fun ω => view (∅ : Finset V) (X ω)) = fun _ _ => none := by
    funext ω v
    simp [view]
  rw [codeEntropy, heq, observationEntropy_const, hp1, Real.negMulLog_one]

theorem codeEntropy_mono (hp : ∀ ω, 0 ≤ p ω) : Monotone (codeEntropy p X) := by
  intro S T hST
  exact observationEntropy_le_of_factorsThrough p hp _ _ (view_factorsThrough X hST)

theorem codeEntropy_union (hp : ∀ ω, 0 ≤ p ω) (S T : Finset V) :
    observationEntropy p (fun ω => (view S (X ω), view T (X ω))) =
      codeEntropy p X (S ∪ T) := by
  apply observationEntropy_eq_of_same_fibers p hp
  intro ω ω'
  simp only [Prod.mk.injEq, view_eq_iff, Finset.mem_union]
  constructor
  · rintro ⟨hS, hT⟩ v (hv | hv)
    · exact hS v hv
    · exact hT v hv
  · intro h
    exact ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩

theorem codeEntropy_submod (hp : ∀ ω, 0 ≤ p ω) (S T : Finset V) :
    codeEntropy p X (S ∪ T) + codeEntropy p X (S ∩ T) ≤
      codeEntropy p X S + codeEntropy p X T := by
  let a := fun ω => view S (X ω)
  let b := fun ω => view T (X ω)
  let c := fun ω => view (S ∩ T) (X ω)
  have hca : c.FactorsThrough a := view_factorsThrough X Finset.inter_subset_left
  have hcb : c.FactorsThrough b := view_factorsThrough X Finset.inter_subset_right
  have hcab : c.FactorsThrough (fun ω => (a ω, b ω)) :=
    fun _ _ h => hca (congrArg Prod.fst h)
  have h := observationEntropy_strong_subadditive p hp a b c
  rw [observationEntropy_pair_of_factorsThrough p hp _ c hcab,
    observationEntropy_pair_of_factorsThrough p hp a c hca,
    observationEntropy_pair_of_factorsThrough p hp b c hcb] at h
  rw [codeEntropy_union p X hp S T] at h
  exact h

/-- Entropy of the symbols on subsets is a polymatroid, for every law. -/
theorem codeEntropy_isPolymatroid (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) :
    IsPolymatroid (codeEntropy p X) :=
  ⟨codeEntropy_empty p X hp1, codeEntropy_mono p X hp, codeEntropy_submod p X hp⟩

/-- Recoverability makes the entropic polymatroid valid. -/
theorem codeEntropy_isValid (hp : ∀ ω, 0 ≤ p ω) {N : V → Finset V}
    (hX : IsRecoverable N X) : IsValid (codeEntropy p X) N := by
  intro v
  apply le_antisymm
  · apply observationEntropy_le_of_factorsThrough p hp
    intro ω ω' h
    rw [view_eq_iff] at h ⊢
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hX u ω ω' h
    · exact h u hu
  · exact codeEntropy_mono p X hp (Finset.subset_insert v (N v))

theorem codeEntropy_singleton_le [Nonempty α] (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (v : V) : codeEntropy p X {v} ≤ Real.log (Fintype.card α) := by
  have heq : codeEntropy p X {v} = observationEntropy p (fun ω => X ω v) := by
    apply observationEntropy_eq_of_same_fibers p hp
    intro ω ω'
    rw [view_eq_iff]
    simp
  rw [heq]
  exact entropy_le_log_card _ (pushforward_nonneg p hp _) (by rw [sum_pushforward, hp1])

/-- A rate bound, in entropy form: `H(X) ≤ c · Σ_v H(X_v)` for every law on a
storage code. -/
theorem codeEntropy_univ_le_of_rateBound {N : V → Finset V} {c : ℝ} (hN : RateBound N c)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (hX : IsRecoverable N X) :
    codeEntropy p X univ ≤ c * ∑ v, codeEntropy p X {v} :=
  hN _ (codeEntropy_isPolymatroid p X hp hp1) (codeEntropy_isValid p X hp hX)

end Law

/-- The uniform law on a nonempty code has entropy `log |C|`. -/
theorem codeEntropy_univ_uniform (C : Finset (V → α)) (hC : C.Nonempty) :
    codeEntropy (fun _ : C => ((C.card : ℝ))⁻¹) (fun x => (x : V → α)) univ =
      Real.log C.card := by
  have : Nonempty C := hC.to_subtype
  have hp : ∀ ω : C, (0 : ℝ) ≤ (fun _ : C => ((C.card : ℝ))⁻¹) ω :=
    fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have heq : codeEntropy (fun _ : C => ((C.card : ℝ))⁻¹) (fun x => (x : V → α)) univ =
      observationEntropy (fun _ : C => ((C.card : ℝ))⁻¹) id := by
    apply observationEntropy_eq_of_same_fibers _ hp
    intro ω ω'
    rw [view_eq_iff]
    simp only [Finset.mem_univ, true_implies, id]
    constructor
    · intro h
      exact Subtype.ext (funext h)
    · intro h v
      rw [h]
  rw [heq, observationEntropy_id]
  have hc : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  simp only [entropy, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
    Real.negMulLog, Real.log_inv]
  field_simp

/-- **Rate bounds for codes.** A rate bound `c` for `N` gives
`log |C| ≤ c · |V| · log |α|` for every storage code `C` over every alphabet. -/
theorem log_card_le_of_rateBound [Nonempty α] {N : V → Finset V} {c : ℝ} (hc : 0 ≤ c)
    (hN : RateBound N c) {C : Finset (V → α)} (hC : IsStorageCode N C) :
    Real.log C.card ≤ c * Fintype.card V * Real.log (Fintype.card α) := by
  have hα : 0 ≤ Real.log (Fintype.card α) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  rcases C.eq_empty_or_nonempty with hCe | hne
  · rw [hCe, Finset.card_empty, Nat.cast_zero, Real.log_zero]
    positivity
  · have hc0 : (0 : ℝ) < C.card := by exact_mod_cast hne.card_pos
    have hp : ∀ ω : C, (0 : ℝ) ≤ (fun _ : C => ((C.card : ℝ))⁻¹) ω :=
      fun _ => inv_nonneg.mpr hc0.le
    have hp1 : ∑ ω : C, (fun _ : C => ((C.card : ℝ))⁻¹) ω = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      field_simp
    have hX : IsRecoverable N (fun x : C => (x : V → α)) :=
      fun v ω ω' h => hC ω.1 ω.2 ω'.1 ω'.2 v h
    have h1 := codeEntropy_univ_le_of_rateBound _ _ hN hp hp1 hX
    rw [codeEntropy_univ_uniform C hne] at h1
    have h2 : ∑ v, codeEntropy (fun _ : C => ((C.card : ℝ))⁻¹) (fun x => (x : V → α)) {v} ≤
        ∑ _v : V, Real.log (Fintype.card α) :=
      Finset.sum_le_sum (fun v _ => codeEntropy_singleton_le _ _ hp hp1 v)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    calc Real.log C.card
        ≤ c * ∑ v, codeEntropy (fun _ : C => ((C.card : ℝ))⁻¹) (fun x => (x : V → α)) {v} := h1
      _ ≤ c * (Fintype.card V * Real.log (Fintype.card α)) :=
          mul_le_mul_of_nonneg_left h2 hc
      _ = c * Fintype.card V * Real.log (Fintype.card α) := by ring

/-- A rate bound with any constant: `log |C| ≤ max c 0 · |V| · log |α|`. -/
theorem log_card_le_of_rateBound' [Nonempty α] {N : V → Finset V} {c : ℝ}
    (hN : RateBound N c) {C : Finset (V → α)} (hC : IsStorageCode N C) :
    Real.log C.card ≤ max c 0 * Fintype.card V * Real.log (Fintype.card α) :=
  log_card_le_of_rateBound (le_max_right c 0) (hN.mono (le_max_left c 0)) hC

end MotionDepthCodes
