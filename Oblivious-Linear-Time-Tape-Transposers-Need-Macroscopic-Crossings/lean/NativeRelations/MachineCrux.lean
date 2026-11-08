import TapeStorageRates.TraceTransfer
import BoundedStackDepth.Machines
import BoundedStackDepth.LowAdaptivity

/-!
# Depth-Bounded Cone Relations and the Oblivious Machine Crux

Defines the family `SConeOf` of depth-bounded native cone relations for an oblivious machine and
proves that positive index-coding crux rate (`MachineCruxAt`) at the fourteenth paper's genie depth
excludes oblivious linear-time transposition (`machine_crux_excludes`).
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape BoundedNesting MergeDepth BoundedStackDepth
  TapeStorageRates

/-- **The cone systems of one machine** at size `(d, b)` and depth `D`: the conditions of
`BoundedStackDepth.SCone` for the fixed machine `M` (oblivious at length `L = d² b`, halting time
`T ≤ C (L + 1)`, exactly `L` appends, `Γ`-free dependency paths with at most `D` edges). -/
def SConeOf (M : TM) (C : ℝ) (D d b : ℕ) : Set (Fin (d * d * b) → Finset (Fin (d * d * b))) :=
  {I | ∃ (T : ℕ) (Γ : Finset ℕ),
    ObliviousOn M (inputsOfLength (d * d * b)) T ∧ (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1) ∧
    (appendList (traceAt M (d * d * b)) T).length = d * d * b ∧
    (∀ π, IsDepPath (traceAt M (d * d * b)).work T π → LinNet.GFree Γ π → π.length ≤ D + 1) ∧
    I = coneSystem (traceAt M (d * d * b)) T Γ d b}

/-- **The crux of one machine at depth `D` and rate `ρ`.** For every `η > 0`, at all large `d`
every index code for every cone system of `M` at depth `D` (width `entryBits d`) has at least
`(ρ - η) L` bits. Unlike `BoundedStackDepth.Crux`, it concerns one machine. -/
def MachineCruxAt (M : TM) (C : ℝ) (D : ℕ) (ρ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ I ∈ SConeOf M C D d (entryBits d),
    ∀ (m : ℕ) (E : (Fin (d * d * entryBits d) → Bool) → (Fin m → Bool)),
      IsIndexCode E I (tposOf d (entryBits d)) → (ρ - η) * (d * d * entryBits d : ℕ) ≤ m

/-- **A depth-independent crux rate** for one machine: the same `ρ` at every depth (the form of
Paper 5's row-word deficit for its rotated shear). -/
def MachineCrux (M : TM) (C ρ : ℝ) : Prop := ∀ D : ℕ, MachineCruxAt M C D ρ

/-- **The exclusion for one machine** (first Lean task: adapt `BoundedStackDepth.crux_excludes`
with `β = valueWidth M`). -/
theorem machine_crux_excludes {M : TM} {C ε ρ : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) (hερ : ε < ρ)
    (h : MachineCruxAt M C (genieDepth M.k (valueWidth M) C ε) ρ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ T : ℕ, ¬ ObliviousLinTime M d (entryBits d) C T := by
  obtain ⟨d₁, hd₁⟩ := h ((ρ - ε) / 2) (by linarith)
  refine ⟨max d₁ 1, fun d hd T ⟨hobl, hT, htr⟩ => ?_⟩
  have hd1 : 1 ≤ d := (le_max_right _ _).trans hd
  have hL : 1 ≤ d * d * entryBits d := Nat.mul_pos (Nat.mul_pos hd1 hd1) (one_le_entryBits d)
  obtain ⟨hM, hlen⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
  have hβ1 : 1 ≤ valueWidth M := (two_le_valueWidth M).trans' (by omega)
  obtain ⟨Γ, hcost, hpath⟩ := genie_of_trace M (List.ofFn fun _ : Fin (d * d * entryBits d) => false)
    hβ1 hL hC hε hT
  obtain ⟨E, hE⟩ := exists_indexCode hM le_rfl Γ
  have hmem : coneSystem (traceAt M (d * d * entryBits d)) T Γ d (entryBits d) ∈
      SConeOf M C (genieDepth M.k (valueWidth M) C ε) d (entryBits d) :=
    ⟨T, Γ, hobl, hT, hlen, fun π h1 h2 => (hpath π h1 h2).trans (Nat.le_succ _), rfl⟩
  have hbits := hd₁ d ((le_max_left _ _).trans hd) _ hmem _ E hE
  have hL' : (1 : ℝ) ≤ (d * d * entryBits d : ℕ) := by exact_mod_cast hL
  push_cast at hbits hcost hL'
  nlinarith

end NativeRelations
