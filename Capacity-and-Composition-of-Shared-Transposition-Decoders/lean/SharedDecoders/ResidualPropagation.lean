import SharedDecoders.ResidualProgram

/-! The explicit chronological sum for the complete affine comparison program.
No stage is replaced by a normal form: each correction is propagated through
exactly the later linear updates and the final readout. -/

namespace SharedDecoders

open scoped BigOperators

variable {F V W Y : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup Y] [Module F Y]

def baselineOffset (L : ℕ → V →ₗ[F] V) (g : ℕ → V) (j : V) : ℕ → V
  | 0 => j
  | n + 1 => L n (baselineOffset L g j n) + g n

/-- For `i < n`, the maps after update `i`, in their actual execution order. -/
def residualPropagation (L : ℕ → V →ₗ[F] V) : ℕ → ℕ → V →ₗ[F] V
  | 0, _ => LinearMap.id
  | n + 1, i => if i < n then (L n).comp (residualPropagation L n i) else LinearMap.id

omit [AddCommGroup W] [Module F W] in
theorem residualOffset_eq_sum (L : ℕ → V →ₗ[F] V) (g : ℕ → V)
    (j : V) (e : ℕ → W → V) (x : W) (n : ℕ) :
    residualOffset L g j e x n = baselineOffset L g j n +
      ∑ i ∈ Finset.range n, residualPropagation L n i (e i x) := by
  induction n with
  | zero => simp [residualOffset, baselineOffset]
  | succ n ih =>
    rw [residualOffset, ih, map_add, map_sum, baselineOffset, Finset.sum_range_succ]
    have hs : (∑ i ∈ Finset.range n, L n (residualPropagation L n i (e i x))) =
        ∑ i ∈ Finset.range n, residualPropagation L (n + 1) i (e i x) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [residualPropagation, Finset.mem_range.mp hi, ite_true,
        LinearMap.comp_apply]
    rw [hs]
    simp only [residualPropagation, lt_self_iff_false, ite_false, LinearMap.id_apply]
    abel

/-- A replay with any fixed correction tuple has the baseline linear part and
the explicitly propagated joint offset. -/
theorem residual_readout_sum (L : ℕ → V →ₗ[F] V) (g : ℕ → V)
    (J : W →ₗ[F] V) (j : V) (O : V →ₗ[F] Y) (o : Y)
    (e : ℕ → W → V) (x : W) (n : ℕ) :
    O (residualRun L g J j e x n) + o =
      (O.comp (residualLinearPart L J n)) x + (O (baselineOffset L g j n) + o) +
        ∑ i ∈ Finset.range n, (O.comp (residualPropagation L n i)) (e i x) := by
  rw [residualRun_eq, residualOffset_eq_sum, map_add, map_add, map_sum]
  simp only [LinearMap.comp_apply]
  abel

/-- Substituting the residuals of the actual nonlinear program reproduces every
update and includes its affine initialization and final readout. -/
theorem actual_readout_sum (T : ℕ → V → V) (L : ℕ → V →ₗ[F] V)
    (g : ℕ → V) (J : W →ₗ[F] V) (j : V) (O : V →ₗ[F] Y) (o : Y)
    (x : W) (n : ℕ) :
    O (actualRun T J j x n) + o =
      (O.comp (residualLinearPart L J n)) x + (O (baselineOffset L g j n) + o) +
        ∑ i ∈ Finset.range n,
          (O.comp (residualPropagation L n i)) (actualResidual T L g J j i x) := by
  rw [actualRun_eq_residualRun]
  exact residual_readout_sum L g J j O o _ x n

/-- Different insertion spaces at different ports require no common-width
padding. Only the actual image of each supplied correction enters the sum. -/
theorem actual_readout_insertions {U : ℕ → Type*}
    [∀ i, AddCommGroup (U i)] [∀ i, Module F (U i)]
    (T : ℕ → V → V) (L : ℕ → V →ₗ[F] V) (g : ℕ → V)
    (J : W →ₗ[F] V) (j : V) (O : V →ₗ[F] Y) (o : Y)
    (E : ∀ i, U i →ₗ[F] V) (u : ∀ i, W → U i) (x : W) (n : ℕ)
    (he : ∀ i < n, actualResidual T L g J j i x = E i (u i x)) :
    O (actualRun T J j x n) + o =
      (O.comp (residualLinearPart L J n)) x + (O (baselineOffset L g j n) + o) +
        ∑ i ∈ Finset.range n,
          ((O.comp (residualPropagation L n i)).comp (E i)) (u i x) := by
  rw [actual_readout_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [he i (Finset.mem_range.mp hi), LinearMap.comp_apply]

end SharedDecoders
