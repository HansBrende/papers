import BoundedStackDepth.Prominence
import BoundedStackDepth.Decomposition

/-!
# The prominence of a top

For a top `τ` of height `H` (`Decomposition.lean`):
* `height_le_prom`: `H ≤ prom τ`, by the owner lemma (P1) for the outermost ladder hop (so the
  scale `σ_τ` is at least `band H`);
* `prom_le_of_left`, `prom_le_of_right`: if an earlier point at least as high, or a later point strictly
  higher, is reached without the walk dropping below `y`, then `prom τ ≤ x τ − y`. The valley side
  vanishes after an up-step (`valley_eq_zero_of_step_up`). With `y` the base of `τ`, the prominence is exactly `H`;
  this is the cap for boundary hops.
-/

namespace BoundedStackDepth

open BoundedNesting Finset

variable {x : ℕ → ℤ} {T : ℕ}

/-- The valley prominence vanishes at a time just above its predecessor. -/
theorem valley_eq_zero_of_step_up {t : ℕ} (ht : 1 ≤ t) (hx : x (t - 1) < x t) : valley x T t = 0 :=
  peak_eq_zero_of_left (x := fun s => -x s) ht (show -x t ≤ -x (t - 1) by omega)

/-- **Left cap.** If `t` is just above its predecessor, and an earlier point `s` at least as high is
reached without dropping below `y`, then `prom t ≤ x t − y`. -/
theorem prom_le_of_left {t s : ℕ} {y : ℤ} (ht : 1 ≤ t) (hup : x (t - 1) < x t)
    (hst : s < t) (hxs : x t ≤ x s) (hy : ∀ r, s ≤ r → r ≤ t → y ≤ x r) :
    (prom x T t : ℤ) ≤ x t - y := by
  have hc := lt_colL (T := T) (y := y - 1) hst hxs (fun r h1 h2 => by have := hy r h1 h2; omega)
  have hyt := hy t hst.le le_rfl
  have := le_max_left (colL x T t) (colR x T t)
  unfold prom
  rw [valley_eq_zero_of_step_up ht hup, max_eq_left (Nat.zero_le _)]
  unfold peak
  omega

/-- **Right cap.** If `t` is just above its predecessor, and a later point `s < T` strictly higher is
reached without dropping below `y`, then `prom t ≤ x t − y`. -/
theorem prom_le_of_right {t s : ℕ} {y : ℤ} (ht : 1 ≤ t) (hup : x (t - 1) < x t) (hts : t < s)
    (hsT : s < T) (hxs : x t < x s) (hy : ∀ r, t ≤ r → r ≤ s → y ≤ x r) :
    (prom x T t : ℤ) ≤ x t - y := by
  have hc := lt_colR (T := T) (y := y - 1) hts hsT hxs (fun r h1 h2 => by have := hy r h1 h2; omega)
  have hp := peak_eq (x := x) (show t < T by omega)
  have := le_max_right (colL x T t) (colR x T t)
  unfold prom
  rw [valley_eq_zero_of_step_up ht hup, max_eq_left (Nat.zero_le _)]
  omega

/-- **The prominence of a top is at least its height.** -/
theorem height_le_prom (hx : IsWalk x) {τ : ℕ} (hτ : τ ∈ tops x T) : height x T τ ≤ prom x T τ := by
  obtain ⟨e, he, hc, -⟩ := exists_ladder_outer hx hτ
  obtain ⟨hh, hu, ho⟩ := (mem_ladder hx).mp he
  have := sub_le_prom hu ho hh.2.1
  omega

end BoundedStackDepth
