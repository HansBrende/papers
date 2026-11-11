import AdaptiveTransfer.Storage

/-! Exact support-duration and persistent-cell consequences for actual native
execution prefixes. No information or future-use assumption is made. -/

namespace AdaptiveTransfer.ExecutionPrefix
open Transpose Finset

variable {M : TM} {w : List Bool} {T : ℕ} (E : ExecutionPrefix M w T)

theorem support_growth (h : Fin M.k) (window : Finset ℤ) {u v : ℕ}
    (huv : u ≤ v) (hv : v ≤ T) :
    (nonblankWithin (E.config v) h window).card ≤
      (nonblankWithin (E.config u) h window).card + (v - u) := by
  induction v, huv using Nat.le_induction with
  | base => simp
  | succ v huv ih =>
    have hg := native_support_growth_le_one (E.successful v (by omega)) h window
    have hp := ih (by omega)
    omega

theorem support_card_le_time (h : Fin M.k) (window : Finset ℤ) {v : ℕ}
    (hv : v ≤ T) : (nonblankWithin (E.config v) h window).card ≤ v := by
  have hg := E.support_growth h window (Nat.zero_le v) hv
  simpa [E.initial, nonblankWithin, init] using hg

/-- A dense terminal support supplies actual unchanged cells over every
preceding interval no longer than its density threshold. The exact loss is
the interval length; the usual half-density claim is a specialization. -/
theorem dense_persistent_interval (h : Fin M.k) (window : Finset ℤ)
    {v ℓ : ℕ} {D : ℝ} (hv : v ≤ T) (hℓ : (ℓ : ℝ) ≤ D)
    (hdense : D < ((nonblankWithin (E.config v) h window).card : ℝ)) :
    D < (v : ℝ) ∧ ∃ S : Finset ℤ,
      S ⊆ nonblankWithin (E.config v) h window ∧
      D - ℓ < (S.card : ℝ) ∧
      ∀ z ∈ S, ∀ t, v - ℓ ≤ t → t ≤ v →
        (E.config t).work h z = (E.config v).work h z := by
  have hvlarge : D < (v : ℝ) :=
    hdense.trans_le (by exact_mod_cast E.support_card_le_time h window hv)
  have hℓv : ℓ ≤ v := by exact_mod_cast (hℓ.trans hvlarge.le)
  obtain ⟨S, hS, hcount, hkeep⟩ := E.persistent_cells h window (Nat.sub_le v ℓ) hv
  rw [Nat.sub_sub_self hℓv] at hcount
  refine ⟨hvlarge, S, hS, ?_, hkeep⟩
  have hc : ((nonblankWithin (E.config v) h window).card : ℝ) ≤ S.card + ℓ := by
    exact_mod_cast hcount
  linarith

end AdaptiveTransfer.ExecutionPrefix
