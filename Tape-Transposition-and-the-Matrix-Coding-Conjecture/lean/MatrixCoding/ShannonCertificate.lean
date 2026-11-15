import MotionDepthCodes.Symmetry
import SoftRecovery.Decomposition

/-!
# Shared tools for paid Shannon certificates

Coordinate purchases, recovery steps, and preservation of the total recovery
error under symmetrization. These lemmas are shared by the Fano and grid
certificates; they do not assume exact recovery or a symmetric source.
-/

namespace LeanBacklog.ShannonCertificate

open Finset MotionDepthCodes SoftRecovery
open scoped BigOperators
set_option autoImplicit false

variable {V : Type*} [DecidableEq V]

/-- Repeated diminishing returns, with a uniform price for the added cells. -/
theorem adjoin_uniform
    {h : Finset V → ℝ} (hh : IsPolymatroid h) (S D : Finset V) (b : ℝ)
    (hb : ∀ v ∈ D, increment h S v ≤ b) :
    h (S ∪ D) ≤ h S + (D.card : ℝ) * b := by
  revert hb
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | @insert v D hv ih =>
    intro hb
    have hi := ih (fun u hu => hb u (mem_insert_of_mem hu))
    have hs := (increment_antitone hh
      (subset_union_left : S ⊆ S ∪ D) v).trans (hb v (mem_insert_self v D))
    simp only [increment] at hs
    rw [union_insert, card_insert_of_notMem hv, Nat.cast_add, Nat.cast_one]
    linarith

/-- Pay for an explicit list of additional coordinates. -/
theorem purchase {h : Finset V → ℝ} (hh : IsPolymatroid h)
    {s : ℝ} (hs : ∀ v, h {v} = s) {A B D : Finset V} {n : ℕ}
    (hcover : A ⊆ B ∪ D) (hcard : D.card = n) :
    h A ≤ h B + (n : ℝ) * s := by
  have h1 := adjoin_uniform hh B D s (fun v _ =>
    (increment_le_singleton hh B v).trans (hs v).le)
  rw [hcard] at h1
  exact (hh.mono hcover).trans h1

/-- A recovery step with its actual conditional-rank error retained. -/
theorem recover_paid {N : V → Finset V} {h : Finset V → ℝ} (hh : IsPolymatroid h)
    {e : ℝ} (he : ∀ v, increment h (N v) v = e)
    {A B D : Finset V} {n : ℕ}
    (hcover : A ⊆ B ∪ D) (hguard : ∀ v ∈ D, N v ⊆ B)
    (hcard : D.card = n) : h A ≤ h B + (n : ℝ) * e := by
  have h1 := adjoin_uniform hh B D e (fun v hv =>
    (increment_antitone hh (hguard v hv) v).trans (he v).le)
  rw [hcard] at h1
  exact (hh.mono hcover).trans h1


/-- Averaging preserves the sum of the actual per-coordinate recovery errors. -/
theorem sum_symmetrize_error [Fintype V] (N : V → Finset V) (h : Finset V → ℝ) :
    ∑ v, increment (symmetrize N h) (N v) v =
      ∑ v, increment h (N v) v := by
  have e : ∀ σ ∈ autSet N,
      (∑ v, (relabel σ h (insert v (N v)) - relabel σ h (N v))) =
        ∑ v, increment h (N v) v := by
    intro σ hσ
    have ha : ∀ v, (N v).map σ.toEmbedding = N (σ v) := mem_autSet.mp hσ
    simp only [relabel, map_insert, ha]
    change (∑ v, increment h (N (σ v)) (σ v)) = _
    exact Equiv.sum_comp σ (fun v => increment h (N v) v)
  simp only [increment, symmetrize, ← mul_sub, ← Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have he :
      (∑ σ ∈ autSet N,
        ∑ v, (relabel σ h (insert v (N v)) - relabel σ h (N v))) =
      ∑ σ ∈ autSet N, ∑ v, increment h (N v) v := by
    apply Finset.sum_congr rfl
    intro σ hσ
    exact e σ hσ
  rw [he]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp [(autSet_card_pos N).ne']
  rfl


end LeanBacklog.ShannonCertificate
