import TransposeFollowup.NestedPulseSchedule
import TransposeFollowup.PaddingCutInequality

/-! Construct the excursion layout from a graph partitioned into nested
matching pages in a fixed vertex order. Event times and head coordinates are
explicit. This discharges the finite walk/layout obligations; existence and
uniform paid generation of an expanding graph are still separate theorems. -/

namespace TransposeFollowup

open Classical Transpose.Tape
open scoped BigOperators
set_option autoImplicit false

structure NestedMatchingPages {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (k : ℕ) where
  src : G.edgeFinset → Fin v
  dst : G.edgeFinset → Fin v
  edge_eq : ∀ e, s(src e, dst e) = e.val
  page : G.edgeFinset → Fin k
  forward : ∀ e, (src e).val < (dst e).val
  nested : ∀ e f, e ≠ f → page e = page f →
    ((src e).val < (src f).val ∧ (dst f).val < (dst e).val) ∨
    ((src f).val < (src e).val ∧ (dst e).val < (dst f).val)

namespace NestedMatchingPages

variable {v k : ℕ} {G : SimpleGraph (Fin v)} [DecidableRel G.Adj]
    (D : NestedMatchingPages G k)

def start (r K offset : ℕ) (i : Fin v) : ℕ := offset + 7 * K * r * i.val
def horizon (r K offset : ℕ) : ℕ := offset + 7 * K * r * v

theorem start_gap (r K offset : ℕ) {i j : Fin v} (hij : i.val < j.val) :
    start r K offset i + 7 * K * r ≤ start r K offset j := by
  have hm := Nat.mul_le_mul_left (7 * K * r) (Nat.succ_le_of_lt hij)
  dsimp [start]
  nlinarith

theorem start_within (r K offset : ℕ) (i : Fin v) :
    start r K offset i + 7 * K * r ≤ horizon (v := v) r K offset := by
  have hm := Nat.mul_le_mul_left (7 * K * r) (Nat.succ_le_of_lt i.isLt)
  dsimp [start, horizon]
  nlinarith

def schedule (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K) :
    NestedPulseSchedule G.edgeFinset k (7 * K * r) where
  gap_pos := by positivity
  page := D.page
  opening e := start r K offset (D.src e) + K * r
  closing e := start r K offset (D.dst e) + K * r
  self_gap e := by
    have hg := start_gap r K offset (D.forward e)
    omega
  nested e f hne hp := by
    rcases D.nested e f hne hp with hg | hg
    · exact Or.inl ⟨by have := start_gap r K offset hg.1; omega,
        by have := start_gap r K offset hg.2; omega⟩
    · exact Or.inr ⟨by have := start_gap r K offset hg.1; omega,
        by have := start_gap r K offset hg.2; omega⟩

noncomputable def walk (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K) : Fin k → ℕ → ℤ :=
  (D.schedule r K offset hr hK).walk (4 * K * r)

noncomputable def base (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K) (e : G.edgeFinset) : ℤ :=
  4 * (K : ℤ) * (D.schedule r K offset hr hK).depth e

theorem nestedExcursion (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K) (e : G.edgeFinset) :
    NestedExcursion r K (start r K offset (D.src e) + K * r)
      (start r K offset (D.dst e) + K * r) (D.base r K offset hr hK e)
      (D.walk r K offset hr hK (D.page e)) := by
  let W := D.schedule r K offset hr hK
  have hL : 4 * K * r ≤ 7 * K * r := by nlinarith
  refine ⟨hr, hK, W.self_gap e, ?_, ?_, ?_⟩
  · intro t ha ht
    have hw := W.walk_rise hL e ha ht
    have he : W.opening e = start r K offset (D.src e) + K * r := rfl
    rw [he] at hw
    change W.walk (4 * K * r) (W.page e) t = _
    rw [hw]
    dsimp [base, W]
    ring
  · intro t ha hc
    have hw := W.walk_middle hL e ha hc
    change _ ≤ W.walk (4 * K * r) (W.page e) t
    convert hw using 1
    dsimp [base, W]
    ring
  · intro t hc ht
    have hw := W.walk_fall hL e hc ht
    have he : W.closing e = start r K offset (D.dst e) + K * r := rfl
    rw [he] at hw
    change W.walk (4 * K * r) (W.page e) t = _
    rw [hw]
    dsimp [base, W]
    ring

theorem base_separated (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K)
    (e f : G.edgeFinset) (hne : e ≠ f) (hp : D.page e = D.page f) :
    D.base r K offset hr hK e + 4 * K ≤ D.base r K offset hr hK f ∨
    D.base r K offset hr hK f + 4 * K ≤ D.base r K offset hr hK e := by
  let W := D.schedule r K offset hr hK
  have hs := W.gap_pos
  have bound : ∀ e f, W.opening e < W.opening f → W.page e = W.page f →
      D.base r K offset hr hK e + 4 * K ≤ D.base r K offset hr hK f := by
    intro e f ho hpage
    have hd := W.depth_strict hpage ho
    have hdi : (W.depth e : ℤ) + 1 ≤ W.depth f := by exact_mod_cast hd
    have hm := mul_le_mul_of_nonneg_left hdi (by positivity : 0 ≤ 4 * (K : ℤ))
    dsimp [base, W] at *
    nlinarith
  rcases W.nested e f hne hp with hg | hg
  · exact Or.inl (bound e f (by omega) hp)
  · exact Or.inr (bound f e (by omega) hp.symm)

noncomputable def layout (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K) :
    ExcursionLayout G r K k (horizon (v := v) r K offset) (D.walk r K offset hr hK) where
  r_pos := hr
  K_pos := hK
  start := start r K offset
  separated i j hne := by
    have hvne : i.val ≠ j.val := fun he => hne (Fin.ext he)
    rcases lt_or_gt_of_ne hvne with h | h
    · exact Or.inl (start_gap r K offset h)
    · exact Or.inr (start_gap r K offset h)
  within := start_within r K offset
  src := D.src
  dst := D.dst
  edge_eq := D.edge_eq
  page := D.page
  base := D.base r K offset hr hK
  excursion := D.nestedExcursion r K offset hr hK
  slabs := D.base_separated r K offset hr hK

theorem walk_unitSteps (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K) (p : Fin k) :
    UnitSteps (D.walk r K offset hr hK p) :=
  (D.schedule r K offset hr hK).walk_unitSteps (by nlinarith) p

theorem walk_zero (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K) (p : Fin k) :
    D.walk r K offset hr hK p 0 = 0 :=
  (D.schedule r K offset hr hK).walk_zero _ p

theorem walk_before (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K) (p : Fin k)
    {t : ℕ} (ht : t ≤ offset) : D.walk r K offset hr hK p t = 0 := by
  unfold walk NestedPulseSchedule.walk
  apply Finset.sum_eq_zero
  intro e _
  split_ifs
  · apply excursionPulse_before
    · have := (D.schedule r K offset hr hK).self_gap e
      omega
    · change t ≤ start r K offset (D.src e) + K * r
      dsimp [start]
      omega
  · rfl

theorem walk_reset (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K) (p : Fin k)
    {t : ℕ} (ht : horizon (v := v) r K offset ≤ t) : D.walk r K offset hr hK p t = 0 := by
  apply (D.schedule r K offset hr hK).walk_reset (T := horizon (v := v) r K offset) _ p ht
  intro e
  have hw := start_within r K offset (D.dst e)
  change start r K offset (D.dst e) + K * r + 4 * K * r ≤ _
  nlinarith

end NestedMatchingPages
end TransposeFollowup
