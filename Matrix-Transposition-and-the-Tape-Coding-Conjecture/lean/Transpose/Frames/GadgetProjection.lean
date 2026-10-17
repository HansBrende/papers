import Mathlib
import Transpose.Frames.Gadget

/-!
# The projection bound: projection frames force cost ≥ W·m/2

Gadgets whose gate frames are idempotent rational matrices (projections, the kind used in the OpenAI
preprint), with arbitrary source frames. Cost of a wire = rank of consecutive differences along
`S w :: gates w ++ [T w]`. Theorem: `W * m ≤ 2 * cost`.
-/

namespace Transpose.ShearFrame

open Matrix Module

variable {m : ℕ}

theorem pathVar_append_single (a : Frame m) (l : List (Frame m)) (x : Frame m) :
    pathVar a (l ++ [x]) = pathVar a l + (x - pathEnd a l).rank := by
  induction l generalizing a with
  | nil => simp [pathVar, pathEnd]
  | cons b rest ih =>
    simp only [List.cons_append, pathVar, pathEnd]
    rw [ih b, Nat.add_assoc]

/-- For idempotent rational matrices, `rank (P + Q) ≥ rank P`. -/
theorem rank_le_rank_add_of_idem (P Q : Frame m) (hP : P * P = P) (hQ : Q * Q = Q) :
    P.rank ≤ (P + Q).rank := by
  classical
  let f := (P + Q).mulVecLin
  let U := LinearMap.range P.mulVecLin
  have hker : LinearMap.ker (f.domRestrict U) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ hfx
    rw [LinearMap.domRestrict_apply] at hfx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    have h1 : P *ᵥ (P *ᵥ y) = P *ᵥ y := by rw [Matrix.mulVec_mulVec, hP]
    have hfx' : P *ᵥ y + Q *ᵥ (P *ᵥ y) = 0 := by
      have := hfx
      simp only [f, Matrix.mulVecLin_apply, Matrix.add_mulVec, h1] at this
      exact this
    have hQx : Q *ᵥ (P *ᵥ y) = -(P *ᵥ y) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hfx'
    have h2 : Q *ᵥ (Q *ᵥ (P *ᵥ y)) = Q *ᵥ (P *ᵥ y) := by rw [Matrix.mulVec_mulVec, hQ]
    rw [hQx, Matrix.mulVec_neg, hQx, neg_neg] at h2
    -- h2 : P *ᵥ y = -(P *ᵥ y)
    have h4 : (2 : ℚ) • (P *ᵥ y) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h2]
      exact add_neg_cancel _
    have h3 : P *ᵥ y = 0 := (smul_eq_zero.mp h4).resolve_left (by norm_num)
    exact Subtype.ext (by simpa using h3)
  have hrn := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  rw [hker, finrank_bot, Nat.add_zero] at hrn
  have hle : finrank ℚ ↥(LinearMap.range (f.domRestrict U)) ≤ finrank ℚ ↥(LinearMap.range f) :=
    Submodule.finrank_mono (LinearMap.range_domRestrict_le_range f U)
  show finrank ℚ ↥U ≤ finrank ℚ ↥(LinearMap.range f)
  omega

theorem idem_one_sub (Q : Frame m) (hQ : Q * Q = Q) : (1 - Q) * (1 - Q) = 1 - Q := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hQ]
  abel

/-- `rank (1 - Q) ≥ m - rank Q` (subadditivity). -/
theorem rank_one_sub_ge (Q : Frame m) : m ≤ (1 - Q).rank + Q.rank := by
  have h := rank_add_le (1 - Q) Q
  rw [sub_add_cancel, Matrix.rank_one, Fintype.card_fin] at h
  exact h

/-- A gadget with idempotent gate frames: sources arbitrary, gates nonempty, sinks determined by
the role permutation. -/
structure PGadget (m W : ℕ) where
  ρ : Equiv.Perm (Fin W)
  S : Fin W → Frame m
  gates : Fin W → List (Frame m)
  gates_ne : ∀ w, gates w ≠ []
  T : Fin W → Frame m
  sink_eq : ∀ w, T (ρ w) = S w + 1
  idem : ∀ w, ∀ M ∈ gates w, M * M = M

namespace PGadget

variable {W : ℕ} (G : PGadget m W)

noncomputable def wireCost (w : Fin W) : ℕ := pathVar (G.S w) (G.gates w ++ [G.T w])
noncomputable def cost : ℕ := ∑ w, G.wireCost w

/-- First gate frame. -/
def first (w : Fin W) : Frame m := (G.gates w).headD 0
/-- Last gate frame. -/
def lastg (w : Fin W) : Frame m := pathEnd (G.first w) (G.gates w).tail

theorem first_idem (w : Fin W) : G.first w * G.first w = G.first w := by
  unfold first
  cases h : G.gates w with
  | nil => exact absurd h (G.gates_ne w)
  | cons g rest => exact G.idem w g (by rw [h]; exact List.mem_cons_self)

theorem pathEnd_mem (a : Frame m) (l : List (Frame m)) : pathEnd a l = a ∨ pathEnd a l ∈ l := by
  induction l generalizing a with
  | nil => left; rfl
  | cons b rest ih =>
    simp only [pathEnd]
    rcases ih b with h | h
    · right; rw [h]; exact List.mem_cons_self
    · right; exact List.mem_cons_of_mem _ h

theorem lastg_idem (w : Fin W) : G.lastg w * G.lastg w = G.lastg w := by
  unfold lastg
  rcases pathEnd_mem (G.first w) (G.gates w).tail with h | h
  · rw [h]; exact G.first_idem w
  · exact G.idem w _ (List.mem_of_mem_tail h)

/-- Decomposition of a wire's cost into source, internal and sink parts. -/
theorem wireCost_ge (w : Fin W) :
    (G.first w - G.S w).rank + (G.lastg w - G.first w).rank + (G.T w - G.lastg w).rank ≤
      G.wireCost w := by
  unfold wireCost lastg first
  cases h : G.gates w with
  | nil => exact absurd h (G.gates_ne w)
  | cons g rest =>
    simp only [List.headD_cons, List.tail_cons, List.cons_append, pathVar]
    rw [pathVar_append_single]
    have := rank_sub_le_pathVar g rest
    omega

theorem wrap_ge (w : Fin W) :
    (G.first w + 1 - G.lastg (G.ρ w)).rank ≤
      (G.first w - G.S w).rank + (G.T (G.ρ w) - G.lastg (G.ρ w)).rank := by
  rw [G.sink_eq w]
  have h := rank_add_le (G.first w - G.S w) (G.S w + 1 - G.lastg (G.ρ w))
  have e : G.first w - G.S w + (G.S w + 1 - G.lastg (G.ρ w)) = G.first w + 1 - G.lastg (G.ρ w) := by
    abel
  rw [e] at h
  exact h

theorem wrap_ge_first (w : Fin W) : (G.first w).rank ≤ (G.first w + 1 - G.lastg (G.ρ w)).rank := by
  have e : G.first w + 1 - G.lastg (G.ρ w) = G.first w + (1 - G.lastg (G.ρ w)) := by abel
  rw [e]
  exact rank_le_rank_add_of_idem _ _ (G.first_idem w) (idem_one_sub _ (G.lastg_idem _))

theorem wrap_ge_sub (w : Fin W) :
    m ≤ (G.first w + 1 - G.lastg (G.ρ w)).rank + (G.lastg (G.ρ w)).rank := by
  have e : G.first w + 1 - G.lastg (G.ρ w) = (1 - G.lastg (G.ρ w)) + G.first w := by abel
  have h1 : (1 - G.lastg (G.ρ w)).rank ≤ (G.first w + 1 - G.lastg (G.ρ w)).rank := by
    rw [e]
    exact rank_le_rank_add_of_idem _ _ (idem_one_sub _ (G.lastg_idem _)) (G.first_idem w)
  have h2 := rank_one_sub_ge (G.lastg (G.ρ w))
  omega

theorem internal_ge (w : Fin W) :
    (G.lastg w).rank ≤ (G.lastg w - G.first w).rank + (G.first w).rank ∧
    (G.first w).rank ≤ (G.lastg w - G.first w).rank + (G.lastg w).rank := by
  constructor
  · have h := rank_add_le (G.lastg w - G.first w) (G.first w)
    rwa [sub_add_cancel] at h
  · have h := rank_add_le (G.first w - G.lastg w) (G.lastg w)
    rw [sub_add_cancel] at h
    have e : (G.first w - G.lastg w).rank = (G.lastg w - G.first w).rank := by
      rw [← neg_sub, ← neg_one_smul ℚ (G.lastg w - G.first w)]
      exact Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (by norm_num))
    omega

/-- **Projection bound.** `W * m ≤ 2 * cost` for gadgets with idempotent gate frames. -/
theorem two_mul_cost_ge : W * m ≤ 2 * G.cost := by
  classical
  -- per-wire quantities
  let A : Fin W → ℕ := fun w => (G.first w - G.S w).rank
  let B : Fin W → ℕ := fun w => (G.lastg w - G.first w).rank
  let C : Fin W → ℕ := fun w => (G.T w - G.lastg w).rank
  let a : Fin W → ℕ := fun w => (G.first w).rank
  let b : Fin W → ℕ := fun w => (G.lastg w).rank
  let Wr : Fin W → ℕ := fun w => (G.first w + 1 - G.lastg (G.ρ w)).rank
  have hcost : ∑ w, (A w + B w + C w) ≤ G.cost :=
    Finset.sum_le_sum fun w _ => G.wireCost_ge w
  -- reindex C by ρ
  have hC : ∑ w, C (G.ρ w) = ∑ w, C w := Equiv.sum_comp G.ρ C
  have hwrap : ∑ w, Wr w ≤ ∑ w, (A w + C (G.ρ w)) :=
    Finset.sum_le_sum fun w _ => G.wrap_ge w
  have hX : ∑ w, a w ≤ ∑ w, Wr w := Finset.sum_le_sum fun w _ => G.wrap_ge_first w
  have hY : ∑ w, (m : ℕ) ≤ ∑ w, (Wr w + b (G.ρ w)) :=
    Finset.sum_le_sum fun w _ => G.wrap_ge_sub w
  have hbρ : ∑ w, b (G.ρ w) = ∑ w, b w := Equiv.sum_comp G.ρ b
  have hB1 : ∑ w, b w ≤ ∑ w, (B w + a w) := Finset.sum_le_sum fun w _ => (G.internal_ge w).1
  have hB2 : ∑ w, a w ≤ ∑ w, (B w + b w) := Finset.sum_le_sum fun w _ => (G.internal_ge w).2
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hcost hwrap hX hY hB1 hB2
  rw [hC] at hwrap
  rw [hbρ] at hY
  omega

end PGadget
end Transpose.ShearFrame
