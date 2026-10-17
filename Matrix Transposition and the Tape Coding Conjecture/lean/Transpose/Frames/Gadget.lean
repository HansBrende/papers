import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

/-!
# The cycle bound for shear-frame gadgets

Abstract model of a shear-frame (XOR-frame) gadget: a gadget has `W` wires; wire `w` carries a
*frame path* `S w :: path w` (rational `m × m` matrices: source, frames at its gates in time order,
sink), the sink of wire `ρ w` equals `S w + 1`, and the cost of a wire is the sum of the ranks of
the consecutive frame differences along its path. The cycle bound: every nonempty `ρ`-invariant
set of wires has total cost at least `m`; hence `k` disjoint such sets force cost ≥ `k * m`.

This file does not depend on the frozen statement.
-/

namespace Transpose.ShearFrame

open Matrix Module

noncomputable section

/-- Frames: rational `m × m` matrices (address shears `(H, D) ↦ (H + M D, D)`). -/
abbrev Frame (m : ℕ) := Matrix (Fin m) (Fin m) ℚ

variable {m : ℕ}

/-- Subadditivity of rank. -/
theorem rank_add_le (A B : Frame m) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc finrank ℚ ↥(LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ finrank ℚ ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

theorem rank_sum_le {ι : Type} (s : Finset ι) (f : ι → Frame m) :
    (∑ i ∈ s, f i).rank ≤ ∑ i ∈ s, (f i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- A nonzero rational multiple of the identity has full rank. -/
theorem rank_natCast_smul_one {k : ℕ} (hk : k ≠ 0) : ((k : ℚ) • (1 : Frame m)).rank = m := by
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk)),
    Matrix.rank_one, Fintype.card_fin]

/-- Variation of the frame path `a :: l`: sum of ranks of consecutive differences. -/
def pathVar (a : Frame m) : List (Frame m) → ℕ
  | [] => 0
  | b :: rest => (b - a).rank + pathVar b rest

/-- Last frame of the path `a :: l`. -/
def pathEnd (a : Frame m) : List (Frame m) → Frame m
  | [] => a
  | b :: rest => pathEnd b rest

/-- Telescoping: the variation of a path dominates the rank of its endpoint difference. -/
theorem rank_sub_le_pathVar (a : Frame m) (l : List (Frame m)) :
    (pathEnd a l - a).rank ≤ pathVar a l := by
  induction l generalizing a with
  | nil => simp [pathEnd, pathVar]
  | cons b rest ih =>
    simp only [pathEnd, pathVar]
    have h2 : pathEnd b rest - a = (b - a) + (pathEnd b rest - b) := by abel
    rw [h2]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left (ih b) _)

/-- A gadget: wires `Fin W`, role permutation `ρ`, source frames `S`, and for each wire the list of
frames after its source (gate frames in time order, then the sink). Condition (G2): the sink of
wire `ρ w` is `S w + 1`. -/
structure Gadget (m W : ℕ) where
  ρ : Equiv.Perm (Fin W)
  S : Fin W → Frame m
  path : Fin W → List (Frame m)
  sink_eq : ∀ w, pathEnd (S (ρ w)) (path (ρ w)) = S w + 1

namespace Gadget

variable {W : ℕ} (G : Gadget m W)

/-- Sink frame of a wire. -/
def T (w : Fin W) : Frame m := pathEnd (G.S w) (G.path w)

/-- Cost of a wire and of the gadget. -/
def wireCost (w : Fin W) : ℕ := pathVar (G.S w) (G.path w)
def cost : ℕ := ∑ w, G.wireCost w

theorem T_ρ (w : Fin W) : G.T (G.ρ w) = G.S w + 1 := G.sink_eq w

/-- A `ρ`-invariant finset is mapped onto itself. -/
theorem map_eq_of_invariant (C : Finset (Fin W)) (hC : ∀ w ∈ C, G.ρ w ∈ C) :
    C.map G.ρ.toEmbedding = C := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact hC w hw
  · rw [Finset.card_map]

/-- **Cycle bound (one invariant set).** A nonempty `ρ`-invariant set of wires costs at least
`m`. -/
theorem invariant_cost_ge (C : Finset (Fin W)) (hC : ∀ w ∈ C, G.ρ w ∈ C) (hne : C.Nonempty) :
    m ≤ ∑ w ∈ C, G.wireCost w := by
  -- Σ (T w - S w) over C equals |C| • 1
  have hsum : ∑ w ∈ C, (G.T w - G.S w) = (C.card : ℚ) • (1 : Frame m) := by
    have h1 : ∑ w ∈ C, G.T w = ∑ w ∈ C, G.T (G.ρ w) := by
      conv_lhs => rw [← G.map_eq_of_invariant C hC]
      rw [Finset.sum_map]
      rfl
    rw [Finset.sum_sub_distrib, h1]
    simp only [G.T_ρ, Finset.sum_add_distrib, Finset.sum_const]
    rw [add_sub_cancel_left, Nat.cast_smul_eq_nsmul]
  have hcard : C.card ≠ 0 := Finset.card_ne_zero.mpr hne
  calc m = ((C.card : ℚ) • (1 : Frame m)).rank := (rank_natCast_smul_one hcard).symm
    _ = (∑ w ∈ C, (G.T w - G.S w)).rank := by rw [hsum]
    _ ≤ ∑ w ∈ C, (G.T w - G.S w).rank := rank_sum_le _ _
    _ ≤ ∑ w ∈ C, G.wireCost w :=
        Finset.sum_le_sum fun w _ => rank_sub_le_pathVar (G.S w) (G.path w)

/-- **Cycle bound (partition form).** `k` pairwise disjoint nonempty `ρ`-invariant sets of wires
force cost at least `k * m`. -/
theorem cost_ge_of_invariant_family {k : ℕ} (C : Fin k → Finset (Fin W))
    (hdisj : Pairwise fun i j => Disjoint (C i) (C j))
    (hinv : ∀ i, ∀ w ∈ C i, G.ρ w ∈ C i) (hne : ∀ i, (C i).Nonempty) :
    k * m ≤ G.cost := by
  classical
  have hbU : ∑ i, ∑ w ∈ C i, G.wireCost w = ∑ w ∈ Finset.univ.biUnion C, G.wireCost w := by
    rw [Finset.sum_biUnion]
    intro i _ j _ hij
    exact hdisj hij
  calc k * m = ∑ _i : Fin k, m := by simp
    _ ≤ ∑ i, ∑ w ∈ C i, G.wireCost w :=
        Finset.sum_le_sum fun i _ => G.invariant_cost_ge (C i) (hinv i) (hne i)
    _ = ∑ w ∈ Finset.univ.biUnion C, G.wireCost w := hbU
    _ ≤ ∑ w, G.wireCost w :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = G.cost := rfl

/-- Every gadget with at least one wire costs at least `m`. -/
theorem cost_ge_m (hW : 0 < W) : m ≤ G.cost :=
  G.invariant_cost_ge Finset.univ (fun _ _ => Finset.mem_univ _)
    ⟨⟨0, hW⟩, Finset.mem_univ _⟩

end Gadget

end

end Transpose.ShearFrame
