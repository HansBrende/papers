import SubcubicMemo.RankOneCore
import SubcubicMemo.ReversibleRules
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The all-line endpoint is the previously verified scalar theorem, applied
to evaluations of ambient linear functionals. Zero coordinates are omitted
from the capacity count, rather than silently counted as full scalar slots. -/

namespace SubcubicMemo.LowRank

open Module Finset MotionDepthCodes LeanMachine.SubspaceRecovery
open scoped BigOperators

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}

theorem scalar_arrangement_half (r : Recovery U) (hs : Supported r G)
    (hspan : (⨆ v, U v) = ⊤) (hdim : ∀ v, finrank K (U v) ≤ 1)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    2 * finrank K W ≤ ∑ v, finrank K (U v) := by
  classical
  have ha : ∀ v, ∃ a : U v, ∀ x : U v, ∃ c : K, c • a = x :=
    fun v => finrank_le_one_iff.mp (hdim v)
  choose a ha using ha
  have hc : ∀ v u, ∃ c : K, c • (a u : W) = r.component v u (a v) := by
    intro v u
    obtain ⟨c, hc⟩ := ha u ⟨r.component v u (a v), r.target v u ⟨a v, rfl⟩⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose c hc using hc
  let d : V → V → K := fun v u => if G.Adj v u then c v u else 0
  have hd : ∀ v u, d v u • (a u : W) = r.component v u (a v) := by
    intro v u
    by_cases h : G.Adj v u
    · simpa only [d, ite_eq_left h] using hc v u
    · simp [d, h, hs v u h]
  have hrow : ∀ v, ∑ u, d v u • (a u : W) = (a v : W) := by
    intro v
    simp_rw [hd]
    exact r.reconstruct v (a v)
  let ev : Module.Dual K W →ₗ[K] (V → K) :=
    { toFun := fun f v => f (a v)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective ev := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    have hz : ∀ v, f (a v) = 0 := fun v => congrFun hf v
    have hU : ∀ v, U v ≤ LinearMap.ker f := by
      intro v x hx
      obtain ⟨c, hc⟩ := ha v ⟨x, hx⟩
      have hc' : c • (a v : W) = x := congrArg Subtype.val hc
      rw [LinearMap.mem_ker, ← hc', map_smul, hz, smul_zero]
    have htop : (⊤ : Submodule K W) ≤ LinearMap.ker f := by
      rw [← hspan]
      exact iSup_le hU
    exact LinearMap.ker_eq_top.mp (top_le_iff.mp htop)
  let M : Matrix V V K := Matrix.of fun v u => (if u = v then 1 else 0) - d v u
  have hdiag : ∀ v, M v v = 1 := by intro v; simp [M, d]
  have hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0 := by
    intro v u hvu h
    simp [M, d, Ne.symm hvu, h]
  let A : Finset V := univ.filter (fun v => U v ≠ ⊥)
  have hle : LinearMap.range ev ≤ subCode M A := by
    rintro _ ⟨f, rfl⟩
    refine ⟨?_, ?_⟩
    · intro v hv
      have hzero : U v = ⊥ := by simpa [A] using hv
      have haz : (a v : W) = 0 := by simpa only [hzero, Submodule.mem_bot] using (a v).property
      change f (a v) = 0
      rw [haz, map_zero]
    · intro v _
      change ∑ u, ((if u = v then 1 else 0) - d v u) * f (a u) = 0
      simp only [sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul,
        sum_ite_eq', mem_univ, ite_true]
      have h := congrArg f (hrow v)
      simp only [map_sum, map_smul, smul_eq_mul] at h
      exact sub_eq_zero.mpr h.symm
  have hhalf := original_subCode_half (thmSHyp_of_cliqueFree hdiag hpat htri) A
    (fun v _ => star_of_degree_le_three hpat hdeg v)
  have hev : finrank K (LinearMap.range ev) = finrank K W := by
    rw [LinearMap.finrank_range_of_inj hinj, Subspace.dual_finrank_eq]
  have hle' := Submodule.finrank_mono hle
  have hcount : A.card = ∑ v, finrank K (U v) := by
    have hval : ∀ v, finrank K (U v) = if U v ≠ ⊥ then 1 else 0 := by
      intro v
      by_cases hv : U v = ⊥
      · rw [hv, finrank_bot]; simp
      · have hp : 0 < finrank K (U v) := by
          have hn : finrank K (U v) ≠ 0 := fun h => hv (Submodule.finrank_eq_zero.mp h)
          omega
        have hle := hdim v
        simp only [ite_eq_left hv]
        omega
    simp_rw [hval]
    rw [sum_boole]
    rfl
  rw [hev] at hle'
  omega

end SubcubicMemo.LowRank
