import SubcubicMemo.RankOneCore
import LeanMachine.LinearCodeRecovery
import MotionDepthCodes.Polymatroid

/-! The arbitrary-field rank specialization of the original polymatroid
certificates. No finite alphabet or uniform probability law is required. -/

namespace SubcubicMemo

open Module Finset MotionDepthCodes LeanMachine.SubspaceRecovery
open scoped BigOperators Classical

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

noncomputable def subspaceRank (U : V → Submodule K W) (A : Finset V) : ℝ :=
  finrank K (A.sup U : Submodule K W)

theorem subspaceRank_polymatroid (U : V → Submodule K W) :
    IsPolymatroid (subspaceRank U) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [subspaceRank]
    rw [Finset.sup_empty, finrank_bot, Nat.cast_zero]
  · intro A B h
    dsimp [subspaceRank]
    exact_mod_cast Submodule.finrank_mono (Finset.sup_mono (f := U) h)
  · intro A B
    have hle : (A ∩ B).sup U ≤ A.sup U ⊓ B.sup U :=
      le_inf (Finset.sup_mono inter_subset_left) (Finset.sup_mono inter_subset_right)
    have hm := Submodule.finrank_sup_add_finrank_inf_eq (A.sup U) (B.sup U)
    have hi := Submodule.finrank_mono hle
    have hn : finrank K ((A ∪ B).sup U : Submodule K W) +
        finrank K ((A ∩ B).sup U : Submodule K W) ≤
          finrank K (A.sup U : Submodule K W) + finrank K (B.sup U : Submodule K W) := by
      rw [Finset.sup_union]
      omega
    dsimp [subspaceRank]
    exact_mod_cast hn

theorem subspaceRank_valid {U : V → Submodule K W} (r : Recovery U)
    {G : SimpleGraph V} [DecidableRel G.Adj] (hs : LowRank.Supported r G) :
    IsValid (subspaceRank U) (nbhd G) := by
  intro v
  have hN : nbhd G v = G.neighborFinset v := by ext; simp [nbhd]
  have hle : U v ≤ (nbhd G v).sup U := by
    rw [hN]
    exact (LowRank.coordinate_le_rowSpan r hs v).trans
      (Finset.sup_mono_fun (fun u _ => r.target v u))
  dsimp [subspaceRank]
  rw [Finset.sup_insert, sup_eq_right.mpr hle]

theorem arrangement_half_of_rateBound {U : V → Submodule K W} (r : Recovery U)
    {G : SimpleGraph V} [DecidableRel G.Adj] (hs : LowRank.Supported r G)
    (hspan : (⨆ v, U v) = ⊤) (hgood : RateBound (nbhd G) (1 / 2)) :
    2 * finrank K W ≤ ∑ v, finrank K (U v) := by
  have h := hgood (subspaceRank U) (subspaceRank_polymatroid U) (subspaceRank_valid r hs)
  have htop : subspaceRank U univ = (finrank K W : ℝ) := by
    dsimp [subspaceRank]
    rw [Finset.sup_univ_eq_iSup, hspan, finrank_top]
  have hsingle (v : V) : subspaceRank U {v} = (finrank K (U v) : ℝ) := by
    dsimp [subspaceRank]
    rw [Finset.sup_singleton]
  rw [htop] at h
  simp_rw [hsingle] at h
  have hr : 2 * (finrank K W : ℝ) ≤ ((∑ v, finrank K (U v) : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    linarith
  exact_mod_cast hr

theorem observation_half_of_rateBound {A : V → Type*} [∀ v, AddCommGroup (A v)]
    [∀ v, Module K (A v)] [∀ v, FiniteDimensional K (A v)]
    (R : ∀ v, W →ₗ[K] A v) (T : ∀ v u, A u →ₗ[K] A v)
    (hrow : ∀ x v, ∑ u, T v u (R u x) = R v x)
    (hsep : ∀ x, (∀ v, R v x = 0) → x = 0)
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
    (hgood : RateBound (nbhd G) (1 / 2)) :
    2 * finrank K W ≤ ∑ v, finrank K (LinearMap.range (R v)) := by
  have hid : ∀ v, ∑ u, (R u).dualMap.comp (T v u).dualMap = (R v).dualMap := by
    intro v
    ext f x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.dualMap_apply]
    rw [← map_sum, hrow]
  obtain ⟨r, hz, _⟩ := recovery_of_generators (fun v => (R v).dualMap)
    (fun v u => (T v u).dualMap) hid
  have hspan : (⨆ v, LinearMap.range (R v).dualMap) = ⊤ := by
    simp_rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    rw [← Subspace.dualAnnihilator_iInf_eq]
    have hker : (⨅ v, LinearMap.ker (R v)) = ⊥ := by
      apply (Submodule.eq_bot_iff _).mpr
      intro x hx
      exact hsep x fun v => (iInf_le (fun v => LinearMap.ker (R v)) v) hx
    rw [hker, Submodule.dualAnnihilator_bot]
  have hs' : LowRank.Supported r G := by
    intro v u h
    apply hz v u
    ext f x
    simp [hs v u h]
  have h := arrangement_half_of_rateBound r hs' hspan hgood
  simpa only [Subspace.dual_finrank_eq,
    LinearMap.finrank_range_dualMap_eq_finrank_range] using h

theorem code_half_of_rateBound {A : V → Type*} [∀ v, AddCommGroup (A v)]
    [∀ v, Module K (A v)] [∀ v, FiniteDimensional K (A v)]
    (C : Submodule K (∀ v, A v)) (T : ∀ v u, A u →ₗ[K] A v)
    (hrow : ∀ x ∈ C, ∀ v, ∑ u, T v u (x u) = x v)
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
    (hgood : RateBound (nbhd G) (1 / 2)) :
    2 * finrank K C ≤ ∑ v, finrank K (LinearMap.range (coordinate C v)) := by
  apply observation_half_of_rateBound (coordinate C) T
    (fun x v => hrow x.val x.property v) _ hs hgood
  intro x hx
  apply Subtype.ext
  exact funext hx

end SubcubicMemo
