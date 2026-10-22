import TransposeFollowup.CommonStageLimits
import TransposeFollowup.ActualStageRegularity
import TransposeFollowup.StageAffineAssembly
import TransposeFollowup.FrozenHaltLimits

/-! The geometric recursion theorem for an actual physical head limit. Every
tick is charged by the supplied finite stage clock. Local regularity is used
only on positive-duration occurrences; the frozen discrete tail is retained.
Applying this theorem separately to every physical head suffices for the
previously formalized affine-time obstruction. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory
open scoped BigOperators
set_option autoImplicit false

theorem regular_physical_limit_locally_affine
    {B J : ℕ} {T : ℕ → ℕ} {P : ℕ → ℝ} {V : ℕ → List (Fin B) → ℝ}
    {rho a C M : ℝ} {hs : ℕ → ℕ → ℤ} {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hV : ∀ n w, 0 ≤ V n w) (hr : 0 ≤ rho) (hr1 : rho < 1)
    (ha : 0 ≤ a) (hP : ∀ n, 0 < P n) (hPinf : Tendsto P atTop atTop)
    (hc : ∀ n w, ∑ b : Fin B, V n (w++[b]) ≤ rho*V n w)
    (hroot : ∀ n, V n [] ≤ C*P n)
    (label : ∀ n, Fin (T n) → List (Fin B) × Fin J)
    (A E : ℕ → List (Fin B) → Fin J → ℕ)
    (hAE : ∀ n w j, A n w j ≤ E n w j) (hE : ∀ n w j, E n w j ≤ T n)
    (hstage : ∀ n w j (t : Fin (T n)),
      (A n w j ≤ t.val ∧ t.val < E n w j) ↔ label n t=(w,j))
    (hbudget : ∀ n w, ((∑ j : Fin J, (E n w j-A n w j) : ℕ) : ℝ) ≤ a*V n w)
    (htime : ∀ n, (T n : ℝ)/P n ≤ M)
    (hf : ∀ n, LipschitzWith 1 (fs n)) (he : ∀ n (m : ℕ), fs n m=(hs n m : ℝ))
    (hconv : TendstoUniformlyOn (fun n => physicalPath (P n) (fs n)) f atTop (Icc 0 M))
    (hstop : ∀ n m, T n ≤ m → hs n m=hs n (T n))
    (hregular : ∀ (w : List (Fin B)) (j : Fin J), HasRegularStageSubsequences a
      (fun n => V n w) (fun n => A n w j) (fun n => E n w j-A n w j) hs) :
    ∃ R : Set ℝ, IsOpen R ∧ R ⊆ Icc 0 M ∧ volume (Icc 0 M \ R)=0 ∧
      ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
        ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d := by
  obtain ⟨φ,hφ,H,l,r,v,_,_,hH,hl,hre,hv,hbounds,_,hcov⟩ :=
    exists_stage_clock_limit_cover hV hr hr1 ha hP hc hroot label A E hAE hE hstage hbudget
  have hconvφ : TendstoUniformlyOn (fun n => physicalPath (P (φ n)) (fs (φ n)))
      f atTop (Icc 0 M) := fun u hu => hφ.tendsto_atTop.eventually (hconv u hu)
  have hpieces : ∀ p : List (Fin B) × Fin J,
      ∃ R : Set ℝ, IsOpen R ∧ R ⊆ Ioo (l p) (r p) ∧ volume (Ioo (l p) (r p) \ R)=0 ∧
        ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
          ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d := by
    intro p
    by_cases hp : l p < r p
    · have hown (n : ℕ) : ((E n p.1 p.2-A n p.1 p.2 : ℕ) : ℝ) ≤ a*V n p.1 := by
        have hsN : E n p.1 p.2-A n p.1 p.2 ≤ ∑ j : Fin J, (E n p.1 j-A n p.1 j) :=
          Finset.single_le_sum (f:=fun j : Fin J => E n p.1 j-A n p.1 j)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)
        exact (show ((E n p.1 p.2-A n p.1 p.2 : ℕ) : ℝ) ≤
          ((∑ j : Fin J, (E n p.1 j-A n p.1 j) : ℕ) : ℝ) by exact_mod_cast hsN).trans (hbudget n p.1)
      have hend (n : ℕ) : (E n p.1 p.2 : ℝ) ≤ M*P n :=
        (show (E n p.1 p.2 : ℝ) ≤ (T n : ℝ) by exact_mod_cast hE n p.1 p.2).trans
          ((div_le_iff₀ (hP n)).mp (htime n))
      obtain ⟨hvp,K,hK⟩ := positive_stage_affine_of_regular_occurrences
        (fun n => hP (φ n)) (hPinf.comp hφ.tendsto_atTop) ha
        (fun n => hAE (φ n) p.1 p.2) (fun n => hf (φ n)) (fun n => he (φ n)) hconvφ
        (hl p) (hre p) (hv p.1) hp (fun n => hend (φ n)) (fun n => hown (φ n))
        ((hregular p.1 p.2).subsequence hφ)
      have heq : l p+v p.1*((r p-l p)/v p.1)=r p := by field_simp; ring
      simpa only [heq] using local_affine_ae_on_stage hvp hK
    · refine ⟨∅,isOpen_empty,Set.empty_subset _,?_,?_⟩
      · simp only [Ioo_eq_empty_of_le (le_of_not_gt hp),Set.sdiff_empty,measure_empty]
      · intro x hx
        exact False.elim hx
  obtain ⟨R,hRo,hRI,hRn,hRl⟩ := assemble_stage_local_affinity
    (fun p => ⟨(hbounds p).1,(hbounds p).2.2⟩) hcov hpieces
  have hHM : H ≤ M := le_of_tendsto hH (Eventually.of_forall (fun n => htime (φ n)))
  have hconst := physical_limit_constant_after_halt (fun n => hP (φ n))
    (hPinf.comp hφ.tendsto_atTop) (fun n => hf (φ n)) (fun n => he (φ n)) hconvφ
    (fun n => htime (φ n)) hH (fun n => hstop (φ n))
  exact extend_affine_cover_by_constant hHM hRo hRI hRn hRl hconst

end TransposeFollowup.RegularMotion
