import TransposeFollowup.ExceptionalCoverageLimits

/-! The actual global exceptional-tick budget bounds the omitted time of an
open locally affine cover of each physical head limit. Bad stages have no
regularity obligation; they retain their full cost in the contracting clock.
Local profiles, stage assembly and the frozen halting tail are reused. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory
open scoped BigOperators
set_option autoImplicit false

def RegularFlaggedClockHead {B J : ℕ} {rho a C : ℝ} {P : ℕ → ℝ} {T : ℕ → ℕ}
    (clocks : ∀ i, ContractingStageClock B J rho a C (P i) (T i))
    (good : ℕ → List (Fin B) × Fin J → Bool) (hs : ℕ → ℕ → ℤ) : Prop :=
  ∀ w j, HasRegularStageSubsequences a (fun i => (clocks i).V w)
    (fun i => (clocks i).A w j)
    (fun i => if good i (w,j)=true then (clocks i).E w j-(clocks i).A w j else 0) hs

theorem flagged_clock_limit_locally_affine
    {B J : ℕ} {T : ℕ → ℕ} {P eps : ℕ → ℝ} {rho a C M eta : ℝ}
    {hs : ℕ → ℕ → ℤ} {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (clocks : ∀ i, ContractingStageClock B J rho a C (P i) (T i))
    (good : ℕ → List (Fin B) × Fin J → Bool)
    (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hP : ∀ i, 0 < P i) (hPinf : Tendsto P atTop atTop)
    (htime : ∀ i, (T i : ℝ)/P i ≤ M)
    (hf : ∀ i, LipschitzWith 1 (fs i)) (he : ∀ i (m : ℕ), fs i m=(hs i m : ℝ))
    (hconv : TendstoUniformlyOn (fun i => physicalPath (P i) (fs i)) f atTop (Icc 0 M))
    (hstop : ∀ i m, T i ≤ m → hs i m=hs i (T i))
    (hregular : RegularFlaggedClockHead clocks good hs)
    (heps : Tendsto eps atTop (𝓝 0))
    (hbad : ∀ i, (exceptionalTicks (clocks i) (good i) : ℝ)/P i ≤ eta+eps i) :
    ∃ R : Set ℝ, IsOpen R ∧ R ⊆ Icc 0 M ∧ volume.real (Icc 0 M \ R) ≤ eta ∧
      ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
        ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d := by
  obtain ⟨φ,hφ,H,l,r,v,g,_,_,hH,hl,hre,hv,hg,hbounds,hcov⟩ :=
    exists_exceptional_stage_limit_cover clocks good hr hr1 ha hP heps hbad
  have hconvφ : TendstoUniformlyOn (fun i => physicalPath (P (φ i)) (fs (φ i)))
      f atTop (Icc 0 M) := fun u hu => hφ.tendsto_atTop.eventually (hconv u hu)
  let κ := {p : List (Fin B) × Fin J // g p=true}
  have hpieces : ∀ p : κ,
      ∃ R : Set ℝ, IsOpen R ∧ R ⊆ Ioo (l p.val) (r p.val) ∧
        volume (Ioo (l p.val) (r p.val) \ R)=0 ∧
        ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
          ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d := by
    intro p
    by_cases hp : l p.val < r p.val
    · let E' : ℕ → ℕ := fun i => if good (φ i) p.val=true
        then (clocks (φ i)).E p.val.1 p.val.2 else (clocks (φ i)).A p.val.1 p.val.2
      have hAE' (i : ℕ) : (clocks (φ i)).A p.val.1 p.val.2 ≤ E' i := by
        dsimp [E']; split
        · exact (clocks (φ i)).ordered _ _
        · exact le_rfl
      have hE' (i : ℕ) : E' i ≤ (clocks (φ i)).E p.val.1 p.val.2 := by
        dsimp [E']; split
        · exact le_rfl
        · exact (clocks (φ i)).ordered _ _
      have hlimE : Tendsto (fun i => (E' i : ℝ)/P (φ i)) atTop (𝓝 (r p.val)) := by
        apply (hre p.val).congr'
        filter_upwards [hg p.val] with i hi
        simp only [E',hi,p.property,ite_true]
      have hown (i : ℕ) : ((E' i-(clocks (φ i)).A p.val.1 p.val.2 : ℕ) : ℝ) ≤
          a*(clocks (φ i)).V p.val.1 := by
        have hN : E' i-(clocks (φ i)).A p.val.1 p.val.2 ≤
            ∑ j : Fin J, ((clocks (φ i)).E p.val.1 j-(clocks (φ i)).A p.val.1 j) :=
          (Nat.sub_le_sub_right (hE' i) _).trans
            (Finset.single_le_sum
              (f:=fun j : Fin J => (clocks (φ i)).E p.val.1 j-(clocks (φ i)).A p.val.1 j)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.val.2))
        exact (show ((E' i-(clocks (φ i)).A p.val.1 p.val.2 : ℕ) : ℝ) ≤
          ((∑ j : Fin J, ((clocks (φ i)).E p.val.1 j-(clocks (φ i)).A p.val.1 j) : ℕ) : ℝ)
          by exact_mod_cast hN).trans ((clocks (φ i)).budget p.val.1)
      have hend (i : ℕ) : (E' i : ℝ) ≤ M*P (φ i) :=
        (show (E' i : ℝ) ≤ (T (φ i) : ℝ) by
          exact_mod_cast (hE' i).trans ((clocks (φ i)).bounded _ _)).trans
            ((div_le_iff₀ (hP (φ i))).mp (htime (φ i)))
      have hreg : HasRegularStageSubsequences a (fun i => (clocks (φ i)).V p.val.1)
          (fun i => (clocks (φ i)).A p.val.1 p.val.2)
          (fun i => E' i-(clocks (φ i)).A p.val.1 p.val.2) (fun i => hs (φ i)) := by
        simpa only [E',ite_sub,Nat.sub_self,Prod.mk.eta] using
          (hregular p.val.1 p.val.2).subsequence hφ
      obtain ⟨hvp,K,hK⟩ := positive_stage_affine_of_regular_occurrences
        (fun i => hP (φ i)) (hPinf.comp hφ.tendsto_atTop) ha hAE'
        (fun i => hf (φ i)) (fun i => he (φ i)) hconvφ
        (hl p.val) hlimE (hv p.val.1) hp hend hown hreg
      have heq : l p.val+v p.val.1*((r p.val-l p.val)/v p.val.1)=r p.val := by
        field_simp; ring
      simpa only [heq] using local_affine_ae_on_stage hvp hK
    · refine ⟨∅,isOpen_empty,Set.empty_subset _,?_,?_⟩
      · simp only [Ioo_eq_empty_of_le (le_of_not_gt hp),Set.sdiff_empty,measure_empty]
      · intro x hx
        exact False.elim hx
  obtain ⟨R,hRo,hRI,hReq,hRl⟩ := assemble_stage_local_affinity_ae
    (fun p : κ => ⟨(hbounds p.val).1,(hbounds p.val).2.2⟩) hpieces
  have hRn : volume.real (Icc 0 H \ R) ≤ eta := by
    rw [measureReal_congr (ae_eq_set_sdiff .rfl hReq)]
    simpa only [κ,Set.iUnion_subtype] using hcov
  have hHM : H ≤ M := le_of_tendsto hH (Eventually.of_forall (fun i => htime (φ i)))
  have hconst := physical_limit_constant_after_halt (fun i => hP (φ i))
    (hPinf.comp hφ.tendsto_atTop) (fun i => hf (φ i)) (fun i => he (φ i)) hconvφ
    (fun i => htime (φ i)) hH (fun i => hstop (φ i))
  obtain ⟨S,hSo,hSI,hSn,hSl⟩ := extend_affine_cover_by_constant_le hHM hRo hRI hRl hconst
  refine ⟨S,hSo,hSI,?_,hSl⟩
  have hfinite : volume (Icc 0 H \ R) ≠ ⊤ :=
    measure_ne_top_of_subset Set.sdiff_subset (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  exact (ENNReal.toReal_mono hfinite hSn).trans hRn

end TransposeFollowup.RegularMotion
