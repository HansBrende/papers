import TransposeFollowup.PhysicalWalkNormalization

/-! The original canonical block size differs from physical input-length
scaling by an explicitly vanishing error. No asymptotic scale identity is
assumed: the estimates reuse the original ceiling inequalities. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram
set_option autoImplicit false

noncomputable def timeScale (G n : ℕ) : ℝ := (n : ℝ)*blockSize G n/inputLength n

theorem timeScale_bounds {G n : ℕ} (hG : 1 ≤ G) (hn : 1 ≤ n) :
    0 < timeScale G n ∧ 1/(G : ℝ) ≤ timeScale G n ∧ timeScale G n ≤ 1 ∧
      timeScale G n-1/(G : ℝ) ≤ 1/(n : ℝ) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hGp : (0 : ℝ) < G := by exact_mod_cast (show 0 < G by omega)
  have hb : (1 : ℝ) ≤ entryBits n := by
    exact_mod_cast (show 1 ≤ entryBits n by unfold entryBits; omega)
  have hbp : (0 : ℝ) < entryBits n := lt_of_lt_of_le (by norm_num) hb
  have hnb : (0 : ℝ) < n*entryBits n := mul_pos hnp hbp
  have hrp : (0 : ℝ) < blockSize G n := by exact_mod_cast one_le_blockSize hG hn
  have hl : (n : ℝ)*entryBits n ≤ blockSize G n*G := by exact_mod_cast blockSize_mul_ge (n:=n) hG
  have hu : (blockSize G n : ℝ)*G ≤ n*entryBits n+G := by exact_mod_cast blockSize_mul_le G n
  have hr : (blockSize G n : ℝ) ≤ n*entryBits n := by exact_mod_cast blockSize_le (n:=n) hG
  have he : timeScale G n=(blockSize G n : ℝ)/((n : ℝ)*entryBits n) := by
    unfold timeScale inputLength
    push_cast
    field_simp
  rw [he]
  refine ⟨div_pos hrp hnb,?_,?_,?_⟩
  · apply (div_le_div_iff₀ hGp hnb).mpr
    simpa only [one_mul] using hl
  · exact (div_le_one hnb).mpr hr
  · apply (mul_le_mul_iff_right₀ (mul_pos hnb hGp)).mp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hb hGp.le]


theorem canonical_physical_error {G n : ℕ} (hG : 1 ≤ G) (hn : 1 ≤ n)
    {h : ℕ → ℤ} (hh : UnitSteps h) (h0 : h 0=0)
    {f : ℝ → ℝ} (hf : LipschitzWith 1 f) (he : ∀ m : ℕ, f m=(h m : ℝ))
    {u : ℝ} (hu : 0 ≤ u) :
    |physicalPath (inputLength n) f (u/G)-blockTraj (blockSize G n) n h u/G| ≤
      2*(u+1)/(n : ℝ) := by
  let r := blockSize G n
  let a := timeScale G n
  let L : ℝ := inputLength n
  let B := blockTraj r n h u
  let Q := physicalPath ((n : ℝ)*r) f u
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hGp : (0 : ℝ) < G := by exact_mod_cast (show 0 < G by omega)
  have hr : 1 ≤ r := one_le_blockSize hG hn
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hb : 0 < entryBits n := by unfold entryBits; omega
  have hLp : 0 < L := by dsimp [L,inputLength]; positivity
  have hLne : (inputLength n : ℝ) ≠ 0 := hLp.ne'
  have hrne : (blockSize G n : ℝ) ≠ 0 := hrp.ne'
  obtain ⟨hap,hal,ha1,had⟩ := timeScale_bounds hG hn
  change 0 < a at hap
  change 1/(G : ℝ) ≤ a at hal
  change a ≤ 1 at ha1
  change a-1/(G : ℝ) ≤ 1/(n : ℝ) at had
  have had0 : 0 ≤ a-1/(G : ℝ) := sub_nonneg.mpr hal
  have heq : physicalPath L f (a*u)=a*Q := by
    have harg : L*(a*u)=((n : ℝ)*r)*u := by
      dsimp [L,a,r,timeScale]
      field_simp [hLne]
    dsimp only [Q,physicalPath]
    rw [harg]
    dsimp [a,timeScale,L,r]
    field_simp [hLne,hrne]
  have hfirst : |physicalPath L f (u/G)-a*Q| ≤ u/n := by
    rw [← heq]
    have hd := (physicalPath_lipschitz hLp hf).dist_le_mul (u/G) (a*u)
    simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hd
    calc
      _ ≤ |u/G-a*u| := hd
      _ = u*(a-1/(G : ℝ)) := by
        rw [show u/G-a*u= -(u*(a-1/(G : ℝ))) by ring,abs_neg,
          abs_mul,abs_of_nonneg hu,abs_of_nonneg had0]
      _ ≤ u*(1/(n : ℝ)) := mul_le_mul_of_nonneg_left had hu
      _ = u/n := by ring
  have hsecond : |a*Q-a*B| ≤ 2/(n : ℝ) := by
    have hs : |Q-B| ≤ 2/(n : ℝ) := by
      simpa only [abs_sub_comm] using block_physical_sample_error hr hn hf he hu
    calc
      _ = a*|Q-B| := by rw [← mul_sub,abs_mul,abs_of_pos hap]
      _ ≤ a*(2/(n : ℝ)) := mul_le_mul_of_nonneg_left hs hap.le
      _ ≤ 1*(2/(n : ℝ)) := mul_le_mul_of_nonneg_right ha1 (by positivity)
      _ = _ := one_mul _
  have hthird : |a*B-B/G| ≤ u/n := by
    have hB : |B| ≤ u := blockTraj_abs_le hh h0 hu
    calc
      _ = (a-1/(G : ℝ))*|B| := by
        rw [show a*B-B/G=(a-1/(G : ℝ))*B by ring,abs_mul,abs_of_nonneg had0]
      _ ≤ (a-1/(G : ℝ))*u := mul_le_mul_of_nonneg_left hB had0
      _ ≤ (1/(n : ℝ))*u := mul_le_mul_of_nonneg_right had hu
      _ = u/n := by ring
  change |physicalPath L f (u/G)-B/G| ≤ 2*(u+1)/(n : ℝ)
  calc
    _ ≤ |physicalPath L f (u/G)-a*Q|+|a*Q-B/G| := abs_sub_le _ _ _
    _ ≤ |physicalPath L f (u/G)-a*Q|+(|a*Q-a*B|+|a*B-B/G|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ u/n+(2/(n : ℝ)+u/n) := add_le_add hfirst (add_le_add hsecond hthird)
    _ = _ := by ring

end TransposeFollowup.RegularMotion
