import LuckApproximation.CertB0
import LuckApproximation.CertB1
import LuckApproximation.CertRest
import LuckApproximation.Bridge
import LeanMachine.KernelCertificate

/-!
# The certificate as matrix identities over `𝔽₃`

The kernel-checked computations of `CertB0`, `CertB1` and `CertRest` give, through
`LeanMachine.PackedCheck.prodOK_sound`:
* an invertible 68 × 68 minor of `B₀` (`hW`);
* 42 left and 42 right kernel vectors of `B₀` with an invertible connecting matrix `C = (b_a B₁ · y_k)`
  (`hb`, `hy`, `hC`, `hCinv`).
Mapped along `𝔽₃ → K`, they give `dim ker (x ↦ x B₀) ≤ 42` (`finrank_ker_B0_K`) and injectivity of the
connecting map (`connecting_K`, via `LeanMachine.KernelCertificate.connecting_injective`) over every field
`K` of characteristic 3.
These are the inputs of the kernel bound on every cyclic 3-power cover (`CyclicTower.lean`).
-/

namespace Luck.Op

open LeanMachine.KernelCertificate LeanMachine.PackedCheck Matrix

/-! ### Small entries and lengths -/

theorem b0Nat_le (i j : ℕ) : b0Nat i j ≤ 2 := by
  unfold b0Nat; split_ifs <;> omega

theorem b1Nat_le (i j : ℕ) : b1Nat i j ≤ 2 := by
  unfold b1Nat; split_ifs <;> omega

theorem getD_rows (f : ℕ → ℕ → ℕ) (i j : ℕ) (hi : i < 110) (hj : j < 110) :
    (((List.range 110).map fun i => (List.range 110).map (f i)).getD i []).getD j 0 = f i j := by
  rw [List.getD_eq_getElem _ [] (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ 0 (by simpa using hj)]
  simp

theorem rowsSmall_rows (f : ℕ → ℕ → ℕ) (hf : ∀ i j, f i j ≤ 2) :
    RowsSmall ((List.range 110).map fun i => (List.range 110).map (f i)) 110 := by
  intro i hi
  have hi' : i < 110 := by simpa using hi
  refine ⟨?_, fun k hk => ?_⟩
  · rw [List.getD_eq_getElem _ [] hi]; simp
  · rw [getD_rows f i k hi' hk]; exact hf i k

theorem B0rows_small : RowsSmall B0rows 110 := rowsSmall_rows b0Nat b0Nat_le
theorem B1rows_small : RowsSmall B1rows 110 := rowsSmall_rows b1Nat b1Nat_le

theorem B0Pk_small : PackedSmall B0Pk 110 110 := by
  have h := packedSmall_map_pk B0rows_small
  rw [show B0rows.length = 110 by simp [B0rows]] at h
  exact h

theorem B1Pk_small : PackedSmall B1Pk 110 110 := by
  have h := packedSmall_map_pk B1rows_small
  rw [show B1rows.length = 110 by simp [B1rows]] at h
  exact h

/-- The entries of `B₀`, `B₁` are the digits of their packed rows. -/
theorem B0_dg (i j : Fin 110) : B0 i j = ((dg (B0Pk.getD i 0) j : ℕ) : ZMod 3) := by
  rw [B0_eq, B0Pk, dg_getD_map_pk B0rows_small i j (by simp [B0rows]) j.2, B0rows,
    getD_rows _ _ _ i.2 j.2]

theorem B1_dg (i j : Fin 110) : B1 i j = ((dg (B1Pk.getD i 0) j : ℕ) : ZMod 3) := by
  rw [B1_eq, B1Pk, dg_getD_map_pk B1rows_small i j (by simp [B1rows]) j.2, B1rows,
    getD_rows _ _ _ i.2 j.2]

/-! ### The certificate data -/

theorem chkCert_parts :
    (Cert.kerLPk.length == 42 && Cert.kerLPk.all fun y => smallDigits y 110) = true ∧
    (Cert.PPk.length == 42 && Cert.PPk.all fun y => smallDigits y 110) = true ∧
    (Cert.CPk.length == 42 && Cert.CPk.all fun y => smallDigits y 42) = true ∧
    (Cert.kerRTpk.length == 110 && Cert.kerRTpk.all fun y => smallDigits y 42) = true ∧
    (Cert.CinvPk.length == 42 && Cert.CinvPk.all fun y => smallDigits y 42) = true ∧
    (Cert.WPk.length == 68 && Cert.WPk.all fun y => smallDigits y 68) = true ∧
    (Cert.minorR.length == 68 && Cert.minorR.all fun a => a.blt 110) = true ∧
    (Cert.minorS.length == 68 && Cert.minorS.all fun b => b.blt 110) = true := by
  have h := chkCert_eq
  simp only [chkCert, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4, by simpa using h5,
    by simpa using h6, by simpa using h7, by simpa using h8⟩

theorem kerL_small : PackedSmall Cert.kerLPk 42 110 := packedSmall_of_check chkCert_parts.1
theorem P_small : PackedSmall Cert.PPk 42 110 := packedSmall_of_check chkCert_parts.2.1
theorem C_small : PackedSmall Cert.CPk 42 42 := packedSmall_of_check chkCert_parts.2.2.1
theorem kerRT_small : PackedSmall Cert.kerRTpk 110 42 := packedSmall_of_check chkCert_parts.2.2.2.1
theorem Cinv_small : PackedSmall Cert.CinvPk 42 42 := packedSmall_of_check chkCert_parts.2.2.2.2.1
theorem W_small : PackedSmall Cert.WPk 68 68 := packedSmall_of_check chkCert_parts.2.2.2.2.2.1

theorem minor_lt (a : Fin 68) : Cert.minorR.getD a 0 < 110 ∧ Cert.minorS.getD a 0 < 110 := by
  obtain ⟨-, -, -, -, -, -, h7, h8⟩ := chkCert_parts
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq] at h7 h8
  constructor
  · rw [List.getD_eq_getElem _ _ (by omega)]; exact h7.2 _ (List.getElem_mem _)
  · rw [List.getD_eq_getElem _ _ (by omega)]; exact h8.2 _ (List.getElem_mem _)

/-! ### The certificate as matrices -/

/-- The 42 left and 42 right kernel vectors, `C` and its inverse. -/
def bvec (a : Fin 42) : Fin 110 → ZMod 3 := fun i => ((dg (Cert.kerLPk.getD a 0) i : ℕ) : ZMod 3)
def yvec (k : Fin 42) : Fin 110 → ZMod 3 := fun j => ((dg (Cert.kerRTpk.getD j 0) k : ℕ) : ZMod 3)
def Cmat : Matrix (Fin 42) (Fin 42) (ZMod 3) :=
  Matrix.of fun a k => ((dg (Cert.CPk.getD a 0) k : ℕ) : ZMod 3)
def CinvMat : Matrix (Fin 42) (Fin 42) (ZMod 3) :=
  Matrix.of fun b c => ((dg (Cert.CinvPk.getD b 0) c : ℕ) : ZMod 3)

theorem hb (a : Fin 42) : bvec a ᵥ* B0 = 0 := by
  funext c
  have h := prodOK_sound (q := 110) (r := 110) (by norm_num) (rowsSmall_rowsOf kerL_small) B0Pk_small
    (zeros_rows 42 110) chk_kerL_B0 a (by simp [rowsOf, kerL_small.1]) c c.2
  simp only [getD_rowsOf _ _ _ _ (Fin.is_lt _), getD_zeros, Nat.cast_zero] at h
  simp only [Matrix.vecMul, dotProduct, bvec, B0_dg, Pi.zero_apply]
  exact h

theorem hy (k : Fin 42) : B0 *ᵥ yvec k = 0 := by
  funext r
  have h := prodOK_sound (q := 110) (r := 42) (by norm_num) B0rows_small kerRT_small
    (zeros_rows 110 42) chk_B0_kerR r (by simp [B0rows]) k k.2
  simp only [B0rows, getD_rows _ _ _ r.2 (Fin.is_lt _), getD_zeros, Nat.cast_zero] at h
  simp only [Matrix.mulVec, dotProduct, yvec, B0_eq, Pi.zero_apply]
  exact h

theorem hC (a k : Fin 42) : Cmat a k = (bvec a ᵥ* B1) ⬝ᵥ yvec k := by
  have hP : ∀ j : Fin 110, (bvec a ᵥ* B1) j = ((dg (Cert.PPk.getD a 0) j : ℕ) : ZMod 3) := by
    intro j
    have h := prodOK_sound (q := 110) (r := 110) (by norm_num) (rowsSmall_rowsOf kerL_small) B1Pk_small
      (fun i hi => length_getD_rowsOf _ _ _ (by simpa [rowsOf] using hi)) chk_P a
      (by simp [rowsOf, kerL_small.1]) j j.2
    simp only [getD_rowsOf _ _ _ _ (Fin.is_lt _)] at h
    simp only [Matrix.vecMul, dotProduct, bvec, B1_dg]
    exact h
  have h := prodOK_sound (q := 110) (r := 42) (by norm_num) (rowsSmall_rowsOf P_small) kerRT_small
    (fun i hi => length_getD_rowsOf _ _ _ (by simpa [rowsOf] using hi)) chk_C a
    (by simp [rowsOf, P_small.1]) k k.2
  simp only [getD_rowsOf _ _ _ _ (Fin.is_lt _)] at h
  simp only [Cmat, Matrix.of_apply, dotProduct, hP, yvec]
  exact h.symm

theorem hCinv : Cmat * CinvMat = 1 := by
  ext a c
  have h := prodOK_sound (q := 42) (r := 42) (by norm_num) (rowsSmall_rowsOf C_small) Cinv_small
    (ident_rows 42) chk_Cinv a (by simp [rowsOf, C_small.1]) c c.2
  simp only [getD_rowsOf _ _ _ _ (Fin.is_lt _), getD_ident 42 a c a.2 c.2] at h
  simp only [Matrix.mul_apply, Cmat, CinvMat, Matrix.of_apply, Matrix.one_apply]
  rw [h]
  simp [Fin.val_eq_val]

def Rm (a : Fin 68) : Fin 110 := ⟨Cert.minorR.getD a 0, (minor_lt a).1⟩
def Sm (b : Fin 68) : Fin 110 := ⟨Cert.minorS.getD b 0, (minor_lt b).2⟩
def Wm : Matrix (Fin 68) (Fin 68) (ZMod 3) := Matrix.of fun b c => ((dg (Cert.WPk.getD b 0) c : ℕ) : ZMod 3)

theorem getD_minorRows (a b : Fin 68) :
    (minorRows.getD a []).getD b 0 = b0Nat (Cert.minorR.getD a 0) (Cert.minorS.getD b 0) := by
  obtain ⟨-, -, -, -, -, -, h7, h8⟩ := chkCert_parts
  simp only [Bool.and_eq_true, beq_iff_eq] at h7 h8
  have ha : (a : ℕ) < Cert.minorR.length := by omega
  have hb : (b : ℕ) < Cert.minorS.length := by omega
  rw [List.getD_eq_getElem minorRows [] (by simpa [minorRows] using ha)]
  simp only [minorRows, List.getElem_map]
  rw [List.getD_eq_getElem _ 0 (by simpa using hb), List.getElem_map, List.getD_eq_getElem _ 0 ha,
    List.getD_eq_getElem _ 0 hb]

theorem minorRows_small : RowsSmall minorRows 68 := by
  obtain ⟨-, -, -, -, -, -, h7, h8⟩ := chkCert_parts
  simp only [Bool.and_eq_true, beq_iff_eq] at h7 h8
  intro i hi
  have hi' : i < 68 := by simpa [minorRows, h7.1] using hi
  refine ⟨?_, fun k hk => ?_⟩
  · rw [List.getD_eq_getElem _ [] hi]; simp [minorRows, h8.1]
  · rw [getD_minorRows ⟨i, hi'⟩ ⟨k, hk⟩]; exact b0Nat_le _ _

theorem hW : B0.submatrix Rm Sm * Wm = 1 := by
  ext a c
  have h := prodOK_sound (q := 68) (r := 68) (by norm_num) minorRows_small W_small (ident_rows 68)
    chk_minor a (by
      obtain ⟨-, -, -, -, -, -, h7, -⟩ := chkCert_parts
      simp only [Bool.and_eq_true, beq_iff_eq] at h7
      simp [minorRows, h7.1]) c c.2
  simp only [getD_ident 68 a c a.2 c.2] at h
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Wm, Matrix.of_apply, Matrix.one_apply, B0_eq]
  have hsum : ∀ b : Fin 68, ((b0Nat (Rm a) (Sm b) : ℕ) : ZMod 3) =
      (((minorRows.getD a []).getD b 0 : ℕ) : ZMod 3) := fun b => by rw [getD_minorRows]; rfl
  simp only [hsum]
  rw [h]
  simp [Fin.val_eq_val]

/-! ### Over any field of characteristic 3

The identities above are equalities of matrices over `𝔽₃`; mapping them along `𝔽₃ → K` gives the same two
facts over every field `K` of characteristic 3. -/

section CharThree

variable (K : Type*) [Field K] [CharP K 3]

/-- The ring map `𝔽₃ → K`. -/
noncomputable abbrev ι3 : ZMod 3 →+* K := ZMod.castHom dvd_rfl K

theorem hW_K : (B0.map (ι3 K)).submatrix Rm Sm * Wm.map (ι3 K) = 1 := by
  rw [Matrix.submatrix_map, ← Matrix.map_mul, hW, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finrank_ker_B0_K :
    Module.finrank K (LinearMap.ker (Matrix.vecMulLinear (B0.map (ι3 K)))) ≤ 42 := by
  have := finrank_ker_add_le_of_minor (B0.map (ι3 K)) Rm Sm (Wm.map (ι3 K)) (hW_K K)
  omega

theorem connecting_K (x : Fin 110 → K) (hx : x ᵥ* B0.map (ι3 K) = 0) (z : Fin 110 → K)
    (hz : x ᵥ* B1.map (ι3 K) = z ᵥ* B0.map (ι3 K)) : x = 0 := by
  refine connecting_injective (B0.map (ι3 K)) (B1.map (ι3 K)) (fun a => ι3 K ∘ bvec a)
    (fun k => ι3 K ∘ yvec k) (Cmat.map (ι3 K)) (CinvMat.map (ι3 K)) (fun a => ?_) (fun k => ?_)
    (fun a k => ?_) ?_ (finrank_ker_B0_K K) x hx z hz
  · funext c
    rw [Pi.zero_apply, ← RingHom.map_vecMul, hb, Pi.zero_apply, map_zero]
  · funext r
    rw [Pi.zero_apply, ← RingHom.map_mulVec, hy, Pi.zero_apply, map_zero]
  · rw [Matrix.map_apply, hC, RingHom.map_dotProduct]
    congr 1
    funext j
    rw [Function.comp_apply, RingHom.map_vecMul]
  · rw [← Matrix.map_mul, hCinv, Matrix.map_one _ (map_zero _) (map_one _)]

end CharThree

end Luck.Op
