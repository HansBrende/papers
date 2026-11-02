import LuckApproximation.CertChecks

/-! # Kernel-checked certificate identities: shapes, `C`, `C⁻¹` and the minor -/

namespace Luck.Op

open LeanMachine.PackedCheck

theorem chkCert_eq : chkCert = true := by decide +kernel
/-- `P · kerRᵀ = C`. -/
theorem chk_C : prodOK (rowsOf Cert.PPk 110) Cert.kerRTpk (rowsOf Cert.CPk 42) = true := by
  decide +kernel
/-- `C · C⁻¹ = 1`. -/
theorem chk_Cinv : prodOK (rowsOf Cert.CPk 42) Cert.CinvPk (ident 42) = true := by decide +kernel
/-- `B₀[R, S] · W = 1`. -/
theorem chk_minor : prodOK minorRows Cert.WPk (ident 68) = true := by decide +kernel

end Luck.Op
