import LuckApproximation.CertChecks

/-! # Kernel-checked certificate identities: the products with `B₀` -/

namespace Luck.Op

open LeanMachine.PackedCheck

/-- `kerL · B₀ = 0`. -/
theorem chk_kerL_B0 : prodOK (rowsOf Cert.kerLPk 110) B0Pk (zeros 42 110) = true := by decide +kernel
/-- `B₀ · kerRᵀ = 0`. -/
theorem chk_B0_kerR : prodOK B0rows Cert.kerRTpk (zeros 110 42) = true := by decide +kernel

end Luck.Op
