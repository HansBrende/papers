import LuckApproximation.CertChecks

/-! # Kernel-checked certificate identities: the product with `B₁` -/

namespace Luck.Op

open LeanMachine.PackedCheck

/-- `kerL · B₁ = P`. -/
theorem chk_P : prodOK (rowsOf Cert.kerLPk 110) B1Pk (rowsOf Cert.PPk 110) = true := by decide +kernel

end Luck.Op
