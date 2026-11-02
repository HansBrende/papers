import LuckApproximation.Data
import LuckApproximation.CertData
import LeanMachine.PackedMatrixCheck

/-!
# Kernel-checked certificate identities

All checks are Boolean computations on natural numbers, evaluated by `decide +kernel`. Packed rows (base 512)
turn each matrix product into one small-by-big product per term (`LeanMachine.PackedCheck.prodOK`).

* `b0Nat`, `b1Nat` read `B₀`, `B₁` from the packed caches of `Data.lean`; `Bridge.lean` identifies them with the
  matrices of `Operator.lean`, through the cache equalities of `ConCache.lean`. `B0Pk`, `B1Pk` (their packed rows)
  are computed, not stored.
* The identities `kerL · B₀ = 0`, `B₀ · kerRᵀ = 0` (`CertB0.lean`), `kerL · B₁ = P` (`CertB1.lean`),
  `P · kerRᵀ = C`, `C · C⁻¹ = 1`, `B₀[R, S] · W = 1` and the shapes (`CertRest.lean`) are checked in three
  files that build in parallel.
-/

namespace Luck.Op

open Luck.Data LeanMachine.PackedCheck

/-- The 3-cover voltage of an edge, as a natural number (0 on spanning-tree edges). -/
def voltEdgeNat (e : ℕ) : ℕ := if edgeGenNat e < 89 then voltNat (edgeGenNat e) else 0

/-- `B₀` and `B₁` as natural-number functions of the packed data, with values in `{0, 1, 2}`. -/
def b0Nat (i j : ℕ) : ℕ :=
  if edgeOfNat (i / 10) (j / 10) < 110 then
    couplingNat (edgeOfNat (i / 10) (j / 10)) (i % 10) (j % 10) % 3
  else 0

def b1Nat (i j : ℕ) : ℕ :=
  if edgeOfNat (i / 10) (j / 10) < 110 then
    voltEdgeNat (edgeOfNat (i / 10) (j / 10)) *
      couplingNat (edgeOfNat (i / 10) (j / 10)) (i % 10) (j % 10) % 3
  else 0

/-- The rows of `B₀`, `B₁` (digit lists), their packed forms, and the rows of the minor `B₀[R, S]`. -/
def B0rows : List (List ℕ) := (List.range 110).map fun i => (List.range 110).map (b0Nat i)
def B1rows : List (List ℕ) := (List.range 110).map fun i => (List.range 110).map (b1Nat i)
def B0Pk : List ℕ := B0rows.map pk
def B1Pk : List ℕ := B1rows.map pk
def minorRows : List (List ℕ) := Cert.minorR.map fun a => Cert.minorS.map fun b => b0Nat a b

/-- Lengths and small digits of the certificate; the minor's indices are in range. -/
def chkCert : Bool :=
  (Cert.kerLPk.length == 42 && Cert.kerLPk.all fun y => smallDigits y 110) &&
  (Cert.PPk.length == 42 && Cert.PPk.all fun y => smallDigits y 110) &&
  (Cert.CPk.length == 42 && Cert.CPk.all fun y => smallDigits y 42) &&
  (Cert.kerRTpk.length == 110 && Cert.kerRTpk.all fun y => smallDigits y 42) &&
  (Cert.CinvPk.length == 42 && Cert.CinvPk.all fun y => smallDigits y 42) &&
  (Cert.WPk.length == 68 && Cert.WPk.all fun y => smallDigits y 68) &&
  (Cert.minorR.length == 68 && Cert.minorR.all fun a => a.blt 110) &&
  (Cert.minorS.length == 68 && Cert.minorS.all fun b => b.blt 110)

end Luck.Op
