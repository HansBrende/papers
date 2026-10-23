import BitWord.CompilerMultiCoverage

namespace BitWord.Compiler
open Geometry

/-- The row-major raw-bit transpose permutation. -/
def transposePerm (d : ℕ) : Equiv.Perm (Fin (d*d)) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin d) (Fin d)).trans finProdFinEquiv)

def transposeNat (d x : ℕ) : ℕ := (x % d) * d + x / d

theorem transposePerm_val (d : ℕ) (x : Fin (d*d)) :
    (transposePerm d x).val = transposeNat d x.val := by
  change x.val / d + d * (x.val % d) = (x.val % d) * d + x.val / d
  ring

theorem finiteAct_transposePerm {d x : ℕ} (hx : x < d*d) :
    finiteAct (transposePerm d) x = transposeNat d x := by
  simp only [finiteAct, dite_eq_left hx]
  exact transposePerm_val d ⟨x,hx⟩

/-- All aligned bin widths dividing the side enjoy the exact dispersion
property. Thus the proof does not depend on a binary-address normalization. -/
theorem transpose_disperses {d B : ℕ} (hB : 0 < B) (hBd : B ∣ d) :
    Disperses (d*d) B (transposeNat d) := by
  intro x hx y hy hbin htarget
  obtain ⟨k, hk⟩ := hBd
  have hdpos : 0 < d := by nlinarith
  have hkpos : 0 < k := by rw [hk] at hdpos; exact Nat.pos_of_mul_pos_left hdpos
  have hrow : x / d = y / d := by
    rw [hk, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hbin]
  have hformula (z : ℕ) : transposeNat d z / B = (z % d) * k + (z / d) / B := by
    unfold transposeNat
    have he : z % d * d + z / d = B * ((z % d) * k) + z / d := by rw [hk]; ring
    rw [he, Nat.mul_add_div hB]
  rw [hformula, hformula, hrow] at htarget
  have hrem : x % d = y % d := by nlinarith
  have hdx := Nat.div_add_mod x d
  have hdy := Nat.div_add_mod y d
  rw [hrow, hrem] at hdx
  omega

 theorem transpose_coverage_bound {d K L m B₀ : ℕ} (paths : Fin K → Path (d*d))
    (hlen : ∀ j, (paths j).length ≤ L) (B : Fin m → ℕ)
    (hm : 0 < m) (hB₀ : 0 < B₀) (hlower : ∀ i, B₀ ≤ B i)
    (hdiv : ∀ i, B i ∣ d)
    (hsep : ∀ i j, i < j → volume (B i) ≤ B j) :
    ((covered paths (transposeNat d)).card : ℝ) ≤
      (K : ℝ) * L * (d*d) / m + K * (11 : ℝ)^L * (d*d) / B₀ := by
   simpa only [Nat.cast_mul] using coverage_bound paths hlen B hm hB₀ hlower
     (fun i => dvd_mul_of_dvd_left (hdiv i) d) hsep (transposeNat d)
     (fun i => transpose_disperses (lt_of_lt_of_le hB₀ (hlower i)) (hdiv i))

end BitWord.Compiler
