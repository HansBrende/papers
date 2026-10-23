import BitWord.CompilerBoolean
import BitWord.ScanThreshold

namespace BitWord.Compiler
open Geometry

/-- The finite scale choices force at least half of all target addresses to be
absent from the union of the paths' source coincidences. -/
theorem coverage_le_half {d K L m B₀ : ℕ} (paths : Fin K → Path (d*d))
    (hlen : ∀ j, (paths j).length ≤ L) (B : Fin m → ℕ)
    (hm : 0 < m) (hB₀ : 0 < B₀) (hlower : ∀ i, B₀ ≤ B i)
    (hdiv : ∀ i, B i ∣ d)
    (hsep : ∀ i j, i < j → volume (B i) ≤ B j)
    (hmany : 4*K*L ≤ m) (hwide : 4*K*11^L ≤ B₀) :
    ((covered paths (transposeNat d)).card : ℝ) ≤ ((d*d:ℕ):ℝ)/2 := by
  have hh := transpose_coverage_bound paths hlen B hm hB₀ hlower hdiv hsep
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hb' : (0:ℝ)<B₀ := by exact_mod_cast hB₀
  have hmn : (4:ℝ)*K*L ≤ m := by exact_mod_cast hmany
  have hwd : (4:ℝ)*K*(11:ℝ)^L ≤ B₀ := by exact_mod_cast hwide
  have h₁ : (K:ℝ)*L*(d*d)/m ≤ ((d*d:ℕ):ℝ)/4 := by
    apply (div_le_iff₀ hm').2
    push_cast
    nlinarith [sq_nonneg (d:ℝ)]
  have h₂ : (K:ℝ)*(11:ℝ)^L*(d*d)/B₀ ≤ ((d*d:ℕ):ℝ)/4 := by
    apply (div_le_iff₀ hb').2
    push_cast
    nlinarith [sq_nonneg (d:ℝ)]
  have ha := add_le_add h₁ h₂
  push_cast at hh ha ⊢
  linarith

 theorem no_readout_of_scales {d K L m B₀ : ℕ} (hd : 0 < d)
    (paths : Fin K → Path (d*d)) (hlen : ∀ j, (paths j).length ≤ L)
    (B : Fin m → ℕ) (hm : 0 < m) (hB₀ : 0 < B₀)
    (hlower : ∀ i, B₀ ≤ B i) (hdiv : ∀ i, B i ∣ d)
    (hsep : ∀ i j, i < j → volume (B i) ≤ B j)
    (hmany : 4*K*L ≤ m) (hwide : 4*K*11^L ≤ B₀)
    (tables : Fin (d*d) → (Fin K → Bool) → Bool) :
    ¬ ∀ (x : Fin (d*d) → Bool) a,
      readout paths tables x a = x ((transposePerm d).symm a) := by
  apply no_transpose_readout_of_coverage_lt paths _ tables
  have hh := coverage_le_half paths hlen B hm hB₀ hlower hdiv hsep hmany hwide
  have hp : (0:ℝ)<((d*d:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos hd hd
  have hl : ((covered paths (transposeNat d)).card : ℝ) < ((d*d:ℕ):ℝ) := by linarith
  exact_mod_cast hl

 def pathScaleCount (K L : ℕ) : ℕ := max 1 (4*K*L)
 def pathInitialExponent (K L : ℕ) : ℕ := Nat.clog 2 (max 1 (4*K*11^L))
 def pathInitial (K L : ℕ) : ℕ := 2 ^ pathInitialExponent K L
 def pathThreshold (K L : ℕ) : ℕ := scanScale (pathInitial K L) (pathScaleCount K L - 1)

 theorem pathInitial_bounds (K L : ℕ) : 0 < pathInitial K L ∧ 4*K*11^L ≤ pathInitial K L := by
   have hh := Nat.le_pow_clog (b := 2) (by decide) (max 1 (4*K*11^L))
   change max 1 (4*K*11^L) ≤ pathInitial K L at hh
   omega

/-- Every selected scale divides the last scale, so the obstruction applies to
all positive multiples of one fixed threshold, not only dyadic dimensions. -/
 theorem no_bounded_path_transpose_of_dvd (K L d : ℕ) (hd : 0 < d)
     (hdiv : pathThreshold K L ∣ d)
     (paths : Fin K → Path (d*d))
     (hlen : ∀ j, (paths j).length ≤ L)
     (tables : Fin (d*d) → (Fin K → Bool) → Bool) :
     ¬ ∀ (x : Fin (d*d) → Bool) a,
       readout paths tables x a = x ((transposePerm d).symm a) := by
   let m := pathScaleCount K L
   let B₀ := pathInitial K L
   let B : Fin m → ℕ := fun i => scanScale B₀ i.val
   have hm : 0 < m := by dsimp [m, pathScaleCount]; omega
   have hb : 0 < B₀ := (pathInitial_bounds K L).1
   have hbl (i : Fin m) : B₀ ≤ B i := (scanScale_strictMono hb).monotone (Nat.zero_le i.val)
   have hBd (i : Fin m) : B i ∣ d := by
     have hi : B i ≤ pathThreshold K L :=
       (scanScale_strictMono hb).monotone (show i.val ≤ m-1 by omega)
     obtain ⟨v, hv⟩ := scanScale_dyadic (pathInitialExponent K L) (m-1)
     have ht : pathThreshold K L = 2^v := hv
     rw [ht] at hi
     exact (scanScale_dvd_dyadic hi).trans (by rwa [← ht])
   apply no_readout_of_scales hd paths hlen B hm hb hbl hBd
   · intro i j hij
     exact scanScale_separated hb hij
   · dsimp [m, pathScaleCount]
     omega
   · exact (pathInitial_bounds K L).2

/-- The actual all-size endpoint obstruction: fixed path count and length,
arbitrary public heterogeneous layouts, and arbitrary pointwise nonlinear
readout fail on every sufficiently large dyadic bit square. -/
 theorem no_bounded_path_transpose (K L h : ℕ) (hlarge : pathThreshold K L ≤ 2^h)
     (paths : Fin K → Path ((2^h)*(2^h)))
     (hlen : ∀ j, (paths j).length ≤ L)
     (tables : Fin ((2^h)*(2^h)) → (Fin K → Bool) → Bool) :
     ¬ ∀ (x : Fin ((2^h)*(2^h)) → Bool) a,
       readout paths tables x a = x ((transposePerm (2^h)).symm a) :=
   no_bounded_path_transpose_of_dvd K L (2^h) (Nat.pow_pos (by decide))
     (scanScale_dvd_dyadic hlarge) paths hlen tables

end BitWord.Compiler
