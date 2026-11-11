import SharedDecoders.CapacityRetentionAverageCounts

/-! The actual independent-shift average and its class-count simplification. -/

namespace SharedDecoders.RetentionAverage

open Module
open scoped BigOperators

variable {d : ℕ} [NeZero d] {κ : Type*} [Fintype κ]

noncomputable def meanGcd (d : ℕ) [NeZero d] : ℝ :=
  (∑ s : ZMod d, (Nat.gcd d s.val : ℝ))/(d : ℝ)

theorem meanGcd_le : meanGcd d ≤ 2*Real.sqrt d := by
  simpa only [meanGcd,pow_zero,one_nsmul,mul_one] using
    (mean_doubled_gcd_zmod_le (d := d) 0)

omit [Fintype κ] in
theorem class_weight_le (p : ZMod d → κ) (j : κ) (k : ℕ) :
    (classCard p j : ℝ)*survivalWeight p j k ≤ 2*(d : ℝ)/(k+2) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hn : (classCard p j : ℝ) ≤ d := by exact_mod_cast classCard_le p j
  have hx : 0 ≤ (classCard p j : ℝ)/d := by positivity
  have hx1 : (classCard p j : ℝ)/d ≤ 1 := (div_le_one hd).mpr hn
  have hh := LeanMachine.IncidenceSecondMoment.power_weight_le
    ((classCard p j : ℝ)/d) ((k : ℝ)/2) hx hx1 (by positivity)
  have hm := mul_le_mul_of_nonneg_left hh hd.le
  have he : (d : ℝ)*(1/((k : ℝ)/2+1)) = 2*(d : ℝ)/(k+2) := by field_simp
  rw [he] at hm
  have he' : (d : ℝ)*((classCard p j : ℝ)/d*(1-(classCard p j : ℝ)/d)^((k : ℝ)/2)) =
      (classCard p j : ℝ)*survivalWeight p j k := by dsimp [survivalWeight]; field_simp
  rwa [he'] at hm

theorem class_weight_sum_le (p : ZMod d → κ) (k : ℕ) :
    (∑ j : κ, (classCard p j : ℝ)*survivalWeight p j k) ≤
      2*(Fintype.card κ : ℝ)*d/(k+2) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => class_weight_le p j k)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  convert hh using 1
  ring

end SharedDecoders.RetentionAverage

namespace SharedDecoders

open Module RetentionAverage
open scoped BigOperators

variable {d : ℕ} [NeZero d] {κ : Type*} [Fintype κ]
variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A] [FiniteDimensional F A]

/-- Average over all actual `k`-tuples of shifts. Row events need not be
independent: their joint contribution is bounded by Cauchy--Schwarz. -/
theorem IsSharedCode.retention_average {p : ZMod d → κ}
    {C : Submodule F (State d A)} (hC : IsSharedCode F p C) (k : ℕ) :
    let S : Submodule F (State d A) := symmetricSpace
    let eta : ℝ := finrank F S-finrank F (C ⊓ S : Submodule F (State d A))
    (finrank F C : ℝ) ≤ finrank F S+(2*(k : ℝ)-1)*eta+
      (d : ℝ)*finrank F A*k/2*(meanGcd d-1)+
      (finrank F A : ℝ)/2*(∑ j : κ, (classCard p j : ℝ)*survivalWeight p j k)^2 := by
  classical
  let S : Submodule F (State d A) := symmetricSpace
  let eta : ℝ := finrank F S-finrank F (C ⊓ S : Submodule F (State d A))
  let base : ℝ := finrank F S+(2*(k : ℝ)-1)*eta
  let V : ℝ := (d : ℝ)^k
  let W : ℝ := ∑ j : κ, (classCard p j : ℝ)*survivalWeight p j k
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hV : 0 < V := by dsimp [V]; positivity
  have hlocal (t : Fin k → ZMod d) :
      (finrank F C : ℝ) ≤ base+(d : ℝ)*finrank F A/2*
        (∑ i : Fin k, ((Nat.gcd d (t i).val : ℝ)-1))+
        (finrank F A : ℝ)/2*(uncoveredCard p t : ℝ)^2 := by
    have hh := hC.retention_bound t
    dsimp only at hh
    rw [← uncoveredCard_eq] at hh
    simp only [Fintype.card_fin] at hh
    change (finrank F C : ℝ) ≤ base+_+_ at hh
    have hu : 0 ≤ (finrank F A : ℝ)/2*(uncoveredCard p t : ℝ) := by positivity
    nlinarith only [hh,hu]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hlocal t)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,nsmul_eq_mul] at hsum
  have hu := (div_le_iff₀ hV).mp (mean_uncovered_square_le (k := k) p)
  have hug := mul_le_mul_of_nonneg_left hu (show 0 ≤ (finrank F A : ℝ)/2 by positivity)
  have hg := (div_eq_iff (ne_of_gt hV)).mp (mean_gcd_sum (d := d) k)
  change (∑ t : Fin k → ZMod d, ∑ i : Fin k, ((Nat.gcd d (t i).val : ℝ)-1)) =
    (k : ℝ)*(meanGcd d-1)*V at hg
  rw [hg] at hsum
  change (finrank F C : ℝ) ≤ base+_+_
  apply (le_of_mul_le_mul_left (a := V) ?_ hV)
  dsimp only [V,W] at *
  nlinarith only [hsum,hug]

/-- The normalized restriction, with the exact number of declared classes.
Surjectivity is not needed; empty classes have zero weight. -/
theorem IsSharedCode.retention_normalized {p : ZMod d → κ}
    {C : Submodule F (State d A)} (hC : IsSharedCode F p C) (k : ℕ)
    (hb : 0 < finrank F A) :
    let N : ℝ := (finrank F A : ℝ)*(d : ℝ)^2
    let eta : ℝ := finrank F (symmetricSpace (F := F) (A := A) (I := ZMod d))-
      finrank F (C ⊓ symmetricSpace : Submodule F (State d A))
    (finrank F C : ℝ)/N-(d+1)/(2*d) ≤
      (2*(k : ℝ)-1)*(eta/N)+(k : ℝ)*(meanGcd d-1)/(2*d)+
      2*(Fintype.card κ : ℝ)^2/(k+2)^2 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hb' : (0 : ℝ) < finrank F A := by exact_mod_cast hb
  have hk : (0 : ℝ) < k+2 := by positivity
  have hh := hC.retention_average k
  dsimp only at hh ⊢
  have hw := class_weight_sum_le p k
  have hw0 : 0 ≤ (∑ j : κ, (classCard p j : ℝ)*survivalWeight p j k) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (survivalWeight_nonneg p j k))
  have hw2 := pow_le_pow_left₀ hw0 hw 2
  have hweighted := mul_le_mul_of_nonneg_left hw2 (show 0 ≤ (finrank F A : ℝ)/2 by positivity)
  have hs := congrArg (Nat.cast (R := ℝ))
    (two_mul_finrank_symmetricSpace (F := F) (A := A) (I := ZMod d))
  simp only [ZMod.card] at hs
  push_cast at hs
  have hraw : (finrank F C : ℝ) ≤
      (finrank F A : ℝ)*d*(d+1)/2+
      (2*(k : ℝ)-1)*((finrank F (symmetricSpace (F := F) (A := A) (I := ZMod d)) : ℝ)-
        finrank F (C ⊓ symmetricSpace : Submodule F (State d A)))+
      (d : ℝ)*finrank F A*k/2*(meanGcd d-1)+
      (finrank F A : ℝ)/2*(2*(Fintype.card κ : ℝ)*d/(k+2))^2 := by
    nlinarith only [hh,hweighted,hs]
  have hN : 0 < (finrank F A : ℝ)*(d : ℝ)^2 := by positivity
  have hdiv := (div_le_div_iff_of_pos_right hN).mpr hraw
  have hsub := sub_le_sub_right hdiv (((d : ℝ)+1)/(2*d))
  convert hsub using 1
  field_simp
  ring

end SharedDecoders
