import SharedDecoders.CapacityRetentionFinite
import SharedDecoders.CapacityMeans
import LeanMachine.IncidenceSecondMoment

/-! Actual independent-shift sample counts for symmetric retention. -/

namespace SharedDecoders.RetentionAverage

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {d k : ℕ} [NeZero d] {κ : Type*}

noncomputable def classCard (p : ZMod d → κ) (j : κ) : ℕ := Fintype.card {c // p c=j}

theorem classCard_le (p : ZMod d → κ) (j : κ) : classCard p j ≤ d := by
  simpa only [classCard,ZMod.card] using Fintype.card_subtype_le (fun c => p c=j)

def Misses (p : ZMod d → κ) (t : Fin k → ZMod d) (c : ZMod d) : Prop :=
  ∀ i, p c ≠ p (c+t i)

noncomputable def uncoveredCard (p : ZMod d → κ) (t : Fin k → ZMod d) : ℕ :=
  Fintype.card {c // Misses p t c}

theorem uncoveredCard_eq (p : ZMod d → κ) (t : Fin k → ZMod d) :
    uncoveredCard p t = (uncoveredRows (fun i => coveredRows p (t i))).card := by
  calc
    uncoveredCard p t = Fintype.card
        {c // c ∈ uncoveredRows (fun i => coveredRows p (t i))} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun c => by
        simp only [uncoveredRows, coveredRows, Finset.mem_filter,
          Finset.mem_univ, true_and, Misses])
    _ = _ := Fintype.card_coe _

noncomputable def shiftAvoidEquiv (p : ZMod d → κ) (c : ZMod d) :
    {s : ZMod d // p c ≠ p (c+s)} ≃ {x : ZMod d // p x ≠ p c} where
  toFun s := ⟨c+s.1,Ne.symm s.2⟩
  invFun x := ⟨x.1-c,by simpa using Ne.symm x.2⟩
  left_inv s := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem shiftAvoid_card (p : ZMod d → κ) (c : ZMod d) :
    Fintype.card {s : ZMod d // p c ≠ p (c+s)} = d-classCard p (p c) := by
  rw [Fintype.card_congr (shiftAvoidEquiv p c), Fintype.card_subtype_compl]
  simp only [ZMod.card,classCard]

noncomputable def missesEquiv (p : ZMod d → κ) (c : ZMod d) :
    {t : Fin k → ZMod d // Misses p t c} ≃
      (Fin k → {s : ZMod d // p c ≠ p (c+s)}) where
  toFun t i := ⟨t.1 i,t.2 i⟩
  invFun t := ⟨fun i => (t i).1,fun i => (t i).2⟩
  left_inv t := by apply Subtype.ext; rfl
  right_inv t := by funext i; apply Subtype.ext; rfl

theorem misses_card (p : ZMod d → κ) (c : ZMod d) :
    Fintype.card {t : Fin k → ZMod d // Misses p t c} =
      (d-classCard p (p c))^k := by
  rw [Fintype.card_congr (missesEquiv p c),Fintype.card_fun,shiftAvoid_card,Fintype.card_fin]

theorem uncovered_square_sum_le (p : ZMod d → κ) :
    (∑ t : Fin k → ZMod d, (uncoveredCard p t : ℝ)^2) ≤
      (∑ c : ZMod d, Real.sqrt (((d-classCard p (p c))^k : ℕ) : ℝ))^2 := by
  have hh := LeanMachine.IncidenceSecondMoment.incidence_squared_sum_le
    (fun (c : ZMod d) (t : Fin k → ZMod d) => Misses p t c)
  simpa only [misses_card,uncoveredCard] using hh

noncomputable def survivalWeight (p : ZMod d → κ) (j : κ) (k : ℕ) : ℝ :=
  (1-(classCard p j : ℝ)/d)^((k : ℝ)/2)

theorem survivalWeight_nonneg (p : ZMod d → κ) (j : κ) (k : ℕ) :
    0 ≤ survivalWeight p j k := by
  apply Real.rpow_nonneg
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hn : (classCard p j : ℝ) ≤ d := by exact_mod_cast classCard_le p j
  have hh : (classCard p j : ℝ)/d ≤ 1 := (div_le_one hd).mpr hn
  linarith

theorem sqrt_marginal (p : ZMod d → κ) (j : κ) (k : ℕ) :
    Real.sqrt (((d-classCard p j)^k : ℕ) : ℝ) =
      Real.sqrt ((d : ℝ)^k)*survivalWeight p j k := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hn : (classCard p j : ℝ) ≤ d := by exact_mod_cast classCard_le p j
  have hu : 0 ≤ 1-(classCard p j : ℝ)/d := by
    have hh := (div_le_one hd).mpr hn
    linarith
  have he : (d : ℝ)-(classCard p j : ℝ) = d*(1-(classCard p j : ℝ)/d) := by field_simp
  rw [Nat.cast_pow,Nat.cast_sub (classCard_le p j),he,mul_pow,Real.sqrt_mul (by positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu]
  congr 1
  ring

theorem sum_class_weights [Fintype κ] (p : ZMod d → κ) (w : κ → ℝ) :
    (∑ c : ZMod d, w (p c)) = ∑ j : κ, (classCard p j : ℝ)*w j := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ p (fun c => w (p c))]
  apply Finset.sum_congr rfl
  intro j _
  have he : (∑ c ∈ Finset.univ.filter (fun c => p c=j), w (p c)) =
      ∑ c ∈ Finset.univ.filter (fun c => p c=j), w j := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [(Finset.mem_filter.mp hc).2]
  rw [he,Finset.sum_const]
  simp only [classCard,Fintype.card_subtype,nsmul_eq_mul]

/-- The actual joint uncovered mean, derived from marginal counts and
Cauchy--Schwarz, not from an independence assumption about rows. -/
theorem mean_uncovered_square_le [Fintype κ] (p : ZMod d → κ) :
    (∑ t : Fin k → ZMod d, (uncoveredCard p t : ℝ)^2)/(d : ℝ)^k ≤
      (∑ j : κ, (classCard p j : ℝ)*survivalWeight p j k)^2 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hh := uncovered_square_sum_le (k := k) p
  simp_rw [sqrt_marginal] at hh
  rw [← Finset.mul_sum, sum_class_weights p (fun j => survivalWeight p j k)] at hh
  rw [mul_pow,Real.sq_sqrt (by positivity)] at hh
  apply (div_le_iff₀ (by positivity : 0 < (d : ℝ)^k)).mpr
  simpa only [mul_comm] using hh

/-- Exact averaging of one coordinate of a uniform finite product. -/
theorem sum_sample_coordinate {J : Type*} [Fintype J] [DecidableEq J]
    (i : J) (f : ZMod d → ℝ) :
    (∑ t : J → ZMod d, f (t i)) * (d : ℝ) =
      (d : ℝ)^(Fintype.card J)*(∑ s : ZMod d, f s) := by
  classical
  have he := Equiv.sum_comp (Equiv.funSplitAt i (ZMod d))
    (fun z : ZMod d × ({j : J // j ≠ i} → ZMod d) => f z.1)
  have hn : Fintype.card {j : J // j ≠ i}+1=Fintype.card J := by
    have hh := Fintype.card_subtype_compl (fun j : J => j=i)
    have hi : Fintype.card {j : J // j=i} = 1 := by simp
    rw [hi] at hh
    change Fintype.card {j : J // j ≠ i} = Fintype.card J-1 at hh
    have hp : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨i⟩
    omega
  rw [Fintype.sum_prod_type] at he
  have hsum : (∑ t : J → ZMod d, f (t i)) =
      (d : ℝ)^(Fintype.card {j : J // j ≠ i})*(∑ s : ZMod d, f s) := by
    simpa only [Equiv.funSplitAt_apply,Finset.sum_const,
      Finset.card_univ,Fintype.card_fun,ZMod.card,Nat.cast_pow,nsmul_eq_mul,
      ← Finset.sum_mul,mul_comm] using he
  rw [hsum,← hn,pow_succ]
  ring

theorem mean_gcd_sum (k : ℕ) :
    (∑ t : Fin k → ZMod d, ∑ i : Fin k, ((Nat.gcd d (t i).val : ℝ)-1))/(d : ℝ)^k =
      (k : ℝ)*((∑ s : ZMod d, (Nat.gcd d s.val : ℝ))/d-1) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  let f (s : ZMod d) : ℝ := (Nat.gcd d s.val : ℝ)-1
  have hsum : (∑ t : Fin k → ZMod d, ∑ i : Fin k, f (t i)) * d =
      (d : ℝ)^k*(k : ℝ)*(∑ s : ZMod d, f s) := by
    calc
      _ = ∑ i : Fin k, (∑ t : Fin k → ZMod d, f (t i))*(d : ℝ) := by
        rw [Finset.sum_comm,Finset.sum_mul]
      _ = ∑ i : Fin k, (d : ℝ)^k*(∑ s : ZMod d, f s) := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [Fintype.card_fin] using sum_sample_coordinate i f
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  have hf : (∑ s : ZMod d, f s) = (∑ s : ZMod d, (Nat.gcd d s.val : ℝ))-(d : ℝ) := by
    simp only [f,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,mul_one]
  rw [hf] at hsum
  change (∑ t : Fin k → ZMod d, ∑ i : Fin k, f (t i))/(d : ℝ)^k = _
  apply (div_eq_iff (by positivity : (d : ℝ)^k ≠ 0)).mpr
  apply (mul_left_inj' (ne_of_gt hd)).mp
  have he : ((k : ℝ)*((∑ s : ZMod d, (Nat.gcd d s.val : ℝ))/d-1)*(d : ℝ)^k)*d =
      (d : ℝ)^k*(k : ℝ)*((∑ s : ZMod d, (Nat.gcd d s.val : ℝ))-d) := by
    field_simp
  rw [he]
  exact hsum

end SharedDecoders.RetentionAverage
