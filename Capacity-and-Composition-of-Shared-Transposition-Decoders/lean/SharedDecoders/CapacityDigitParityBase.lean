import SharedDecoders.CapacityMaskProbability
import SharedDecoders.CapacityMaskStructured

/-! # Literal binary digit parity and its signed finite correlations -/

namespace SharedDecoders.CapacityDigitParity

open CapacityMaskProbability
open scoped BigOperators

/-- Parity of the lowest `h` binary digits, by repeated division by two. -/
def parity : ℕ → ℕ → Bool
  | 0,_ => false
  | h+1,n => decide (n%2=1) ^^ parity h (n/2)

@[simp] theorem parity_zero (n : ℕ) : parity 0 n=false := rfl

theorem parity_even (h n : ℕ) : parity (h+1) (2*n)=parity h n := by
  simp [parity]

theorem parity_odd (h n : ℕ) : parity (h+1) (2*n+1)=!parity h n := by
  simp [parity,Nat.add_comm,Nat.add_mul_div_left]

theorem parity_period (h n : ℕ) : parity h (n+2^h)=parity h n := by
  induction h generalizing n with
  | zero => rfl
  | succ h ih =>
    simp only [parity,pow_succ]
    have hm : (n+2^h*2)%2=n%2 := by omega
    have hd : (n+2^h*2)/2=n/2+2^h := by omega
    rw [hm,hd,ih]

theorem parity_mul_period (h n k : ℕ) : parity h (n+k*2^h)=parity h n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul,← Nat.add_assoc,parity_period,ih]

theorem parity_mod (h n : ℕ) : parity h (n%2^h)=parity h n := by
  have hh := parity_mul_period h (n%2^h) (n/2^h)
  rw [Nat.mod_add_div'] at hh
  exact hh.symm

/-- The exact low/high digit split, with the low coordinate restricted to its
literal binary block. -/
theorem parity_block (h m a r : ℕ) (ha : a<2^h) :
    parity (h+m) (a+2^h*r)=(parity h a ^^ parity m r) := by
  induction h generalizing a with
  | zero =>
    have ha0 : a=0 := by simpa using ha
    subst a
    simp [parity]
  | succ h ih =>
    have hd : (a+2^(h+1)*r)/2=a/2+2^h*r := by
      rw [pow_succ,show 2^h*2*r=(2^h*r)*2 by ring]
      omega
    have hm : (a+2^(h+1)*r)%2=a%2 := by
      rw [pow_succ,show 2^h*2*r=(2^h*r)*2 by ring]
      omega
    have ha' : a/2<2^h := by rw [pow_succ] at ha; omega
    rw [show h+1+m=(h+m)+1 by omega,parity,hd,hm,ih _ ha']
    rw [parity,Bool.xor_assoc]

def sign (h n : ℕ) : ℝ := if parity h n then -1 else 1

theorem sign_even (h n : ℕ) : sign (h+1) (2*n)=sign h n := by
  simp only [sign,parity_even]

theorem sign_odd (h n : ℕ) : sign (h+1) (2*n+1)=-sign h n := by
  simp only [sign,parity_odd]
  cases parity h n <;> norm_num

theorem sign_period (h n : ℕ) : sign h (n+2^h)=sign h n := by rw [sign,parity_period]; rfl

theorem sign_mod (h n : ℕ) : sign h (n%2^h)=sign h n := by rw [sign,parity_mod]; rfl

theorem sign_square (h n : ℕ) : sign h n*sign h n=1 := by
  unfold sign
  cases parity h n <;> norm_num

theorem sign_product_bounds (h a b : ℕ) : -1≤sign h a*sign h b ∧ sign h a*sign h b≤1 := by
  unfold sign
  cases parity h a <;> cases parity h b <;> norm_num

noncomputable def correlation (h k : ℕ) : ℝ :=
  avg (fun c : Fin (2^h) => sign h c.val*sign h (c.val+k))

theorem correlation_bounds (h k : ℕ) : -1≤correlation h k ∧ correlation h k≤1 :=
  ⟨le_avg (fun _ => (sign_product_bounds _ _ _).1),
    avg_le (fun _ => (sign_product_bounds _ _ _).2)⟩

theorem correlation_zero (h : ℕ) : correlation h 0=1 := by
  simp only [correlation,Nat.add_zero,sign_square,avg_const]

theorem correlation_period (h k : ℕ) : correlation h (k+2^h)=correlation h k := by
  simp only [correlation,← Nat.add_assoc,sign_period]

theorem avg_fin_two (f : Fin 2 → ℝ) : avg f=(f 0+f 1)/2 := by
  simp [avg_eq_sum_div_card,Fin.sum_univ_two]

theorem avg_double {n : ℕ} (f : ℕ → ℝ) :
    avg (fun c : Fin (n*2) => f c.val)=avg (fun a : Fin n => (f (2*a.val)+f (2*a.val+1))/2) := by
  rw [← avg_equiv (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n*2)),avg_product]
  congr 1
  funext a
  rw [avg_fin_two]
  change (f (0+2*a.val)+f (1+2*a.val))/2=_
  simp only [zero_add,Nat.add_comm]

theorem avg_power_double (h : ℕ) (f : ℕ → ℝ) :
    avg (fun c : Fin (2^(h+1)) => f c.val)=
      avg (fun a : Fin (2^h) => (f (2*a.val)+f (2*a.val+1))/2) := by
  let e : Fin (2^h) × Fin 2 ≃ Fin (2^(h+1)) :=
    finProdFinEquiv.trans (finCongr (pow_succ 2 h).symm)
  rw [← avg_equiv e,avg_product]
  congr 1
  funext a
  rw [avg_fin_two]
  change (f (0+2*a.val)+f (1+2*a.val))/2=_
  simp only [zero_add,Nat.add_comm]

theorem correlation_even (h k : ℕ) : correlation (h+1) (2*k)=correlation h k := by
  simp only [correlation]
  rw [avg_power_double h (fun n => sign (h+1) n*sign (h+1) (n+2*k))]
  have he (a : Fin (2^h)) :
      (sign (h+1) (2*a.val)*sign (h+1) (2*a.val+2*k)+
        sign (h+1) (2*a.val+1)*sign (h+1) (2*a.val+1+2*k))/2=
      sign h a.val*sign h (a.val+k) := by
    rw [show 2*a.val+2*k=2*(a.val+k) by omega,
      show 2*a.val+1+2*k=2*(a.val+k)+1 by omega,sign_even,sign_even,sign_odd,sign_odd]
    ring
  simp_rw [he]

theorem correlation_odd (h k : ℕ) :
    correlation (h+1) (2*k+1)=-(correlation h k+correlation h (k+1))/2 := by
  simp only [correlation]
  rw [avg_power_double h (fun n => sign (h+1) n*sign (h+1) (n+(2*k+1)))]
  have he (a : Fin (2^h)) :
      (sign (h+1) (2*a.val)*sign (h+1) (2*a.val+(2*k+1))+
        sign (h+1) (2*a.val+1)*sign (h+1) (2*a.val+1+(2*k+1)))/2=
      (-1/2)*(sign h a.val*sign h (a.val+k)+sign h a.val*sign h (a.val+(k+1))) := by
    rw [show 2*a.val+(2*k+1)=2*(a.val+k)+1 by omega,
      show 2*a.val+1+(2*k+1)=2*(a.val+(k+1)) by omega,sign_even,sign_odd,sign_odd,sign_even]
    ring
  simp_rw [he]
  rw [avg_const_mul,avg_add]
  ring

/-- The adjacent sum bound removes the exceptional-index case analysis in
the usual correlation induction. -/
theorem correlation_adjacent (h k : ℕ) :
    -1≤correlation (h+1) k+correlation (h+1) (k+1) ∧
      correlation (h+1) k+correlation (h+1) (k+1)≤1 := by
  obtain hm|hm := Nat.mod_two_eq_zero_or_one k
  · have he : k=2*(k/2) := by omega
    rw [he,correlation_even,correlation_odd]
    have hb := correlation_bounds h (k/2)
    have hb' := correlation_bounds h (k/2+1)
    constructor <;> linarith
  · have he : k=2*(k/2)+1 := by omega
    have he' : 2*(k/2)+1+1=2*(k/2+1) := by omega
    rw [he,correlation_odd,he',correlation_even]
    have hb := correlation_bounds h (k/2)
    have hb' := correlation_bounds h (k/2+1)
    constructor <;> linarith

theorem correlation_two_nonzero (k : ℕ) (hk : 0<k) (hk' : k<4) :
    correlation 2 k≤1/2 := by
  change (avg (fun c : Fin 4 => sign 2 c.val*sign 2 (c.val+k)))≤1/2
  interval_cases k <;> norm_num [avg_eq_sum_div_card,Fin.sum_univ_succ,sign,parity]

/-- Every nonzero shift has agreement correlation at most one half. -/
theorem correlation_nonzero_upper (h : ℕ) (hh : 2≤h) (k : ℕ)
    (hk : 0<k) (hk' : k<2^h) : correlation h k≤1/2 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hh
  clear hh
  induction n generalizing k with
  | zero => exact correlation_two_nonzero k hk (by simpa using hk')
  | succ n ih =>
    obtain hm|hm := Nat.mod_two_eq_zero_or_one k
    · have he : k=2*(k/2) := by omega
      rw [show 2+(n+1)=(2+n)+1 by omega,he,correlation_even]
      apply ih
      · omega
      · rw [show 2+(n+1)=(2+n)+1 by omega,pow_succ] at hk'
        omega
    · have he : k=2*(k/2)+1 := by omega
      rw [show 2+(n+1)=(2+n)+1 by omega,he,correlation_odd]
      have hb := correlation_adjacent (1+n) (k/2)
      have heh : 1+n+1=2+n := by omega
      rw [heh] at hb
      linarith

end SharedDecoders.CapacityDigitParity
