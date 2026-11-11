import SharedDecoders.CapacityDigitParityBase
import SharedDecoders.CapacityMaskDirectCertificate

/-! # Exact direct-certificate envelope of literal cyclic binary digit parity -/

namespace SharedDecoders.CapacityDigitParity

open CapacityMaskProbability CapacityMask CapacityMaskStructured CapacityRuns
open scoped BigOperators

/-- The actual cyclic mask, not a sequence supplied with correlation certificates. -/
def digitMask (h : ℕ) (c : ZMod (2^h)) : Bool := parity h c.val

theorem finEquiv_val {n : ℕ} [NeZero n] (i : Fin n) : ((ZMod.finEquiv n) i).val=i.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

theorem correlation_change_count (h : ℕ) (s : ZMod (2^h)) :
    correlation h s.val=1-2*(changeCount (digitMask h) s : ℝ)/(2^h : ℕ) := by
  classical
  have he := avg_equiv (ZMod.finEquiv (2^h)).toEquiv
    (fun c => sign h c.val*sign h (c+s).val)
  have hleft : (fun c : Fin (2^h) =>
      sign h ((ZMod.finEquiv (2^h)) c).val*sign h (((ZMod.finEquiv (2^h)) c)+s).val)=
      (fun c : Fin (2^h) => sign h c.val*sign h (c.val+s.val)) := by
    funext c
    rw [ZMod.val_add,finEquiv_val,sign_mod]
  simp only [RingEquiv.toEquiv_eq_coe,EquivLike.coe_coe] at he
  rw [hleft] at he
  change correlation h s.val=_ at he
  rw [he]
  have hpoint (c : ZMod (2^h)) : sign h c.val*sign h (c+s).val=
      1-2*(if digitMask h (c+s)≠digitMask h c then (1 : ℝ) else 0) := by
    unfold sign digitMask
    cases parity h c.val <;> cases parity h (c+s).val <;> norm_num
  simp_rw [hpoint]
  rw [avg_sub,avg_const,avg_const_mul]
  have hp := prob_eq_card (fun c : ZMod (2^h) => digitMask h (c+s)≠digitMask h c)
  simp only [← Nat.card_eq_fintype_card] at hp
  have hc : Nat.card {c : ZMod (2^h) // digitMask h (c+s)≠digitMask h c}=
      changeCount (digitMask h) s := Nat.card_eq_fintype_card
  have hd : Nat.card (ZMod (2^h))=2^h := by rw [Nat.card_eq_fintype_card,ZMod.card]
  rw [hc,hd] at hp
  have hind : (avg fun c : ZMod (2^h) => if digitMask h (c+s)≠digitMask h c then (1 : ℝ) else 0)=
      prob (fun c : ZMod (2^h) => digitMask h (c+s)≠digitMask h c) := by
    unfold prob
    congr 1
    funext c
    by_cases hh : digitMask h (c+s)≠digitMask h c <;> simp [hh]
  rw [hind,hp]
  ring

theorem digit_change_quarter (h : ℕ) (hh : 2≤h) (s : ZMod (2^h)) (hs : s≠0) :
    (2^h : ℕ)/4≤(changeCount (digitMask h) s : ℝ) := by
  have hval : 0<s.val := by
    have hv : s.val≠0 := fun hv => hs ((ZMod.val_eq_zero s).mp hv)
    omega
  have hc := correlation_nonzero_upper h hh s.val hval s.val_lt
  rw [correlation_change_count] at hc
  have hd : (0 : ℝ)<(2^h : ℕ) := by positivity
  have he : (1-2*(changeCount (digitMask h) s : ℝ)/(2^h : ℕ))*(2^h : ℕ)=
      (2^h : ℕ)-2*(changeCount (digitMask h) s : ℝ) := by
    field_simp
  have hm := mul_le_mul_of_nonneg_right hc (le_of_lt hd)
  rw [he] at hm
  linarith

theorem digit_direct_lower (h : ℕ) (hh : 2≤h) (b : ℕ)
    (Δ : Finset (ZMod (2^h))) (hΔ : Δ.Nonempty) :
    (5/8)*(b : ℝ)*(2^h : ℕ)^2≤directCertificate (digitMask h) b Δ := by
  have he := directCertificate_floor_of_changes (digitMask h) b (1/4) (by norm_num)
    (fun s hs => by simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using digit_change_quarter h hh s hs) Δ hΔ
  convert he using 1; ring

theorem position_val {ℓ : ℕ} [NeZero ℓ] (a : Fin ℓ) (r : Fin 8) :
    (position a r).val=a.val+ℓ*r.val := by
  rw [position_formula,← Nat.cast_mul,← Nat.cast_add]
  apply ZMod.val_natCast_of_lt
  have ha := a.isLt
  have hr := r.isLt
  have hl := NeZero.pos ℓ
  nlinarith

theorem parity_three_seed (r : Fin 8) : parity 3 r.val=seed r := by
  fin_cases r <;> decide

theorem structured_parity_mask (n : ℕ) :
    (fun c : ZMod (8*2^n) => parity (n+3) c.val)=
      mask (fun a : Fin (2^n) => parity n a.val) := by
  funext c
  obtain ⟨⟨a,r⟩,rfl⟩ := positionEquiv.surjective c
  change parity (n+3) (position a r).val=mask _ (position a r)
  rw [position_val,parity_block n 3 a.val r.val a.isLt,mask_position,parity_three_seed]

theorem structured_first_card (ℓ : ℕ) [NeZero ℓ] : (firstShifts (ℓ := ℓ)).card=2 := by
  have hs : (3*(ℓ : ZMod (8*ℓ)))≠0 := by
    intro hz
    have hc : ((3*ℓ : ℕ) : ZMod (8*ℓ))=0 := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using hz
    have hh := congrArg ZMod.val hc
    have hl := NeZero.pos ℓ
    rw [ZMod.val_natCast_of_lt (by omega : 3*ℓ<8*ℓ),ZMod.val_zero] at hh
    omega
  simp [firstShifts,extendShifts,Ne.symm hs]

/-- Exact attainment comes from the actual two-color quotient of the first
structured graph, rather than an assumed all-orbit component formula. -/
theorem digit_direct_attainment_block (n b : ℕ) :
    ∃ Δ : Finset (ZMod (8*2^n)), Δ.Nonempty ∧
      directCertificate (fun c => parity (n+3) c.val) b Δ=
        (5/8)*(b : ℝ)*(8*2^n : ℕ)^2 := by
  refine ⟨firstShifts,by simp [firstShifts,extendShifts],?_⟩
  rw [structured_parity_mask,directCertificate,structured_first_card,first_component_count]
  push_cast
  norm_num
  ring

private def Attains (h b d : ℕ) [NeZero d] : Prop :=
  ∃ Δ : Finset (ZMod d), Δ.Nonempty ∧
    directCertificate (fun c => parity h c.val) b Δ=(5/8)*(b : ℝ)*(d : ℝ)^2

private theorem attainment_congr (h b d e : ℕ) [NeZero d] [NeZero e] (he : d=e) :
    Attains h b d ↔ Attains h b e := by
  subst e
  rfl

/-- The complete original envelope: every nonempty actual shift set has the
claimed certificate lower bound, and one actual two-shift set attains it. -/
theorem digit_parity_envelope (h : ℕ) (hh : 3≤h) (b : ℕ) :
    (∀ Δ : Finset (ZMod (2^h)), Δ.Nonempty →
      (5/8)*(b : ℝ)*(2^h : ℕ)^2≤directCertificate (digitMask h) b Δ) ∧
    (∃ Δ : Finset (ZMod (2^h)), Δ.Nonempty ∧
      directCertificate (digitMask h) b Δ=(5/8)*(b : ℝ)*(2^h : ℕ)^2) := by
  refine ⟨fun Δ hΔ => digit_direct_lower h (by omega) b Δ hΔ,?_⟩
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hh
  have he := digit_direct_attainment_block n b
  change Attains (3+n) b (2^(3+n))
  apply (attainment_congr (3+n) b _ _ (show (2 : ℕ)^(3+n)=8*2^n by rw [pow_add]; norm_num)).mpr
  simpa only [Attains,show 3+n=n+3 by omega] using he



theorem digit_envelope_integral (h : ℕ) (hh : 3≤h) (b : ℕ) :
    ∃ z : ℤ, (z : ℝ)=(5/8)*(b : ℝ)*(2^h : ℕ)^2 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hh
  refine ⟨(40 : ℤ)*b*(2^n : ℕ)^2,?_⟩
  rw [pow_add]
  push_cast
  norm_num
  ring

/-- Exactness survives final integer flooring because the attained value is
itself integral at every power-of-two width at least eight. -/
theorem digit_parity_floor_envelope (h : ℕ) (hh : 3≤h) (b : ℕ) :
    ∃ z : ℤ, (z : ℝ)=(5/8)*(b : ℝ)*(2^h : ℕ)^2 ∧
      (∀ Δ : Finset (ZMod (2^h)), Δ.Nonempty → z≤⌊directCertificate (digitMask h) b Δ⌋) ∧
      (∃ Δ : Finset (ZMod (2^h)), Δ.Nonempty ∧ ⌊directCertificate (digitMask h) b Δ⌋=z) := by
  obtain ⟨z,hz⟩ := digit_envelope_integral h hh b
  obtain ⟨hlower,Δ,hΔ,hattain⟩ := digit_parity_envelope h hh b
  refine ⟨z,hz,?_,Δ,hΔ,?_⟩
  · intro Γ hΓ
    apply Int.le_floor.mpr
    rw [hz]
    exact hlower Γ hΓ
  · rw [hattain,← hz,Int.floor_intCast]

theorem structured_envelope_gap (b d : ℝ) :
    (5/8)*b*d^2-((9/16)*b*d^2+(1/2)*b*d)=b*d*(d-8)/16 := by ring

end SharedDecoders.CapacityDigitParity
