import SharedDecoders.CompositionAgreementCounting

/-! # Full-input agreement of arbitrary deterministic shared maps

All counts are on the complete input cube. No linearity, independent owners,
or probabilistic correctness-fibre hypothesis is used.
-/

namespace SharedDecoders

open scoped BigOperators

variable {d : ℕ} [NeZero d] {A κ : Type*} [Fintype A] [Fintype κ]

noncomputable def correctInputs (K : State d A → State d A) : Finset (State d A) := by
  classical
  exact Finset.univ.filter (fun X => K X = swap X)

noncomputable def correctPhases (K : State d A → State d A) (X : State d A) :
    Finset (ZMod d) := by
  classical
  exact Finset.univ.filter (fun c => K (rot (-c) X) = swap (rot (-c) X))

omit [Fintype A] [Fintype κ] in
lemma phase_words_equal (p : ZMod d → κ) (K : State d A → State d A)
    (hK : ClassUniform p K) (X : State d A)
    {c e : ZMod d} (hc : c ∈ correctPhases K X) (he : e ∈ correctPhases K X)
    (hp : p c = p e) : twistedRowsEquiv X c = twistedRowsEquiv X e := by
  classical
  obtain ⟨f, hf⟩ := hK
  have hc' : K (rot (-c) X) = swap (rot (-c) X) := (Finset.mem_filter.mp hc).2
  have he' : K (rot (-e) X) = swap (rot (-e) X) := (Finset.mem_filter.mp he).2
  funext i
  have h₁ := congrFun (congrFun hc' i) c
  have h₂ := congrFun (congrFun he' i) e
  simp only [hf, rot_rot_neg, swap_apply, rot_apply, hp] at h₁ h₂
  change X c (i - c) = X e (i - e)
  simpa only [sub_eq_add_neg] using h₁.symm.trans h₂

lemma correctPhases_sum (K : State d A → State d A) :
    (∑ X : State d A, (correctPhases K X).card) = d * (correctInputs K).card := by
  classical
  have hrot (c : ZMod d) :
      (Finset.univ.filter (fun X : State d A => K (rot (-c) X) = swap (rot (-c) X))).card =
        (correctInputs K).card := by
    have h := Nat.card_congr ((rotEquiv (-c)).subtypeEquiv
      (p := fun X : State d A => K (rot (-c) X) = swap (rot (-c) X))
      (q := fun X : State d A => K X = swap X) (fun _ => Iff.rfl))
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, correctInputs] using h
  simp only [correctPhases, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have he (c : ZMod d) : (∑ X : State d A,
      if K (rot (-c) X) = swap (rot (-c) X) then 1 else 0) = (correctInputs K).card := by
    simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using hrot c
  simp_rw [he]
  simp [ZMod.card]

omit [Fintype κ] in
lemma equalClassPairs_sum (p : ZMod d → κ) :
    (∑ X : State d A, (equalClassPairs p (twistedRowsEquiv X)).card) =
      (sameClassPairs p).card * (Fintype.card A ^ d) ^ (d - 1) := by
  classical
  have he (X : State d A) : equalClassPairs p (twistedRowsEquiv X) =
      (sameClassPairs p).filter (fun ce => twistedRowsEquiv X ce.1 = twistedRowsEquiv X ce.2) := by
    ext ce
    simp [equalClassPairs, sameClassPairs, and_assoc]
  simp_rw [he]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hpair (ce : ZMod d × ZMod d) (hce : ce ∈ sameClassPairs p) :
      (∑ X : State d A, if twistedRowsEquiv X ce.1 = twistedRowsEquiv X ce.2 then 1 else 0) =
        (Fintype.card A ^ d) ^ (d - 1) := by
    have hne : ce.1 ≠ ce.2 := (mem_sameClassPairs p ce).mp hce |>.1
    have h := twisted_pair_card (A := A) ce.1 ce.2 hne
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.card_eq_sum_ones, Finset.sum_filter] using h
  calc
    _ = ∑ _ce ∈ sameClassPairs p, (Fintype.card A ^ d) ^ (d - 1) :=
      Finset.sum_congr rfl hpair
    _ = _ := by simp

/-- Integer form of the phase-count bound; division gives the stated uniform
probability inequality. Unused class labels only weaken the upper bound. -/
theorem full_input_agreement_count (p : ZMod d → κ) (K : State d A → State d A)
    (hK : ClassUniform p K) :
    2 * d * (Fintype.card A ^ d) * (correctInputs K).card ≤
      (2 * Fintype.card κ * (Fintype.card A ^ d) +
        ∑ J : κ, receiverClassSize p J * (receiverClassSize p J - 1)) *
          Fintype.card (State d A) := by
  classical
  have hlocal (X : State d A) : 2 * (correctPhases K X).card ≤
      2 * Fintype.card κ + (equalClassPairs p (twistedRowsEquiv X)).card := by
    apply selected_card_bound
    intro c hc e he hp
    exact phase_words_equal p K hK X hc he hp
  have h := Finset.sum_le_sum (s := Finset.univ) (fun X _ => hlocal X)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, correctPhases_sum,
    equalClassPairs_sum, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  have hp : (Fintype.card A ^ d) * (Fintype.card A ^ d) ^ (d - 1) =
      Fintype.card (State d A) := by
    rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos d)]
    simp [State, ZMod.card]
  have hmul := Nat.mul_le_mul_left (Fintype.card A ^ d) h
  rw [sameClassPairs_card] at hmul
  have hprod := congrArg (fun n => (∑ J : κ, receiverClassSize p J *
    (receiverClassSize p J - 1)) * n) hp
  nlinarith


omit [Fintype κ] in
/-- A single repeated receiver class already bounds full-input agreement away
from one, independently of the other classes. -/
theorem repeated_class_agreement_count (p : ZMod d → κ) (K : State d A → State d A)
    (hK : ClassUniform p K) {c e : ZMod d} (hce : c ≠ e) (hpce : p c = p e) :
    2 * (Fintype.card A ^ d) * (correctInputs K).card ≤
      (Fintype.card A ^ d + 1) * Fintype.card (State d A) := by
  classical
  let G := correctInputs K
  let G' := Finset.univ.filter (fun X : State d A =>
    K (rot (e - c) X) = swap (rot (e - c) X))
  let E := Finset.univ.filter (fun X : State d A =>
    twistedRowsEquiv X c = twistedRowsEquiv X e)
  have hG' : G'.card = G.card := by
    have h := Nat.card_congr ((rotEquiv (e - c)).subtypeEquiv
      (p := fun X : State d A => K (rot (e - c) X) = swap (rot (e - c) X))
      (q := fun X : State d A => K X = swap X) (fun _ => Iff.rfl))
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, G', G, correctInputs] using h
  have hE : E.card = (Fintype.card A ^ d) ^ (d - 1) := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, E] using
      twisted_pair_card (A := A) c e hce
  have hsub : G ∩ G' ⊆ E := by
    intro X hX
    obtain ⟨hx, hx'⟩ := Finset.mem_inter.mp hX
    have h₀ : K X = swap X := (Finset.mem_filter.mp hx).2
    have h₁ : K (rot (e - c) X) = swap (rot (e - c) X) := (Finset.mem_filter.mp hx').2
    have hc := hK.columns_of_same_class hpce X
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    funext i
    have heq := hc (i - e)
    rw [h₀, h₁] at heq
    change X e (i - e) = X c ((i - e) + (e - c)) at heq
    have hi : (i - e) + (e - c) = i - c := by abel
    rw [hi] at heq
    exact heq.symm
  have hinter := (Finset.card_le_card hsub).trans_eq hE
  have hunion : (G ∪ G').card ≤ Fintype.card (State d A) := Finset.card_le_univ _
  have hinc := Finset.card_union_add_card_inter G G'
  rw [hG'] at hinc
  have hcount : 2 * G.card ≤ Fintype.card (State d A) +
      (Fintype.card A ^ d) ^ (d - 1) := by omega
  have hpower : (Fintype.card A ^ d) * (Fintype.card A ^ d) ^ (d - 1) =
      Fintype.card (State d A) := by
    rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos d)]
    simp [State, ZMod.card]
  have h := Nat.mul_le_mul_left (Fintype.card A ^ d) hcount
  change 2 * (Fintype.card A ^ d) * G.card ≤ _
  nlinarith


/-- Uniform probability, written as the exact ratio of finite cardinalities. -/
noncomputable def agreementProbability (K : State d A → State d A) : ℚ :=
  ((correctInputs K).card : ℚ) / Fintype.card (State d A)

theorem full_input_agreement_probability [Nonempty A]
    (p : ZMod d → κ) (K : State d A → State d A) (hK : ClassUniform p K) :
    agreementProbability K ≤ (Fintype.card κ : ℚ) / d +
      (∑ J : κ, (receiverClassSize p J * (receiverClassSize p J - 1) : ℕ)) /
        (2 * (d : ℚ) * (Fintype.card A ^ d : ℕ)) := by
  let q := Fintype.card A ^ d
  let S := Fintype.card (State d A)
  let t := ∑ J : κ, receiverClassSize p J * (receiverClassSize p J - 1)
  have hd : (0 : ℚ) < d := by exact_mod_cast NeZero.pos d
  have hq : (0 : ℚ) < q := by exact_mod_cast pow_pos Fintype.card_pos d
  have hS : (0 : ℚ) < S := by exact_mod_cast Fintype.card_pos (α := State d A)
  have hc : 2 * (d : ℚ) * q * (correctInputs K).card ≤
      (2 * Fintype.card κ * q + t) * S := by
    exact_mod_cast full_input_agreement_count p K hK
  have hf : (Fintype.card κ : ℚ) / d + (t : ℚ) / (2 * d * q) =
      (2 * Fintype.card κ * q + t) / (2 * d * q) := by
    field_simp
  change ((correctInputs K).card : ℚ) / S ≤ _
  change ((correctInputs K).card : ℚ) / S ≤ (Fintype.card κ : ℚ) / d + (t : ℚ) / (2 * d * q)
  rw [hf]
  apply (div_le_div_iff₀ hS (by positivity : (0 : ℚ) < 2 * d * q)).mpr
  nlinarith

omit [Fintype κ] in
theorem repeated_class_agreement_probability [Nonempty A]
    (p : ZMod d → κ) (K : State d A → State d A) (hK : ClassUniform p K)
    {c e : ZMod d} (hce : c ≠ e) (hpce : p c = p e) :
    agreementProbability K ≤ (1 + (Fintype.card A ^ d : ℚ)⁻¹) / 2 := by
  let q := Fintype.card A ^ d
  let S := Fintype.card (State d A)
  have hq : (0 : ℚ) < q := by exact_mod_cast pow_pos Fintype.card_pos d
  have hS : (0 : ℚ) < S := by exact_mod_cast Fintype.card_pos (α := State d A)
  have hc : 2 * (q : ℚ) * (correctInputs K).card ≤ (q + 1) * S := by
    exact_mod_cast repeated_class_agreement_count p K hK hce hpce
  have hf : (1 + (q : ℚ)⁻¹) / 2 = (q + 1) / (2 * q) := by
    field_simp
  simp only [agreementProbability, ← Nat.cast_pow]
  change ((correctInputs K).card : ℚ) / S ≤ (1 + (q : ℚ)⁻¹) / 2
  rw [hf]
  apply (div_le_div_iff₀ hS (by positivity : (0 : ℚ) < 2 * q)).mpr
  nlinarith

end SharedDecoders
