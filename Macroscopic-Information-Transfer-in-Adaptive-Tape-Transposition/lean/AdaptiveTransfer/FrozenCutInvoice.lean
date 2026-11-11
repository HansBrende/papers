import NativeRelations.OneFreeHeadSmallExcursion
import TransposeFollowup.ConditionalObservation
import TransposeFollowup.UniformEntropy
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! Exact invoices for actual frozen native traces. The cut is the literal
endpoint-inclusive native dependency-path separator. Neither record injectivity
nor cone determination is assumed. Output bits are needed at cut roots only. -/

namespace AdaptiveTransfer

open Finset Classical Transpose Transpose.Tape Transpose.Tape.Impl
  SourceCovers BoundedNesting MergeDepth NativeRelations
open scoped BigOperators

abbrev StateWriteValue (M : TM) := Fin (M.q + 1) × (Fin M.k → Fin (M.g + 1))

def stateWriteValue (M : TM) (X : Fin L → Bool) (t : ℕ) : StateWriteValue M :=
  ((stepValue M (List.ofFn X) t).1, (stepValue M (List.ofFn X) t).2.1)

noncomputable def demandedReadSteps {k : ℕ} (τ : Trace k) (L T : ℕ)
    (Q : Finset (Fin L)) : Finset ℕ :=
  (range T).filter fun t => ∃ p ∈ Q, readPos τ L t = some p

theorem depStep_of_actualParent {k T t u : ℕ} {xs : Fin k → ℕ → ℤ}
    (ht : t < T) (hu : u ∈ actualParents xs T t) : DepStep xs T t u := by
  rcases mem_actualParents.mp hu with hs | ⟨h, h₁, h₂, h₃, h₄⟩
  · exact Or.inl ⟨hs, ht⟩
  · exact Or.inr (mem_image.mpr
      ⟨(h, u, t), mem_allHops.mpr ⟨h₁, h₂, h₃, h₄⟩, rfl⟩)

theorem singleton_cut_of_parent {k T t u : ℕ} {xs : Fin k → ℕ → ℤ}
    {D Γ : Finset ℕ} (htΓ : t ∉ Γ) (hdep : DepStep xs T t u)
    (hcut : IsMengerVertexCut xs T {t} D Γ) :
    IsMengerVertexCut xs T {u} D Γ := by
  intro ρ v hv hpath hend
  have hvu : v = u := mem_singleton.mp hv
  subst v
  have hend' : (t :: u :: ρ).getLastD t ∈ D := by
    simpa only [LinNet.getLastD_cons_cons] using hend
  obtain ⟨z, hz, hzΓ⟩ := hcut (u :: ρ) t (mem_singleton_self t) ⟨hdep, hpath⟩ hend'
  rcases List.mem_cons.mp hz with rfl | hz
  · exact (htΓ hzΓ).elim
  · exact ⟨z, hz, hzΓ⟩

theorem stepValue_eq_of_uncut_native_cut {M : TM} {L T : ℕ} {τ : Trace M.k}
    {X Y : Fin L → Bool} {Q : Finset (Fin L)} {Γ : Finset ℕ}
    (hX : ∀ u < T, trace M (List.ofFn X) u = τ u)
    (hY : ∀ u < T, trace M (List.ofFn Y) u = τ u)
    (hext : ∀ p ∉ Q, X p = Y p)
    (hfields : ∀ u ∈ Γ, stateWriteValue M X u = stateWriteValue M Y u)
    (t : ℕ) (ht : t < T) (htΓ : t ∉ Γ)
    (hcut : IsMengerVertexCut τ.work T {t} (demandedReadSteps τ L T Q) Γ) :
    stepValue M (List.ofFn X) t = stepValue M (List.ofFn Y) t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    have hparent : ∀ u ∈ actualParents τ.work T t,
        stateWriteValue M X u = stateWriteValue M Y u := by
      intro u hu
      by_cases huΓ : u ∈ Γ
      · exact hfields u huΓ
      · have hd := depStep_of_actualParent ht hu
        have heq := ih u (depStep_lt hd).1 ((depStep_lt hd).1.trans ht) huΓ
          (singleton_cut_of_parent htΓ hd hcut)
        exact congrArg (fun v : Value M => (v.1, v.2.1)) heq
    apply stepValue_eq_of_fields hX hY ht
    · intro p hp hpL
      apply hext
      intro hpQ
      have hread : t ∈ demandedReadSteps τ L T Q :=
        mem_filter.mpr ⟨mem_range.mpr ht, ⟨p, hpL⟩, hpQ, readPos_eq_some hp hpL⟩
      obtain ⟨z, hz, hzΓ⟩ := hcut [] t (mem_singleton_self t) trivial (by simpa using hread)
      have hzt : z = t := by simpa using hz
      exact htΓ (hzt ▸ hzΓ)
    · intro ht₁
      obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      exact congrArg Prod.fst (hparent u (mem_actualParents.mpr (Or.inl rfl)))
    · intro h u hlast
      have hu := mem_actualParents_of_lastVisit h ht (fun _ _ => rfl) hlast
      exact congrFun (congrArg Prod.snd (hparent u hu)) h

/-- Actual native recovery on any demanded coordinates. The field records have
no output component; the additional one-bit values occur only at cut roots. -/
theorem native_cut_recovers {M : TM} {L T : ℕ} {τ : Trace M.k}
    {X Y : Fin L → Bool} {Q : Finset (Fin L)} {Γ : Finset ℕ}
    (root : Fin L → ℕ) (hroot : ∀ p ∈ Q, root p < T)
    (hX : ∀ u < T, trace M (List.ofFn X) u = τ u)
    (hY : ∀ u < T, trace M (List.ofFn Y) u = τ u)
    (hcorrectX : ∀ p ∈ Q, (outBit M (List.ofFn X) (root p)).getD false = X p)
    (hcorrectY : ∀ p ∈ Q, (outBit M (List.ofFn Y) (root p)).getD false = Y p)
    (hcut : IsMengerVertexCut τ.work T (Q.image root) (demandedReadSteps τ L T Q) Γ)
    (hext : ∀ p ∉ Q, X p = Y p)
    (hfields : ∀ u ∈ Γ, stateWriteValue M X u = stateWriteValue M Y u)
    (houtput : ∀ u ∈ Γ ∩ Q.image root,
      (outBit M (List.ofFn X) u).getD false = (outBit M (List.ofFn Y) u).getD false) :
    X = Y := by
  funext p
  by_cases hp : p ∈ Q
  · rw [← hcorrectX p hp, ← hcorrectY p hp]
    by_cases hr : root p ∈ Γ
    · exact houtput (root p) (mem_inter.mpr ⟨hr, mem_image_of_mem root hp⟩)
    · have hc : IsMengerVertexCut τ.work T {root p} (demandedReadSteps τ L T Q) Γ := by
        intro ρ t ht hpath hend
        have htp : t = root p := mem_singleton.mp ht
        subst t
        exact hcut ρ (root p) (mem_image_of_mem root hp) hpath hend
      exact congrArg (fun v : Value M => v.2.2.getD false)
        (stepValue_eq_of_uncut_native_cut hX hY hext hfields (root p) (hroot p hp) hr hc)
  · exact hext p hp

def stateWriteWidth (M : TM) : ℕ :=
  Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1)

theorem card_stateWriteValue_le (M : TM) :
    Fintype.card (StateWriteValue M) ≤ 2 ^ stateWriteWidth M := by
  simp only [StateWriteValue, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [stateWriteWidth, pow_add, mul_comm M.k, pow_mul]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) _)
    (Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _)

noncomputable def fullCutRecord (M : TM) (Γ : Finset ℕ) (X : Fin L → Bool) :
    Γ → Value M := fun u => stepValue M (List.ofFn X) u.val

noncomputable def fieldCutRecord (M : TM) (Γ R : Finset ℕ) (X : Fin L → Bool) :
    (Γ → StateWriteValue M) × (↑(Γ ∩ R) → Bool) :=
  (fun u => stateWriteValue M X u.val,
   fun u => (outBit M (List.ofFn X) u.val).getD false)

section Invoice

variable {M : TM} {L T : ℕ} {τ : Trace M.k}
  (S : Finset (Fin L → Bool)) (Q : Finset (Fin L)) (Γ : Finset ℕ)
  (root : Fin L → ℕ) (hroot : ∀ p ∈ Q, root p < T)
  (htrace : ∀ X ∈ S, ∀ u < T, trace M (List.ofFn X) u = τ u)
  (hcorrect : ∀ X ∈ S, ∀ p ∈ Q, (outBit M (List.ofFn X) (root p)).getD false = X p)
  (hcut : IsMengerVertexCut τ.work T (Q.image root) (demandedReadSteps τ L T Q) Γ)

include hroot htrace hcorrect hcut

theorem native_field_encoding_injective : Function.Injective
    (fun X : S => ((fun p : ↑Qᶜ => X.val p.val), fieldCutRecord M Γ (Q.image root) X.val)) := by
  intro X Y hxy
  apply Subtype.ext
  apply native_cut_recovers root hroot (htrace X X.property) (htrace Y Y.property)
    (hcorrect X X.property) (hcorrect Y Y.property) hcut
  · intro p hp
    exact congrFun (congrArg Prod.fst hxy) ⟨p, mem_compl.mpr hp⟩
  · intro u hu
    exact congrFun (congrArg (fun z => z.2.1) hxy) ⟨u, hu⟩
  · intro u hu
    exact congrFun (congrArg (fun z => z.2.2) hxy) ⟨u, hu⟩

theorem native_full_encoding_injective : Function.Injective
    (fun X : S => ((fun p : ↑Qᶜ => X.val p.val), fullCutRecord M Γ X.val)) := by
  intro X Y hxy
  apply Subtype.ext
  apply native_cut_recovers root hroot (htrace X X.property) (htrace Y Y.property)
    (hcorrect X X.property) (hcorrect Y Y.property) hcut
  · intro p hp
    exact congrFun (congrArg Prod.fst hxy) ⟨p, mem_compl.mpr hp⟩
  · intro u hu
    exact congrArg (fun v : Value M => (v.1, v.2.1))
      (congrFun (congrArg Prod.snd hxy) ⟨u, hu⟩)
  · intro u hu
    exact congrArg (fun v : Value M => v.2.2.getD false)
      (congrFun (congrArg Prod.snd hxy) ⟨u, (mem_inter.mp hu).1⟩)

/-- Exact joint attained record range, not the product of marginal ranges. -/
theorem native_cut_card_le_joint :
    S.card ≤ 2 ^ (L - Q.card) * (S.image (fullCutRecord M Γ)).card := by
  let enc (X : S) : (↑Qᶜ → Bool) × (S.image (fullCutRecord M Γ)) :=
    ((fun p => X.val p.val), ⟨fullCutRecord M Γ X.val, mem_image_of_mem _ X.property⟩)
  have hi : Function.Injective enc := by
    intro X Y hxy
    apply native_full_encoding_injective S Q Γ root hroot htrace hcorrect hcut
    exact Prod.ext
      (congrArg (fun z : (↑Qᶜ → Bool) × (S.image (fullCutRecord M Γ)) => z.1) hxy)
      (congrArg (fun z : (↑Qᶜ → Bool) × (S.image (fullCutRecord M Γ)) => z.2.val) hxy)
  have hc := Fintype.card_le_of_injective enc hi
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, card_compl, Fintype.card_fin] using hc

theorem native_cut_card_le_fields :
    S.card ≤ 2 ^ (L - Q.card + stateWriteWidth M * Γ.card + (Γ ∩ Q.image root).card) := by
  have hc := Fintype.card_le_of_injective _
    (native_field_encoding_injective S Q Γ root hroot htrace hcorrect hcut)
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, card_compl, Fintype.card_fin] at hc
  calc S.card ≤ 2 ^ (L - Q.card) *
        (Fintype.card (StateWriteValue M) ^ Γ.card * 2 ^ (Γ ∩ Q.image root).card) := by
          simpa only [StateWriteValue, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] using hc
    _ ≤ 2 ^ (L - Q.card) *
        ((2 ^ stateWriteWidth M) ^ Γ.card * 2 ^ (Γ ∩ Q.image root).card) := by
          gcongr
          exact card_stateWriteValue_le M
    _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega

end Invoice

theorem fullCutRecord_range_card_le {M : TM} {L : ℕ}
    (S : Finset (Fin L → Bool)) (Γ : Finset ℕ) :
    (S.image (fullCutRecord M Γ)).card ≤ 2 ^ (valueWidth M * Γ.card) := by
  calc _ ≤ Fintype.card (Γ → Value M) := card_le_univ _
    _ = Fintype.card (Value M) ^ Γ.card := by simp only [Fintype.card_fun, Fintype.card_coe]
    _ ≤ (2 ^ valueWidth M) ^ Γ.card := Nat.pow_le_pow_left (card_value_le M) _
    _ = _ := (pow_mul _ _ _).symm

theorem logb_le_of_card_le_two_pow {c n : ℕ} (hc : 0 < c) (hcn : c ≤ 2 ^ n) :
    Real.logb 2 (c : ℝ) ≤ n := by
  have hp : (0 : ℝ) < c := by exact_mod_cast hc
  have hh : (c : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hcn
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp hh
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using hl

theorem logb_joint_invoice_of_card {c L d r : ℕ} (hc : 0 < c) (hd : d ≤ L)
    (hcount : c ≤ 2 ^ (L - d) * r) :
    (d : ℝ) - ((L : ℝ) - Real.logb 2 (c : ℝ)) ≤ Real.logb 2 (r : ℝ) := by
  have hr : 0 < r := by
    by_contra hn
    have hz : r = 0 := by omega
    simp only [hz, mul_zero] at hcount
    omega
  have hcp : (0 : ℝ) < c := by exact_mod_cast hc
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hh : (c : ℝ) ≤ (2 : ℝ) ^ (L - d) * r := by exact_mod_cast hcount
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hcp hh
  rw [Real.logb_mul (by positivity) (ne_of_gt hrp), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one, Nat.cast_sub hd] at hl
  linarith

/-- The full frozen-trace invoice, at arbitrary input length and for arbitrary
correct designated output roots. This includes the exact attained joint range. -/
theorem native_frozen_full_invoice {M : TM} {L T : ℕ} {τ : Trace M.k}
    (S : Finset (Fin L → Bool)) (hS : S.Nonempty)
    (Q : Finset (Fin L)) (Γ : Finset ℕ) (root : Fin L → ℕ)
    (hroot : ∀ p ∈ Q, root p < T)
    (htrace : ∀ X ∈ S, ∀ u < T, trace M (List.ofFn X) u = τ u)
    (hcorrect : ∀ X ∈ S, ∀ p ∈ Q, (outBit M (List.ofFn X) (root p)).getD false = X p)
    (hcut : IsMengerVertexCut τ.work T (Q.image root) (demandedReadSteps τ L T Q) Γ) :
    (Q.card : ℝ) - ((L : ℝ) - Real.logb 2 (S.card : ℝ)) ≤
        Real.logb 2 ((S.image (fullCutRecord M Γ)).card : ℝ) ∧
      Real.logb 2 ((S.image (fullCutRecord M Γ)).card : ℝ) ≤
        (valueWidth M : ℝ) * Γ.card := by
  constructor
  · exact logb_joint_invoice_of_card hS.card_pos
      (Q.card_le_univ.trans_eq (Fintype.card_fin L))
      (native_cut_card_le_joint S Q Γ root hroot htrace hcorrect hcut)
  · have hp : 0 < (S.image (fullCutRecord M Γ)).card :=
      (hS.image (fullCutRecord M Γ)).card_pos
    simpa only [Nat.cast_mul] using
      logb_le_of_card_le_two_pow hp (fullCutRecord_range_card_le S Γ)

/-- Field-only records pay one bit for each cut desired root, with no blanket
two-bit output-field surcharge at the other cut vertices. -/
theorem native_frozen_field_invoice {M : TM} {L T : ℕ} {τ : Trace M.k}
    (S : Finset (Fin L → Bool)) (hS : S.Nonempty)
    (Q : Finset (Fin L)) (Γ : Finset ℕ) (root : Fin L → ℕ)
    (hroot : ∀ p ∈ Q, root p < T)
    (htrace : ∀ X ∈ S, ∀ u < T, trace M (List.ofFn X) u = τ u)
    (hcorrect : ∀ X ∈ S, ∀ p ∈ Q, (outBit M (List.ofFn X) (root p)).getD false = X p)
    (hcut : IsMengerVertexCut τ.work T (Q.image root) (demandedReadSteps τ L T Q) Γ) :
    (Q.card : ℝ) - ((L : ℝ) - Real.logb 2 (S.card : ℝ)) ≤
      (stateWriteWidth M : ℝ) * Γ.card + (Γ ∩ Q.image root).card := by
  have hc := native_cut_card_le_fields S Q Γ root hroot htrace hcorrect hcut
  have hl := logb_le_of_card_le_two_pow hS.card_pos hc
  have hQ : Q.card ≤ L := Q.card_le_univ.trans_eq (Fintype.card_fin L)
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hQ, Nat.cast_mul] at hl
  linarith

/-- The same actual native injection gives a conditional information invoice
under any one normalized law on the frozen correct set, not only its uniform law.
Entropy is in nats here; division by log 2 yields the bit statement. -/
theorem native_frozen_cut_entropy_lower {M : TM} {L T : ℕ} {τ : Trace M.k}
    (S : Finset (Fin L → Bool)) (hS : S.Nonempty)
    (Q : Finset (Fin L)) (Γ : Finset ℕ) (root : Fin L → ℕ)
    (hroot : ∀ p ∈ Q, root p < T)
    (htrace : ∀ X ∈ S, ∀ u < T, trace M (List.ofFn X) u = τ u)
    (hcorrect : ∀ X ∈ S, ∀ p ∈ Q, (outBit M (List.ofFn X) (root p)).getD false = X p)
    (hcut : IsMengerVertexCut τ.work T (Q.image root) (demandedReadSteps τ L T Q) Γ)
    (p : S → ℝ) (hp : ∀ X, 0 ≤ p X) (hp1 : ∑ X, p X = 1) :
    TransposeFollowup.entropy p - ((L : ℝ) - Q.card) * Real.log 2 ≤
      TransposeFollowup.conditionalObservationEntropy p
        (fun X : S => fullCutRecord M Γ X.val)
        (fun X : S => fun x : ↑Qᶜ => X.val x.val) := by
  let : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  let exterior (X : S) : ↑Qᶜ → Bool := fun x => X.val x.val
  have hi := native_full_encoding_injective S Q Γ root hroot htrace hcorrect hcut
  have heq := TransposeFollowup.observationEntropy_injective p hp _ hi
  have hbound := TransposeFollowup.entropy_le_log_card
    (TransposeFollowup.pushforward p exterior)
    (TransposeFollowup.pushforward_nonneg p hp exterior)
    (by rw [TransposeFollowup.sum_pushforward, hp1])
  have hQ : Q.card ≤ L := Q.card_le_univ.trans_eq (Fintype.card_fin L)
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
    card_compl, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow, Nat.cast_sub hQ] at hbound
  change TransposeFollowup.observationEntropy p exterior ≤ _ at hbound
  rw [TransposeFollowup.conditionalObservationEntropy, heq]
  exact sub_le_sub_left hbound _

end AdaptiveTransfer
