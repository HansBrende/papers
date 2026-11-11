import AdaptiveTransfer.CurrentVersion

/-! Pairwise reconstruction for actual native executions. The proof compares
actual record fields; it does not assume an input injection or a common trace. -/

namespace AdaptiveTransfer

open Transpose Finset

def SameControl {M : TM} (c e : Config M) : Prop :=
  c.state = e.state ∧ c.inPos = e.inPos ∧ c.workPos = e.workPos

def nativeInstruction (M : TM) (w : List Bool) (c : Config M) :=
  M.δ c.state (readInput w c.inPos) (fun h => c.work h (c.workPos h))

/-- Equal old head positions and actual instructions give the next control
and all written symbols. The old states themselves need not agree. -/
theorem step_positions_instruction_agreement {M : TM} {w v : List Bool} {c c' e e' : Config M}
    (hE : step M w c = some c') (hF : step M v e = some e')
    (hin : c.inPos = e.inPos) (hwork : c.workPos = e.workPos)
    (hi : nativeInstruction M w c = nativeInstruction M v e) :
    SameControl c' e' ∧
      ∀ h, c'.work h (c.workPos h) = e'.work h (e.workPos h) := by
  cases hd : nativeInstruction M w c with
  | none =>
    simp only [nativeInstruction] at hd
    simp [step, hd] at hE
  | some x =>
    rcases x with ⟨q, move, acts, out⟩
    have hf : nativeInstruction M v e = some (q, move, acts, out) := hi.symm.trans hd
    simp only [nativeInstruction] at hd hf
    simp only [step, hd, Option.some.injEq] at hE
    simp only [step, hf, Option.some.injEq] at hF
    cases hE
    cases hF
    constructor
    · exact ⟨rfl, congrArg (fun z => move.shift z) hin,
        by funext h; simp only [hwork]⟩
    · intro h
      simp

/-- Equal current control and actual instructions give the next control and
all written symbols. Unscanned memory and previous outputs may differ. -/
theorem step_record_agreement {M : TM} {w v : List Bool} {c c' e e' : Config M}
    (hE : step M w c = some c') (hF : step M v e = some e')
    (hc : SameControl c e)
    (hi : nativeInstruction M w c = nativeInstruction M v e) :
    SameControl c' e' ∧
      ∀ h, c'.work h (c.workPos h) = e'.work h (e.workPos h) :=
  step_positions_instruction_agreement hE hF hc.2.1 hc.2.2 hi

namespace ExecutionPrefix

variable {M : TM} {w v : List Bool} {T : ℕ}

theorem work_constant (E : ExecutionPrefix M w T) (h : Fin M.k)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ T) (z : ℤ)
    (hmiss : ∀ u, a ≤ u → u < b → z ≠ (E.config u).workPos h) :
    (E.config b).work h z = (E.config a).work h z := by
  rw [E.work_eq_memoryAfter h hb, E.work_eq_memoryAfter h (hab.trans hb)]
  exact memoryAfter_no_write _ _ _ _ hab (fun u hau hub _ => hmiss u hau hub)

theorem work_virgin (E : ExecutionPrefix M w T) (h : Fin M.k)
    {t : ℕ} (ht : t ≤ T) (z : ℤ)
    (hmiss : ∀ u < t, z ≠ (E.config u).workPos h) :
    (E.config t).work h z = 0 := by
  rw [E.work_constant h (Nat.zero_le _) ht z (fun u _ hu => hmiss u hu), E.initial]
  rfl

/-- The literal tag used by adaptive replay: a first read in this run,
outside its entry window, with a previous global visit. -/
noncomputable def incomingRecord (E : ExecutionPrefix M w T) (H a t : ℕ)
    (h : Fin M.k) : Option (Fin (M.g + 1)) :=
  if H < ((E.config t).workPos h - (E.config a).workPos h).natAbs ∧
      (∀ u, a ≤ u → u < t → (E.config t).workPos h ≠ (E.config u).workPos h) ∧
      (∃ u < t, (E.config t).workPos h = (E.config u).workPos h)
  then some ((E.config t).work h ((E.config t).workPos h)) else none

/-- An equal actual typed import record determines an outside first read.
When both records are absent, both actual cells are virgin and therefore blank. -/
theorem first_outside_read_eq (E : ExecutionPrefix M w T) (F : ExecutionPrefix M v T)
    {H a t : ℕ} (ht : t ≤ T) (h : Fin M.k)
    (hEt : H < ((E.config t).workPos h - (E.config a).workPos h).natAbs)
    (hFt : H < ((F.config t).workPos h - (F.config a).workPos h).natAbs)
    (hEfirst : ∀ u, a ≤ u → u < t → (E.config t).workPos h ≠ (E.config u).workPos h)
    (hFfirst : ∀ u, a ≤ u → u < t → (F.config t).workPos h ≠ (F.config u).workPos h)
    (hrec : E.incomingRecord H a t h = F.incomingRecord H a t h) :
    (E.config t).work h ((E.config t).workPos h) =
      (F.config t).work h ((F.config t).workPos h) := by
  have hecond : (H < ((E.config t).workPos h - (E.config a).workPos h).natAbs ∧
      (∀ u, a ≤ u → u < t → (E.config t).workPos h ≠ (E.config u).workPos h) ∧
      (∃ u < t, (E.config t).workPos h = (E.config u).workPos h)) ↔
      (∃ u < t, (E.config t).workPos h = (E.config u).workPos h) :=
    ⟨fun hh => hh.2.2, fun hh => ⟨hEt, hEfirst, hh⟩⟩
  have hfcond : (H < ((F.config t).workPos h - (F.config a).workPos h).natAbs ∧
      (∀ u, a ≤ u → u < t → (F.config t).workPos h ≠ (F.config u).workPos h) ∧
      (∃ u < t, (F.config t).workPos h = (F.config u).workPos h)) ↔
      (∃ u < t, (F.config t).workPos h = (F.config u).workPos h) :=
    ⟨fun hh => hh.2.2, fun hh => ⟨hFt, hFfirst, hh⟩⟩
  simp only [incomingRecord, hecond, hfcond] at hrec
  by_cases he : ∃ u < t, (E.config t).workPos h = (E.config u).workPos h
  · by_cases hf : ∃ u < t, (F.config t).workPos h = (F.config u).workPos h
    · simpa only [ite_eq_left he, ite_eq_left hf, Option.some.injEq] using hrec
    · simp only [ite_eq_left he, ite_eq_right hf] at hrec
      contradiction
  · have hf : ¬ ∃ u < t, (F.config t).workPos h = (F.config u).workPos h := by
      intro hf
      simp only [ite_eq_right he, ite_eq_left hf] at hrec
      contradiction
    rw [E.work_virgin h ht _ (by simpa only [not_exists, not_and] using he),
      F.work_virgin h ht _ (by simpa only [not_exists, not_and] using hf)]

/-- Native read reconstruction inside a run. Earlier writes, the entry window
and the actual incoming record are the only memory fields used. -/
theorem run_read_eq (E : ExecutionPrefix M w T) (F : ExecutionPrefix M v T)
    {H a t : ℕ} (hat : a ≤ t) (ht : t ≤ T) (h : Fin M.k)
    (hpos : ∀ u, a ≤ u → u ≤ t →
      (E.config u).workPos h = (F.config u).workPos h)
    (hwrite : ∀ u, a ≤ u → u < t → E.written h u = F.written h u)
    (hwindow : ∀ z, (z - (E.config a).workPos h).natAbs ≤ H →
      (E.config a).work h z = (F.config a).work h z)
    (hrec : E.incomingRecord H a t h = F.incomingRecord H a t h) :
    (E.config t).work h ((E.config t).workPos h) =
      (F.config t).work h ((F.config t).workPos h) := by
  classical
  let z := (E.config t).workPos h
  have hz : z = (F.config t).workPos h := hpos t hat le_rfl
  let visits := (Ico a t).filter fun u => z = (E.config u).workPos h
  by_cases hv : visits.Nonempty
  · let p := visits.max' hv
    have hp := mem_filter.mp (max'_mem visits hv)
    have hpa := (mem_Ico.mp hp.1).1
    have hpt := (mem_Ico.mp hp.1).2
    have hlast : ∀ u, p < u → u < t → z ≠ (E.config u).workPos h := by
      intro u hpu hut hzu
      have hu : u ∈ visits := mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, hut⟩, hzu⟩
      have := le_max' visits u hu
      omega
    have hlastF : ∀ u, p < u → u < t → z ≠ (F.config u).workPos h := by
      intro u hpu hut
      rw [← hpos u (by omega) (by omega)]
      exact hlast u hpu hut
    have hE : (E.config t).work h z = E.written h p := by
      rw [E.work_eq_memoryAfter h ht]
      exact memoryAfter_last_write _ _ _ _ hpt hp.2 rfl hlast
    have hF : (F.config t).work h z = F.written h p := by
      rw [F.work_eq_memoryAfter h ht]
      exact memoryAfter_last_write _ _ _ _ hpt
        (hp.2.trans (hpos p hpa hpt.le)) rfl hlastF
    change (E.config t).work h z = _
    rw [← hz, hE, hF, hwrite p hpa hpt]
  · have hnone : ∀ u, a ≤ u → u < t → z ≠ (E.config u).workPos h := by
      intro u hau hut hzu
      exact hv ⟨u, mem_filter.mpr ⟨mem_Ico.mpr ⟨hau, hut⟩, hzu⟩⟩
    have hnoneF : ∀ u, a ≤ u → u < t → z ≠ (F.config u).workPos h := by
      intro u hau hut
      rw [← hpos u hau hut.le]
      exact hnone u hau hut
    by_cases hnear : (z - (E.config a).workPos h).natAbs ≤ H
    · change (E.config t).work h z = _
      rw [← hz, E.work_constant h hat ht z hnone,
        F.work_constant h hat ht z hnoneF]
      exact hwindow z hnear
    · apply E.first_outside_read_eq F ht h (by omega) _ hnone _ hrec
      · rw [← hz, ← hpos a le_rfl hat]
        omega
      · simpa only [← hz] using hnoneF

/-- Simultaneous adaptive replay of two actual runs. The selected time set is
exactly the times at which the free head lies in the slab, in both executions.
Only run-entry control/windows, the initial slab, actual incoming records and
raw symbols on the paid coordinate set are compared. No detailed common trace
or unproved reconstruction function is assumed. -/
theorem adaptive_replay_agreement
    (E : ExecutionPrefix M w T) (F : ExecutionPrefix M v T)
    {a b H : ℕ} (hbT : b ≤ T)
    (f : Fin M.k) (S : Set ℤ) (C : Finset ℕ) (entry : ℕ → ℕ)
    (hC : ∀ t ∈ C, a ≤ t ∧ t < b)
    (hEC : ∀ t, a ≤ t → t < b → (t ∈ C ↔ (E.config t).workPos f ∈ S))
    (hFC : ∀ t, a ≤ t → t < b → (t ∈ C ↔ (F.config t).workPos f ∈ S))
    (hentry : ∀ t ∈ C, a ≤ entry t ∧ entry t ≤ t)
    (hfill : ∀ t ∈ C, ∀ u, entry t ≤ u → u ≤ t → u ∈ C)
    (hcontrol : ∀ t ∈ C, SameControl (E.config (entry t)) (F.config (entry t)))
    (hwindow : ∀ t ∈ C, ∀ h, h ≠ f → ∀ z,
      (z - (E.config (entry t)).workPos h).natAbs ≤ H →
      (E.config (entry t)).work h z = (F.config (entry t)).work h z)
    (himports : ∀ t ∈ C, ∀ h, h ≠ f →
      E.incomingRecord H (entry t) t h = F.incomingRecord H (entry t) t h)
    (hslab : ∀ z ∈ S, (E.config a).work f z = (F.config a).work f z)
    (I : Set ℤ) (hraw : ∀ t ∈ C, (E.config t).inPos ∈ I)
    (hexterior : ∀ z ∈ I, readInput w z = readInput v z) :
    (∀ t, a ≤ t → t ≤ b → ∀ z ∈ S,
      (E.config t).work f z = (F.config t).work f z) ∧
    (∀ t ∈ C, SameControl (E.config t) (F.config t) ∧
      nativeInstruction M w (E.config t) = nativeInstruction M v (F.config t)) := by
  classical
  have main : ∀ t, a ≤ t → t ≤ b →
      (∀ z ∈ S, (E.config t).work f z = (F.config t).work f z) ∧
      (t ∈ C → SameControl (E.config t) (F.config t) ∧
        nativeInstruction M w (E.config t) = nativeInstruction M v (F.config t)) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro hat htb
      have hmem : ∀ z ∈ S, (E.config t).work f z = (F.config t).work f z := by
        by_cases hta : t = a
        · simpa only [hta] using hslab
        · have htp : t - 1 + 1 = t := by omega
          have hpa : a ≤ t - 1 := by omega
          have hpb : t - 1 < b := by omega
          have hp := ih (t - 1) (by omega) hpa hpb.le
          have hEs := E.successful (t - 1) (hpb.trans_le hbT)
          have hFs := F.successful (t - 1) (hpb.trans_le hbT)
          rw [htp] at hEs hFs
          intro z hz
          by_cases hpC : t - 1 ∈ C
          · have hc := hp.2 hpC
            have hw := (step_record_agreement hEs hFs hc.1 hc.2).2 f
            have hpos := congrFun hc.1.2.2 f
            rw [step_work_update hEs f z, step_work_update hFs f z]
            by_cases hzp : z = (E.config (t - 1)).workPos f
            · rw [ite_eq_left hzp, ite_eq_left (hzp.trans hpos)]
              exact hw
            · rw [ite_eq_right hzp, ite_eq_right (by simpa only [← hpos] using hzp)]
              exact hp.1 z hz
          · have hEout : z ≠ (E.config (t - 1)).workPos f := by
              intro heq
              exact hpC ((hEC _ hpa hpb).mpr (heq ▸ hz))
            have hFout : z ≠ (F.config (t - 1)).workPos f := by
              intro heq
              exact hpC ((hFC _ hpa hpb).mpr (heq ▸ hz))
            rw [step_preserves_unscanned hEs f z hEout,
              step_preserves_unscanned hFs f z hFout]
            exact hp.1 z hz
      refine ⟨hmem, ?_⟩
      intro htC
      have hentryt := hentry t htC
      have htend := (hC t htC).2
      have hc : SameControl (E.config t) (F.config t) := by
        by_cases het : entry t = t
        · simpa only [het] using hcontrol t htC
        · have htp : t - 1 + 1 = t := by omega
          have hep : entry t ≤ t - 1 := by omega
          have hpC := hfill t htC (t - 1) hep (by omega)
          have hp := (ih (t - 1) (by omega) (hentryt.1.trans hep)
            (by omega)).2 hpC
          have hstep := step_record_agreement
            (E.successful (t - 1) (by omega)) (F.successful (t - 1) (by omega)) hp.1 hp.2
          simpa only [htp] using hstep.1
      refine ⟨hc, ?_⟩
      apply instruction_eq_of_old_tuple hc.1
      · rw [← hc.2.1]
        exact hexterior _ (hraw t htC)
      · intro h
        by_cases hh : h = f
        · subst h
          rw [← congrFun hc.2.2 f]
          exact hmem _ ((hEC t hat htend).mp htC)
        · apply E.run_read_eq F hentryt.2 (htb.trans hbT) h
          · intro u heu hut
            by_cases hut' : u = t
            · subst u
              exact congrFun hc.2.2 h
            · have huC := hfill t htC u heu hut
              exact congrFun ((ih u (by omega) (hentryt.1.trans heu)
                (hut.trans htb)).2 huC).1.2.2 h
          · intro u heu hut
            have huC := hfill t htC u heu hut.le
            have hu := (ih u hut (hentryt.1.trans heu) (hut.le.trans htb)).2 huC
            exact (step_record_agreement (E.successful u (by omega))
              (F.successful u (by omega)) hu.1 hu.2).2 h
          · exact hwindow t htC h hh
          · exact himports t htC h hh
  exact ⟨fun t hat htb => (main t hat htb).1,
    fun t ht => (main t (hC t ht).1 (hC t ht).2.le).2 ht⟩

def emitted (E : ExecutionPrefix M w T) (t : ℕ) : Option Bool :=
  (nativeInstruction M w (E.config t)).bind fun v => v.2.2.2

theorem output_next (E : ExecutionPrefix M w T) {t : ℕ} (ht : t < T) :
    (E.config (t + 1)).outRev = match E.emitted t with
      | none => (E.config t).outRev
      | some bit => bit :: (E.config t).outRev := by
  have hs := E.successful t ht
  cases hd : nativeInstruction M w (E.config t) with
  | none =>
    simp only [nativeInstruction] at hd
    simp [step, hd] at hs
  | some x =>
    rcases x with ⟨q, move, acts, out⟩
    have hd' := hd
    simp only [nativeInstruction] at hd'
    simp only [step, hd', Option.some.injEq] at hs
    rw [← hs]
    simp only [emitted, hd, Option.bind_some]
    rfl

theorem output_count_next (E : ExecutionPrefix M w T) {t : ℕ} (ht : t < T) :
    (E.config (t + 1)).outRev.length =
      (E.config t).outRev.length + if (E.emitted t).isSome then 1 else 0 := by
  rw [E.output_next ht]
  cases E.emitted t <;> simp

/-- Every ordinal between the entry and exit output counters is actually
appended inside that run interval. This follows from the native 0/1 increment. -/
theorem exists_append_between (E : ExecutionPrefix M w T) {a e j : ℕ}
    (hae : a ≤ e) (heT : e ≤ T)
    (ha : (E.config a).outRev.length ≤ j) (he : j < (E.config e).outRev.length) :
    ∃ t, a ≤ t ∧ t < e ∧ (E.config t).outRev.length = j ∧ (E.emitted t).isSome := by
  induction e, hae using Nat.le_induction with
  | base => omega
  | succ e hae ih =>
    by_cases hj : j < (E.config e).outRev.length
    · obtain ⟨t, hat, hte, hc, ho⟩ := ih (by omega) hj
      exact ⟨t, hat, by omega, hc, ho⟩
    · have hc := E.output_count_next (show e < T by omega)
      have ho : (E.emitted e).isSome := by
        by_contra hn
        simp only [Bool.not_eq_true] at hn
        simp only [hn, Bool.false_eq_true, ↓reduceIte, add_zero] at hc
        omega
      simp only [ho, ite_eq_left] at hc
      exact ⟨e, hae, by omega, by omega, ho⟩

/-- The paid entry ordinals and reconstructed actual instructions recover
every retained append ordinal, even though omitted outputs may differ. -/
theorem replay_output_count_agreement
    (E : ExecutionPrefix M w T) (F : ExecutionPrefix M v T)
    (C : Finset ℕ) (entry : ℕ → ℕ)
    (hCT : ∀ t ∈ C, t < T)
    (hentry : ∀ t ∈ C, entry t ≤ t)
    (hfill : ∀ t ∈ C, ∀ u, entry t ≤ u → u ≤ t → u ∈ C)
    (hcount : ∀ t ∈ C,
      (E.config (entry t)).outRev.length = (F.config (entry t)).outRev.length)
    (hinstr : ∀ t ∈ C,
      nativeInstruction M w (E.config t) = nativeInstruction M v (F.config t)) :
    ∀ t ∈ C, (E.config t).outRev.length = (F.config t).outRev.length := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    by_cases he : entry t = t
    · simpa only [he] using hcount t ht
    · have htp : t - 1 + 1 = t := by have := hentry t ht; omega
      have hep : entry t ≤ t - 1 := by have := hentry t ht; omega
      have hpC := hfill t ht (t - 1) hep (by omega)
      have hpcount := ih (t - 1) (by omega) hpC
      have hpout : E.emitted (t - 1) = F.emitted (t - 1) :=
        congrArg (fun x => x.bind fun v => v.2.2.2) (hinstr (t - 1) hpC)
      have heq := E.output_count_next (hCT _ hpC)
      have hfq := F.output_count_next (hCT _ hpC)
      rw [htp] at heq hfq
      rw [heq, hfq, hpcount, hpout]

/-- Equality of reconstructed instructions and ordinals recovers actual
correct output coordinates. Only coordinates outside the demanded set are
assumed equal; output roots are chosen separately in the first actual run. -/
theorem replay_recovers_input {P : ℕ} {X Y : Fin P → Bool}
    (E : ExecutionPrefix M (List.ofFn X) T)
    (F : ExecutionPrefix M (List.ofFn Y) T)
    (π : Fin P → Fin P) (C : Finset ℕ) (U : Finset (Fin P))
    (hCT : ∀ t ∈ C, t < T)
    (hcover : ∀ p ∈ U, ∃ t ∈ C, ∃ j : Fin P,
      π j = p ∧ (E.config t).outRev.length = j.val ∧ (E.emitted t).isSome)
    (hcount : ∀ t ∈ C, (E.config t).outRev.length = (F.config t).outRev.length)
    (hinstr : ∀ t ∈ C,
      nativeInstruction M (List.ofFn X) (E.config t) =
        nativeInstruction M (List.ofFn Y) (F.config t))
    (hcorrectE : ∀ t < T, ∀ j : Fin P, ∀ bit,
      (E.config t).outRev.length = j.val → E.emitted t = some bit → bit = X (π j))
    (hcorrectF : ∀ t < T, ∀ j : Fin P, ∀ bit,
      (F.config t).outRev.length = j.val → F.emitted t = some bit → bit = Y (π j))
    (hexterior : ∀ p ∉ U, X p = Y p) : X = Y := by
  funext p
  by_cases hp : p ∈ U
  · obtain ⟨t, ht, j, hj, hc, he⟩ := hcover p hp
    obtain ⟨bit, hb⟩ := Option.isSome_iff_exists.mp he
    have hf : F.emitted t = some bit := by
      have hh : E.emitted t = F.emitted t :=
        congrArg (fun x => x.bind fun v => v.2.2.2) (hinstr t ht)
      exact hh.symm.trans hb
    have heqE := hcorrectE t (hCT t ht) j bit hc hb
    have heqF := hcorrectF t (hCT t ht) j bit ((hcount t ht).symm.trans hc) hf
    simpa only [hj] using heqE.symm.trans heqF
  · exact hexterior p hp

end ExecutionPrefix
end AdaptiveTransfer
