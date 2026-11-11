import AdaptiveTransfer.GetterReplayCore

/-! Sparse getter corrections recover the ordinary native import records by
strong induction. Each induction step reuses the existing adaptive replay
engine on earlier retained times. The actual observer and strict prior output
are derived before evaluating any unknown sibling symbol.
-/

namespace AdaptiveTransfer.Getter

open Transpose Finset Transpose.Tape Transpose.Tape.Impl

variable {M : TM} {U Λ : Type*} {v R P T : ℕ} {X Y : Fin P → Bool}

/-- The actual sparse correction payload suffices for native adaptive replay.
All observer/port/prefix agreement is proved, not supplied as a getter promise. -/
theorem import_reconstruction
    (E : ExecutionPrefix M (List.ofFn X) T) (F : ExecutionPrefix M (List.ofFn Y) T)
    (A : Observer M U v R) (G : Getters M U Λ v R) (label : Λ)
    (π : Fin P → Fin P) (hπ : Function.Injective π) (NE NF : ℕ)
    (hTE : T ≤ NE) (hTF : T ≤ NF)
    (hfinalE : (Transpose.Tape.run M (List.ofFn X) NE).outRev.reverse = List.ofFn (fun j => X (π j)))
    (hfinalF : (Transpose.Tape.run M (List.ofFn Y) NF).outRev.reverse = List.ofFn (fun j => Y (π j)))
    {a b H : ℕ} (hbT : b ≤ T)
    (f : Fin M.k) (S : Set ℤ) (C : Finset ℕ) (entry : ℕ → ℕ) (omitted : Finset (Fin P))
    (hC : ∀ t ∈ C, a ≤ t ∧ t < b)
    (hEC : ∀ t, a ≤ t → t < b → (t ∈ C ↔ (E.config t).workPos f ∈ S))
    (hFC : ∀ t, a ≤ t → t < b → (t ∈ C ↔ (F.config t).workPos f ∈ S))
    (hentry : ∀ t ∈ C, a ≤ entry t ∧ entry t ≤ t)
    (hfill : ∀ t ∈ C, ∀ u, entry t ≤ u → u ≤ t → u ∈ C)
    (hcontrol : ∀ t ∈ C, SameControl (E.config (entry t)) (F.config (entry t)))
    (hobserver : ∀ t ∈ C, A.run (List.ofFn X) (entry t) = A.run (List.ofFn Y) (entry t))
    (hwindow : ∀ t ∈ C, ∀ h, h ≠ f → ∀ z,
      (z - (E.config (entry t)).workPos h).natAbs ≤ H →
      (E.config (entry t)).work h z = (F.config (entry t)).work h z)
    (hpast : ∀ t ∈ C, ∀ h, h ≠ f → visitedBefore E (entry t) h = visitedBefore F (entry t) h)
    (herrors : ∀ t ∈ C, ∀ h, h ≠ f →
      errorRecord E A G f label H (entry t) t h = errorRecord F A G f label H (entry t) t h)
    (hslab : ∀ z ∈ S, (E.config a).work f z = (F.config a).work f z)
    (I : Set ℤ) (hraw : ∀ t ∈ C, (E.config t).inPos ∈ I)
    (hrawWindows : ∀ t ∈ C, ∀ j i, windowAddress (A.allPorts (List.ofFn X) t j) R i ∈ I)
    (hdisjoint : ∀ q : Fin P, (q.val : ℤ) ∈ I → q ∉ omitted)
    (hexterior : ∀ q ∉ omitted, X q = Y q)
    (hcount : ∀ t ∈ C, (E.config (entry t)).outRev.length = (F.config (entry t)).outRev.length)
    (hcover : ∀ q ∈ omitted, ∃ t ∈ C, ∃ j : Fin P,
      π j = q ∧ (E.config t).outRev.length = j.val ∧ (E.emitted t).isSome) :
    ∀ t ∈ C,
      (∀ h, h ≠ f → E.incomingRecord H (entry t) t h = F.incomingRecord H (entry t) t h) ∧
      A.run (List.ofFn X) t = A.run (List.ofFn Y) t ∧
      (∀ h, (E.config t).work h ((E.config t).workPos h) =
        (F.config t).work h ((F.config t).workPos h)) := by
  classical
  have hrawEq : ∀ z ∈ I, readInput (List.ofFn X) z = readInput (List.ofFn Y) z :=
    fun _ hz => readInput_eq_of_exterior omitted I hexterior hdisjoint hz
  have ports_agree (t : ℕ) (ht : t ∈ C)
      (hc : SameControl (E.config t) (F.config t))
      (ha : A.run (List.ofFn X) t = A.run (List.ofFn Y) t) :
      A.allPorts (List.ofFn X) t = A.allPorts (List.ofFn Y) t := by
    have htT := (hC t ht).2.le.trans hbT
    unfold Observer.allPorts Observer.ports
    rw [ha, ← E.config_eq_run htT, ← F.config_eq_run htT, hc.2.1]
  have raw_agree (t : ℕ) (ht : t ∈ C)
      (hc : SameControl (E.config t) (F.config t))
      (ha : A.run (List.ofFn X) t = A.run (List.ofFn Y) t) :
      A.rawWindows (List.ofFn X) t = A.rawWindows (List.ofFn Y) t := by
    have hp := ports_agree t ht hc ha
    funext j i
    unfold Observer.rawWindows
    rw [← congrFun hp j]
    exact hrawEq _ (hrawWindows t ht j i)
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro htC
    have htT := (hC t htC).2.le.trans hbT
    have hb := replay_before E F hbT f S C entry hC hEC hFC hentry hfill hcontrol hwindow
      (fun u hu hut => (ih u hut hu).1) hslab I hraw hrawEq hcount htC
    have hc := hb.2.1
    have hnowcount := hb.2.2.2.1
    have he := hentry t htC
    have haux : A.run (List.ofFn X) t = A.run (List.ofFn Y) t := by
      by_cases het : entry t = t
      · simpa only [het] using hobserver t htC
      · have htp : t - 1 + 1 = t := by omega
        have hep : entry t ≤ t - 1 := by omega
        have hpC := hfill t htC (t - 1) hep (by omega)
        have hp := ih (t - 1) (by omega) hpC
        have hprev := hb.2.2.1 (t - 1) hpC (by omega)
        have hprevcount := hb.2.2.2.2 (t - 1) hpC (by omega)
        have htprev : t - 1 ≤ T := by omega
        have hnative : transAt M (List.ofFn X) (t - 1) = transAt M (List.ofFn Y) (t - 1) := by
          change nativeInstruction M (List.ofFn X) (Transpose.Tape.run M (List.ofFn X) (t - 1)) =
            nativeInstruction M (List.ofFn Y) (Transpose.Tape.run M (List.ofFn Y) (t - 1))
          simpa only [E.config_eq_run htprev, F.config_eq_run htprev] using hprev.2
        have hh := A.update_agreement (List.ofFn X) (List.ofFn Y) (t - 1)
          (by simpa only [E.config_eq_run htprev, F.config_eq_run htprev] using hprev.1.1)
          (congrArg Prod.fst hp.2.1)
          (by simpa only [E.config_eq_run htprev, F.config_eq_run htprev] using hprev.1.2.2)
          (ports_agree _ hpC hprev.1 hp.2.1)
          (by simpa only [E.config_eq_run htprev, F.config_eq_run htprev] using hprevcount)
          (by simpa only [E.config_eq_run htprev, F.config_eq_run htprev] using hp.2.2)
          (raw_agree _ hpC hprev.1 hp.2.1) hnative
        simpa only [htp] using hh
    have hports := ports_agree t htC hc haux
    have hrawnow := raw_agree t htC hc haux
    have hprefix : (E.config t).outRev.reverse = (F.config t).outRev.reverse := by
      rw [E.config_eq_run htT, F.config_eq_run htT, ← PrefixOutput.native_word, ← PrefixOutput.native_word]
      apply PrefixOutput.strictPrefix_eq π hπ _ _ NE NF t (htT.trans hTE) (htT.trans hTF)
        (by rw [PrefixOutput.native_word]; exact hfinalE)
        (by rw [PrefixOutput.native_word]; exact hfinalF) C omitted
      · simpa only [PrefixOutput.native_word, List.length_reverse,
          ← E.config_eq_run htT, ← F.config_eq_run htT] using hnowcount
      · intro q hq
        obtain ⟨u, hu, j, hj, hcu, hem⟩ := hcover q hq
        have huT := (hC u hu).2.le.trans hbT
        refine ⟨u, hu, j, hj, ?_, ?_⟩
        · simpa only [PrefixOutput.native_word, List.length_reverse, ← E.config_eq_run huT] using hcu
        · simpa only [← E.emitted_eq_outBit huT] using hem
      · intro u hu hut
        have huT := (hC u hu).2.le.trans hbT
        refine ⟨?_, ?_⟩
        · simpa only [PrefixOutput.native_word, List.length_reverse,
            ← E.config_eq_run huT, ← F.config_eq_run huT] using hb.2.2.2.2 u hu hut
        · have hh : E.emitted u = F.emitted u :=
            congrArg (fun x => x.bind fun z => z.2.2.2) (hb.2.2.1 u hu hut).2
          simpa only [E.emitted_eq_outBit huT, F.emitted_eq_outBit huT] using hh
      · exact hexterior
    have hcarrier : (E.config t).work f ((E.config t).workPos f) =
        (F.config t).work f ((F.config t).workPos f) := by
      rw [← congrFun hc.2.2 f]
      exact hb.1 _ ((hEC t (hC t htC).1 (hC t htC).2).mp htC)
    have hctx : getterContext A f label (List.ofFn X) t = getterContext A f label (List.ofFn Y) t := by
      dsimp only [getterContext]
      rw [← E.config_eq_run htT, ← F.config_eq_run htT]
      rw [hcarrier, hprefix, hrawnow, hports, congrArg Prod.fst haux, hc.1, hc.2.2, hnowcount]
    have hpred (h : Fin M.k) : prediction A G f label (List.ofFn X) t h =
        prediction A G f label (List.ofFn Y) t h := congrArg (G h) hctx
    have hpos (h : Fin M.k) : ∀ u, entry t ≤ u → u ≤ t →
        (E.config u).workPos h = (F.config u).workPos h := by
      intro u heu hut
      by_cases hu : u = t
      · subst u; exact congrFun hc.2.2 h
      · exact congrFun (hb.2.2.1 u (hfill t htC u heu hut) (by omega)).1.2.2 h
    have himports : ∀ h, h ≠ f →
        E.incomingRecord H (entry t) t h = F.incomingRecord H (entry t) t h := by
      intro h hh
      have hp := incoming_presence_eq E F (H := H) he.2 h (hpos h) (hpast t htC h hh)
      have herr := herrors t htC h hh
      unfold errorRecord at herr
      rw [← hpred h] at herr
      exact correction_recovers _ _ _ hp herr
    refine ⟨himports, haux, ?_⟩
    intro h
    by_cases hh : h = f
    · subst h; exact hcarrier
    · apply E.run_read_eq F he.2 htT h (hpos h)
      · intro u heu hut
        have huC := hfill t htC u heu hut.le
        have hu := hb.2.2.1 u huC hut
        exact (step_record_agreement (E.successful u (by omega))
          (F.successful u (by omega)) hu.1 hu.2).2 h
      · exact hwindow t htC h hh
      · exact himports h hh

end AdaptiveTransfer.Getter
