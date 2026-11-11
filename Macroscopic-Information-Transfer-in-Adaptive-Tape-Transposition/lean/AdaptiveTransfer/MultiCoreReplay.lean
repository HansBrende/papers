import AdaptiveTransfer.AdaptiveReplay

/-! Native adaptive replay with several protected cores and separately paid
entry fringes. The selected steps need not be defined by any single work head.
Only the original actual core-ownership and read-coverage facts are used. -/

namespace AdaptiveTransfer
open Transpose Finset

namespace ExecutionPrefix
variable {M : TM} {w v : List Bool} {T : ℕ}

/-- On an interval whose actual writes and positions agree, equality of one
cell at entry suffices for that cell at exit. Other entry cells may differ. -/
theorem work_eq_from_entry (E : ExecutionPrefix M w T) (F : ExecutionPrefix M v T)
    (h : Fin M.k) (z : ℤ) {a t : ℕ} (hat : a ≤ t) (ht : t ≤ T)
    (hentry : (E.config a).work h z = (F.config a).work h z)
    (hpos : ∀ u, a ≤ u → u < t → (E.config u).workPos h = (F.config u).workPos h)
    (hwrite : ∀ u, a ≤ u → u < t → E.written h u = F.written h u) :
    (E.config t).work h z = (F.config t).work h z := by
  induction t, hat using Nat.le_induction with
  | base => exact hentry
  | succ t hat ih =>
    rw [step_work_update (E.successful t (by omega)) h z,
      step_work_update (F.successful t (by omega)) h z]
    rw [← hpos t hat (by omega)]
    split_ifs with hz
    · simpa only [written, ← hpos t hat (by omega)] using hwrite t hat (by omega)
    · exact ih (by omega) (fun u hau hut => hpos u hau (by omega))
        (fun u hau hut => hwrite u hau (by omega))

/-- Several protected cores persist simultaneously. Clustered fringe reads
use their actual entry snapshots; only complementary heads use sparse imports.
This is a two-actual-execution theorem, with no assumed common detailed trace. -/
theorem multicore_replay_agreement
    (E : ExecutionPrefix M w T) (F : ExecutionPrefix M v T)
    {a b H : ℕ} (hbT : b ≤ T) (cluster : Finset (Fin M.k))
    (core fringe : Fin M.k → Set ℤ) (C : Finset ℕ) (entry : ℕ → ℕ)
    (hC : ∀ t ∈ C, a ≤ t ∧ t < b)
    (hEoutside : ∀ t, a ≤ t → t < b → t ∉ C → ∀ h ∈ cluster,
      (E.config t).workPos h ∉ core h)
    (hFoutside : ∀ t, a ≤ t → t < b → t ∉ C → ∀ h ∈ cluster,
      (F.config t).workPos h ∉ core h)
    (hselected : ∀ t ∈ C, ∀ h ∈ cluster,
      (E.config t).workPos h ∈ core h ∪ fringe h)
    (hentry : ∀ t ∈ C, a ≤ entry t ∧ entry t ≤ t)
    (hfill : ∀ t ∈ C, ∀ u, entry t ≤ u → u ≤ t → u ∈ C)
    (hcontrol : ∀ t ∈ C, SameControl (E.config (entry t)) (F.config (entry t)))
    (hfringe : ∀ t ∈ C, ∀ h ∈ cluster, ∀ z ∈ fringe h,
      (E.config (entry t)).work h z = (F.config (entry t)).work h z)
    (hwindow : ∀ t ∈ C, ∀ h ∉ cluster, ∀ z,
      (z - (E.config (entry t)).workPos h).natAbs ≤ H →
      (E.config (entry t)).work h z = (F.config (entry t)).work h z)
    (himports : ∀ t ∈ C, ∀ h ∉ cluster,
      E.incomingRecord H (entry t) t h = F.incomingRecord H (entry t) t h)
    (hcores : ∀ h ∈ cluster, ∀ z ∈ core h,
      (E.config a).work h z = (F.config a).work h z)
    (I : Set ℤ) (hraw : ∀ t ∈ C, (E.config t).inPos ∈ I)
    (hexterior : ∀ z ∈ I, readInput w z = readInput v z) :
    (∀ t, a ≤ t → t ≤ b → ∀ h ∈ cluster, ∀ z ∈ core h,
      (E.config t).work h z = (F.config t).work h z) ∧
    (∀ t ∈ C, SameControl (E.config t) (F.config t) ∧
      nativeInstruction M w (E.config t) = nativeInstruction M v (F.config t)) := by
  classical
  have main : ∀ t, a ≤ t → t ≤ b →
      (∀ h ∈ cluster, ∀ z ∈ core h, (E.config t).work h z = (F.config t).work h z) ∧
      (t ∈ C → SameControl (E.config t) (F.config t) ∧
        nativeInstruction M w (E.config t) = nativeInstruction M v (F.config t)) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro hat htb
      have hmem : ∀ h ∈ cluster, ∀ z ∈ core h,
          (E.config t).work h z = (F.config t).work h z := by
        by_cases hta : t = a
        · simpa only [hta] using hcores
        · have htp : t - 1 + 1 = t := by omega
          have hpa : a ≤ t - 1 := by omega
          have hpb : t - 1 < b := by omega
          have hp := ih (t - 1) (by omega) hpa hpb.le
          have hEs := E.successful (t - 1) (hpb.trans_le hbT)
          have hFs := F.successful (t - 1) (hpb.trans_le hbT)
          rw [htp] at hEs hFs
          intro h hh z hz
          by_cases hpC : t - 1 ∈ C
          · have hc := hp.2 hpC
            have hw := (step_record_agreement hEs hFs hc.1 hc.2).2 h
            have hpos := congrFun hc.1.2.2 h
            rw [step_work_update hEs h z, step_work_update hFs h z]
            by_cases hzp : z = (E.config (t - 1)).workPos h
            · rw [ite_eq_left hzp, ite_eq_left (hzp.trans hpos)]
              exact hw
            · rw [ite_eq_right hzp, ite_eq_right (by simpa only [← hpos] using hzp)]
              exact hp.1 h hh z hz
          · have hEout : z ≠ (E.config (t - 1)).workPos h := by
              intro heq
              exact hEoutside _ hpa hpb hpC h hh (heq ▸ hz)
            have hFout : z ≠ (F.config (t - 1)).workPos h := by
              intro heq
              exact hFoutside _ hpa hpb hpC h hh (heq ▸ hz)
            rw [step_preserves_unscanned hEs h z hEout,
              step_preserves_unscanned hFs h z hFout]
            exact hp.1 h hh z hz
      refine ⟨hmem, ?_⟩
      intro htC
      have hentryt := hentry t htC
      have hc : SameControl (E.config t) (F.config t) := by
        by_cases het : entry t = t
        · simpa only [het] using hcontrol t htC
        · have htp : t - 1 + 1 = t := by omega
          have hep : entry t ≤ t - 1 := by omega
          have hpC := hfill t htC (t - 1) hep (by omega)
          have hp := (ih (t - 1) (by omega) (hentryt.1.trans hep) (by omega)).2 hpC
          have hstep := step_record_agreement
            (E.successful (t - 1) (by omega)) (F.successful (t - 1) (by omega)) hp.1 hp.2
          simpa only [htp] using hstep.1
      have hpositions : ∀ h u, entry t ≤ u → u ≤ t →
          (E.config u).workPos h = (F.config u).workPos h := by
        intro h u heu hut
        by_cases hut' : u = t
        · subst u
          exact congrFun hc.2.2 h
        · exact congrFun ((ih u (by omega) (hentryt.1.trans heu)
            (hut.trans htb)).2 (hfill t htC u heu hut)).1.2.2 h
      have hwrites : ∀ h u, entry t ≤ u → u < t → E.written h u = F.written h u := by
        intro h u heu hut
        have hu := (ih u hut (hentryt.1.trans heu) (hut.le.trans htb)).2 (hfill t htC u heu hut.le)
        exact (step_record_agreement (E.successful u (by omega))
          (F.successful u (by omega)) hu.1 hu.2).2 h
      refine ⟨hc, instruction_eq_of_old_tuple hc.1 ?_ ?_⟩
      · rw [← hc.2.1]
        exact hexterior _ (hraw t htC)
      · intro h
        by_cases hh : h ∈ cluster
        · have hz := congrFun hc.2.2 h
          rw [← hz]
          rcases hselected t htC h hh with hcore | hfr
          · exact hmem h hh _ hcore
          · exact E.work_eq_from_entry F h _ hentryt.2 (htb.trans hbT)
              (hfringe t htC h hh _ hfr)
              (fun u heu hut => hpositions h u heu hut.le) (hwrites h)
        · exact E.run_read_eq F hentryt.2 (htb.trans hbT) h (hpositions h)
            (hwrites h) (hwindow t htC h hh) (himports t htC h hh)
  exact ⟨fun t hat htb => (main t hat htb).1,
    fun t ht => (main t (hC t ht).1 (hC t ht).2.le).2 ht⟩

end ExecutionPrefix
end AdaptiveTransfer
