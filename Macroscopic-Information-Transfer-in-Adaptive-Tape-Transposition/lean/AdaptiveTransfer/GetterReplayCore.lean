import AdaptiveTransfer.GetterObserver

/-! Reuse of the checked native replay engine on strict time prefixes. It
recovers the current carrier, native control and output ordinal from earlier
ordinary imports, allowing getter corrections to be converted causally.
-/

namespace AdaptiveTransfer.Getter

open Transpose Finset

variable {M : TM} {w x : List Bool} {T : ℕ}

noncomputable def visitedBefore (E : ExecutionPrefix M w T) (a : ℕ) (h : Fin M.k) : Finset ℤ :=
  (range a).image (fun u => (E.config u).workPos h)

/-- Paid pre-entry visit sets together with the reconstructed in-run path
identify exactly the presence of an ordinary import. -/
theorem incoming_presence_eq (E : ExecutionPrefix M w T) (F : ExecutionPrefix M x T)
    {H a t : ℕ} (hat : a ≤ t) (h : Fin M.k)
    (hpos : ∀ u, a ≤ u → u ≤ t → (E.config u).workPos h = (F.config u).workPos h)
    (hpast : visitedBefore E a h = visitedBefore F a h) :
    (E.incomingRecord H a t h).isSome = (F.incomingRecord H a t h).isSome := by
  have hpa := hpos a le_rfl hat
  have hpt := hpos t hat le_rfl
  have hfirst : (∀ u, a ≤ u → u < t → (E.config t).workPos h ≠ (E.config u).workPos h) ↔
      (∀ u, a ≤ u → u < t → (F.config t).workPos h ≠ (F.config u).workPos h) := by
    constructor <;> intro hh u hau hut
    · rw [← hpt, ← hpos u hau hut.le]; exact hh u hau hut
    · rw [hpt, hpos u hau hut.le]; exact hh u hau hut
  have hpast' (z : ℤ) :
      (∃ u < a, z = (E.config u).workPos h) ↔ (∃ u < a, z = (F.config u).workPos h) := by
    have hh : z ∈ visitedBefore E a h ↔ z ∈ visitedBefore F a h := by rw [hpast]
    simpa only [visitedBefore, mem_image, mem_range, eq_comm] using hh
  have hglobal : (∃ u < t, (E.config t).workPos h = (E.config u).workPos h) ↔
      (∃ u < t, (F.config t).workPos h = (F.config u).workPos h) := by
    constructor
    · rintro ⟨u, hut, hu⟩
      by_cases hua : u < a
      · obtain ⟨v, hva, hv⟩ := (hpast' _).mp ⟨u, hua, hu⟩
        exact ⟨v, hva.trans_le hat, hpt.symm.trans hv⟩
      · exact ⟨u, hut, hpt.symm.trans (hu.trans (hpos u (by omega) hut.le))⟩
    · rintro ⟨u, hut, hu⟩
      by_cases hua : u < a
      · obtain ⟨v, hva, hv⟩ := (hpast' _).mpr ⟨u, hua, hu⟩
        exact ⟨v, hva.trans_le hat, hpt.trans hv⟩
      · exact ⟨u, hut, hpt.trans (hu.trans (hpos u (by omega) hut.le).symm)⟩
  unfold ExecutionPrefix.incomingRecord
  simp only [hfirst, hglobal]
  simp only [hpa, hpt]
  split_ifs <;> rfl

/-- The existing native replay theorem, restricted to earlier selected times,
also determines current control and counters before the next selected read.
No current import or prediction is used in this theorem. -/
theorem replay_before (E : ExecutionPrefix M w T) (F : ExecutionPrefix M x T)
    {a b H t : ℕ} (hbT : b ≤ T)
    (f : Fin M.k) (S : Set ℤ) (C : Finset ℕ) (entry : ℕ → ℕ)
    (hC : ∀ u ∈ C, a ≤ u ∧ u < b)
    (hEC : ∀ u, a ≤ u → u < b → (u ∈ C ↔ (E.config u).workPos f ∈ S))
    (hFC : ∀ u, a ≤ u → u < b → (u ∈ C ↔ (F.config u).workPos f ∈ S))
    (hentry : ∀ u ∈ C, a ≤ entry u ∧ entry u ≤ u)
    (hfill : ∀ u ∈ C, ∀ v, entry u ≤ v → v ≤ u → v ∈ C)
    (hcontrol : ∀ u ∈ C, SameControl (E.config (entry u)) (F.config (entry u)))
    (hwindow : ∀ u ∈ C, ∀ h, h ≠ f → ∀ z,
      (z - (E.config (entry u)).workPos h).natAbs ≤ H →
      (E.config (entry u)).work h z = (F.config (entry u)).work h z)
    (himports : ∀ u ∈ C, u < t → ∀ h, h ≠ f →
      E.incomingRecord H (entry u) u h = F.incomingRecord H (entry u) u h)
    (hslab : ∀ z ∈ S, (E.config a).work f z = (F.config a).work f z)
    (I : Set ℤ) (hraw : ∀ u ∈ C, (E.config u).inPos ∈ I)
    (hexterior : ∀ z ∈ I, readInput w z = readInput x z)
    (hcount : ∀ u ∈ C, (E.config (entry u)).outRev.length = (F.config (entry u)).outRev.length)
    (htC : t ∈ C) :
    (∀ z ∈ S, (E.config t).work f z = (F.config t).work f z) ∧
      SameControl (E.config t) (F.config t) ∧
      (∀ u ∈ C, u < t → SameControl (E.config u) (F.config u) ∧
        nativeInstruction M w (E.config u) = nativeInstruction M x (F.config u)) ∧
      (E.config t).outRev.length = (F.config t).outRev.length ∧
      (∀ u ∈ C, u < t → (E.config u).outRev.length = (F.config u).outRev.length) := by
  classical
  let earlier := C.filter (fun u => u < t)
  have ht := hC t htC
  have hearlier (u : ℕ) : u ∈ earlier ↔ u ∈ C ∧ u < t := mem_filter
  have hcut : ∀ u ∈ earlier, a ≤ u ∧ u < t := by
    intro u hu
    exact ⟨(hC u (hearlier u |>.mp hu).1).1, (hearlier u |>.mp hu).2⟩
  have hcutentry : ∀ u ∈ earlier, a ≤ entry u ∧ entry u ≤ u :=
    fun u hu => hentry u (hearlier u |>.mp hu).1
  have hcutfill : ∀ u ∈ earlier, ∀ v, entry u ≤ v → v ≤ u → v ∈ earlier := by
    intro u hu v hv hvo
    have hh := (hearlier u).mp hu
    exact (hearlier v).mpr ⟨hfill u hh.1 v hv hvo, hvo.trans_lt hh.2⟩
  have hr := E.adaptive_replay_agreement F (a := a) (b := t) (H := H)
    (ht.2.le.trans hbT) f S earlier entry hcut
    (fun u hau hut => by simpa only [hearlier, and_iff_left hut] using hEC u hau (hut.trans ht.2))
    (fun u hau hut => by simpa only [hearlier, and_iff_left hut] using hFC u hau (hut.trans ht.2))
    hcutentry hcutfill
    (fun u hu => hcontrol u (hearlier u |>.mp hu).1)
    (fun u hu => hwindow u (hearlier u |>.mp hu).1)
    (fun u hu => himports u (hearlier u |>.mp hu).1 (hearlier u |>.mp hu).2)
    hslab I (fun u hu => hraw u (hearlier u |>.mp hu).1) hexterior
  have hpast := fun u hu hut => hr.2 u ((hearlier u).mpr ⟨hu, hut⟩)
  have hcounts := E.replay_output_count_agreement F earlier entry
    (fun u hu => (hcut u hu).2.trans_le (ht.2.le.trans hbT))
    (fun u hu => (hcutentry u hu).2) hcutfill
    (fun u hu => hcount u (hearlier u |>.mp hu).1) (fun u hu => (hr.2 u hu).2)
  have hc : SameControl (E.config t) (F.config t) := by
    by_cases he : entry t = t
    · simpa only [he] using hcontrol t htC
    · have htp : t - 1 + 1 = t := by have := hentry t htC; omega
      have hpC := hfill t htC (t - 1) (by have := hentry t htC; omega) (by omega)
      have hp := hpast (t - 1) hpC (by omega)
      have hs := step_record_agreement (E.successful (t - 1) (by omega))
        (F.successful (t - 1) (by omega)) hp.1 hp.2
      simpa only [htp] using hs.1
  have hct : (E.config t).outRev.length = (F.config t).outRev.length := by
    by_cases he : entry t = t
    · simpa only [he] using hcount t htC
    · have htp : t - 1 + 1 = t := by have := hentry t htC; omega
      have hpC := hfill t htC (t - 1) (by have := hentry t htC; omega) (by omega)
      have hpC' : t - 1 ∈ earlier := (hearlier _).mpr ⟨hpC, by omega⟩
      have hpout : E.emitted (t - 1) = F.emitted (t - 1) :=
        congrArg (fun x => x.bind fun v => v.2.2.2) (hr.2 _ hpC').2
      have heq := E.output_count_next (show t - 1 < T by omega)
      have hfq := F.output_count_next (show t - 1 < T by omega)
      rw [htp] at heq hfq
      rw [heq, hfq, hcounts _ hpC', hpout]
  exact ⟨hr.1 t ht.1 le_rfl, hc, hpast, hct,
    fun u hu hut => hcounts u ((hearlier u).mpr ⟨hu, hut⟩)⟩

end AdaptiveTransfer.Getter
