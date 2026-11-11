import AdaptiveTransfer.EnlargedRule

/-! Pairwise replay of the whole enlarged one-work-tape rule, including its
port updates and strict-prefix dependence. The native multihead replay proof
is not duplicated: this is the single persistent slab case, with actual prefix
recovery supplied by PrefixOutput.
-/

namespace AdaptiveTransfer.Enlarged

open Transpose Finset

variable {Q Γ Λ : Type*} {p R : ℕ}

/-- Positions and ordinal are paid geometry; state is the complete mutable control. -/
def SameControl (c e : Config Q Γ 1 p) : Prop :=
  c.state = e.state ∧ c.workPos = e.workPos ∧ c.ports = e.ports ∧ c.outRev.length = e.outRev.length

namespace System
variable (M : System Q Γ Λ 1 p R)

/-- Equality of actual instructions propagates all dynamic control and actual
written symbols. The absent-instruction branch is genuine frozen halting. -/
theorem record_agreement (label : Λ) (w x : List Bool) (t : ℕ)
    (hc : SameControl (M.run label w t) (M.run label x t))
    (hi : M.instruction label w t = M.instruction label x t)
    (hold : ∀ h, (M.run label w t).work h ((M.run label w t).workPos h) =
      (M.run label x t).work h ((M.run label x t).workPos h)) :
    SameControl (M.run label w (t + 1)) (M.run label x (t + 1)) ∧
      ∀ h, M.written label w h t = M.written label x h t := by
  unfold written
  rw [run_succ, run_succ, hi]
  cases M.instruction label x t with
  | none => exact ⟨hc, hold⟩
  | some v =>
    constructor
    · refine ⟨rfl, ?_, ?_, ?_⟩
      · simp only [applyInstruction, hc.2.1]
      · simp only [applyInstruction, hc.2.2.1]
      · cases ha : v.append <;> simp only [applyInstruction, ha, hc.2.2.2, List.length_cons]
    · intro h; simp [applyInstruction]

theorem instruction_agreement (label : Λ) (w x : List Bool) (t : ℕ)
    (hliveE : M.live label w t = true) (hliveF : M.live label x t = true)
    (hc : SameControl (M.run label w t) (M.run label x t))
    (hold : ∀ h, (M.run label w t).work h ((M.run label w t).workPos h) =
      (M.run label x t).work h ((M.run label x t).workPos h))
    (hraw : ∀ j i, readInput w (windowAddress ((M.run label w t).ports j) R i) =
      readInput x (windowAddress ((M.run label x t).ports j) R i))
    (hprefix : (M.run label w t).outRev.reverse = (M.run label x t).outRev.reverse) :
    M.instruction label w t = M.instruction label x t := by
  have hctx : M.context label w t (M.run label w t) = M.context label x t (M.run label x t) := by
    unfold context
    rw [funext hold, hprefix, funext (fun j => funext (hraw j)), hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
  simp only [instruction, hliveE, hliveF, ite_true, hctx]

/-- Exact reconstruction of the whole one-tape enlarged transition. Its prefix
is proved from earlier instructions and final correctness before the rule runs. -/
theorem replay_agreement {P : ℕ} {X Y : Fin P → Bool} (label : Λ)
    (π : Fin P → Fin P) (hπ : Function.Injective π) (NE NF a b : ℕ)
    (hbE : b ≤ NE) (hbF : b ≤ NF)
    (hfinalE : (M.run label (List.ofFn X) NE).outRev.reverse = List.ofFn (fun j => X (π j)))
    (hfinalF : (M.run label (List.ofFn Y) NF).outRev.reverse = List.ofFn (fun j => Y (π j)))
    (S : Set ℤ) (C : Finset ℕ) (entry : ℕ → ℕ) (U : Finset (Fin P))
    (hC : ∀ t ∈ C, a ≤ t ∧ t < b)
    (hEC : ∀ t, a ≤ t → t < b → (t ∈ C ↔ (M.run label (List.ofFn X) t).workPos 0 ∈ S))
    (hFC : ∀ t, a ≤ t → t < b → (t ∈ C ↔ (M.run label (List.ofFn Y) t).workPos 0 ∈ S))
    (hentry : ∀ t ∈ C, a ≤ entry t ∧ entry t ≤ t)
    (hfill : ∀ t ∈ C, ∀ u, entry t ≤ u → u ≤ t → u ∈ C)
    (hcontrol : ∀ t ∈ C,
      SameControl (M.run label (List.ofFn X) (entry t)) (M.run label (List.ofFn Y) (entry t)))
    (hlive : ∀ t ∈ C, M.live label (List.ofFn X) t = true ∧ M.live label (List.ofFn Y) t = true)
    (hslab : ∀ z ∈ S, (M.run label (List.ofFn X) a).work 0 z =
      (M.run label (List.ofFn Y) a).work 0 z)
    (I : Set ℤ)
    (hraw : ∀ t ∈ C, ∀ j i, windowAddress ((M.run label (List.ofFn X) t).ports j) R i ∈ I)
    (hdisjoint : ∀ q : Fin P, (q.val : ℤ) ∈ I → q ∉ U)
    (hexterior : ∀ q ∉ U, X q = Y q)
    (hcover : ∀ q ∈ U, ∃ t ∈ C, ∃ j : Fin P,
      π j = q ∧ (M.run label (List.ofFn X) t).outRev.length = j.val ∧
      (M.emitted label (List.ofFn X) t).isSome) :
    (∀ t, a ≤ t → t ≤ b → ∀ z ∈ S,
      (M.run label (List.ofFn X) t).work 0 z = (M.run label (List.ofFn Y) t).work 0 z) ∧
    (∀ t ∈ C, SameControl (M.run label (List.ofFn X) t) (M.run label (List.ofFn Y) t) ∧
      M.instruction label (List.ofFn X) t = M.instruction label (List.ofFn Y) t) := by
  classical
  have hcorrectE : PrefixOutput.word (M.emitted label (List.ofFn X)) NE =
      List.ofFn (fun j => X (π j)) := (M.output_eq_word _ _ _).symm.trans hfinalE
  have hcorrectF : PrefixOutput.word (M.emitted label (List.ofFn Y)) NF =
      List.ofFn (fun j => Y (π j)) := (M.output_eq_word _ _ _).symm.trans hfinalF
  have main : ∀ t, a ≤ t → t ≤ b →
      (∀ z ∈ S, (M.run label (List.ofFn X) t).work 0 z = (M.run label (List.ofFn Y) t).work 0 z) ∧
      (t ∈ C → SameControl (M.run label (List.ofFn X) t) (M.run label (List.ofFn Y) t) ∧
        M.instruction label (List.ofFn X) t = M.instruction label (List.ofFn Y) t) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro hat htb
      have hmem : ∀ z ∈ S, (M.run label (List.ofFn X) t).work 0 z =
          (M.run label (List.ofFn Y) t).work 0 z := by
        by_cases hta : t = a
        · simpa only [hta] using hslab
        · have htp : t - 1 + 1 = t := by omega
          have hpa : a ≤ t - 1 := by omega
          have hpb : t - 1 < b := by omega
          have hp := ih (t - 1) (by omega) hpa hpb.le
          intro z hz
          have hE := M.work_update label (List.ofFn X) (t - 1) 0 z
          have hF := M.work_update label (List.ofFn Y) (t - 1) 0 z
          rw [htp] at hE hF
          rw [hE, hF]
          by_cases hpC : t - 1 ∈ C
          · have hc := hp.2 hpC
            have hold : ∀ h, (M.run label (List.ofFn X) (t - 1)).work h
                ((M.run label (List.ofFn X) (t - 1)).workPos h) =
                (M.run label (List.ofFn Y) (t - 1)).work h
                ((M.run label (List.ofFn Y) (t - 1)).workPos h) := by
              intro h
              have hh : h = 0 := Subsingleton.elim _ _
              subst h
              rw [← congrFun hc.1.2.1 0]
              exact hp.1 _ ((hEC _ hpa hpb).mp hpC)
            have hw := (M.record_agreement label _ _ _ hc.1 hc.2 hold).2 0
            rw [← congrFun hc.1.2.1 0, hw, hp.1 z hz]
          · have hEout : z ≠ (M.run label (List.ofFn X) (t - 1)).workPos 0 := by
              intro heq; exact hpC ((hEC _ hpa hpb).mpr (heq ▸ hz))
            have hFout : z ≠ (M.run label (List.ofFn Y) (t - 1)).workPos 0 := by
              intro heq; exact hpC ((hFC _ hpa hpb).mpr (heq ▸ hz))
            rw [ite_eq_right hEout, ite_eq_right hFout]
            exact hp.1 z hz
      refine ⟨hmem, ?_⟩
      intro htC
      have he := hentry t htC
      have htend := (hC t htC).2
      have hc : SameControl (M.run label (List.ofFn X) t) (M.run label (List.ofFn Y) t) := by
        by_cases het : entry t = t
        · simpa only [het] using hcontrol t htC
        · have htp : t - 1 + 1 = t := by omega
          have hep : entry t ≤ t - 1 := by omega
          have hpC := hfill t htC (t - 1) hep (by omega)
          have hp := ih (t - 1) (by omega) (he.1.trans hep) (by omega)
          have hold : ∀ h, (M.run label (List.ofFn X) (t - 1)).work h
              ((M.run label (List.ofFn X) (t - 1)).workPos h) =
              (M.run label (List.ofFn Y) (t - 1)).work h
              ((M.run label (List.ofFn Y) (t - 1)).workPos h) := by
            intro h
            have hh : h = 0 := Subsingleton.elim _ _
            subst h
            rw [← congrFun (hp.2 hpC).1.2.1 0]
            exact hp.1 _ ((hEC _ (he.1.trans hep) (by omega)).mp hpC)
          have hs := (M.record_agreement label _ _ _ (hp.2 hpC).1 (hp.2 hpC).2 hold).1
          simpa only [htp] using hs
      have hpref : (M.run label (List.ofFn X) t).outRev.reverse =
          (M.run label (List.ofFn Y) t).outRev.reverse := by
        rw [M.output_eq_word, M.output_eq_word]
        apply PrefixOutput.strictPrefix_eq π hπ _ _ NE NF t (htb.trans hbE) (htb.trans hbF)
          hcorrectE hcorrectF C U
        · simpa only [← M.count_eq_word] using hc.2.2.2
        · intro q hq
          obtain ⟨u, hu, j, hj, hcu, hemit⟩ := hcover q hq
          exact ⟨u, hu, j, hj, (M.count_eq_word _ _ _).symm.trans hcu, hemit⟩
        · intro u hu hut
          have hh := (ih u hut (hC u hu).1 (hC u hu).2.le).2 hu
          refine ⟨?_, congrArg (fun v => v.bind Instruction.append) hh.2⟩
          simpa only [← M.count_eq_word] using hh.1.2.2.2
        · exact hexterior
      refine ⟨hc, M.instruction_agreement label _ _ t (hlive t htC).1 (hlive t htC).2 hc ?_ ?_ hpref⟩
      · intro h
        have hh : h = 0 := Subsingleton.elim _ _
        subst h
        rw [← congrFun hc.2.1 0]
        exact hmem _ ((hEC t hat htend).mp htC)
      · intro j i
        rw [← congrFun hc.2.2.1 j]
        exact readInput_eq_of_exterior U I hexterior hdisjoint (hraw t htC j i)
  exact ⟨fun t hat htb => (main t hat htb).1,
    fun t ht => (main t (hC t ht).1 (hC t ht).2.le).2 ht⟩

end System
end AdaptiveTransfer.Enlarged
