import BitWord.NativeStagesRun
import BitWord.AddressFields

namespace BitWord

theorem moveBank_trans {N : ℕ} {α : Type*} (p q : Fin N ≃ Fin N)
    (b : Address N → α) : moveBank q (moveBank p b)=moveBank (p.trans q) b := by
  funext a
  rfl

theorem gatesEquiv_append (N : ℕ) (as bs : List Gate)
    (h : ∀ g ∈ as++bs,g.Legal N) :
    gatesEquiv N (as++bs) h =
      (gatesEquiv N as (fun g hg => h g (List.mem_append_left _ hg))).trans
      (gatesEquiv N bs (fun g hg => h g (List.mem_append_right _ hg))) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.cons_append,gatesEquiv]
    rw [ih]
    rfl

namespace NativeStages

theorem moved_of_some {N : ℕ} {g : Option Gate} (hg : NativeGate.Legal N g)
    {a : Gate} (ha : a.Legal N) (he : g=some a) (b : Address N → Bool) :
    NativeGate.moved g hg b=moveBank (a.equiv N ha) b := by
  subst g
  rfl

theorem moved_of_none {N : ℕ} {g : Option Gate} (hg : NativeGate.Legal N g)
    (he : g=none) (b : Address N → Bool) : NativeGate.moved g hg b=b := by
  subst g
  rfl

def padded (gs : List Gate) (i : Fin 13) : Option Gate := gs[i.val]?

theorem padded_legal {N : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs,g.Legal N)
    (i : Fin 13) : NativeGate.Legal N (padded gs i) := by
  unfold padded
  by_cases hi : i.val<gs.length
  · rw [List.getElem?_eq_getElem hi]
    exact hg _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none (by omega)]
    trivial

theorem after_padded_take {N : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs,g.Legal N)
    (b : Address N → Bool) (n : ℕ) (hn : n≤13) :
    after (padded gs) (padded_legal gs hg) b n =
      moveBank (gatesEquiv N (gs.take n) (fun g hm => hg g (List.mem_of_mem_take hm))) b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n<13 := by omega
    rw [after, dif_pos hn',ih (by omega)]
    by_cases hi : n<gs.length
    · simp only [List.take_succ_eq_append_getElem hi]
      rw [gatesEquiv_append]
      simp only [gatesEquiv,Equiv.trans_refl]
      rw [←moveBank_trans]
      exact moved_of_some _ _ (List.getElem?_eq_getElem hi) _
    · have hnil := List.getElem?_eq_none (l:=gs) (i:=n) (by omega)
      simp only [List.take_succ,hnil,Option.toList_none,List.append_nil]
      exact moved_of_none _ hnil _

theorem after_padded {N : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs,g.Legal N)
    (hlen : gs.length≤13) (b : Address N → Bool) :
    after (padded gs) (padded_legal gs hg) b 13=moveBank (gatesEquiv N gs hg) b := by
  rw [after_padded_take gs hg b 13 (by rfl)]
  have htake := (List.take_eq_self_iff gs).2 hlen
  simp only [htake]

theorem canonical_after {h : ℕ} (hh : 0<h) (b : Address (2*h+tailBits h) → Bool) :
    after (padded (canonicalGates h))
      (padded_legal _ (canonicalGates_legal hh)) b 13 =
      moveBank (gatesEquiv _ (canonicalGates h) (canonicalGates_legal hh)) b :=
  after_padded _ _ (canonicalGates_length h) b

end NativeStages
end BitWord
