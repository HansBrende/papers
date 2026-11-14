import Mathlib.Data.Fintype.EquivFin

/-!
# Ordering a finite relation from a root

If every proper cut containing a chosen root has an outgoing edge, the vertices
can be listed without repetition, starting at that root, so that every later
vertex has a predecessor joined to it by an edge. No symmetry is required.
-/

namespace LeanMachine.SupportTraversal

set_option autoImplicit false

variable {V : Type*} (E : V → V → Prop)

/-- Every noninitial entry has an incoming edge from an earlier entry. -/
def EarlierParent (l : List V) : Prop :=
  ∀ (i : ℕ) (hi : i < l.length), 0 < i →
    ∃ (j : ℕ) (hj : j < i), E l[j] l[i]

theorem EarlierParent.snoc {l : List V} (h : EarlierParent E l)
    {u v : V} (hu : u ∈ l) (huv : E u v) :
    EarlierParent E (l ++ [v]) := by
  intro i hi hpos
  by_cases hil : i < l.length
  · obtain ⟨j, hj, hE⟩ := h i hil hpos
    refine ⟨j, hj, ?_⟩
    simpa only [List.getElem_append_left hil,
      List.getElem_append_left (Nat.lt_trans hj hil)] using hE
  · have hie : i = l.length := by
      simp only [List.length_append, List.length_singleton] at hi
      omega
    subst i
    obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.mp hu
    refine ⟨j, hj, ?_⟩
    simpa only [List.getElem_append_left hj,
      List.getElem_append_right (le_refl l.length), Nat.sub_self,
      List.getElem_cons_zero, hju] using huv

variable [Fintype V]

/-- The root-containing version of the cut condition is enough; cuts not
containing the root need no hypothesis. -/
theorem exists_list (s : V)
    (hcut : ∀ P : Finset V, s ∈ P → P ≠ Finset.univ →
      ∃ u ∈ P, ∃ v ∉ P, E u v) :
    ∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.head? = some s ∧
      EarlierParent E l := by
  classical
  have extend : ∀ t : ℕ, ∀ l : List V,
      Fintype.card V - l.length = t → l.Nodup → l.head? = some s →
      EarlierParent E l →
      ∃ L : List V, L.Nodup ∧ (∀ v, v ∈ L) ∧ L.head? = some s ∧
        EarlierParent E L := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro l ht hnd hhead hord
      by_cases hall : ∀ v, v ∈ l
      · exact ⟨l, hnd, hall, hhead, hord⟩
      have hs : s ∈ l := by
        cases l with
        | nil => simp at hhead
        | cons a l => exact List.mem_cons.mpr (Or.inl (Option.some.inj hhead).symm)
      have hproper : l.toFinset ≠ Finset.univ := by
        intro heq
        apply hall
        intro v
        simpa only [List.mem_toFinset, Finset.mem_univ] using
          (show v ∈ l.toFinset from heq.symm ▸ Finset.mem_univ v)
      obtain ⟨u, hu, v, hv, huv⟩ := hcut l.toFinset
        (List.mem_toFinset.mpr hs) hproper
      have hv' : v ∉ l := by simpa only [List.mem_toFinset] using hv
      have hnd' : (l ++ [v]).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨hnd, by simp, ?_⟩
        intro a ha b hb
        have hb' : b = v := by simpa only [List.mem_singleton] using hb
        subst b
        exact fun heq => hv' (heq ▸ ha)
      have hlt : Fintype.card V - (l ++ [v]).length < t := by
        have hlen := hnd'.length_le_card
        simp only [List.length_append, List.length_singleton] at hlen ⊢
        omega
      apply ih _ hlt (l ++ [v]) rfl hnd'
      · simp only [List.head?_append, hhead, Option.some_or]
      · exact hord.snoc E (List.mem_toFinset.mp hu) huv
  apply extend _ [s] rfl (List.nodup_singleton s) rfl
  intro i hi hpos
  simp only [List.length_singleton] at hi
  omega

/-- Permutation form, suitable for reindexing the rows and columns of a
matrix by the same traversal. The initial vertex may be prescribed. -/
theorem exists_equiv (s : V)
    (hcut : ∀ P : Finset V, s ∈ P → P ≠ Finset.univ →
      ∃ u ∈ P, ∃ v ∉ P, E u v) :
    ∃ e : Fin (Fintype.card V) ≃ V,
      (∀ i, i.val = 0 → e i = s) ∧
      (∀ i, 0 < i.val → ∃ j, j < i ∧ E (e j) (e i)) := by
  classical
  obtain ⟨l, hnd, hall, hhead, hord⟩ := exists_list E s hcut
  let e₀ := hnd.getEquivOfForallMemList l hall
  have hn : Fintype.card V = l.length := by
    simpa using (Fintype.card_congr e₀).symm
  let e := (finCongr hn).trans e₀
  refine ⟨e, ?_, ?_⟩
  · intro i hi
    change l[i.val] = s
    cases l with
    | nil => simp at hhead
    | cons a l =>
      simpa only [hi, List.getElem_cons_zero] using Option.some.inj hhead
  · intro i hi
    have hil : i.val < l.length := hn ▸ i.isLt
    obtain ⟨j, hj, hE⟩ := hord i.val hil hi
    refine ⟨⟨j, Nat.lt_trans hj i.isLt⟩, hj, ?_⟩
    exact hE

end LeanMachine.SupportTraversal

#print axioms LeanMachine.SupportTraversal.exists_list
#print axioms LeanMachine.SupportTraversal.exists_equiv
