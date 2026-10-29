import SourceCovers.TerminalCoreCover
import LeanMachine.ContinuationSuppliers

/-! Complete causal closures for zero, one or two actual exceptional families.
Missing exceptions are identity maps, rather than fictitious actual families. -/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.SourceBank
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}
variable {K : Finset (ActualFamily xs T)} {B : Bank}

def ExactCoreBank.closure (hB : ExactCoreBank K B) : CausalClosure where
  reach := values B
  self_mem := hB.root_mem
  trans := fun hu hv => hB.values_subset ((hB _).subset hu) hv
  past := fun hu => shadowOrbit_le ((hB _).subset hu)

def exceptionMap (e : Option (ActualFamily xs T)) (t : ℕ) : ℕ :=
  e.elim t (fun q => q.shadow t)

theorem exceptionMap_le (e : Option (ActualFamily xs T)) (t : ℕ) :
    exceptionMap e t ≤ t := by
  cases e with
  | none => exact le_rfl
  | some q => exact q.shadowAction.apply_le t

def oneExceptionBank (B : Bank) (e : Option (ActualFamily xs T)) : Bank :=
  ordered B (e.toList.map ActualFamily.shadowAction)

def twoExceptionBank (B : Bank) (g e : Option (ActualFamily xs T)) : Bank :=
  ordered B ((g.toList ++ e.toList).map ActualFamily.shadowAction)

theorem oneExceptionBank_exact (hB : ExactCoreBank K B) (e : Option (ActualFamily xs T)) :
    ExactCoreBank (K ∪ e.toList.toFinset) (oneExceptionBank B e) := by
  intro t
  exact ordered_values_exact hB e.toList (by cases e <;> simp) t

theorem twoExceptionBank_exact (hB : ExactCoreBank K B) (g e : Option (ActualFamily xs T))
    (horder : (g.toList ++ e.toList).Pairwise (fun a b => b.owner ≤ a.owner)) :
    ExactCoreBank (K ∪ (g.toList ++ e.toList).toFinset) (twoExceptionBank B g e) := by
  intro t
  exact ordered_values_exact hB _ horder t

/-- Existing ordered-bank exactness supplies the decomposition, including the
identity padding cases. No closure identity is assumed as an extra premise. -/
theorem optional_ordered_values (hB : ExactCoreBank K B) (E : List (ActualFamily xs T))
    (hE : E.Pairwise (fun a b => b.owner ≤ a.owner))
    (g : Option (ActualFamily xs T)) (t : ℕ) :
    values (ordered B ((g.toList ++ E).map ActualFamily.shadowAction)) t =
      hB.closure.extend (ExactCoreBank.closure (ordered_values_exact hB E hE))
        (exceptionMap g) t := by
  cases g with
  | none =>
    change values (ordered B (E.map ActualFamily.shadowAction)) t =
      values (ordered B (E.map ActualFamily.shadowAction)) t ∪
      (values B t).biUnion (fun u => values (ordered B (E.map ActualFamily.shadowAction)) u)
    apply Eq.symm
    apply union_eq_left.mpr
    intro v hv
    obtain ⟨u, hu, hv⟩ := mem_biUnion.mp hv
    exact ExactCoreBank.values_subset (ordered_values_exact hB E hE)
      (shadowOrbit_mono subset_union_left t ((hB t).subset hu)) hv
  | some g =>
    ext u
    simpa [CausalClosure.extend, ExactCoreBank.closure, exceptionMap, ActualFamily.shadow] using
      ordered_values_cons B g.shadowAction (E.map ActualFamily.shadowAction) t u

theorem oneExceptionBank_decomposition (hB : ExactCoreBank K B)
    (e : Option (ActualFamily xs T)) (t : ℕ) :
    (oneExceptionBank_exact hB e).closure.reach t =
      hB.closure.extend hB.closure (exceptionMap e) t := by
  simpa only [List.append_nil, List.toFinset_nil, union_empty, List.map_nil,
    ExactCoreBank.closure, ordered, oneExceptionBank] using
    optional_ordered_values hB [] (by simp) e t

theorem core_subset_oneException (hB : ExactCoreBank K B)
    (e : Option (ActualFamily xs T)) (t : ℕ) :
    hB.closure.reach t ⊆ (oneExceptionBank_exact hB e).closure.reach t :=
  fun _ hu => (oneExceptionBank_exact hB e t).superset
    (shadowOrbit_mono subset_union_left t ((hB t).subset hu))

def continuationSuppliers (hB : ExactCoreBank K B)
    (g e : Option (ActualFamily xs T)) (t : ℕ) : Finset ℕ :=
  hB.closure.suppliers (oneExceptionBank_exact hB e).closure (exceptionMap g) t

/-- The full source set is exactly the union of complete older closures
rooted at maximal suppliers. The statement precedes any raw-coordinate map. -/
theorem continuationSuppliers_exact (hB : ExactCoreBank K B)
    (g e : Option (ActualFamily xs T)) (t : ℕ) :
    values (twoExceptionBank B g e) t =
      (oneExceptionBank_exact hB e).closure.hull (continuationSuppliers hB g e t) := by
  rw [twoExceptionBank, optional_ordered_values hB e.toList (by cases e <;> simp)]
  exact hB.closure.extend_eq_hull_suppliers _ (core_subset_oneException hB e) _ t

/-- Any exact older bank may be used; the slots, including multiplicities,
are fixed independently of a later clustering or raw-coordinate path. -/
theorem continuationSuppliers_exact_bank (hB : ExactCoreBank K B)
    (g e : Option (ActualFamily xs T)) {D : Bank}
    (hD : ExactCoreBank (K ∪ e.toList.toFinset) D) (t : ℕ) :
    values (twoExceptionBank B g e) t =
      (continuationSuppliers hB g e t).biUnion (values D) := by
  rw [continuationSuppliers_exact hB g e t]
  apply biUnion_congr rfl
  intro u _
  exact coe_injective ((oneExceptionBank_exact hB e u).trans (hD u).symm)

theorem continuationSuppliers_root (hB : ExactCoreBank K B)
    (g e : Option (ActualFamily xs T)) (t : ℕ) :
    t ∈ continuationSuppliers hB g e t :=
  hB.closure.root_mem_suppliers _ _ (exceptionMap_le g) t

theorem continuationSuppliers_past (hB : ExactCoreBank K B)
    (g e : Option (ActualFamily xs T)) {t u : ℕ}
    (hu : u ∈ continuationSuppliers hB g e t) : u ≤ t :=
  hB.closure.supplier_past _ _ (exceptionMap_le g) hu

def olderLandingSuppliers (hB : ExactCoreBank K B)
    (g e : Option (ActualFamily xs T)) (t : ℕ) : Finset ℕ :=
  hB.closure.maximal (CausalClosure.landings (values (oneExceptionBank B g) t)
    (exceptionMap e) \ values (oneExceptionBank B g) t)

theorem olderLandingSuppliers_exact (hB : ExactCoreBank K B)
    (g e : Option (ActualFamily xs T)) (t : ℕ) :
    values (twoExceptionBank B g e) t = values (oneExceptionBank B g) t ∪
      hB.closure.hull (olderLandingSuppliers hB g e t) := by
  rw [twoExceptionBank, optional_ordered_values hB e.toList (by cases e <;> simp)]
  exact hB.closure.two_extension_maximal_landings _ _ _ _
    (core_subset_oneException hB g) (oneExceptionBank_decomposition hB e)
    (oneExceptionBank_decomposition hB g) t

end
end SourceCovers
