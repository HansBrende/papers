import LeanMachine.BoundedTuples

/-! A multiset recovers sampled values of a monotone function when the sample
times are known. Samples may be listed in any order and repeated times are
allowed; sorting their known times supplies the chronological correspondence. -/

namespace LeanMachine

/-- All sampled values, stored without their input listing order. -/
def sampledCounterMultiset {m P : ℕ} (time : Fin m → ℕ) (value : ℕ → Fin (P + 1)) :
    Sym (Fin (P + 1)) m := ⟨(List.ofFn (fun i => value (time i)) : Multiset _), by simp⟩

/-- Known sample times and monotonicity recover every value from the multiset,
including duplicated times/counters. There is no supplied sorting certificate. -/
theorem sampledCounterMultiset_recovers {m P : ℕ} (time : Fin m → ℕ)
    {x y : ℕ → Fin (P + 1)} (hx : Monotone x) (hy : Monotone y)
    (he : sampledCounterMultiset time x = sampledCounterMultiset time y) :
    ∀ i, x (time i) = y (time i) := by
  let cmp (i j : Fin m) : Bool := decide (time i ≤ time j)
  let l := (List.finRange m).mergeSort cmp
  have hl : l.Perm (List.finRange m) := List.mergeSort_perm _ _
  have ht : l.Pairwise (fun i j => time i ≤ time j) := by
    have hh := List.pairwise_mergeSort (le := cmp)
      (fun i j k hij hjk => by
        exact decide_eq_true (le_trans (of_decide_eq_true hij) (of_decide_eq_true hjk)))
      (fun i j => by
        rcases le_total (time i) (time j) with hij | hji
        · simp [cmp, hij]
        · simp [cmp, hji]) (List.finRange m)
    simpa only [cmp, decide_eq_true_eq] using hh
  have hp : (List.ofFn (fun i => x (time i))).Perm (List.ofFn (fun i => y (time i))) :=
    Multiset.coe_eq_coe.mp (congrArg Subtype.val he)
  rw [List.ofFn_eq_map, List.ofFn_eq_map] at hp
  have hxy : (l.map (fun i => x (time i))).Perm (l.map (fun i => y (time i))) :=
    (hl.map _).trans (hp.trans (hl.map _).symm)
  have hsx : (l.map (fun i => x (time i))).SortedLE := by
    exact (List.pairwise_map.mpr (ht.imp fun {_ _} hij => hx hij)).sortedLE
  have hsy : (l.map (fun i => y (time i))).SortedLE := by
    exact (List.pairwise_map.mpr (ht.imp fun {_ _} hij => hy hij)).sortedLE
  have heq := hxy.eq_of_sortedLE hsx hsy
  intro i
  exact List.map_inj_left.mp heq i (hl.mem_iff.mpr (List.mem_finRange i))

end LeanMachine
