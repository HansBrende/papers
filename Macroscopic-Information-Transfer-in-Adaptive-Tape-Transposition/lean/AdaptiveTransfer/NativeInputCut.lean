import AdaptiveTransfer.FragmentInjection

/-! Actual adaptive input cuts for an arbitrary fixed output permutation.
Witnesses contain successful runs and literal graph separators only. Their
retained fragments, paid records and missing raw coordinates are derived. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape MergeDepth Finset BoundedNesting NativeRelations

noncomputable def permutationOutputRoots {k P : ℕ} (τ : Trace k) (finish : ℕ)
    (π : Equiv.Perm (Fin P)) (V : Finset (Fin P)) : Finset ℕ :=
  V.image fun p => appendTime τ finish (π.symm p).val

/-- A real successful bounded native run, a desired set inside a read set,
and an endpoint-inclusive separator in that run's native dependency graph. -/
structure NativeInputCutWitness (M : TM) (P T : ℕ) (π : Equiv.Perm (Fin P)) (X : Fin P → Bool) where
  finish : ℕ
  finish_le : finish ≤ T
  active : ∀ t < finish, transAt M (List.ofFn X) t ≠ none
  output : (run M (List.ofFn X) finish).outRev.reverse = List.ofFn (fun j => X (π j))
  reads : Finset (Fin P)
  desired : Finset (Fin P)
  desired_subset : desired ⊆ reads
  cut : Finset ℕ
  cut_lt : ∀ t ∈ cut, t < finish
  separates : IsMengerVertexCut (trace M (List.ofFn X)).work finish
    (permutationOutputRoots (trace M (List.ofFn X)) finish π desired)
    (demandedReadSteps (trace M (List.ofFn X)) P finish reads) cut

namespace NativeInputCutWitness
variable {M : TM} {P T : ℕ} {π : Equiv.Perm (Fin P)} {X : Fin P → Bool}

noncomputable def roots (g : NativeInputCutWitness M P T π X) : Finset ℕ :=
  permutationOutputRoots (trace M (List.ofFn X)) g.finish π g.desired

theorem output_length (g : NativeInputCutWitness M P T π X) :
    (run M (List.ofFn X) g.finish).outRev.length = P := by
  simpa only [List.length_reverse, List.length_ofFn] using congrArg List.length g.output

theorem append_length (g : NativeInputCutWitness M P T π X) :
    (appendList (trace M (List.ofFn X)) g.finish).length = P := by
  rw [← native_output_count, g.output_length]

noncomputable def fragment (g : NativeInputCutWitness M P T π X) : FragmentObservation M P T X g.cut where
  finish := g.finish
  finish_le := g.finish_le
  active := g.active
  kept := cutFreeAncestors (trace M (List.ofFn X)).work g.finish g.roots g.cut
  kept_lt := fun _ ht => cutFreeAncestors_time ht
  cut_lt := g.cut_lt
  closed := cutFreeAncestors_state_closed _ _ _ _
  count_le := g.output_length.le

theorem fragment_parents (g : NativeInputCutWitness M P T π X) : g.fragment.Parents := by
  intro t ht i p hpt hpos hlast
  simp only [workPos_eq_work] at hpos hlast
  exact cutFreeAncestors_last_parent ht i hpt hpos hlast

theorem fragment_avoids_reads (g : NativeInputCutWitness M P T π X)
    {p : Fin P} (hp : p ∈ g.reads) : (p.val : ℤ) ∉ g.fragment.rawCells := by
  intro hraw
  obtain ⟨t, ht, hpos⟩ := mem_image.mp hraw
  have hread : t ∈ demandedReadSteps (trace M (List.ofFn X)) P g.finish g.reads :=
    mem_filter.mpr ⟨mem_range.mpr (g.fragment.kept_lt t ht), p, hp, readPos_eq_some_iff.mpr hpos⟩
  exact cutFreeAncestors_avoid_targets g.separates ht hread

/-- Every desired bit lies among the actual output coordinates recovered by
the record, including roots paid directly as cut steps. -/
theorem desired_subset_omitted (g : NativeInputCutWitness M P T π X) :
    g.desired ⊆ g.fragment.omitted π := by
  intro p hp
  let j := π.symm p
  let t := appendTime (trace M (List.ofFn X)) g.finish j.val
  have hj : j.val < (appendList (trace M (List.ofFn X)) g.finish).length := by
    rw [g.append_length]
    exact j.isLt
  have htT : t < g.finish := appendTime_lt _ _ hj
  have hroot : t ∈ g.roots := mem_image.mpr ⟨p, hp, rfl⟩
  have ht : t ∈ g.fragment.kept ∪ g.cut := root_mem_cut_or_ancestors hroot htT
  have hc : g.fragment.counter t = j.val := by
    have hh := appendCount_appendTime (trace M (List.ofFn X)) g.finish hj
    simp only [appendCount] at hh
    change (run M (List.ofFn X) t).outRev.length = j.val
    rw [native_output_count]
    exact_mod_cast hh
  have ho : (g.fragment.exec.emitted t).isSome := by
    rw [g.fragment.exec.emitted_eq_outBit htT.le, outBit_isSome_eq]
    rw [show t = (appendList (trace M (List.ofFn X)) g.finish)[j.val] from appendTime_eq_getElem _ _ hj]
    exact (List.mem_filter.mp (List.getElem_mem hj)).2
  refine mem_filter.mpr ⟨mem_image.mpr ⟨j, g.fragment.ordinal_mem_of_append ht j hc ho, ?_⟩,
    g.fragment_avoids_reads (g.desired_subset hp)⟩
  exact π.apply_symm_apply p

end NativeInputCutWitness
end AdaptiveTransfer
