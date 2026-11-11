import AdaptiveTransfer.NativeInputCutCounting

/-! The literal timely correct bad-input event. This final wrapper requires
an actual first halt and identifies the existential sets and separator with
the witness fields used by the stronger successful-prefix counting theorem. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape MergeDepth Finset BoundedNesting NativeRelations
open scoped BigOperators

noncomputable def nativeBadInputCuts (M : TM) (P T : ℕ) (π : Equiv.Perm (Fin P))
    (D : ℝ) (r : ℕ) : Finset (Fin P → Bool) := by
  classical
  exact univ.filter fun X => ∃ g : NativeInputCutWitness M P T π X,
    transAt M (List.ofFn X) g.finish = none ∧ D ≤ (g.desired.card : ℝ) ∧ g.cut.card ≤ r

/-- The bounded event is exactly a timely correct halted input admitting the
sets and original endpoint-inclusive vertex cut stated in the theorem. -/
theorem mem_nativeBadInputCuts_iff {M : TM} {P T r : ℕ} {π : Equiv.Perm (Fin P)}
    {D : ℝ} {X : Fin P → Bool} : X ∈ nativeBadInputCuts M P T π D r ↔
    ∃ finish, finish ≤ T ∧ HaltsAt M (List.ofFn X) finish ∧
      (run M (List.ofFn X) finish).outRev.reverse = List.ofFn (fun j => X (π j)) ∧
      ∃ U V : Finset (Fin P), ∃ B : Finset ℕ,
        V ⊆ U ∧ D ≤ (V.card : ℝ) ∧ B.card ≤ r ∧ (∀ t ∈ B, t < finish) ∧
        IsMengerVertexCut (trace M (List.ofFn X)).work finish
          (permutationOutputRoots (trace M (List.ofFn X)) finish π V)
          (demandedReadSteps (trace M (List.ofFn X)) P finish U) B := by
  classical
  constructor
  · intro hX
    obtain ⟨g, hhalt, hD, hr⟩ := (mem_filter.mp hX).2
    exact ⟨g.finish, g.finish_le, ⟨g.active, hhalt⟩, g.output, g.reads, g.desired, g.cut,
      g.desired_subset, hD, hr, g.cut_lt, g.separates⟩
  · rintro ⟨finish, hfinish, hhalt, hout, U, V, B, hVU, hD, hr, hBT, hsep⟩
    let g : NativeInputCutWitness M P T π X :=
      ⟨finish, hfinish, hhalt.1, hout, U, V, hVU, B, hBT, hsep⟩
    exact mem_filter.mpr ⟨mem_univ _, g, hhalt.2, hD, hr⟩

/-- The manuscript's finite adaptive input-cut inequality, with exactly its
geometry sum and full step-value width. All quantities are actual run data. -/
theorem native_bad_input_cut_bound (M : TM) (P T r q a : ℕ) (π : Equiv.Perm (Fin P)) (D : ℝ)
    (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a) :
    ((nativeBadInputCuts M P T π D r).card : ℝ) ≤ (2 : ℝ) ^ ((P : ℝ) - D) *
      (∑ s ∈ range (min r T + 1), globalGeometryMenuSize M.k P T s * 2 ^ ((q + M.k * a + 2) * s) : ℕ) := by
  classical
  let C := nativeBadInputCuts M P T π D r
  have hex (X : C) : ∃ g : NativeInputCutWitness M P T π X.val,
      transAt M (List.ofFn X.val) g.finish = none ∧ D ≤ (g.desired.card : ℝ) ∧ g.cut.card ≤ r :=
    (mem_filter.mp X.property).2
  exact native_input_cut_bound π D hq ha C (fun X => (hex X).choose)
    (fun X => (hex X).choose_spec.2.1) (fun X => (hex X).choose_spec.2.2)

end AdaptiveTransfer
