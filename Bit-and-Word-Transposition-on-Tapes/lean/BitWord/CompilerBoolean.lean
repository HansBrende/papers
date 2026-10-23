import BitWord.CompilerTranspose

namespace BitWord.Compiler
open Geometry
open Classical

/-- Arbitrary fixed address-dependent pointwise Boolean readout of all paths. -/
def readout {P K : ℕ} (paths : Fin K → Path P)
    (tables : Fin P → (Fin K → Bool) → Bool) (x : Fin P → Bool) : Fin P → Bool :=
  fun a => tables a (fun j => x ((endpoint (paths j)).symm a))

/-- A missing target source cannot be manufactured by an arbitrary nonlinear
pointwise table. Both compared inputs lie in the full original raw cube. -/
theorem no_readout_of_coverage_lt {P K : ℕ} (paths : Fin K → Path P)
    (target : Equiv.Perm (Fin P))
    (hcard : (covered paths (finiteAct target)).card < P)
    (tables : Fin P → (Fin K → Bool) → Bool) :
    ¬ ∀ (x : Fin P → Bool) a, readout paths tables x a = x (target.symm a) := by
  have hn : ¬ Finset.range P ⊆ covered paths (finiteAct target) := by
    intro h
    have hc := Finset.card_le_card h
    rw [Finset.card_range] at hc
    omega
  obtain ⟨v, hv, hmiss⟩ := Finset.not_subset.mp hn
  let x : Fin P := ⟨v, Finset.mem_range.mp hv⟩
  let a := target x
  have hneq (j : Fin K) : (endpoint (paths j)).symm a ≠ x := by
    intro he
    have ht : endpoint (paths j) x = a := by
      rw [← he]
      exact (endpoint (paths j)).apply_symm_apply a
    apply hmiss
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hv, ?_⟩⟩
    have ht' := congrArg Fin.val ht
    rw [endpoint_val] at ht'
    have ha : finiteAct target v = (target x).val := by simp only [finiteAct, dite_eq_left (Finset.mem_range.mp hv)]; rfl
    simpa only [x, a, ha] using ht'
  intro hc
  let zero : Fin P → Bool := fun _ => false
  let one : Fin P → Bool := fun w => decide (w = x)
  have he : (fun j => one ((endpoint (paths j)).symm a)) =
      (fun j => zero ((endpoint (paths j)).symm a)) := by
    funext j
    simp [one, zero, hneq j]
  have hz := hc zero a
  have ho := hc one a
  have htarget : target.symm a = x := target.symm_apply_apply x
  simp only [readout] at hz ho
  rw [he] at ho
  rw [hz] at ho
  simp [zero, one, htarget] at ho

 theorem no_transpose_readout_of_coverage_lt {d K : ℕ} (paths : Fin K → Path (d*d))
    (hcard : (covered paths (transposeNat d)).card < d*d)
    (tables : Fin (d*d) → (Fin K → Bool) → Bool) :
    ¬ ∀ (x : Fin (d*d) → Bool) a,
      readout paths tables x a = x ((transposePerm d).symm a) := by
  apply no_readout_of_coverage_lt paths (transposePerm d) _ tables
  have he : covered paths (finiteAct (transposePerm d)) = covered paths (transposeNat d) := by
    unfold covered
    apply congrArg (fun f => Finset.univ.biUnion f)
    funext j
    ext x
    simp only [agreement, Finset.mem_filter, Finset.mem_range]
    constructor <;> rintro ⟨hx, he⟩
    · exact ⟨hx, by simpa only [finiteAct_transposePerm hx] using he⟩
    · exact ⟨hx, by simpa only [finiteAct_transposePerm hx] using he⟩
  rwa [he]

end BitWord.Compiler
