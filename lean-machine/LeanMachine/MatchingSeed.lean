import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Order.Minimal
import Mathlib.Order.Preorder.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# One matching endpoint meeting every extra-helper trap

Minimal traps of a loopless helper relation with at most one helper per
vertex are disjoint and have at least two vertices. Hall's theorem assigns
them distinct matching pairs, even with one prescribed endpoint reserved.
-/

namespace LeanMachine.MatchingSeed

open Finset
open scoped BigOperators

set_option autoImplicit false

variable {V : Type*} [DecidableEq V]

/-- Every vertex of a nonempty trap has an extra helper inside the trap. -/
def IsTrap (f : V → Finset V) (D : Finset V) : Prop :=
  D.Nonempty ∧ ∀ v ∈ D, (f v ∩ D).Nonempty

theorem IsTrap.card_two_le {f : V → Finset V} {D : Finset V}
    (hD : IsTrap f D) (hself : ∀ v, v ∉ f v) : 2 ≤ D.card := by
  obtain ⟨v, hv⟩ := hD.1
  obtain ⟨w, hw⟩ := hD.2 v hv
  have hwv : w ≠ v := by
    intro he
    exact hself v (he ▸ (mem_inter.mp hw).1)
  have hc : ({v, w} : Finset V) ⊆ D := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hv
    · exact (mem_inter.mp hw).2
  simpa [hwv, Ne.symm hwv] using card_le_card hc

theorem IsTrap.inter {f : V → Finset V} {D E : Finset V}
    (hcard : ∀ v, (f v).card ≤ 1) (hD : IsTrap f D) (hE : IsTrap f E)
    (hne : (D ∩ E).Nonempty) : IsTrap f (D ∩ E) := by
  refine ⟨hne, ?_⟩
  intro v hv
  obtain ⟨x, hx⟩ := hD.2 v (mem_inter.mp hv).1
  obtain ⟨y, hy⟩ := hE.2 v (mem_inter.mp hv).2
  have hxy : x = y := card_le_one.mp (hcard v)
    x (mem_inter.mp hx).1 y (mem_inter.mp hy).1
  refine ⟨x, mem_inter.mpr ⟨(mem_inter.mp hx).1, mem_inter.mpr ?_⟩⟩
  exact ⟨(mem_inter.mp hx).2, hxy.symm ▸ (mem_inter.mp hy).2⟩

theorem minimal_traps_disjoint {f : V → Finset V}
    (hcard : ∀ v, (f v).card ≤ 1) {D E : Finset V}
    (hD : Minimal (IsTrap f) D) (hE : Minimal (IsTrap f) E) (hne : D ≠ E) :
    Disjoint D E := by
  rw [disjoint_iff_inter_eq_empty]
  by_contra h
  have ht := hD.1.inter hcard hE.1 (nonempty_iff_ne_empty.mpr h)
  exact hne ((hD.eq_of_ge ht inter_subset_left).trans
    (hE.eq_of_ge ht inter_subset_right).symm)

theorem exists_minimal_trap {f : V → Finset V} {D : Finset V}
    (hD : IsTrap f D) : ∃ E ⊆ D, Minimal (IsTrap f) E :=
  exists_minimal_le_of_wellFoundedLT (IsTrap f) D hD

private def pair (m : V → V) (v : V) : Finset V := {v, m v}

private theorem pair_mate (m : V → V) (hm : Function.Involutive m) (v : V) :
    pair m (m v) = pair m v := by simp [pair, hm v, pair_comm]

variable [Fintype V]

/-- Extend any choice containing at most one matching endpoint per pair. -/
theorem extend_seed (m : V → V) (hm : Function.Involutive m)
    (hfixed : ∀ v, m v ≠ v) (R : Finset V)
    (hR : ∀ v ∈ R, m v ∉ R) :
    ∃ S : Finset V, R ⊆ S ∧ (∀ v, v ∈ S ↔ m v ∉ S) ∧
      2 * S.card = Fintype.card V := by
  classical
  obtain ⟨S, hRS, hmax⟩ := exists_maximal_ge_of_wellFoundedGT
    (fun S : Finset V => ∀ v ∈ S, m v ∉ S) R hR
  have hone : ∀ v, v ∈ S ↔ m v ∉ S := by
    intro v
    refine ⟨hmax.1 v, ?_⟩
    intro hmv
    by_contra hv
    have hi : ∀ w ∈ insert v S, m w ∉ insert v S := by
      intro w hw
      rcases mem_insert.mp hw with hwv | hw
      · subst w
        intro hh
        rcases mem_insert.mp hh with he | he
        · exact hfixed v he
        · exact hmv he
      · intro hmw
        rcases mem_insert.mp hmw with hmv' | hmw
        · have hwv : w = m v := by simpa only [hm w] using congrArg m hmv'
          exact hmv (hwv ▸ hw)
        · exact hmax.1 w hw hmw
    have hsub := hmax.2 hi (subset_insert v S)
    exact hv (hsub (mem_insert_self v S))
  have himage : S.image m = Sᶜ := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
      exact mem_compl.mpr ((hone w).mp hw)
    · intro hv
      have hmS : m v ∈ S := (hone (m v)).mpr (by simpa only [hm v] using mem_compl.mp hv)
      exact mem_image.mpr ⟨m v, hmS, hm v⟩
  have hc := card_image_of_injective S hm.injective
  rw [himage] at hc
  have htot := S.card_add_card_compl
  exact ⟨S, hRS, hone, by omega⟩

/-- Choose exactly one endpoint of every matching pair, retaining a
prescribed endpoint and meeting every nonempty extra-helper trap. -/
theorem exists_seed (m : V → V) (hm : Function.Involutive m)
    (hfixed : ∀ v, m v ≠ v) (f : V → Finset V)
    (hcard : ∀ v, (f v).card ≤ 1) (hself : ∀ v, v ∉ f v) (s : V) :
    ∃ S : Finset V, 2 * S.card = Fintype.card V ∧ s ∈ S ∧
      (∀ v, v ∈ S ↔ m v ∉ S) ∧
      ∀ D, IsTrap f D → (S ∩ D).Nonempty := by
  classical
  let I := {D : Finset V // Minimal (IsTrap f) D ∧ s ∉ D}
  let t : I → Finset (Finset V) := fun D => (D.val.image (pair m)).erase (pair m s)
  have hhall : ∀ J : Finset I, J.card ≤ (J.biUnion t).card := by
    intro J
    let U := J.biUnion (fun D => D.val)
    let P := J.biUnion t
    have hdis : (J : Set I).PairwiseDisjoint (fun D => D.val) := by
      intro D _ E _ hne
      exact minimal_traps_disjoint hcard D.property.1 E.property.1
        (fun he => hne (Subtype.ext he))
    have hlow : 2 * J.card ≤ U.card := by
      dsimp only [U]
      rw [card_biUnion hdis]
      calc
        2 * J.card = ∑ _D ∈ J, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ D ∈ J, D.val.card := sum_le_sum fun D _ =>
          D.property.1.1.card_two_le hself
    have hcover : U ⊆ insert (m s) (P.biUnion id) := by
      intro v hv
      obtain ⟨D, hDJ, hvD⟩ := mem_biUnion.mp hv
      by_cases hvms : v = m s
      · exact mem_insert.mpr (Or.inl hvms)
      have hvns : v ≠ s := fun he => D.property.2 (he ▸ hvD)
      have hpne : pair m v ≠ pair m s := by
        intro he
        have hvp : v ∈ pair m s := he ▸ (mem_insert_self v {m v})
        simp only [pair, mem_insert, mem_singleton] at hvp
        exact hvp.elim hvns hvms
      have hpt : pair m v ∈ t D := mem_erase.mpr
        ⟨hpne, mem_image.mpr ⟨v, hvD, rfl⟩⟩
      exact mem_insert.mpr (Or.inr (mem_biUnion.mpr
        ⟨pair m v, mem_biUnion.mpr ⟨D, hDJ, hpt⟩, mem_insert_self v {m v}⟩))
    have hup : (P.biUnion id).card ≤ P.card * 2 := by
      apply card_biUnion_le_card_mul P id 2
      intro p hp
      obtain ⟨D, _, hpD⟩ := mem_biUnion.mp hp
      obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_of_mem_erase hpD)
      exact Finset.card_le_two
    have hu := (card_le_card hcover).trans (card_insert_le _ _)
    change J.card ≤ P.card
    omega
  obtain ⟨g, hginj, hg⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  have hex : ∀ D : I, ∃ v, v ∈ D.val ∧ pair m v = g D := by
    intro D
    exact mem_image.mp (mem_of_mem_erase (hg D))
  choose r hr hrpair using hex
  have hrreserved : ∀ D, pair m (r D) ≠ pair m s := by
    intro D
    rw [hrpair D]
    exact (mem_erase.mp (hg D)).1
  have hrms : ∀ D, r D ≠ m s := by
    intro D he
    exact hrreserved D (by rw [he, pair_mate m hm s])
  have hrsep : ∀ D E, m (r D) ≠ r E := by
    intro D E he
    have hge : g D = g E := by
      rw [← hrpair D, ← hrpair E, ← pair_mate m hm (r D), he]
    have hDE := hginj hge
    subst E
    exact hfixed (r D) he
  let R := insert s (univ.image r)
  have hR : ∀ v ∈ R, m v ∉ R := by
    intro v hv hmv
    rcases mem_insert.mp hv with hvs | hv
    · subst v
      rcases mem_insert.mp hmv with he | he
      · exact hfixed s he
      · obtain ⟨D, _, hD⟩ := mem_image.mp he
        exact hrms D hD
    · obtain ⟨D, _, rfl⟩ := mem_image.mp hv
      rcases mem_insert.mp hmv with he | he
      · exact hrms D (by simpa only [hm (r D)] using congrArg m he)
      · obtain ⟨E, _, hE⟩ := mem_image.mp he
        exact hrsep D E hE.symm
  obtain ⟨S, hRS, hone, hsize⟩ := extend_seed m hm hfixed R hR
  have hsS : s ∈ S := hRS (mem_insert_self s _)
  refine ⟨S, hsize, hsS, hone, ?_⟩
  intro D hD
  obtain ⟨E, hED, hE⟩ := exists_minimal_trap hD
  by_cases hsE : s ∈ E
  · exact ⟨s, mem_inter.mpr ⟨hsS, hED hsE⟩⟩
  · let i : I := ⟨E, hE, hsE⟩
    refine ⟨r i, mem_inter.mpr ⟨?_, hED (hr i)⟩⟩
    exact hRS (mem_insert_of_mem (mem_image.mpr ⟨i, mem_univ _, rfl⟩))

end LeanMachine.MatchingSeed

#print axioms LeanMachine.MatchingSeed.extend_seed
#print axioms LeanMachine.MatchingSeed.exists_seed
