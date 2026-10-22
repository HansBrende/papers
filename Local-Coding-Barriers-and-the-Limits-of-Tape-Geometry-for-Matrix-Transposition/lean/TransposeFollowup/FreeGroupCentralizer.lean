import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic

/-! Cyclic centralizers from native reduced-word letter positions and
Nielsen--Schreier. No centralizer or commutativity premise is assumed. -/
namespace TransposeFollowup.FreeWordFamily
open Classical FreeGroup
set_option autoImplicit false

variable {α : Type*}

theorem letter_eq_of_commute_generator [DecidableEq α] {a : α} {x : FreeGroup α}
    (hcomm : FreeGroup.of a * x = x * FreeGroup.of a) {b : α × Bool} (hb : b ∈ x.toWord) :
    b.1 = a := by
  by_contra hne
  have hi := congrArg (fun y : FreeGroup α => y.toWord.idxOf b) hcomm
  rw [idxOf_toWord_of_mul_eq x hne, idxOf_toWord_mul_of_eq x hne hb] at hi
  split_ifs at hi with hh
  · have hpos : x.toWord.idxOf b ≠ 0 := by
      intro hz
      rcases (List.idxOf_eq_zero_iff_eq_nil_or_head_eq b).mp hz with he | he
      · simp only [he, List.not_mem_nil] at hb
      · have hba : b = (a, false) := Option.some.inj (he.symm.trans hh)
        exact hne (congrArg Prod.fst hba)
    omega
  · omega

theorem isCyclic_of_central_nonidentity {G : Type*} [Group G] [IsFreeGroup G]
    {a : G} (ha : a ≠ 1) (hcentral : ∀ x : G, x * a = a * x) : IsCyclic G := by
  let e := IsFreeGroup.toFreeGroup G
  have hne : e a ≠ 1 := by
    intro he
    exact ha (e.injective (by simpa only [_root_.map_one] using he))
  have hw : (e a).toWord ≠ [] := by
    exact fun hz => hne (FreeGroup.toWord_eq_nil_iff.mp hz)
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ hw
  have hletter (i : IsFreeGroup.Generators G) : b.1 = i := by
    apply letter_eq_of_commute_generator (x := e a) _ hb
    have h := congrArg e (hcentral (e.symm (FreeGroup.of i)))
    simpa only [_root_.map_mul, MulEquiv.apply_symm_apply] using h
  let : Unique (IsFreeGroup.Generators G) :=
    { default := b.1, uniq := fun i => (hletter i).symm }
  exact isCyclic_of_surjective e.symm e.symm.surjective

theorem centralizer_isCyclic {a : FreeGroup α} (ha : a ≠ 1) :
    IsCyclic (Subgroup.centralizer ({a} : Set (FreeGroup α))) := by
  let H := Subgroup.centralizer ({a} : Set (FreeGroup α))
  have ham : a ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let z : H := ⟨a, ham⟩
  have hz : z ≠ 1 := by
    intro he
    exact ha (congrArg (fun v : H => (v : FreeGroup α)) he)
  apply isCyclic_of_central_nonidentity hz
  intro v
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp v.property

end TransposeFollowup.FreeWordFamily
