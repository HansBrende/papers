import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Tactic

/-! Linear recovery on an arrangement and its images. Component maps are
supplied explicitly. Passing to an image constructs new maps using linear
sections; it does not assume that old maps descend through a quotient. -/

namespace LeanMachine.SubspaceRecovery

open Module Finset
open scoped BigOperators

variable {ι K W Z : Type*} [Fintype ι] [Field K]
  [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]

/-- A row decomposes the inclusion of its coordinate space into maps whose
images lie in the other specified coordinate spaces. Zeros encode missing ports. -/
structure Recovery (U : ι → Submodule K W) where
  component : ∀ v, ι → U v →ₗ[K] W
  target : ∀ v u, LinearMap.range (component v u) ≤ U u
  sum_eq : ∀ v, ∑ u, component v u = (U v).subtype

theorem Recovery.reconstruct {U : ι → Submodule K W} (r : Recovery U)
    (v : ι) (x : U v) : ∑ u, r.component v u x = (x : W) := by
  simpa using LinearMap.congr_fun (r.sum_eq v) x

/-- A row is contained in any subspace containing all its component images. -/
theorem Recovery.row_le {U : ι → Submodule K W} (r : Recovery U) (v : ι)
    (S : Submodule K W) (h : ∀ u, LinearMap.range (r.component v u) ≤ S) : U v ≤ S := by
  intro x hx
  have heq : x = ∑ u, r.component v u ⟨x, hx⟩ := (r.reconstruct v ⟨x, hx⟩).symm
  rw [heq]
  exact S.sum_mem fun u _ => h u (LinearMap.mem_range_self _ _)

theorem Recovery.partial_sum_mem {U : ι → Submodule K W} (r : Recovery U)
    (v : ι) (x : U v) (S : Submodule K W) (hx : (x : W) ∈ S)
    (F : Finset ι) (hrest : ∀ u ∉ F, r.component v u x ∈ S) :
    (∑ u ∈ F, r.component v u x) ∈ S := by
  classical
  have hknown : (∑ u ∈ univ \ F, r.component v u x) ∈ S :=
    S.sum_mem (fun u hu => hrest u (mem_sdiff.mp hu).2)
  have hsplit : (∑ u ∈ F, r.component v u x) +
      (∑ u ∈ univ \ F, r.component v u x) = ∑ u, r.component v u x := by
    simpa only [univ_inter] using sum_inter_add_sum_sdiff univ F (fun u => r.component v u x)
  apply (S.add_mem_iff_left hknown).mp
  rw [hsplit, r.reconstruct]
  exact hx

/-- If a row and all but one component lie in a subspace, so does the remaining component. -/
theorem Recovery.component_range_le_of_rest {U : ι → Submodule K W}
    (r : Recovery U) (v u : ι) (S : Submodule K W) (hv : U v ≤ S)
    (hrest : ∀ w, w ≠ u → LinearMap.range (r.component v w) ≤ S) :
    LinearMap.range (r.component v u) ≤ S := by
  classical
  rintro _ ⟨x, rfl⟩
  simpa only [Finset.sum_singleton] using r.partial_sum_mem v x S (hv x.property) {u}
    (fun w hw => hrest w (by simpa only [mem_singleton] using hw)
      (LinearMap.mem_range_self _ _))

/-- The restriction to a coordinate surjects onto its actual image. -/
def imageMap (f : W →ₗ[K] Z) (U : Submodule K W) : U →ₗ[K] U.map f :=
  (f.comp U.subtype).codRestrict (U.map f) (fun x => ⟨x, x.property, rfl⟩)

@[simp] theorem imageMap_val (f : W →ₗ[K] Z) (U : Submodule K W) (x : U) :
    (imageMap f U x : Z) = f (x : W) := rfl

theorem imageMap_surjective (f : W →ₗ[K] Z) (U : Submodule K W) :
    Function.Surjective (imageMap f U) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := y.property
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- Every image arrangement has recoveries with no increase in any component
rank. This includes arbitrary ambient quotients and arbitrary graph supports. -/
theorem Recovery.image [FiniteDimensional K W] {U : ι → Submodule K W}
    (r : Recovery U) (f : W →ₗ[K] Z) :
    ∃ r' : Recovery (fun v => (U v).map f),
      (∀ v u, r.component v u = 0 → r'.component v u = 0) ∧
      (∀ v u, finrank K (LinearMap.range (r'.component v u)) ≤
        finrank K (LinearMap.range (r.component v u))) := by
  classical
  have hs : ∀ v, ∃ s : (U v).map f →ₗ[K] U v,
      (imageMap f (U v)).comp s = LinearMap.id := fun v =>
    (imageMap f (U v)).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (imageMap_surjective f (U v)))
  choose s hs using hs
  let r' : Recovery (fun v => (U v).map f) :=
    { component := fun v u => f.comp ((r.component v u).comp (s v))
      target := by
        intro v u y hy
        obtain ⟨x, rfl⟩ := hy
        exact ⟨r.component v u (s v x), r.target v u ⟨s v x, rfl⟩, rfl⟩
      sum_eq := by
        intro v
        ext x
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply]
        change (∑ u, f (r.component v u (s v x))) = (x : Z)
        rw [← map_sum, r.reconstruct]
        exact congrArg Subtype.val (LinearMap.congr_fun (hs v) x) }
  refine ⟨r', ?_, ?_⟩
  · intro v u hz
    change f.comp ((r.component v u).comp (s v)) = 0
    simp [hz]
  · intro v u
    change finrank K (LinearMap.range (f.comp ((r.component v u).comp (s v)))) ≤ _
    rw [LinearMap.range_comp]
    exact (Submodule.finrank_map_le f _).trans
      (Submodule.finrank_mono (LinearMap.range_comp_le_range (s v) (r.component v u)))

/-- Restrict an arrangement to an actually closed ambient subspace. Unlike
an image construction, this uses the supplied maps themselves on the restriction. -/
theorem Recovery.restrict [FiniteDimensional K W] {U : ι → Submodule K W}
    (r : Recovery U) (S : Submodule K W)
    (hclosed : ∀ v u (x : U v), (x : W) ∈ S → r.component v u x ∈ S) :
    ∃ r' : Recovery (fun v => (U v).comap S.subtype),
      (∀ v u, r.component v u = 0 → r'.component v u = 0) ∧
      (∀ v u, finrank K (LinearMap.range (r'.component v u)) ≤
        finrank K (LinearMap.range (r.component v u))) := by
  let d : ∀ v, (U v).comap S.subtype →ₗ[K] U v := fun v =>
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let c : ∀ v, ι → (U v).comap S.subtype →ₗ[K] S := fun v u =>
    ((r.component v u).comp (d v)).codRestrict S
      (fun x => hclosed v u (d v x) x.val.property)
  have hc : ∀ v u, S.subtype.comp (c v u) = (r.component v u).comp (d v) := by
    intro v u
    rfl
  let r' : Recovery (fun v => (U v).comap S.subtype) :=
    { component := c
      target := by
        intro v u y hy
        obtain ⟨x, rfl⟩ := hy
        exact r.target v u (LinearMap.mem_range_self _ _)
      sum_eq := by
        intro v
        ext x
        change S.subtype ((∑ u, c v u) x) = x.val.val
        simp only [LinearMap.sum_apply, map_sum]
        exact r.reconstruct v (d v x) }
  refine ⟨r', ?_, ?_⟩
  · intro v u hz
    ext x
    change r.component v u (d v x) = 0
    rw [hz, LinearMap.zero_apply]
  · intro v u
    change finrank K (LinearMap.range (c v u)) ≤ _
    rw [← Submodule.finrank_map_subtype_eq S (LinearMap.range (c v u)),
      ← LinearMap.range_comp, hc]
    exact Submodule.finrank_mono (LinearMap.range_comp_le_range (d v) (r.component v u))

section Dimensions

variable [FiniteDimensional K W]

omit [Fintype ι] in
theorem finrank_finset_sup_le (s : Finset ι) (U : ι → Submodule K W) :
    finrank K (s.sup U : Submodule K W) ≤ ∑ v ∈ s, finrank K (U v) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert v s hv ih =>
    rw [Finset.sup_insert, sum_insert hv]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

omit [FiniteDimensional K W] in
/-- The actual row images span a space containing the recovered coordinate. -/
theorem Recovery.le_row_span {U : ι → Submodule K W} (r : Recovery U)
    (v : ι) (s : Finset ι) (hs : ∀ u ∉ s, r.component v u = 0) :
    U v ≤ s.sup (fun u => LinearMap.range (r.component v u)) := by
  intro x hx
  have heq : x = ∑ u, r.component v u ⟨x, hx⟩ := (r.reconstruct v ⟨x, hx⟩).symm
  rw [heq]
  apply Submodule.sum_mem
  intro u _
  by_cases hu : u ∈ s
  · exact (Finset.le_sup (f := fun u => LinearMap.range (r.component v u)) hu)
      (LinearMap.mem_range_self _ _)
  · simp [hs u hu]

/-- A nonzero coordinate disjoint from every other coordinate cannot equal
the span of its row images. -/
theorem Recovery.strict_row_span {U : ι → Submodule K W} (r : Recovery U)
    (hdisj : Pairwise (fun u v => Disjoint (U u) (U v)))
    (hdiag : ∀ v, r.component v v = 0) (v : ι) (hv : U v ≠ ⊥)
    (s : Finset ι) (hs : ∀ u ∉ s, r.component v u = 0) :
    finrank K (U v) < finrank K
      (s.sup (fun u => LinearMap.range (r.component v u)) : Submodule K W) := by
  classical
  let P := s.sup (fun u => LinearMap.range (r.component v u))
  have hle : U v ≤ P := r.le_row_span v s hs
  by_contra hn
  change ¬ finrank K (U v) < finrank K P at hn
  have heq : U v = P := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hz : ∀ u ∈ s, LinearMap.range (r.component v u) = ⊥ := by
    intro u hu
    by_cases huv : u = v
    · subst u
      rw [hdiag, LinearMap.range_zero]
    · have hi : LinearMap.range (r.component v u) ≤ U v :=
        (Finset.le_sup (f := fun u => LinearMap.range (r.component v u)) hu).trans_eq heq.symm
      exact le_bot_iff.mp ((le_inf hi (r.target v u)).trans_eq (hdisj (Ne.symm huv)).eq_bot)
  have hP : P = ⊥ := by
    apply le_bot_iff.mp
    exact Finset.sup_le fun u hu => (hz u hu).le
  exact hv (heq.trans hP)

/-- If distinct coordinate spaces are disjoint, recovering a nonzero coordinate
requires strictly more total image dimension than the coordinate itself. -/
theorem Recovery.strict_row_dimension {U : ι → Submodule K W} (r : Recovery U)
    (hdisj : Pairwise (fun u v => Disjoint (U u) (U v)))
    (hdiag : ∀ v, r.component v v = 0) (v : ι) (hv : U v ≠ ⊥)
    (s : Finset ι) (hs : ∀ u ∉ s, r.component v u = 0) :
    finrank K (U v) < ∑ u ∈ s, finrank K (LinearMap.range (r.component v u)) :=
  (r.strict_row_span hdisj hdiag v hv s hs).trans_le (finrank_finset_sup_le s _)

end Dimensions

end LeanMachine.SubspaceRecovery
