import SharedDecoders.CapacityClosure
import SharedDecoders.ConstructionSymmetric

/-! The symmetric-copy source has extensive scalar-closure defect. -/

namespace SharedDecoders.CapacityClosure

open Module CapacityIntervals
open scoped BigOperators

variable {d b : ℕ} [NeZero d]

noncomputable def supportedSymmetric (S : Finset (ZMod d)) :
    Submodule Bit (BinaryState d b) := symmetricSpace ⊓ rowSpace S

noncomputable def supportedSymmetricEquiv (S : Finset (ZMod d)) :
    supportedSymmetric S (b := b) ≃ₗ[Bit]
      symmetricSpace (F := Bit) (A := Fin b → Bit) (I := S) := by
  classical
  exact
    { toFun := fun X => ⟨fun i j => X.1 i.1 j.1, fun i j => X.2.1 i.1 j.1⟩
      invFun := fun Y => ⟨fun i j => if hi : i ∈ S then
          if hj : j ∈ S then Y.1 ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0, by
        constructor
        · intro i j
          by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp only [hi,hj,↓reduceDIte]
          exact Y.2 _ _
        · intro i hi
          funext j
          simp [hi]⟩
      left_inv := fun X => by
        apply Subtype.ext
        funext i j
        by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
        · simp [hi,hj]
        · simp only [hi, hj, ↓reduceDIte]
          rw [X.2.1 i j]
          exact (congrFun (X.2.2 j hj) i).symm
        · simp only [hi, ↓reduceDIte]
          exact (congrFun (X.2.2 i hi) j).symm
        · simp only [hi, ↓reduceDIte]
          exact (congrFun (X.2.2 i hi) j).symm
      right_inv := fun Y => by apply Subtype.ext; funext i j; simp
      map_add' := fun X Y => rfl
      map_smul' := fun a X => rfl }

omit [NeZero d] in
theorem twice_finrank_supportedSymmetric (S : Finset (ZMod d)) :
    2*finrank Bit (supportedSymmetric S (b := b)) = S.card*(S.card+1)*b := by
  rw [(supportedSymmetricEquiv S).finrank_eq]
  simpa using two_mul_finrank_symmetricSpace (F := Bit) (A := Fin b → Bit) (I := S)

noncomputable def diagonalUnit (c : ZMod d) (l : Fin b) : BinaryState d b :=
  fun i j t => if i=c ∧ j=c ∧ t=l then 1 else 0

omit [NeZero d] in
theorem diagonalUnit_mem {S : Finset (ZMod d)} {c : ZMod d} (hc : c ∈ S) (l : Fin b) :
    diagonalUnit c l ∈ supportedSymmetric S := by
  classical
  constructor
  · intro i j
    funext t
    simp only [diagonalUnit]
    by_cases hi : i=c <;> by_cases hj : j=c <;> simp [hi,hj]
  · intro i hi
    funext j t
    have hne : i ≠ c := fun he => hi (he ▸ hc)
    simp [diagonalUnit, hne]

theorem fieldEncode_diagonalUnit (c : ZMod d) (l : Fin b) :
    fieldEncode d (diagonalUnit c l) =
      Pi.single c (Pi.single l (phase d (-c) (normalElement d))) := by
  classical
  funext i t
  by_cases hi : i=c <;> by_cases ht : t=l
  · subst i; subst t
    simp [fieldEncode_apply, rowEncode_apply, diagonalUnit]
  · subst i
    simp [fieldEncode_apply, rowEncode_apply, diagonalUnit, ht]
  · simp [fieldEncode_apply, rowEncode_apply, diagonalUnit, hi]
  · simp [fieldEncode_apply, rowEncode_apply, diagonalUnit, hi]

theorem scalarHull_supportedSymmetric (S : Finset (ZMod d)) :
    scalarHull (supportedSymmetric S (b := b)) = rowSpace S := by
  classical
  apply le_antisymm (scalarHull_le_rowSpace inf_le_right)
  intro X hX
  let H := scalarHull (supportedSymmetric S (b := b))
  have hsingle (c : ZMod d) (l : Fin b) :
      (fieldEncode d).symm (Pi.single c (Pi.single l (fieldEncode d X c l))) ∈ H := by
    by_cases hc : c ∈ S
    · let eta := phase d (-c) (normalElement d)
      have heta : eta ≠ 0 := by
        intro he
        exact normalElement_ne_zero ((phase d (-c)).injective (he.trans (map_zero _).symm))
      have hm := (scalarHull_stable (supportedSymmetric S (b := b)))
        (fieldEncode d X c l / eta) (diagonalUnit c l)
        (le_scalarHull _ (diagonalUnit_mem hc l))
      have heq : scalarMul (fieldEncode d X c l / eta) (diagonalUnit c l) =
          (fieldEncode d).symm (Pi.single c (Pi.single l (fieldEncode d X c l))) := by
        apply (fieldEncode d).injective
        rw [fieldEncode_scalarMul, fieldEncode_diagonalUnit, LinearEquiv.apply_symm_apply]
        funext i t
        by_cases hi : i=c <;> by_cases ht : t=l
        · subst i; subst t
          simp [eta, Pi.smul_apply, div_mul_cancel₀ _ heta]
        · subst i
          simp [ht]
        · simp [hi]
        · simp [hi]
      rwa [heq] at hm
    · have hz : fieldEncode d X c l = 0 := by
        have hh := (fieldEncode_row_zero_iff X c).mpr (hX c hc)
        exact congrFun hh l
      simp only [hz, Pi.single_zero, map_zero]
      exact H.zero_mem
  have hsum : (∑ c : ZMod d, ∑ l : Fin b,
      (fieldEncode d).symm (Pi.single c (Pi.single l (fieldEncode d X c l)))) ∈ H :=
    H.sum_mem (fun c _ => H.sum_mem (fun l _ => hsingle c l))
  have heq : (∑ c : ZMod d, ∑ l : Fin b,
      (fieldEncode d).symm (Pi.single c (Pi.single l (fieldEncode d X c l)))) = X := by
    apply (fieldEncode d).injective
    simp only [map_sum, LinearEquiv.apply_symm_apply]
    have hinner (c : ZMod d) :
        (∑ l : Fin b, (Pi.single c (Pi.single l (fieldEncode d X c l)) : FieldState d b)) =
          (Pi.single c (fieldEncode d X c) : FieldState d b) := by
      funext i t
      by_cases hi : i=c
      · subst i
        simpa only [Finset.sum_apply, Pi.single_eq_same] using
          congrFun (Finset.univ_sum_single (fieldEncode d X c)) t
      · simp [hi]
    rw [Finset.sum_congr rfl (fun c _ => hinner c)]
    exact Finset.univ_sum_single (fieldEncode d X)
  rwa [heq] at hsum

theorem twice_defect_supportedSymmetric (S : Finset (ZMod d)) :
    2*defect (supportedSymmetric S (b := b)) + S.card*(S.card+1)*b =
      2*(S.card*d*b) := by
  have hd := hull_dimension (supportedSymmetric S (b := b))
  rw [scalarHull_supportedSymmetric, finrank_rowSpace] at hd
  have hs := twice_finrank_supportedSymmetric (b := b) S
  omega

omit [NeZero d] in
/-- The identity column output is correct on every symmetric input, whatever
receiver partition is declared. -/
theorem symmetric_isSharedCode {κ : Type*} (p : ZMod d → κ) :
    IsSharedCode Bit p (symmetricSpace (A := Fin b → Bit)) := by
  refine ⟨fun _ Y i => Y i 0, ?_⟩
  intro X hX c
  funext i
  change X c i = X i (0+c)
  simpa using hX c i

theorem symmetric_residual_eq {p : ZMod d → Bool} {r : Bool → ZMod d}
    (hr : ∀ a, p (r a) = a) :
    residual (symmetricSpace (A := Fin b → Bit)) p r = supportedSymmetric (residualRows r) := by
  apply le_antisymm
  · exact le_inf inf_le_left (residual_le_rows _ hr)
  · intro X hX
    refine ⟨hX.1, (mem_classProjection_ker hr).mpr ?_⟩
    intro a
    apply hX.2 (r a)
    cases a <;> simp [residualRows]

/-- Exact bit dimensions of the symmetric-copy residual and its scalar hull.
The defect is extensive even though copying needs no nontrivial decoder. -/
theorem symmetric_copy_defect {p : ZMod d → Bool} {r : Bool → ZMod d}
    (hr : ∀ a, p (r a) = a) :
    let L := residual (symmetricSpace (F := Bit) (A := Fin b → Bit)) p r
    (2*finrank Bit L = b*(d-2)*(d-1)) ∧
    (finrank Bit (scalarHull L) = b*d*(d-2)) ∧
    (2*defect L = b*(d-2)*(d+1)) := by
  dsimp only
  rw [symmetric_residual_eq hr]
  have hc := residual_rows_card hr
  have hdim := twice_finrank_supportedSymmetric (b := b) (residualRows r)
  have hdef := twice_defect_supportedSymmetric (b := b) (residualRows r)
  have hc' : (residualRows r).card = d-2 := by omega
  rw [scalarHull_supportedSymmetric, finrank_rowSpace]
  have hd : 2 ≤ d := by omega
  have hd₁ : d-1 = (residualRows r).card+1 := by omega
  constructor
  · rw [hdim, ← hc', hd₁]
    ring
  constructor
  · rw [← hc']
    ring
  · rw [← hc']
    have alg (n z w : ℕ) (hn : n+2=z) :
        2*(n*z*w) = n*(n+1)*w+w*n*(z+1) := by rw [← hn]; ring
    have hrhs := alg (residualRows r).card d b hc
    rw [hrhs] at hdef
    omega

end SharedDecoders.CapacityClosure
