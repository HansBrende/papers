import TransposeFollowup.TotalCorrelation
import TransposeFollowup.ConditionalCoordinateEntropy
import TransposeFollowup.FractionalIndependentCover

/-! Shared demanded coordinates, disjoint latent views, and graph covers. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false

/-- A twice-covered tuple contributes at least its entropy to the total
correlation of its local views. -/
theorem conditionalTotalCorrelation_two_cover {Ω κ ε C : Type*}
    [Fintype Ω] [Fintype κ] [DecidableEq κ] [Fintype ε] [DecidableEq ε]
    [Fintype C] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (Z : Ω → ε → Bool) (w : Ω → C)
    (S : κ → Finset ε)
    (hcover : ∀ e, (2 : ℝ) ≤ ∑ j, if e ∈ S j then (1 : ℝ) else 0) :
    conditionalObservationEntropy p Z w ≤
      conditionalTotalCorrelation p (fun x j => bitView (S j) (Z x)) w := by
  have hc := conditionalCoordinateEntropy_cover p hp Z w S 2 hcover
  have hj : conditionalObservationEntropy p (fun x j => bitView (S j) (Z x)) w ≤
      conditionalObservationEntropy p Z w := by
    apply conditionalObservationEntropy_le_of_factorsThrough p hp
    intro x y he
    funext j
    have hz : Z x = Z y := congrArg Prod.snd he
    exact congrArg (bitView (S j)) hz
  dsimp only [conditionalTotalCorrelation, conditionalCoordinateEntropy] at *
  linarith

/-- A shared output tuple obtained twice from disjoint latent views is
bounded by the total correlation of the latent blocks. -/
theorem sharedObservation_conditionalEntropy_le {Ω ι κ α ε C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype α] [Nonempty α] [Fintype ε] [DecidableEq ε]
    [Fintype C] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : Ω → ι → α) (Z : Ω → ε → Bool) (w : Ω → C)
    (R : κ → Finset ι) (S : κ → Finset ε)
    (hR : ∀ i j, i ≠ j → Disjoint (R i) (R j))
    (hcover : ∀ e, (2 : ℝ) ≤ ∑ j, if e ∈ S j then (1 : ℝ) else 0)
    (hdecode : ∀ j, (fun x => bitView (S j) (Z x)).FactorsThrough
      (fun x => (w x, finiteView (R j) (A x)))) :
    conditionalObservationEntropy p Z w ≤ conditionalTotalCorrelation p A w :=
  (conditionalTotalCorrelation_two_cover p hp Z w S hcover).trans
    (conditionalTotalCorrelation_disjoint_processing_le p hp A _ w R hR hdecode)

theorem twoEndpoint_cover {κ ε : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype ε] [DecidableEq ε]
    (left right : ε → κ) (hne : ∀ e, left e ≠ right e) (e : ε) :
    (2 : ℝ) ≤ ∑ j, if e ∈ Finset.univ.filter
      (fun f => left f = j ∨ right f = j) then (1 : ℝ) else 0 := by
  have he : Finset.univ.filter (fun j => left e = j ∨ right e = j) =
      {left e, right e} := by
    ext j
    simp [eq_comm]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← Finset.sum_filter]
  rw [he]
  simp [hne e]

/-- On an independent vertex set, demands with both endpoints in the set
are controlled by the total correlation of all latent blocks. -/
theorem sharedDemand_independent_set_entropy_le {Ω ι κ α ε C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype α] [Nonempty α] [Fintype ε] [DecidableEq ε]
    [Fintype C] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : Ω → ι → α) (Z : Ω → ε → Bool) (w : Ω → C)
    (R : κ → Finset ι) (left right : ε → κ) (hne : ∀ e, left e ≠ right e)
    (G : SimpleGraph κ)
    (hR : ∀ i j, i ≠ j → ¬ G.Adj i j → Disjoint (R i) (R j))
    (hleft : ∀ e, (fun x => Z x e).FactorsThrough
      (fun x => (w x, finiteView (R (left e)) (A x))))
    (hright : ∀ e, (fun x => Z x e).FactorsThrough
      (fun x => (w x, finiteView (R (right e)) (A x))))
    (V : Finset κ) (hV : G.IsIndepSet (V : Set κ)) :
    conditionalCoordinateEntropy p Z w
      (Finset.univ.filter (fun e => left e ∈ V ∧ right e ∈ V)) ≤
        conditionalTotalCorrelation p A w := by
  classical
  let D := Finset.univ.filter (fun e => left e ∈ V ∧ right e ∈ V)
  let Z' := fun x => bitView D (Z x)
  let R' := fun j => if j ∈ V then R j else ∅
  let S := fun j => Finset.univ.filter (fun e => left e = j ∨ right e = j)
  have hdis : ∀ i j, i ≠ j → Disjoint (R' i) (R' j) := by
    intro i j hij
    by_cases hi : i ∈ V
    · by_cases hj : j ∈ V
      · simp only [R', hi, hj, ite_true]
        exact hR i j hij (hV hi hj hij)
      · simp [R', hj]
    · simp [R', hi]
  have hdecode : ∀ j, (fun x => bitView (S j) (Z' x)).FactorsThrough
      (fun x => (w x, finiteView (R' j) (A x))) := by
    intro j x y he
    have hw : w x = w y := congrArg (fun z : C × (ι → α) => z.1) he
    have hview := congrArg (fun z : C × (ι → α) => z.2) he
    apply (bitView_eq_iff _ _ _).mpr
    intro e heS
    have hinc : left e = j ∨ right e = j := by simpa [S] using heS
    by_cases heD : e ∈ D
    · have hends : left e ∈ V ∧ right e ∈ V := by simpa [D] using heD
      have hj : j ∈ V := hinc.elim (fun h => h ▸ hends.1) (fun h => h ▸ hends.2)
      have hview' : finiteView (R j) (A x) = finiteView (R j) (A y) := by
        simpa only [R', hj, ite_true] using hview
      have hz : Z x e = Z y e := by
        rcases hinc with h | h
        · have hl := hleft e
          rw [h] at hl
          exact hl (Prod.ext hw hview')
        · have hr := hright e
          rw [h] at hr
          exact hr (Prod.ext hw hview')
      simpa only [Z', bitView, heD, ite_true] using hz
    · simp only [Z', bitView, heD, ite_false]
  exact sharedObservation_conditionalEntropy_le p hp A Z' w R' S hdis
    (twoEndpoint_cover left right hne) hdecode

/-- Shared nonedge demands are bounded by an explicit fractional independent-
set cover. The constant is derived from the graph degree, not assumed. -/
theorem sharedDemand_conditionalEntropy_le_fractionalCover {Ω ι κ α ε C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype α] [Nonempty α] [Fintype ε] [DecidableEq ε]
    [Fintype C] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : Ω → ι → α) (Z : Ω → ε → Bool) (w : Ω → C)
    (R : κ → Finset ι) (left right : ε → κ)
    (G : SimpleGraph κ) (K : ℕ)
    (hdegree : ∀ i, G.degree i ≤ K)
    (hne : ∀ e, left e ≠ right e) (hfar : ∀ e, ¬ G.Adj (left e) (right e))
    (hR : ∀ i j, i ≠ j → ¬ G.Adj i j → Disjoint (R i) (R j))
    (hleft : ∀ e, (fun x => Z x e).FactorsThrough
      (fun x => (w x, finiteView (R (left e)) (A x))))
    (hright : ∀ e, (fun x => Z x e).FactorsThrough
      (fun x => (w x, finiteView (R (right e)) (A x)))) :
    conditionalObservationEntropy p Z w ≤
      (16 * ((K : ℝ) + 1)^2) * conditionalTotalCorrelation p A w := by
  obtain ⟨weight, hw, hsum, hind, hcov⟩ :=
    exists_fractional_independent_cover_scaled G K hdegree
  let D := fun V : Finset κ => Finset.univ.filter (fun e => left e ∈ V ∧ right e ∈ V)
  have hc : ∀ e, (1 : ℝ) ≤ ∑ V, if e ∈ D V then weight V else 0 := by
    intro e
    convert hcov (left e) (right e) (hne e) (hfar e) using 1
    apply Finset.sum_congr rfl
    intro V _
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> rfl
  have hcover := conditionalCoordinateEntropy_weighted_cover p hp Z w D weight hw 1 hc
  rw [one_mul] at hcover
  have hterm : ∀ V, weight V * conditionalCoordinateEntropy p Z w (D V) ≤
      weight V * conditionalTotalCorrelation p A w := by
    intro V
    by_cases hpos : 0 < weight V
    · exact mul_le_mul_of_nonneg_left
        (sharedDemand_independent_set_entropy_le p hp A Z w R left right hne G hR
          hleft hright V (hind V hpos)) (hw V)
    · have hz : weight V = 0 := le_antisymm (le_of_not_gt hpos) (hw V)
      simp only [hz, zero_mul, le_refl]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun V _ => hterm V)
  rw [← Finset.sum_mul, hsum] at hs
  exact hcover.trans hs


/-- A deterministic common observation of two disjoint latent views is
bounded by the total correlation of the entire latent family. -/
theorem commonObservation_conditionalEntropy_le {Ω ι α β C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [Fintype C] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : Ω → ι → α) (Z : Ω → β) (w : Ω → C) (R S : Finset ι)
    (hRS : Disjoint R S)
    (hR : Z.FactorsThrough (fun x => (w x, finiteView R (A x))))
    (hS : Z.FactorsThrough (fun x => (w x, finiteView S (A x)))) :
    conditionalObservationEntropy p Z w ≤ conditionalTotalCorrelation p A w := by
  let views : Bool → Finset ι := fun b => if b then R else S
  have hdis : ∀ i j, i ≠ j → Disjoint (views i) (views j) := by
    intro i j hij
    cases i <;> cases j <;> simp_all [views, Disjoint.symm]
  have hlocal : ∀ j : Bool, Z.FactorsThrough
      (fun x => (w x, finiteView (views j) (A x))) := by
    intro j
    cases j
    · exact hS
    · exact hR
  have ht := conditionalTotalCorrelation_disjoint_processing_le p hp A
    (fun x (_ : Bool) => Z x) w views hdis hlocal
  have heq : conditionalObservationEntropy p (fun x (_ : Bool) => Z x) w =
      conditionalObservationEntropy p Z w := by
    apply conditionalObservationEntropy_eq_of_same_fibers p hp
    intro x y _
    exact ⟨fun h => congrFun h false, fun h => funext (fun _ => h)⟩
  simpa only [conditionalTotalCorrelation, Fintype.sum_bool, heq, add_sub_cancel_right] using ht

/-- Summing the common-information bound over receivers gives a second
coefficient, the number of receiver vertices. -/
theorem sharedDemand_conditionalEntropy_le_card {Ω ι κ α ε C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype α] [Nonempty α] [Fintype ε] [DecidableEq ε]
    [Fintype C] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : Ω → ι → α) (Z : Ω → ε → Bool) (w : Ω → C)
    (R : κ → Finset ι) (left right : ε → κ)
    (hdis : ∀ e, Disjoint (R (left e)) (R (right e)))
    (hleft : ∀ e, (fun x => Z x e).FactorsThrough
      (fun x => (w x, finiteView (R (left e)) (A x))))
    (hright : ∀ e, (fun x => Z x e).FactorsThrough
      (fun x => (w x, finiteView (R (right e)) (A x)))) :
    conditionalObservationEntropy p Z w ≤
      (Fintype.card κ : ℝ) * conditionalTotalCorrelation p A w := by
  classical
  let Q := fun j => Finset.univ.filter (fun e => right e = j)
  let sources := fun j => (Q j).biUnion (fun e => R (left e))
  have hsets : ∀ j, Disjoint (R j) (sources j) := by
    intro j
    apply Finset.disjoint_left.mpr
    intro t ht hu
    obtain ⟨e, he, hte⟩ := Finset.mem_biUnion.mp hu
    have hej : right e = j := by simpa only [Q, Finset.mem_filter, Finset.mem_univ, true_and] using he
    exact Finset.disjoint_left.mp (hdis e) hte (hej ▸ ht)
  have hreceiver : ∀ j, (fun x => bitView (Q j) (Z x)).FactorsThrough
      (fun x => (w x, finiteView (R j) (A x))) := by
    intro j x y he
    have hw : w x = w y := congrArg (fun z : C × (ι → α) => z.1) he
    have hv := congrArg (fun z : C × (ι → α) => z.2) he
    apply (bitView_eq_iff _ _ _).mpr
    intro e heQ
    have hej : right e = j := by simpa only [Q, Finset.mem_filter, Finset.mem_univ, true_and] using heQ
    have hr := hright e
    rw [hej] at hr
    exact hr (Prod.ext hw hv)
  have hsource : ∀ j, (fun x => bitView (Q j) (Z x)).FactorsThrough
      (fun x => (w x, finiteView (sources j) (A x))) := by
    intro j x y he
    have hw : w x = w y := congrArg (fun z : C × (ι → α) => z.1) he
    have hv := congrArg (fun z : C × (ι → α) => z.2) he
    apply (bitView_eq_iff _ _ _).mpr
    intro e heQ
    apply hleft e
    apply Prod.ext hw
    apply (finiteView_eq_iff _ _ _).mpr
    intro t ht
    exact (finiteView_eq_iff _ _ _).mp hv t (Finset.mem_biUnion.mpr ⟨e, heQ, ht⟩)
  have hbound : ∀ j, conditionalCoordinateEntropy p Z w (Q j) ≤
      conditionalTotalCorrelation p A w := by
    intro j
    exact commonObservation_conditionalEntropy_le p hp A (fun x => bitView (Q j) (Z x))
      w (R j) (sources j) (hsets j) (hreceiver j) (hsource j)
  have hcover : ∀ e, (1 : ℝ) ≤ ∑ j, if e ∈ Q j then (1 : ℝ) else 0 := by
    intro e
    simp [Q]
  have hc := conditionalCoordinateEntropy_cover p hp Z w Q 1 hcover
  rw [one_mul] at hc
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hbound j)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hc.trans hs

/-- The two independently proved coefficients give their minimum. -/
theorem sharedDemand_conditionalEntropy_le_min {Ω ι κ α ε C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype α] [Nonempty α] [Fintype ε] [DecidableEq ε]
    [Fintype C] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : Ω → ι → α) (Z : Ω → ε → Bool) (w : Ω → C)
    (R : κ → Finset ι) (left right : ε → κ)
    (G : SimpleGraph κ) (K : ℕ)
    (hdegree : ∀ i, G.degree i ≤ K)
    (hne : ∀ e, left e ≠ right e) (hfar : ∀ e, ¬ G.Adj (left e) (right e))
    (hR : ∀ i j, i ≠ j → ¬ G.Adj i j → Disjoint (R i) (R j))
    (hleft : ∀ e, (fun x => Z x e).FactorsThrough
      (fun x => (w x, finiteView (R (left e)) (A x))))
    (hright : ∀ e, (fun x => Z x e).FactorsThrough
      (fun x => (w x, finiteView (R (right e)) (A x)))) :
    conditionalObservationEntropy p Z w ≤
      min (Fintype.card κ : ℝ) (16 * ((K : ℝ) + 1)^2) *
        conditionalTotalCorrelation p A w := by
  have hcard := sharedDemand_conditionalEntropy_le_card p hp A Z w R left right
    (fun e => hR (left e) (right e) (hne e) (hfar e)) hleft hright
  have hgeom := sharedDemand_conditionalEntropy_le_fractionalCover p hp A Z w R left right
    G K hdegree hne hfar hR hleft hright
  by_cases hc : (Fintype.card κ : ℝ) ≤ 16 * ((K : ℝ) + 1)^2
  · rw [min_eq_left hc]
    exact hcard
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hc))]
    exact hgeom

end TransposeFollowup
