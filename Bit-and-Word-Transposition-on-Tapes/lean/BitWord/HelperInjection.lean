import BitWord.HelperSelection
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Range

/-! A single global helper must distinguish a public zero-complement subcube.
No independence of helper fields or linearity of the local decoders is assumed. -/
namespace BitWord
open scoped BigOperators
open Classical
set_option autoImplicit false

noncomputable def zeroExtend {V : Type*} (S : Finset V) (x : S → Bool) : V → Bool :=
  fun v => if hv : v ∈ S then x ⟨v,hv⟩ else false

@[simp] theorem zeroExtend_on {V : Type*} (S : Finset V) (x : S → Bool) (v : S) :
    zeroExtend S x v = x v := by simp [zeroExtend]

@[simp] theorem zeroExtend_off {V : Type*} (S : Finset V) (x : S → Bool) (v : V)
    (hv : v ∉ S) : zeroExtend S x v = false := by simp [zeroExtend,hv]

/-- Each named bit can be determined from the helper and its publicly specified
source bins. This is a pairwise statement, so no decoder is supplied as an oracle. -/
def DeterminesDemands {V J H : Type*} (helper : (V → Bool) → H)
    (bin : V → J) (ancestors : V → Finset J) : Prop :=
  ∀ v x y, helper x = helper y →
    (∀ w, bin w ∈ ancestors v → x w = y w) → x v = y v

/-- Local determination is required only for the named demands being counted. -/
def DeterminesDemandsOn {V J H : Type*} (F : Finset V) (helper : (V → Bool) → H)
    (bin : V → J) (ancestors : V → Finset J) : Prop :=
  ∀ v ∈ F, ∀ x y, helper x = helper y →
    (∀ w, bin w ∈ ancestors v → x w = y w) → x v = y v

/-- Rank increase makes the selected dependencies acyclic; equal helper values
recover all selected input bits by descending source-bin rank. -/
theorem ordered_helper_injective {V J H : Type*} {N : ℕ} [Fintype V]
    (helper : (V → Bool) → H) (bin : V → J) (ancestors : V → Finset J)
    (F : Finset V) (hdet : DeterminesDemandsOn F helper bin ancestors) (rank : J → Fin N) :
    Function.Injective (fun x : orderSelected F bin ancestors rank → Bool =>
      helper (zeroExtend (orderSelected F bin ancestors rank) x)) := by
  intro x y he
  let S := orderSelected F bin ancestors rank
  have hrec (t : ℕ) : ∀ v : S, N - (rank (bin v)).val = t → x v = y v := by
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro v ht
      have hv := (mem_orderSelected F bin ancestors rank v).mp v.property
      have hd := hdet v hv.1 (zeroExtend S x) (zeroExtend S y) he
      have hxy : ∀ w, bin w ∈ ancestors v → zeroExtend S x w = zeroExtend S y w := by
        intro w hw
        by_cases hs : w ∈ S
        · have hlt := hv.2 (bin w) hw
          have hvlt := (rank (bin v)).isLt
          have hh := ih (N - (rank (bin w)).val) (by omega) ⟨w,hs⟩ rfl
          simpa only [zeroExtend, dite_eq_left hs] using hh
        · simp only [zeroExtend, dite_eq_right hs]
      simpa only [zeroExtend_on] using hd hxy
  funext v
  exact hrec _ v rfl

/-- The same global range budget bounds every acyclically selected subcube. -/
theorem ordered_card_le_helper_budget {V J H : Type*} {N : ℕ} [Fintype V]
    (helper : (V → Bool) → H) (bin : V → J) (ancestors : V → Finset J)
    (F : Finset V) (hdet : DeterminesDemandsOn F helper bin ancestors) (h : ℕ)
    (hcap : Nat.card (Set.range helper) ≤ 2^h) (rank : J → Fin N) :
    (orderSelected F bin ancestors rank).card ≤ h := by
  let S := orderSelected F bin ancestors rank
  let f : (S → Bool) → Set.range helper := fun x => ⟨helper (zeroExtend S x),⟨_,rfl⟩⟩
  have hinj : Function.Injective f := by
    intro x y he
    exact ordered_helper_injective helper bin ancestors F hdet rank (congrArg Subtype.val he)
  have hc := (Fintype.card_le_of_injective f hinj).trans
    (show Fintype.card (Set.range helper) ≤ 2^h by simpa only [Nat.card_eq_fintype_card] using hcap)
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hc
  exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hc

/-- Sharp uniform-degree named-demand bound. Only the named demands need local
recovery; input assignments range over the full Boolean cube. The helper range
is charged once, with no linearity or independent-field assumption. -/
theorem helper_named_demands_bound {V J H : Type*} [Fintype V] [Fintype J]
    (helper : (V → Bool) → H) (bin : V → J) (ancestors : V → Finset J)
    (F : Finset V) (hdet : DeterminesDemandsOn F helper bin ancestors) (D h : ℕ)
    (hfar : ∀ v ∈ F, bin v ∉ ancestors v)
    (hdegree : ∀ v ∈ F, (ancestors v).card ≤ D)
    (hcap : Nat.card (Set.range helper) ≤ 2^h) :
    F.card ≤ (D+1)*h :=
  far_card_le_of_orderSelected_card_le F bin ancestors D h hfar hdegree
    (fun e => ordered_card_le_helper_budget helper bin ancestors F hdet h hcap e)

end BitWord
