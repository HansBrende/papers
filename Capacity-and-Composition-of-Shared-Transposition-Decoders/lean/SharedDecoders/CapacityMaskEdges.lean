import SharedDecoders.CapacityDifferenceCover
import SharedDecoders.ConstructionBlockRecovery

/-! # Edge budgets for the actual translate-link quotient

The index is an unordered pair of distinct shifts with a chosen orientation.
Repeated graph edges and steps of order two can only increase this budget.
-/

namespace SharedDecoders.CapacityMask

open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d] {κ : Type*}

noncomputable def monochromaticCount (p : ZMod d → κ) (s : ZMod d) : ℕ :=
  Nat.card {c : ZMod d // p (c+s)=p c}

def constantSpace (p : ZMod d → κ) (Δ : Finset (ZMod d)) :
    Submodule ℚ (ZMod d → ℚ) where
  carrier := {x | ∀ c e, Relation.EqvGen (Link p Δ) c e → x c=x e}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy c e hce; exact congrArg₂ (·+·) (hx c e hce) (hy c e hce)
  smul_mem' := by intro a x hx c e hce; exact congrArg (a • ·) (hx c e hce)

noncomputable def constantEquiv (p : ZMod d → κ) (Δ : Finset (ZMod d)) :
    constantSpace p Δ ≃ₗ[ℚ] (LinkComponent p Δ → ℚ) where
  toFun x := Quotient.lift x.1 (fun c e h => x.2 c e h)
  invFun y := ⟨fun c => y (Quotient.mk _ c), fun c e h => congrArg y (Quotient.sound h)⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv y := by funext q; induction q using Quotient.inductionOn with | h c => rfl
  map_add' x y := by funext q; induction q using Quotient.inductionOn with | h c => rfl
  map_smul' a x := by funext q; induction q using Quotient.inductionOn with | h c => rfl

theorem finrank_constantSpace (p : ZMod d → κ) (Δ : Finset (ZMod d)) :
    finrank ℚ (constantSpace p Δ) = componentCount p Δ := by
  rw [(constantEquiv p Δ).finrank_eq, Module.finrank_fintype_fun_eq_card]
  rfl

variable {k : ℕ}

abbrev PairEdges (p : ZMod d → κ) (e : Fin k → ZMod d) :=
  Σ ij : UpperBlocks k, {c : ZMod d // p (c+(e ij.1.2-e ij.1.1))=p c}

noncomputable def incidence (p : ZMod d → κ) (e : Fin k → ZMod d) :
    (ZMod d → ℚ) →ₗ[ℚ] (PairEdges p e → ℚ) where
  toFun x z := x z.2.1 - x (z.2.1+(e z.1.1.2-e z.1.1.1))
  map_add' x y := by funext z; dsimp; ring
  map_smul' a x := by funext z; dsimp; ring

omit [NeZero d] in
theorem incidence_ker (p : ZMod d → κ) (e : Fin k → ZMod d)
    (Δ : Finset (ZMod d)) (hΔ : ∀ s, s∈Δ ↔ ∃ i, e i=s) :
    LinearMap.ker (incidence p e) = constantSpace p Δ := by
  ext x
  constructor
  · intro hx c c' hcc
    have hbase : ∀ c c', Link p Δ c c' → x c=x c' := by
      intro c c' hh
      obtain ⟨hp,s,hs,t,ht,hst⟩ := hh
      obtain ⟨i,rfl⟩ := (hΔ s).mp hs
      obtain ⟨j,rfl⟩ := (hΔ t).mp ht
      rcases lt_trichotomy i j with hij|hij|hij
      · have he : c'+(e j-e i)=c := by linear_combination -hst
        have hm : p (c'+(e j-e i))=p c' := by rw [he]; exact hp
        have hh := congrFun (LinearMap.mem_ker.mp hx) ⟨⟨(i,j),hij⟩,⟨c',hm⟩⟩
        change x c' - x (c'+(e j-e i))=0 at hh
        rw [he] at hh
        exact (sub_eq_zero.mp hh).symm
      · subst j
        exact congrArg x (add_right_cancel hst)
      · have he : c+(e i-e j)=c' := by linear_combination hst
        have hm : p (c+(e i-e j))=p c := by rw [he]; exact hp.symm
        have hh := congrFun (LinearMap.mem_ker.mp hx) ⟨⟨(j,i),hij⟩,⟨c,hm⟩⟩
        change x c - x (c+(e i-e j))=0 at hh
        rw [he] at hh
        exact sub_eq_zero.mp hh
    induction hcc with
    | rel c c' h => exact hbase c c' h
    | refl c => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  · intro hx
    apply LinearMap.mem_ker.mpr
    funext z
    apply sub_eq_zero.mpr
    apply hx _ _ (.rel _ _ ?_)
    refine ⟨z.2.2.symm, e z.1.1.2, (hΔ _).mpr ⟨_,rfl⟩,
      e z.1.1.1, (hΔ _).mpr ⟨_,rfl⟩, ?_⟩
    abel

/-- The graph deficit is bounded by the sum of one oriented step count for
each unordered pair of shifts. -/
theorem component_defect_le_pair_sum (p : ZMod d → κ) (e : Fin k → ZMod d)
    (Δ : Finset (ZMod d)) (hΔ : ∀ s, s∈Δ ↔ ∃ i, e i=s) :
    d ≤ componentCount p Δ + ∑ ij : UpperBlocks k, monochromaticCount p (e ij.1.2-e ij.1.1) := by
  have hr := Submodule.finrank_le (LinearMap.range (incidence p e))
  have hn := LinearMap.finrank_range_add_finrank_ker (incidence p e)
  rw [incidence_ker p e Δ hΔ, finrank_constantSpace] at hn
  simp only [Module.finrank_fintype_fun_eq_card, ZMod.card] at hr hn
  have hc : Fintype.card (PairEdges p e) =
      ∑ ij : UpperBlocks k, monochromaticCount p (e ij.1.2-e ij.1.1) :=
    by simp only [Fintype.card_sigma, monochromaticCount, Nat.card_eq_fintype_card]
  rw [hc] at hr
  omega

theorem component_defect_real_bound (p : ZMod d → κ) (e : Fin k → ZMod d)
    (he : Function.Injective e) (Δ : Finset (ZMod d))
    (hΔ : ∀ s, s∈Δ ↔ ∃ i, e i=s) (A : ℝ)
    (hA : ∀ s : ZMod d, s≠0 → (monochromaticCount p s : ℝ) ≤ A) :
    2*((d : ℝ)-componentCount p Δ) ≤ (k : ℝ)*(k-1)*A := by
  have hsum : (∑ ij : UpperBlocks k, (monochromaticCount p (e ij.1.2-e ij.1.1) : ℝ)) ≤
      Fintype.card (UpperBlocks k)*A := by
    calc
      _ ≤ ∑ _ij : UpperBlocks k, A := Finset.sum_le_sum fun ij _ => hA _ (by
        intro hz
        have heq := he (sub_eq_zero.mp hz)
        exact (ne_of_lt ij.2) heq.symm)
      _ = _ := by simp
  have hd := component_defect_le_pair_sum p e Δ hΔ
  have hd' : (d : ℝ) ≤ componentCount p Δ +
      ∑ ij : UpperBlocks k, (monochromaticCount p (e ij.1.2-e ij.1.1) : ℝ) := by exact_mod_cast hd
  have hc := two_mul_card_upperBlocks k
  have hc' : 2*(Fintype.card (UpperBlocks k) : ℝ)+(k : ℝ)=(k : ℝ)*k := by exact_mod_cast hc
  have hca := congrArg (fun t : ℝ => t*A) hc'
  nlinarith only [hsum, hd', hca]

end SharedDecoders.CapacityMask
