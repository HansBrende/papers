import BitWord.ScanAncestry

/-! Separated named demands turn the generic helper injection into a finite
bound for a concrete layered scan program. -/
namespace BitWord
open scoped BigOperators
open Classical
set_option autoImplicit false

/-- Each output bin requests bits from distinct source bins. -/
def BinSpread {n B : ℕ} (tau : Equiv.Perm (Grid n B)) : Prop :=
  ∀ j : Fin n, Function.Injective (fun i : Fin B => (tau.symm (j,i)).1)

/-- At most D demands per output bin can come from its D named ancestor bins. -/
theorem near_demands_card_le {n B : ℕ} (tau : Equiv.Perm (Grid n B))
    (hspread : BinSpread tau) (A : Fin n → Finset (Fin n)) (D : ℕ)
    (hA : ∀ j, (A j).card ≤ D) :
    (Finset.univ.filter (fun v : Grid n B => v.1 ∈ A (tau v).1)).card ≤ n*D := by
  let near := Finset.univ.filter (fun v : Grid n B => v.1 ∈ A (tau v).1)
  let f : near → Σ j : Fin n, A j := fun v =>
    ⟨(tau v).1,⟨v.val.1,(Finset.mem_filter.mp v.property).2⟩⟩
  have hinj : Function.Injective f := by
    intro v w he
    have hh := congrArg (fun z : Σ j : Fin n, A j => (z.1,z.2.val)) he
    have hh' : ((tau v).1,v.val.1)=((tau w).1,w.val.1) := hh
    have hout := congrArg (fun p : Fin n × Fin n => p.1) hh'
    have hinput := congrArg (fun p : Fin n × Fin n => p.2) hh'
    have hsrc : (tau.symm ((tau v).1,(tau v).2)).1 =
        (tau.symm ((tau v).1,(tau w).2)).1 := by
      calc
        _ = v.val.1 := by simp
        _ = w.val.1 := hinput
        _ = _ := by rw [hout]; simp
    have hlane := hspread (tau v).1 hsrc
    exact Subtype.ext (tau.injective (Prod.ext hout hlane))
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_coe,Fintype.card_sigma] at hc
  exact hc.trans ((Finset.sum_le_sum (fun j _ => hA j)).trans_eq (by simp))

namespace ScanProgram
variable {n B q L : ℕ} {State : Type*} [Fintype State]

/-- Finite helper inequality for an actual scan program and a spread target. -/
theorem spread_target_bound (C : ScanProgram n B q L State)
    (V : ∀ t a, PermutationView ((C.layer t).perm a))
    (s : ℕ) (hstate : Fintype.card State ≤ 2^s)
    (out : Fin q) (tau : Equiv.Perm (Grid n B)) (hspread : BinSpread tau)
    (hcorrect : ∀ x p, (C.run x L).1 p out = x (tau.symm p)) :
    (n*B : ℝ) - n*(11*q)^L ≤
      (((11*q)^L+1:ℕ):ℝ) * (C.badVolume V + s*L*n) := by
  let A := C.ancestry V L out
  let ancestors := fun v : Grid n B => A (tau v).1
  let F := Finset.univ.filter (fun v : Grid n B => v.1 ∉ ancestors v)
  have hdet : DeterminesDemands (C.record V) Prod.fst ancestors := by
    intro v x y hr hxy
    have hh := C.run_congr_on_ancestry V x y hr L le_rfl out (tau v).1
      (fun j hj i => hxy (j,i) hj) (tau v).2
    simpa only [Prod.eta,hcorrect,Equiv.symm_apply_apply] using hh
  have hcap : Nat.card (Set.range (C.record V)) ≤
      2^(C.badVolume V + s*L*n) := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_le_of_injective
      (fun z : Set.range (C.record V) => (z.val : C.Record V)) Subtype.val_injective).trans
        (C.record_card_le V s hstate)
  have hboundNat := helper_named_demands_bound (C.record V) Prod.fst ancestors F (fun v _ => hdet v)
    ((11*q)^L) (C.badVolume V + s*L*n)
    (fun v hv => (Finset.mem_filter.mp hv).2)
    (fun v _ => C.ancestry_card V L le_rfl out (tau v).1) hcap
  have hnear := near_demands_card_le tau hspread A ((11*q)^L)
    (fun j => C.ancestry_card V L le_rfl out j)
  have hcount : F.card + (Finset.univ.filter (fun v : Grid n B => v.1 ∈ ancestors v)).card = n*B := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Grid n B))) (p := fun v => v.1 ∉ ancestors v)
    simpa only [not_not,Fintype.card_prod,Fintype.card_fin,Finset.card_univ] using h
  have hn : ((Finset.univ.filter (fun v : Grid n B => v.1 ∈ ancestors v)).card : ℝ) ≤
      (n:ℝ)*(11*q)^L := by exact_mod_cast hnear
  have hc : (F.card : ℝ) + (Finset.univ.filter (fun v : Grid n B => v.1 ∈ ancestors v)).card =
      (n:ℝ)*B := by exact_mod_cast hcount
  have hbound : (F.card : ℝ) ≤ (((11*q)^L+1:ℕ):ℝ) *
      (C.badVolume V + s*L*n) := by exact_mod_cast hboundNat
  push_cast at hbound ⊢
  linarith

end ScanProgram
end BitWord
