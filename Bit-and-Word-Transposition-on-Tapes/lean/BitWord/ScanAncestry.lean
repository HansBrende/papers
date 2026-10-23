import BitWord.ScanTrace
import BitWord.HelperInjection

/-! Actual layered computations, one global record, and public original-bin ancestry.
The geometry interface is discharged separately for the admitted permutation grammar. -/
namespace BitWord
open scoped BigOperators
open Classical
set_option autoImplicit false

/-- Good predecessors of the endpoint permutation, at one fixed aligned scale. -/
structure PermutationView {n B : ℕ} (pi : Equiv.Perm (Grid n B)) where
  bad : Finset (Grid n B)
  pred : Fin n → Finset (Fin n)
  pred_card : ∀ j, (pred j).card ≤ 11
  good_pred : ∀ p, pi.symm p ∉ bad → (pi.symm p).1 ∈ pred p.1

structure ScanLayer (n B q : ℕ) (State : Type*) where
  perm : Fin q → Equiv.Perm (Grid n B)
  scan : Scan n B q State

namespace ScanLayer
variable {n B q : ℕ} {State : Type*}
def permuted (C : ScanLayer n B q State) (x : Banks n B q) : Banks n B q :=
  fun p a => x ((C.perm a).symm p) a

def apply (C : ScanLayer n B q State) (x : Banks n B q × State) : Banks n B q × State :=
  (C.scan.output (C.permuted x.1) x.2, C.scan.terminal (C.permuted x.1) x.2)
end ScanLayer

/-- Input banks are copies of the same source, or fixed public constants.
The single state is carried through all layers, including their scan boundaries. -/
structure ScanProgram (n B q L : ℕ) (State : Type*) where
  copyInput : Fin q → Bool
  constants : Banks n B q
  initialState : State
  layer : Fin L → ScanLayer n B q State

namespace ScanProgram
variable {n B q L : ℕ} {State : Type*}

def initial (C : ScanProgram n B q L State) (x : Grid n B → Bool) : Banks n B q × State :=
  (fun p a => if C.copyInput a then x p else C.constants p a, C.initialState)

def run (C : ScanProgram n B q L State) (x : Grid n B → Bool) : ℕ → Banks n B q × State
  | 0 => C.initial x
  | t+1 => if ht : t < L then (C.layer ⟨t,ht⟩).apply (C.run x t) else C.run x t

variable (C : ScanProgram n B q L State)
variable (V : ∀ t a, PermutationView ((C.layer t).perm a))

abbrev BadRecord := ∀ t : Fin L, ∀ a : Fin q, (V t a).bad → Bool
abbrev StateRecord := Fin L → Fin n → State
abbrev Record := C.BadRecord V × StateRecord (n := n) (L := L) (State := State)

noncomputable def record (x : Grid n B → Bool) : C.Record V :=
  (fun t a p => (C.run x t.val).1 p a,
   fun t => (C.layer t).scan.boundaryRecord
     ((C.layer t).permuted (C.run x t.val).1) (C.run x t.val).2)

noncomputable def ancestry (C : ScanProgram n B q L State)
    (V : ∀ t a, PermutationView ((C.layer t).perm a)) : ℕ → Fin q → Fin n → Finset (Fin n)
  | 0, _, j => {j}
  | t+1, a, j => if ht : t < L then
      Finset.univ.biUnion (fun a' : Fin q =>
        ((V ⟨t,ht⟩ a').pred j).biUnion (fun k => C.ancestry V t a' k))
    else C.ancestry V t a j

/-- Actual reconstruction follows by induction through permutation predecessors
and the proved entering-state replay of each nonlinear scan. -/
theorem run_congr_on_ancestry (x y : Grid n B → Bool) (hrecord : C.record V x = C.record V y)
    (t : ℕ) (ht : t ≤ L) (a : Fin q) (j : Fin n)
    (hxy : ∀ k ∈ C.ancestry V t a j, ∀ i, x (k,i)=y (k,i)) :
    ∀ i, (C.run x t).1 (j,i) a = (C.run y t).1 (j,i) a := by
  induction t generalizing a j with
  | zero =>
    intro i
    have he := hxy j (by simp [ancestry]) i
    simp only [run,initial]
    split <;> simp_all
  | succ t ih =>
    have ht' : t < L := by omega
    simp only [run, dite_eq_left ht']
    let layer := C.layer ⟨t,ht'⟩
    have hboundary : layer.scan.boundaryRecord (layer.permuted (C.run x t).1) (C.run x t).2 =
        layer.scan.boundaryRecord (layer.permuted (C.run y t).1) (C.run y t).2 :=
      congrFun (congrArg Prod.snd hrecord) ⟨t,ht'⟩
    have hlocal : ∀ i, layer.permuted (C.run x t).1 (j,i) =
        layer.permuted (C.run y t).1 (j,i) := by
      intro i
      funext a'
      let p := (layer.perm a').symm (j,i)
      change (C.run x t).1 p a' = (C.run y t).1 p a'
      by_cases hp : p ∈ (V ⟨t,ht'⟩ a').bad
      · exact congrFun (congrFun (congrFun (congrArg Prod.fst hrecord) ⟨t,ht'⟩) a') ⟨p,hp⟩
      · apply ih (by omega) a' p.1
        intro k hk i'
        apply hxy k _ i'
        simp only [ancestry,dite_eq_left ht',Finset.mem_biUnion,Finset.mem_univ,true_and]
        exact ⟨a',p.1,(V ⟨t,ht'⟩ a').good_pred (j,i) hp,hk⟩
    intro i
    exact congrFun (layer.scan.output_congr_of_record _ _ _ _ j hboundary hlocal i) a

/-- Uniform ancestry size, independent of data and helper values. -/
theorem ancestry_card (t : ℕ) (ht : t ≤ L) (a : Fin q) (j : Fin n) :
    (C.ancestry V t a j).card ≤ (11*q)^t := by
  induction t generalizing a j with
  | zero => simp [ancestry]
  | succ t ih =>
    have ht' : t < L := by omega
    simp only [ancestry,dite_eq_left ht']
    apply (Finset.card_biUnion_le).trans
    calc
      _ ≤ ∑ a' : Fin q, 11 * (11*q)^t := by
        apply Finset.sum_le_sum
        intro a' _
        apply (Finset.card_biUnion_le).trans
        calc
          _ ≤ ∑ k ∈ (V ⟨t,ht'⟩ a').pred j, (11*q)^t :=
            Finset.sum_le_sum (fun k _ => ih (by omega) a' k)
          _ = ((V ⟨t,ht'⟩ a').pred j).card * (11*q)^t := by simp
          _ ≤ 11 * (11*q)^t := Nat.mul_le_mul_right _ ((V ⟨t,ht'⟩ a').pred_card j)
      _ = _ := by simp; ring

noncomputable def badVolume : ℕ := ∑ t : Fin L, ∑ a : Fin q, (V t a).bad.card

/-- The actual record has at most the advertised number of values. -/
theorem record_card_le [Fintype State] (s : ℕ) (hstate : Fintype.card State ≤ 2^s) :
    Fintype.card (C.Record V) ≤ 2^(C.badVolume V + s*L*n) := by
  have hbad : Fintype.card (C.BadRecord V) = 2^(C.badVolume V) := by
    simp [BadRecord,Fintype.card_pi,Finset.prod_pow_eq_pow_sum,badVolume]
  have hs : Fintype.card (StateRecord (n := n) (L := L) (State := State)) ≤
      2^(s*L*n) := by
    simp only [StateRecord,Fintype.card_fun,Fintype.card_fin]
    calc
      _ ≤ ((2^s)^n)^L := Nat.pow_le_pow_left (Nat.pow_le_pow_left hstate _ ) _
      _ = _ := by simp only [← pow_mul]; congr 1; ring
  rw [Fintype.card_prod,hbad,pow_add]
  exact Nat.mul_le_mul_left _ hs

end ScanProgram
end BitWord
