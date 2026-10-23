import BitWord.CompilerThreshold

namespace BitWord.Compiler
open Geometry Classical

/-- A fixed-depth, fixed-fanin circuit. Each edge applies an actual permitted
stage; each vertex has an arbitrary public address-dependent Boolean table.
Unrolling a shared circuit into this tree does not increase its depth. -/
inductive Circuit (P q : ℕ) : ℕ → Type
  | leaf (table : Fin P → Bool → Bool) : Circuit P q 0
  | node {L : ℕ} (stage : Fin q → Stage P) (child : Fin q → Circuit P q L)
      (table : Fin P → (Fin q → Bool) → Bool) : Circuit P q (L+1)

def CircuitIndex (q : ℕ) : ℕ → Type
  | 0 => Unit
  | L+1 => Fin q × CircuitIndex q L

instance circuitIndexFintype (q : ℕ) : (L : ℕ) → Fintype (CircuitIndex q L)
  | 0 => inferInstanceAs (Fintype Unit)
  | L+1 => letI := circuitIndexFintype q L
           inferInstanceAs (Fintype (Fin q × CircuitIndex q L))

 theorem circuitIndex_card (q L : ℕ) : Fintype.card (CircuitIndex q L) = q^L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change Fintype.card (Fin q × CircuitIndex q L) = _
    simp [Fintype.card_prod, ih, Nat.pow_succ, Nat.mul_comm]

 theorem endpoint_append {P : ℕ} (s t : Path P) :
     endpoint (s++t) = (endpoint s).trans (endpoint t) := by
   induction s with
   | nil => rfl
   | cons T s ih =>
     simp only [List.cons_append, endpoint, ih]
     rfl

namespace Circuit
variable {P q L : ℕ}

def eval : {L : ℕ} → Circuit P q L → (Fin P → Bool) → Fin P → Bool
  | 0, .leaf table, x, a => table a (x a)
  | _+1, .node stage child table, x, a =>
      table a (fun j => eval (child j) x ((stage j).endpoint.symm a))

def paths : {L : ℕ} → Circuit P q L → CircuitIndex q L → Path P
  | 0, .leaf _, _ => []
  | _+1, .node stage child _, i => paths (child i.1) i.2 ++ [stage i.1]

def table : {L : ℕ} → Circuit P q L → Fin P → (CircuitIndex q L → Bool) → Bool
  | 0, .leaf f, a, v => f a (v ())
  | _+1, .node stage child f, a, v =>
      f a (fun j => table (child j) ((stage j).endpoint.symm a) (fun i => v (j,i)))

 theorem paths_length (C : Circuit P q L) (i : CircuitIndex q L) :
     (C.paths i).length = L := by
   induction C with
   | leaf => rfl
   | node stage child table ih => simp [paths, ih]

/-- Exact semantics, not an assumed dependency certificate: every circuit is a
pointwise readout of the explicitly constructed root-to-leaf permutation paths. -/
 theorem unroll (C : Circuit P q L) (x : Fin P → Bool) (a : Fin P) :
     C.eval x a = C.table a (fun i => x ((endpoint (C.paths i)).symm a)) := by
   induction C generalizing a with
   | leaf => rfl
   | node stage child f ih =>
     simp only [eval, table]
     congr 1
     funext j
     rw [ih j]
     congr 1
     funext i
     change x ((endpoint ((child j).paths i)).symm ((stage j).endpoint.symm a)) =
       x ((endpoint ((child j).paths i ++ [stage j])).symm a)
     rw [endpoint_append]
     rfl

 noncomputable def indexEquiv (q L : ℕ) : CircuitIndex q L ≃ Fin (q^L) :=
   (Fintype.equivFin _).trans (finCongr (circuitIndex_card q L))

 noncomputable def finitePaths (C : Circuit P q L) : Fin (q^L) → Path P :=
   fun j => C.paths ((indexEquiv q L).symm j)

 noncomputable def finiteTable (C : Circuit P q L) : Fin P → (Fin (q^L) → Bool) → Bool :=
   fun a v => C.table a (fun i => v (indexEquiv q L i))

 theorem finite_unroll (C : Circuit P q L) (x : Fin P → Bool) (a : Fin P) :
     C.eval x a = readout C.finitePaths C.finiteTable x a := by
   rw [unroll]
   simp only [readout, finiteTable, finitePaths, Equiv.symm_apply_apply]

/-- The circuit exclusion also holds at every positive dimension divisible by
its fixed path threshold. -/
 theorem no_bounded_circuit_transpose_of_dvd (q L d : ℕ) (hd : 0 < d)
     (hdiv : pathThreshold (q^L) L ∣ d) (C : Circuit (d*d) q L) :
     ¬ ∀ (x : Fin (d*d) → Bool) a,
       C.eval x a = x ((transposePerm d).symm a) := by
   intro hc
   apply no_bounded_path_transpose_of_dvd (q^L) L d hd hdiv C.finitePaths
     (fun j => le_of_eq (C.paths_length _)) C.finiteTable
   intro x a
   rw [← C.finite_unroll]
   exact hc x a

/-- Bounded-depth bounded-fanin circuits, with arbitrary Boolean tables and
actual permitted geometry on every edge, do not compute large bit transposes. -/
 theorem no_bounded_circuit_transpose (q L h : ℕ)
     (hlarge : pathThreshold (q^L) L ≤ 2^h)
     (C : Circuit ((2^h)*(2^h)) q L) :
     ¬ ∀ (x : Fin ((2^h)*(2^h)) → Bool) a,
       C.eval x a = x ((transposePerm (2^h)).symm a) :=
   no_bounded_circuit_transpose_of_dvd q L (2^h) (Nat.pow_pos (by decide))
     (scanScale_dvd_dyadic hlarge) C

end Circuit
end BitWord.Compiler
