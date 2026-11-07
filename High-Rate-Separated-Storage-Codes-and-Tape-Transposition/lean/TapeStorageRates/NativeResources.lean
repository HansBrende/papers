import TapeStorageRates.NativeMachine
import TapeStorageRates.ResourceBounds

/-! Uniform resource bounds for the actual finite control. In particular there
is no head-position or input-length field in the simulator. -/

namespace TapeStorageRates.Native

open Transpose

open TapeStorageRates.ResourceBounds

private abbrev RegTuple (M : TM) (s : ℕ) :=
  Fin (M.q+1) × Fin s × (Fin M.k → Fin s) × Cells (Option Bool) s ×
    (Fin M.k → Cells (Fin (M.g+1)) s) × Descriptor M.k ×
    Fin s × (Fin s → Bool) × (Fin s → Bool) × Bool

private def regEquiv (M : TM) (s : ℕ) : Registers M s ≃ RegTuple M s where
  toFun r := (r.q,r.oi,r.ow,r.inp,r.wrk,r.desc,r.pendingLen,r.pending,r.toEmit,r.stopped)
  invFun := fun ⟨a,b,c,d,e,f,g,h,i,j⟩ => ⟨a,b,c,d,e,f,g,h,i,j⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem registers_bound (M : TM) : expBound (fun s => Fintype.card (Registers M s)) := by
  apply exp_mono (exp_mul (exp_const (M.q+1)) (exp_mul exp_self
    (exp_mul (exp_pow exp_self M.k) (exp_mul (exp_array 3 3)
    (exp_mul (exp_pow (exp_array (M.g+1) 3) M.k) (exp_mul (exp_const (2*3^(M.k+1)))
    (exp_mul exp_self (exp_mul (exp_array 2 1) (exp_mul (exp_array 2 1) (exp_const 2))))))))))
  intro s hs
  rw [Fintype.card_congr (regEquiv M s)]
  simp only [RegTuple, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_option, Cells, Nat.one_mul, id_eq]
  norm_num [Descriptor, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

private def phaseCode {s : ℕ} (p : Phase s) : Fin (11*s+2) :=
  match p with
  | .left i => ⟨i.val, by omega⟩
  | .read i => ⟨s+i.val, by omega⟩
  | .table => ⟨4*s, by omega⟩
  | .write i => ⟨4*s+1+i.val, by omega⟩
  | .home i => ⟨7*s+1+i.val, by omega⟩
  | .carry i => ⟨8*s+1+i.val, by omega⟩
  | .emit i => ⟨9*s+1+i.val, by omega⟩
  | .drain i => ⟨10*s+1+i.val, by omega⟩
  | .done => ⟨11*s+1, by omega⟩

private theorem phaseCode_injective {s : ℕ} : Function.Injective (@phaseCode s) := by
  intro p q h
  have e := congrArg Fin.val h
  clear h
  cases p <;> cases q <;> simp only [phaseCode] at e <;>
    first | rfl | (exfalso; omega) | (congr 1; apply Fin.ext; omega)

/-- For every source machine there is one constant independent of s such that
the compiled native machine uses at most K*s bits of finite control. -/
theorem control_bits (M : TM) :
    ∃ K : ℕ, ∀ (s : ℕ) (hs : 0<s), (machine M hs).q+1 ≤ 2^(K*s) := by
  have hp : expBound (fun s => Fintype.card (Phase s)) := by
    apply exp_mono (exp_mul (exp_const 13) exp_self)
    intro s hs
    refine (Fintype.card_le_of_injective _ (@phaseCode_injective s)).trans ?_
    simp only [Fintype.card_fin, id_eq]
    omega
  obtain ⟨K,hK⟩ := exp_mul hp (registers_bound M)
  refine ⟨K,fun s hs => ?_⟩
  let _ : Nonempty (Label M s) := ⟨initialLabel M hs⟩
  have hc : 0 < Fintype.card (Label M s) := Fintype.card_pos
  change Fintype.card (Label M s)-1+1 ≤ _
  rw [Nat.sub_add_cancel hc]
  simpa [Label, Fintype.card_prod] using hK s hs

end TapeStorageRates.Native
