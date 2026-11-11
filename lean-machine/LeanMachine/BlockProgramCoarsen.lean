import LeanMachine.BlockProgramExports

/-! Grouping original raw owners changes only which raw block is supplied to
an operation. Restriction recovers the original input; the evaluated program
and every resident state and dated value remain identical. -/

namespace LeanMachine.BlockProgram

variable {O I S A : Type*} {R : O → Type*} {R' : I → Type*}

def coarsen (p : BlockProgram O R S A) (group : O → I)
    (restrict : (o : O) → R' (group o) → R o) : BlockProgram I R' S A where
  initial := p.initial
  constant := p.constant
  owner := group ∘ p.owner
  reads := p.reads
  earlier := p.earlier
  update t s r v := p.update t s (restrict (p.owner t) r) v

theorem coarsen_eval (p : BlockProgram O R S A) (group : O → I)
    (restrict : (o : O) → R' (group o) → R o) (x : (i : I) → R' i) (t : ℕ) :
    (p.coarsen group restrict).eval x t = p.eval (fun o => restrict o (x (group o))) t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    conv_lhs => rw [eval_eq]
    conv_rhs => rw [eval_eq]
    change p.update t _ _ _ = p.update t _ _ _
    congr 1
    · split_ifs with ht
      · rfl
      · rw [ih (t - 1) (by omega)]
    · funext j
      exact congrArg Prod.snd (ih j.val (p.earlier t j.val j.property))

end LeanMachine.BlockProgram
