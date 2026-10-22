import TransposeFollowup.MaskedStrideGroupSemantics

/-! Cross-group semantics for the single-buffer masked scan. The initial
bank is read through its actual absolute cells. A blank-decoding scratch
buffer supplies zero boundary values. Both prefix and difference modes
preserve the original bank operands until their own group is processed. -/
namespace TransposeFollowup.MaskedStrideScan
open Classical FixedTapeCompiler
open CopyMachine (Sym)
open MaskedStrideCell (Mode State bit)
open MaskedStrideGroup (cells)
set_option autoImplicit false

def input (c : State) (j : ℕ) : Bool := bit (cells c 0 (c.work.pos 0+j))

def buffer (isPrefix : Bool) (mask x : ℕ → Bool) (S : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | r+1, j => MaskedStrideCell.stored isPrefix (mask (r*S+j)) (x (r*S+j))
      (buffer isPrefix mask x S r j)

def output (isPrefix : Bool) (mask x : ℕ → Bool) (S r j : ℕ) : Bool :=
  MaskedStrideCell.output (mask (r*S+j)) (x (r*S+j)) (buffer isPrefix mask x S r j)

theorem buffer_succ (isPrefix : Bool) (mask x : ℕ → Bool) (S r j : ℕ) :
    buffer isPrefix mask x S (r+1) j=
      if isPrefix then output isPrefix mask x S r j else x (r*S+j) := rfl

structure AtGroup (isPrefix : Bool) (mask : ℕ → Bool) (S : ℕ) (c₀ : State)
    (r : ℕ) (c : State) : Prop where
  bank_pos : c.work.pos 0=c₀.work.pos 0+(r*S : ℕ)
  scratch_pos : c.work.pos 1=c₀.work.pos 1
  past : ∀ i < r, ∀ j < S,
    cells c 0 (c₀.work.pos 0+(i*S+j : ℕ))=.data (output isPrefix mask (input c₀) S i j)
  future : ∀ z, c₀.work.pos 0+(r*S : ℕ) ≤ z → cells c 0 z=cells c₀ 0 z
  scratch : ∀ j < S, bit (cells c 1 (c₀.work.pos 1+j))=buffer isPrefix mask (input c₀) S r j

theorem at_zero (isPrefix : Bool) (mask : ℕ → Bool) (S : ℕ) (c : State)
    (hzero : ∀ j < S, bit (cells c 1 (c.work.pos 1+j))=false) :
    AtGroup isPrefix mask S c 0 c := by
  refine ⟨by simp, rfl, ?_, fun _ _ => rfl, hzero⟩
  intro i hi
  omega

theorem AtGroup.written {isPrefix : Bool} {mask : ℕ → Bool} {S r : ℕ} {c₀ c : State}
    (h : AtGroup isPrefix mask S c₀ r c) (j : ℕ) (hj : j < S) (t : Fin 2) :
    MaskedStrideGroup.written isPrefix (fun j => mask (r*S+j)) c j t=
      if t=0 then output isPrefix mask (input c₀) S r j
      else buffer isPrefix mask (input c₀) S (r+1) j := by
  have hx : bit (cells c 0 (c.work.pos 0+j))=input c₀ (r*S+j) := by
    rw [h.bank_pos,show c₀.work.pos 0+(r*S : ℕ)+(j : ℕ)=c₀.work.pos 0+(r*S+j : ℕ) by push_cast; ring]
    rw [h.future _ (by push_cast; omega)]
    rfl
  have hp : bit (cells c 1 (c.work.pos 1+j))=buffer isPrefix mask (input c₀) S r j := by
    rw [h.scratch_pos]
    exact h.scratch j hj
  simp only [MaskedStrideGroup.written,hx,hp,output,buffer]

theorem AtGroup.result_written {isPrefix : Bool} {mask : ℕ → Bool} {S r g : ℕ}
    {c₀ c : State} (h : AtGroup isPrefix mask S c₀ r c) (hg : g ≤ S)
    (w : List Bool) (j : ℕ) (hj : j < g) (t : Fin 2) :
    cells (MaskedStrideGroup.result isPrefix (fun j => mask (r*S+j)) S g w c)
      t (c.work.pos t+j)=.data (if t=0 then output isPrefix mask (input c₀) S r j
        else buffer isPrefix mask (input c₀) S (r+1) j) := by
  rw [MaskedStrideGroup.result_written (isPrefix:=isPrefix) (mask:=fun j => mask (r*S+j)) hg w c t j hj,h.written j (by omega) t]

theorem AtGroup.step {isPrefix : Bool} {mask : ℕ → Bool} {S r : ℕ} {c₀ c : State}
    (h : AtGroup isPrefix mask S c₀ r c) (w : List Bool) :
    AtGroup isPrefix mask S c₀ (r+1)
      (MaskedStrideGroup.result isPrefix (fun j => mask (r*S+j)) S S w c) := by
  have hpos := MaskedStrideGroup.result_positions (isPrefix:=isPrefix)
    (mask:=fun j => mask (r*S+j)) (S:=S) (g:=S) le_rfl w c
  refine ⟨?_, hpos.2.trans h.scratch_pos, ?_, ?_, ?_⟩
  · rw [hpos.1,h.bank_pos]
    push_cast
    ring
  · intro i hi j hj
    by_cases hir : i=r
    · subst i
      have he := h.result_written (g:=S) le_rfl w j hj 0
      simpa [h.bank_pos,Nat.cast_add,add_assoc] using he
    · have hi' : i < r := by omega
      rw [MaskedStrideGroup.result_outside (isPrefix:=isPrefix) (mask:=fun j => mask (r*S+j)) le_rfl w c 0 _
        (Or.inl (by
          rw [h.bank_pos]
          have ht : (i*S+j : ℕ)<r*S := by nlinarith
          omega))]
      exact h.past i hi' j hj
  · intro z hz
    rw [MaskedStrideGroup.result_outside (isPrefix:=isPrefix) (mask:=fun j => mask (r*S+j)) le_rfl w c 0 z
      (Or.inr (by rw [h.bank_pos]; push_cast at hz ⊢; nlinarith))]
    exact h.future z (by push_cast at hz ⊢; nlinarith)
  · intro j hj
    have he := h.result_written (g:=S) le_rfl w j hj 1
    simpa [h.scratch_pos,bit] using congrArg bit he

def groups (isPrefix : Bool) (mask : ℕ → Bool) (S : ℕ) (w : List Bool)
    (c : State) : ℕ → State
  | 0 => c
  | r+1 => MaskedStrideGroup.result isPrefix (fun j => mask (r*S+j)) S S w
      (groups isPrefix mask S w c r)

theorem groups_invariant (isPrefix : Bool) (mask : ℕ → Bool) (S : ℕ) (w : List Bool)
    (c : State) (hzero : ∀ j < S, bit (cells c 1 (c.work.pos 1+j))=false) (r : ℕ) :
    AtGroup isPrefix mask S c r (groups isPrefix mask S w c r) := by
  induction r with
  | zero => exact at_zero isPrefix mask S c hzero
  | succ r ih => exact ih.step w

/-- After full groups and any final partial group, all earlier groups and
the real part of the last group contain the prescribed scan output. -/
theorem partial_correct (isPrefix : Bool) (mask : ℕ → Bool) {S g : ℕ} (hg : g ≤ S)
    (w : List Bool) (c : State) (hzero : ∀ j < S, bit (cells c 1 (c.work.pos 1+j))=false)
    (r : ℕ) :
    let d := groups isPrefix mask S w c r
    let e := MaskedStrideGroup.result isPrefix (fun j => mask (r*S+j)) S g w d
    e.work.pos 0=c.work.pos 0+(r*S+g : ℕ) ∧ e.work.pos 1=c.work.pos 1 ∧
    (∀ i < r, ∀ j < S, cells e 0 (c.work.pos 0+(i*S+j : ℕ))=
      .data (output isPrefix mask (input c) S i j)) ∧
    (∀ j < g, cells e 0 (c.work.pos 0+(r*S+j : ℕ))=
      .data (output isPrefix mask (input c) S r j)) ∧
    (∀ z, c.work.pos 0+(r*S+g : ℕ) ≤ z → cells e 0 z=cells c 0 z) := by
  dsimp only
  have h := groups_invariant isPrefix mask S w c hzero r
  have hpos := MaskedStrideGroup.result_positions (isPrefix:=isPrefix)
    (mask:=fun j => mask (r*S+j)) hg w (groups isPrefix mask S w c r)
  refine ⟨?_,hpos.2.trans h.scratch_pos,?_,?_,?_⟩
  · rw [hpos.1,h.bank_pos]
    push_cast
    ring
  · intro i hi j hj
    rw [MaskedStrideGroup.result_outside (isPrefix:=isPrefix) (mask:=fun j => mask (r*S+j)) hg w _ 0 _
      (Or.inl (by
          rw [h.bank_pos]
          have ht : (i*S+j : ℕ)<r*S := by nlinarith
          omega))]
    exact h.past i hi j hj
  · intro j hj
    have he := h.result_written hg w j hj 0
    simpa [h.bank_pos,Nat.cast_add,add_assoc] using he
  · intro z hz
    rw [MaskedStrideGroup.result_outside (isPrefix:=isPrefix) (mask:=fun j => mask (r*S+j)) hg w _ 0 z
      (Or.inr (by rw [h.bank_pos]; push_cast at hz ⊢; omega))]
    exact h.future z (by push_cast at hz ⊢; omega)

end TransposeFollowup.MaskedStrideScan
