import TransposeFollowup.ScheduledWord
import TransposeFollowup.ScheduledTapeAction
import TransposeFollowup.MaskedStrideCell

/-! A bank invariant shared by operation palettes. It records all work
head positions, the decoded bank, reusable scratch and external IO.
The tape/mode/value types are parameters; concrete stages must prove the
invariant and bank dependence before the word theorem applies. -/
namespace TransposeFollowup.BankWord
open Classical FixedTapeCompiler ScheduledTapeAction
set_option autoImplicit false
variable {O T M V : Type*}

structure Interface (T M V : Type*) where
  bank : T
  decode : CopyMachine.Sym Bool → V
  clean : NativeIO.Config T M → Prop

def input (I : Interface T M V) (c : NativeIO.Config T M) (j : ℕ) : V :=
  I.decode (cells c I.bank (c.work.pos I.bank+j))

def Represents (I : Interface T M V) (P : ℕ) (origin c : NativeIO.Config T M) (x : ℕ → V) : Prop :=
  (∀ t, c.work.pos t=origin.work.pos t) ∧
  (∀ j<P, I.decode (cells c I.bank (origin.work.pos I.bank+j))=x j) ∧
  I.clean c ∧ c.inputPos=origin.inputPos ∧ c.outRev=origin.outRev

def Congruent (P : ℕ) (f : (ℕ → V) → ℕ → V) : Prop :=
  ∀ x y, (∀ j<P, x j=y j) → ∀ j<P, f x j=f y j

theorem represents_self (I : Interface T M V) (P : ℕ) (c : NativeIO.Config T M) (hc : I.clean c) :
    Represents I P c c (input I c) := ⟨fun _ => rfl,fun _ _ => rfl,hc,rfl,rfl⟩

theorem represents_step (I : Interface T M V) (P : ℕ) (f : (ℕ → V) → ℕ → V)
    (c d e : NativeIO.Config T M) (x : ℕ → V) (hd : Represents I P c d x)
    (he : Represents I P d e (f (input I d))) (hf : Congruent P f) :
    Represents I P c e (f x) := by
  refine ⟨fun t => (he.1 t).trans (hd.1 t),?_,he.2.2.1,
    he.2.2.2.1.trans hd.2.2.2.1,he.2.2.2.2.trans hd.2.2.2.2⟩
  intro j hj
  have hv := he.2.1 j hj
  rw [hd.1 I.bank] at hv
  refine hv.trans (hf _ _ ?_ j hj)
  intro k hk
  simp only [input,hd.1 I.bank]
  exact hd.2.1 k hk

theorem transform_congr (P : ℕ) (f : O → (ℕ → V) → ℕ → V) (ops : List O)
    (hf : ∀ op ∈ ops, Congruent P (f op)) : Congruent P (ScheduledWord.transform f ops) := by
  intro x y hxy
  exact ScheduledWord.transform_rel f f ops (fun a b => ∀ j<P, a j=b j) x y hxy
    (fun op hop a b hab => hf op hop a b hab)

theorem word_spec (I : Interface T M V) (P : ℕ)
    (run : O → NativeIO.Config T M → NativeIO.Config T M)
    (f : O → (ℕ → V) → ℕ → V) (ops : List O) (c : NativeIO.Config T M) (hc : I.clean c)
    (hrun : ∀ op ∈ ops, ∀ d, I.clean d → Represents I P d (run op d) (f op (input I d)))
    (hf : ∀ op ∈ ops, Congruent P (f op)) :
    Represents I P c (ScheduledWord.transform run ops c) (ScheduledWord.transform f ops (input I c)) := by
  apply ScheduledWord.transform_rel run f ops (Represents I P c) c (input I c) (represents_self I P c hc)
  intro op hop d x hd
  exact represents_step I P (f op) c d (run op d) x hd (hrun op hop d hd.2.2.1) (hf op hop)

def binary : Interface (Fin 2) MaskedStrideCell.Mode Bool :=
  ⟨0,MaskedStrideCell.bit,fun c => ∀ z, cells c 1 z=.blank⟩

end TransposeFollowup.BankWord

namespace TransposeFollowup.BankWord
open FixedTapeCompiler ScheduledTapeAction
set_option autoImplicit false

def symbols {M : Type*} : Interface (Fin 2) M (CopyMachine.Sym Bool) :=
  ⟨0,id,fun c => ∀ z, cells c 1 z=.blank⟩

end TransposeFollowup.BankWord

