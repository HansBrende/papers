import TransposeFollowup.NativeMatchingXorMasks

/-! Exact page-mask values produced by the native opcode demultiplexer. -/
namespace TransposeFollowup.MatchingXorMasksSemantics
open FixedTapeCompiler CopyMachine NativeMatchingXorMaskRow
set_option autoImplicit false
variable {q : ℕ}

theorem writeMany_before (reverse : Bool) (i : ℕ) (xs : List (Bool×Bool))
    (out : Fin q → Tape Bool) (j : Fin q) (hj : j.val < i) :
    NativeMatchingXorMaskRow.writeMany reverse i xs out j=out j := by
  induction xs generalizing i out with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨a,b⟩
    rw [NativeMatchingXorMaskRow.writeMany,ih (i+1) _ (by omega)]
    simp [writeOne,show j.val≠i by omega]

theorem writeMany_at (reverse : Bool) (i : ℕ) (xs : List (Bool×Bool))
    (out : Fin q → Tape Bool) (j : Fin q) (hlo : i≤j.val) (hhi : j.val < i+xs.length) :
    NativeMatchingXorMaskRow.writeMany reverse i xs out j=
      pushed reverse (xs.getD (j.val-i) (false,false)).1 (out j) := by
  induction xs generalizing i out with
  | nil => simp at hhi; omega
  | cons x xs ih =>
    rcases x with ⟨a,b⟩
    by_cases he : j.val=i
    · rw [NativeMatchingXorMaskRow.writeMany,writeMany_before reverse (i+1) xs _ j (by omega)]
      simp [writeOne,he]
    · have hn : i+1≤j.val := by omega
      have hi : j.val < i+1+xs.length := by simp at hhi; omega
      rw [NativeMatchingXorMaskRow.writeMany,ih (i+1) _ hn hi]
      rw [show j.val-i=(j.val-(i+1))+1 by omega,List.getD_cons_succ]
      simp [writeOne,he]

theorem writeMany_row (reverse : Bool) (xs : List (Bool×Bool)) (hx : xs.length=q)
    (out : Fin q → Tape Bool) (j : Fin q) :
    NativeMatchingXorMaskRow.writeMany reverse 0 xs out j=
      pushed reverse (xs.getD j.val (false,false)).1 (out j) := by
  simpa using writeMany_at reverse 0 xs out j (Nat.zero_le _) (by simpa [hx] using j.isLt)

def flags (rows : List (List (Bool×Bool))) (j : Fin q) : List Bool :=
  rows.map (fun xs => (xs.getD j.val (false,false)).1)

def foldPush (reverse : Bool) (xs : List Bool) (t : Tape Bool) : Tape Bool :=
  xs.foldl (fun t b => pushed reverse b t) t

theorem writeMany_rows (reverse : Bool) (rows : List (List (Bool×Bool)))
    (hr : ∀xs∈rows,xs.length=q) (out : Fin q → Tape Bool) (j : Fin q) :
    NativeMatchingXorMasks.writeMany reverse rows out j=foldPush reverse (flags rows j) (out j) := by
  induction rows generalizing out with
  | nil => rfl
  | cons xs rows ih =>
    have hx := hr xs (by simp)
    have ht : ∀x∈rows,x.length=q := by intro x h;exact hr x (by simp [h])
    rw [NativeMatchingXorMasks.writeMany,ih ht,writeMany_row reverse xs hx]
    rfl

def leftOpen (xs : List Bool) : Tape Bool := ⟨[],.blank::symbols xs++[.stop]⟩

theorem push_right (b : Bool) (acc : List Bool) :
    pushed false b (NativeSealBack.openWord acc)=NativeSealBack.openWord (acc++[b]) := by
  simp [pushed,Tape.write,Tape.moveRight,Tape.read,NativeSealBack.openWord,symbols,List.map_append]

theorem push_left (b : Bool) (acc : List Bool) :
    pushed true b (leftOpen acc)=leftOpen (b::acc) := by
  simp [pushed,Tape.write,Tape.moveLeft,leftOpen,symbols]

theorem foldPush_right (xs acc : List Bool) :
    foldPush false xs (NativeSealBack.openWord acc)=NativeSealBack.openWord (acc++xs) := by
  induction xs generalizing acc with
  | nil => simp [foldPush]
  | cons b xs ih =>
    change foldPush false xs (pushed false b (NativeSealBack.openWord acc))=_
    rw [push_right,ih]
    simp [List.append_assoc]

theorem foldPush_left (xs acc : List Bool) :
    foldPush true xs (leftOpen acc)=leftOpen (xs.reverse++acc) := by
  induction xs generalizing acc with
  | nil => simp [foldPush]
  | cons b xs ih =>
    change foldPush true xs (pushed true b (leftOpen acc))=_
    rw [push_left,ih]
    simp [List.reverse_cons,List.append_assoc]

theorem masks_right (rows : List (List (Bool×Bool))) (hr : ∀xs∈rows,xs.length=q)
    (acc : Fin q → List Bool) (j : Fin q) :
    NativeMatchingXorMasks.writeMany false rows (fun j => NativeSealBack.openWord (acc j)) j=
      NativeSealBack.openWord (acc j++flags rows j) := by
  rw [writeMany_rows false rows hr,foldPush_right]

theorem masks_left (rows : List (List (Bool×Bool))) (hr : ∀xs∈rows,xs.length=q)
    (acc : Fin q → List Bool) (j : Fin q) :
    NativeMatchingXorMasks.writeMany true rows (fun j => leftOpen (acc j)) j=
      leftOpen ((flags rows j).reverse++acc j) := by
  rw [writeMany_rows true rows hr,foldPush_left]


theorem row_advance (reverse : Bool) (i n : ℕ)
    (pos : NativeMatchingXorMaskRow.Port q → ℤ) (p : NativeMatchingXorMaskRow.Port q) :
    NativeMatchingXorMaskRow.advanceMany reverse i n pos p = pos p +
      match p with
      | none => 2*n
      | some j => if i≤j.val ∧ j.val < i+n then (if reverse then -1 else 1) else 0 := by
  induction n generalizing i pos with
  | zero => cases p <;> simp [NativeMatchingXorMaskRow.advanceMany]
  | succ n ih =>
    rw [NativeMatchingXorMaskRow.advanceMany,ih]
    cases p with
    | none => simp [NativeMatchingXorMaskRow.advance]; ring
    | some j =>
      simp only [NativeMatchingXorMaskRow.advance]
      by_cases he : j.val=i
      · subst i
        simp [show ¬j.val+1≤j.val by omega]
      · by_cases hl : j.val < i
        · have h1 : ¬i+1≤j.val := by omega
          have h2 : ¬i≤j.val := by omega
          simp [he,h1,h2]
        · have h1 : i+1≤j.val := by omega
          have h2 : i≤j.val := by omega
          have hr : (j.val < i+1+n) ↔ (j.val < i+(n+1)) := by omega
          simp [he,h1,h2,hr]

theorem row_advance_complete (reverse : Bool) (pos : NativeMatchingXorMaskRow.Port q → ℤ) :
    NativeMatchingXorMaskRow.advanceMany reverse 0 q pos =
      fun p => pos p + match p with | none => 2*q | some _ => if reverse then -1 else 1 := by
  funext p
  rw [row_advance]
  cases p with
  | none => rfl
  | some j => simp [j.isLt]

theorem masks_advance (reverse : Bool) (n : ℕ) (pos : NativeMatchingXorMasks.Port q → ℤ) :
    NativeMatchingXorMasks.advanceMany reverse n pos = fun p => pos p +
      match p with
      | none => 0
      | some none => 2*q*n
      | some (some _) => (if reverse then -1 else 1)*(n:ℤ) := by
  induction n generalizing pos with
  | zero => funext p; cases p with
    | none => simp [NativeMatchingXorMasks.advanceMany]
    | some p => cases p <;> simp [NativeMatchingXorMasks.advanceMany]
  | succ n ih =>
    rw [NativeMatchingXorMasks.advanceMany,ih]
    funext p
    cases p with
    | none => simp [NativeMatchingXorMasks.advance]
    | some p =>
      simp only [NativeMatchingXorMasks.advance,row_advance_complete]
      cases p <;> push_cast <;> ring

end TransposeFollowup.MatchingXorMasksSemantics
