import TapeStorageRates.NativeCoarseMotion

namespace TapeStorageRates.Native

open Transpose MergeDepth

/-- `none` denotes the input head; `some h` denotes work head `h`. -/
def headMove {k : ℕ} (h : Option (Fin k)) (m : Motion k) : Dir :=
  match h with | none => m.1 | some j => m.2.1 j

def headPosition {k : ℕ} (τ : Trace k) (h : Option (Fin k)) (t : ℕ) : ℤ :=
  match h with | none => τ.input t | some j => τ.work j t

def headCarry {k : ℕ} (a : Descriptor k) (h : Option (Fin k)) : Fin 3 :=
  match h with | none => a.1.1 | some j => a.1.2 j

def wordPosition {k : ℕ} (xs : List (Motion k)) (h : Option (Fin k)) (t : ℕ) : ℤ :=
  ((xs.take t).map (fun m => moveInt (headMove h m))).sum

theorem headPosition_succ {k : ℕ} (τ : Trace k) (h : Option (Fin k)) (t : ℕ) :
    headPosition τ h (t+1) = headPosition τ h t +
      (τ t).elim 0 (fun m => moveInt (headMove h m)) := by
  cases h <;> simp [headPosition,Trace.input_succ,Trace.work_succ,
    Trace.inStep,Trace.workStep,headMove]

theorem wordPosition_succ {k : ℕ} (xs : List (Motion k)) (h : Option (Fin k))
    (t : ℕ) (ht : t<xs.length) :
    wordPosition xs h (t+1) = wordPosition xs h t + moveInt (headMove h xs[t]) := by
  unfold wordPosition
  rw [List.take_succ_eq_append_getElem ht]
  simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,
    List.sum_cons,List.sum_nil,add_zero]

theorem replay_head_position {k s : ℕ} (r : Fin s) (as : List (Descriptor k))
    (h : Option (Fin k)) (t : ℕ) :
    headPosition (replay r as) h t = wordPosition (fineWord s r as) h t := by
  induction t with
  | zero => cases h <;> simp [headPosition,Trace.input_zero,Trace.work_zero,wordPosition]
  | succ t ih =>
    rw [headPosition_succ,ih]
    by_cases ht : t<(fineWord s r as).length
    · rw [wordPosition_succ _ _ _ ht]
      simp [replay,List.getElem?_eq_getElem ht]
    · have le : (fineWord s r as).length≤t := by omega
      have ht1 : (fineWord s r as).length≤t+1 := by omega
      simp only [replay,List.getElem?_eq_none le,Option.elim_none,add_zero,wordPosition,
        List.take_of_length_le le,List.take_of_length_le ht1]

theorem wordPosition_append {k : ℕ} (xs ys : List (Motion k)) (h : Option (Fin k))
    (t : ℕ) :
    wordPosition (xs++ys) h (xs.length+t) =
      wordPosition xs h xs.length + wordPosition ys h t := by
  simp [wordPosition,List.take_append,List.take_of_length_le (Nat.le_add_right _ _)]

theorem wordPosition_initial {k : ℕ} (xs ys : List (Motion k)) (h : Option (Fin k))
    (t : ℕ) (ht : t≤xs.length) : wordPosition (xs++ys) h t = wordPosition xs h t := by
  simp [wordPosition,List.take_append,show t-xs.length=0 by omega]

theorem core_head_moves {k s : ℕ} (hs : 0<s) (a : Descriptor k) (h : Option (Fin k)) :
    (coreMoves s a).map (fun m => moveInt (headMove h m)) = scalarMoves s (headCarry a h) := by
  cases h with
  | none => exact core_input_moves hs a
  | some j => exact core_work_moves hs a j

theorem core_head_position {k s : ℕ} (hs : 0<s) (a : Descriptor k)
    (h : Option (Fin k)) (i : ℕ) (hi : i≤10*s+1) :
    wordPosition (coreMoves s a) h i = fineOffset s (headCarry a h) i := by
  rw [wordPosition,List.map_take,core_head_moves hs a h]
  exact scalarMoves_prefix hs _ i hi

theorem replay_head_cons {k s : ℕ} (hs : 0<s) (r : Fin s) (a : Descriptor k)
    (as : List (Descriptor k)) (h : Option (Fin k)) (t : ℕ) :
    headPosition (replay r (a::as)) h ((10*s+1)+t) =
      (s : ℤ)*moveInt (direction (headCarry a h)) + headPosition (replay r as) h t := by
  rw [replay_head_position,replay_head_position]
  have he : fineWord s r (a::as)=coreMoves s a++fineWord s r as := by
    simp [fineWord,List.append_assoc]
  rw [he,← length_coreMoves hs a,wordPosition_append,length_coreMoves hs a,
    core_head_position hs a h _ le_rfl,fineOffset_end]

theorem replay_head_first {k s : ℕ} (hs : 0<s) (r : Fin s) (a : Descriptor k)
    (as : List (Descriptor k)) (h : Option (Fin k)) (i : ℕ) (hi : i≤10*s+1) :
    headPosition (replay r (a::as)) h i = fineOffset s (headCarry a h) i := by
  rw [replay_head_position]
  have he : fineWord s r (a::as)=coreMoves s a++fineWord s r as := by
    simp [fineWord,List.append_assoc]
  rw [he,wordPosition_initial _ _ _ _ (by simpa [length_coreMoves hs a] using hi)]
  exact core_head_position hs a h i hi

/-- The aligned coarse anchor after `j` complete descriptor batches. -/
def batchAnchor {k : ℕ} (as : List (Descriptor k)) (h : Option (Fin k)) (j : ℕ) : ℤ :=
  ((as.take j).map (fun a => moveInt (direction (headCarry a h)))).sum

theorem batchAnchor_zero {k : ℕ} (as : List (Descriptor k)) (h : Option (Fin k)) :
    batchAnchor as h 0=0 := by simp [batchAnchor]

theorem batchAnchor_cons {k : ℕ} (a : Descriptor k) (as : List (Descriptor k))
    (h : Option (Fin k)) (j : ℕ) :
    batchAnchor (a::as) h (j+1)=moveInt (direction (headCarry a h))+batchAnchor as h j := by
  simp [batchAnchor]

theorem replay_head_batch {k s : ℕ} (hs : 0<s) (r : Fin s) (as : List (Descriptor k))
    (h : Option (Fin k)) (j : ℕ) (hj : j<as.length) (i : ℕ) (hi : i≤10*s+1) :
    headPosition (replay r as) h ((10*s+1)*j+i) =
      (s : ℤ)*batchAnchor as h j + fineOffset s (headCarry as[j] h) i := by
  induction as generalizing j with
  | nil => simp at hj
  | cons a as ih =>
    cases j with
    | zero => simpa [batchAnchor] using replay_head_first hs r a as h i hi
    | succ j =>
      have hj' : j<as.length := by simpa using hj
      rw [show (10*s+1)*(j+1)+i=(10*s+1)+((10*s+1)*j+i) by ring,
        replay_head_cons hs r a as h,ih j hj',batchAnchor_cons]
      simp [mul_add,add_assoc]

theorem replay_head_nil {k s : ℕ} (r : Fin s) (h : Option (Fin k)) (t : ℕ) :
    headPosition (replay r []) h t=0 := by
  rw [replay_head_position]
  cases h <;> simp [wordPosition,fineWord,List.map_take,List.map_ofFn,Function.comp_def,
    headMove,straight,moveInt]

theorem replay_head_drain {k s : ℕ} (hs : 0<s) (r : Fin s) (as : List (Descriptor k))
    (h : Option (Fin k)) (i : ℕ) :
    headPosition (replay r as) h ((10*s+1)*as.length+i) =
      (s : ℤ)*batchAnchor as h as.length := by
  induction as with
  | nil => simp [replay_head_nil,batchAnchor]
  | cons a as ih =>
    rw [List.length_cons,show (10*s+1)*(as.length+1)+i=
      (10*s+1)+((10*s+1)*as.length+i) by ring,
      replay_head_cons hs r a as h,ih,batchAnchor_cons,mul_add]

end TapeStorageRates.Native
