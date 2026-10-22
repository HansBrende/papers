import TransposeFollowup.InPlaceAdd
import TransposeFollowup.NativeClosedStream

/-! Specification of the paid row consumer: true flags select fixed-width
pairs, and a real repeated-addition word is advanced once per input flag.
No arithmetic operation here is charged as a primitive machine step. -/
namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def targets : List Bool → ℕ → List ℕ
  | [], _ => []
  | b::bs, j => (if b then [j] else []) ++ targets bs (j+1)

def records (row unit : List Bool) : List Bool → List Bool → List (List Bool × List Bool)
  | [], _ => []
  | b::bs, j => (if b then [(row,j)] else []) ++ records row unit bs (RepeatedAdd.addWord j unit)

def encoded (row unit flags j : List Bool) : List Bool :=
  (records row unit flags j).flatMap (fun p => p.1 ++ p.2)

def after (unit flags j : List Bool) : List Bool := RepeatedAdd.repeatWord unit flags.length j

theorem records_length (row unit flags j : List Bool) :
    (records row unit flags j).length = flags.count true := by
  induction flags generalizing j with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [records,ih]

theorem records_width (row unit flags j : List Bool) (hr : row.length=unit.length)
    (hj : j.length=unit.length) :
    ∀ p ∈ records row unit flags j, p.1.length=unit.length ∧ p.2.length=unit.length := by
  induction flags generalizing j with
  | nil => simp [records]
  | cons b bs ih =>
    cases b <;> simp only [records, Bool.false_eq_true, ↓reduceIte, List.nil_append,
      List.singleton_append, List.mem_cons, forall_eq_or_imp]
    · exact ih _ (RepeatedAdd.addWord_length j unit hj)
    · exact ⟨⟨hr,hj⟩, ih _ (RepeatedAdd.addWord_length j unit hj)⟩

theorem encoded_length (row unit flags j : List Bool) (hr : row.length=unit.length)
    (hj : j.length=unit.length) :
    (encoded row unit flags j).length=2*unit.length*(flags.count true) := by
  induction flags generalizing j with
  | nil => simp [encoded,records]
  | cons b bs ih =>
    have h := ih _ (RepeatedAdd.addWord_length j unit hj)
    cases b <;> simp [encoded,records] at h ⊢
    · exact h
    · rw [h,hr,hj]
      simp only [Nat.mul_add,Nat.mul_one]
      omega

theorem records_values (row unit flags j : List Bool) (hj : j.length=unit.length)
    (hu : BinaryCompare.value unit=1)
    (hfit : BinaryCompare.value j+flags.length<2^unit.length) :
    (records row unit flags j).map (fun p => (BinaryCompare.value p.1,BinaryCompare.value p.2)) =
      (targets flags (BinaryCompare.value j)).map (fun k => (BinaryCompare.value row,k)) := by
  induction flags generalizing j with
  | nil => rfl
  | cons b bs ih =>
    have hv : BinaryCompare.value (RepeatedAdd.addWord j unit)=BinaryCompare.value j+1 := by
      rw [RepeatedAdd.addWord_value j unit hj,hu,Nat.mod_eq_of_lt (by simp only [List.length_cons] at hfit; omega)]
    have hh : BinaryCompare.value (RepeatedAdd.addWord j unit)+bs.length<2^unit.length := by
      rw [hv]; simp only [List.length_cons] at hfit; omega
    have h := ih _ (RepeatedAdd.addWord_length j unit hj) hh
    rw [hv] at h
    cases b <;> simpa [records,targets] using h

theorem after_length (unit flags j : List Bool) (hj : j.length=unit.length) :
    (after unit flags j).length=unit.length := RepeatedAdd.repeatWord_length _ _ _ hj

theorem after_value (unit flags j : List Bool) (hj : j.length=unit.length)
    (hu : BinaryCompare.value unit=1)
    (hfit : BinaryCompare.value j+flags.length<2^unit.length) :
    BinaryCompare.value (after unit flags j)=BinaryCompare.value j+flags.length := by
  simpa only [after,hu,Nat.mul_one] using RepeatedAdd.repeatWord_value_exact unit flags.length j hj
    (by simpa only [hu,Nat.mul_one] using hfit)

theorem targets_bounds (flags : List Bool) (j k : ℕ) (h : k ∈ targets flags j) :
    j ≤ k ∧ k<j+flags.length := by
  induction flags generalizing j with
  | nil => simp [targets] at h
  | cons b bs ih =>
    cases b with
    | false =>
      simp only [targets,Bool.false_eq_true,↓reduceIte,List.nil_append] at h
      obtain ⟨hl,hr⟩ := ih (j+1) h
      simp only [List.length_cons]; omega
    | true =>
      simp only [targets,↓reduceIte,List.singleton_append,List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · obtain ⟨hl,hr⟩ := ih (j+1) h
        simp only [List.length_cons]; omega

theorem targets_nodup (flags : List Bool) (j : ℕ) : (targets flags j).Nodup := by
  induction flags generalizing j with
  | nil => simp [targets]
  | cons b bs ih =>
    cases b with
    | false => simpa [targets] using ih (j+1)
    | true =>
      simp only [targets,↓reduceIte,List.singleton_append,List.nodup_cons]
      exact ⟨fun h => by have := (targets_bounds bs (j+1) j h).1; omega,ih (j+1)⟩

theorem targets_map_range (f : ℕ → Bool) (n j : ℕ) :
    targets ((List.range n).map f) j =
      (List.range n).filterMap (fun k => if f k then some (j+k) else none) := by
  induction n generalizing f j with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ_eq_map,List.map_cons,List.map_map,targets]
    rw [ih]
    cases h : f 0 <;> simp [h,List.filterMap_map,Nat.add_comm,Nat.add_left_comm]

theorem mem_targets_range (f : ℕ → Bool) (n k : ℕ) :
    k ∈ targets ((List.range n).map f) 0 ↔ k<n ∧ f k=true := by
  rw [targets_map_range]
  simp only [Nat.zero_add,List.mem_filterMap,List.mem_range]
  constructor
  · rintro ⟨j,hj,h⟩
    split_ifs at h with hb
    · have he : j=k := Option.some.inj h
      subst j; exact ⟨hj,hb⟩
  · rintro ⟨hk,hf⟩
    exact ⟨k,hk,by simp [hf]⟩

end TransposeFollowup.RowConsumer
