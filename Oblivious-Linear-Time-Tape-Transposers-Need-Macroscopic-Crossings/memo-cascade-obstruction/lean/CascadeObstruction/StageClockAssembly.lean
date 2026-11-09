import TransposeFollowup.ContractingStageClock
import Mathlib.Data.Fin.Tuple.Basic

/-! Assemble a complete integer stage clock from an ordered list of distinct
labelled chunks. The interval partition is proved from concatenation, including
zero-length chunks. Keys absent from the list have an empty interval at the end. -/

namespace CascadeObstruction.StageClockAssembly

open TransposeFollowup.RegularMotion
open scoped BigOperators

set_option autoImplicit false

variable {Key : Type*} [DecidableEq Key]

/-- Total physical ticks in a list of labelled chunks. -/
def total : List (Key × ℕ) → ℕ
  | [] => 0
  | (_, n) :: xs => n + total xs

/-- Entry time of the first chunk with a given key, or the terminal time. -/
def start : List (Key × ℕ) → Key → ℕ
  | [], _ => 0
  | (k, n) :: xs, q => if q = k then 0 else n + start xs q

/-- Exit time of the first chunk with a given key, or the terminal time. -/
def finish : List (Key × ℕ) → Key → ℕ
  | [], _ => 0
  | (k, n) :: xs, q => if q = k then n else n + finish xs q

/-- Duration of the first chunk with the given key, zero for an absent key. -/
def duration : List (Key × ℕ) → Key → ℕ
  | [], _ => 0
  | (k, n) :: xs, q => if q = k then n else duration xs q

/-- Each physical tick belongs to the chunk containing it. -/
def label : (xs : List (Key × ℕ)) → Fin (total xs) → Key
  | [], t => Fin.elim0 t
  | (k, _) :: xs, t => Fin.addCases (fun _ => k) (label xs) t

omit [DecidableEq Key] in
@[simp] theorem label_castAdd (k : Key) (n : ℕ) (xs : List (Key × ℕ)) (t : Fin n) :
    label ((k, n) :: xs) (Fin.castAdd (total xs) t) = k :=
  Fin.addCases_left t

omit [DecidableEq Key] in
@[simp] theorem label_natAdd (k : Key) (n : ℕ) (xs : List (Key × ℕ))
    (t : Fin (total xs)) :
    label ((k, n) :: xs) (Fin.natAdd n t) = label xs t :=
  Fin.addCases_right t

omit [DecidableEq Key] in
@[simp] theorem total_eq_sum (xs : List (Key × ℕ)) :
    total xs = (xs.map Prod.snd).sum := by
  induction xs with
  | nil => rfl
  | cons p xs ih => rcases p with ⟨k, n⟩; simpa [total] using congrArg (n + ·) ih

omit [DecidableEq Key] in
@[simp] theorem total_append (xs ys : List (Key × ℕ)) :
    total (xs ++ ys) = total xs + total ys := by
  simp [total_eq_sum]

omit [DecidableEq Key] in
/-- Every emitted label is one of the listed chunk keys. -/
theorem label_mem (xs : List (Key × ℕ)) (t : Fin (total xs)) :
    label xs t ∈ xs.map Prod.fst := by
  induction xs with
  | nil => exact Fin.elim0 t
  | cons p xs ih =>
    rcases p with ⟨k, n⟩
    cases t using Fin.addCases with
    | left t => simp only [label_castAdd, List.map_cons, List.mem_cons, true_or]
    | right t => simpa only [label_natAdd, List.map_cons] using List.mem_cons_of_mem k (ih t)

theorem start_le_finish (xs : List (Key × ℕ)) (q : Key) :
    start xs q ≤ finish xs q := by
  induction xs with
  | nil => exact le_rfl
  | cons p xs ih =>
    rcases p with ⟨k, n⟩
    simp only [start, finish]
    split
    · exact Nat.zero_le _
    · exact Nat.add_le_add_left ih n

theorem finish_le_total (xs : List (Key × ℕ)) (q : Key) :
    finish xs q ≤ total xs := by
  induction xs with
  | nil => exact le_rfl
  | cons p xs ih =>
    rcases p with ⟨k, n⟩
    simp only [finish, total]
    split
    · omega
    · exact Nat.add_le_add_left ih n

@[simp] theorem finish_sub_start (xs : List (Key × ℕ)) (q : Key) :
    finish xs q - start xs q = duration xs q := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨k, n⟩
    by_cases hq : q = k <;> simp [start, finish, duration, hq, Nat.add_sub_add_left, ih]

theorem start_eq_total_of_not_mem {xs : List (Key × ℕ)} {q : Key}
    (hq : q ∉ xs.map Prod.fst) : start xs q = total xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨k, n⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hq
    simp [start, total, hq.1, ih hq.2]

theorem finish_eq_total_of_not_mem {xs : List (Key × ℕ)} {q : Key}
    (hq : q ∉ xs.map Prod.fst) : finish xs q = total xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨k, n⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hq
    simp [finish, total, hq.1, ih hq.2]

/-- Concatenating distinct labelled chunks proves the complete tick partition.
No positive-duration hypothesis is needed. -/
theorem partition {xs : List (Key × ℕ)} (hkeys : (xs.map Prod.fst).Nodup)
    (q : Key) (t : Fin (total xs)) :
    (start xs q ≤ t.val ∧ t.val < finish xs q) ↔ label xs t = q := by
  induction xs with
  | nil => exact Fin.elim0 t
  | cons p xs ih =>
    rcases p with ⟨k, n⟩
    have hk : k ∉ xs.map Prod.fst := (List.nodup_cons.mp hkeys).1
    have htail : (xs.map Prod.fst).Nodup := (List.nodup_cons.mp hkeys).2
    cases t using Fin.addCases with
    | left t =>
      by_cases hq : q = k
      · simp [start, finish, hq, t.isLt]
      · simp [start, finish, hq, Ne.symm hq]
        omega
    | right t =>
      by_cases hq : q = k
      · have hne : label xs t ≠ k := by
          intro heq
          exact hk (heq ▸ label_mem xs t)
        simp [start, finish, hq, hne]
      · simpa [start, finish, hq] using ih htail t

/-- A listed unique key has exactly its stated duration. -/
theorem duration_eq_of_mem {xs : List (Key × ℕ)}
    (hkeys : (xs.map Prod.fst).Nodup) {q : Key} {n : ℕ}
    (hmem : (q, n) ∈ xs) : duration xs q = n := by
  induction xs with
  | nil => simp at hmem
  | cons p xs ih =>
    rcases p with ⟨k, m⟩
    rcases List.mem_cons.mp hmem with heq | hmem
    · cases heq; simp [duration]
    · have hq : q ≠ k := by
        intro heq
        apply (List.nodup_cons.mp hkeys).1
        rw [← heq]
        exact List.mem_map.mpr ⟨(q, n), hmem, rfl⟩
      simp [duration, hq, ih (List.nodup_cons.mp hkeys).2 hmem]

/-- An absent key contributes zero duration. -/
theorem duration_eq_zero_of_not_mem {xs : List (Key × ℕ)} {q : Key}
    (hq : q ∉ xs.map Prod.fst) : duration xs q = 0 := by
  rw [← finish_sub_start, start_eq_total_of_not_mem hq,
    finish_eq_total_of_not_mem hq, Nat.sub_self]

theorem start_append_of_not_mem {xs ys : List (Key × ℕ)} {q : Key}
    (hq : q ∉ xs.map Prod.fst) :
    start (xs ++ ys) q = total xs + start ys q := by
  induction xs with
  | nil => simp [total]
  | cons p xs ih =>
    rcases p with ⟨k, n⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hq
    simp [start, total, hq.1, ih hq.2, Nat.add_assoc]

theorem finish_append_of_not_mem {xs ys : List (Key × ℕ)} {q : Key}
    (hq : q ∉ xs.map Prod.fst) :
    finish (xs ++ ys) q = total xs + finish ys q := by
  induction xs with
  | nil => simp [total]
  | cons p xs ih =>
    rcases p with ⟨k, n⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hq
    simp [finish, total, hq.1, ih hq.2, Nat.add_assoc]

/-- Change chunk keys without changing their order or durations. -/
def mapKeys {Key' : Type*} (f : Key → Key') (xs : List (Key × ℕ)) :
    List (Key' × ℕ) := xs.map fun p => (f p.1, p.2)

omit [DecidableEq Key] in
@[simp] theorem total_mapKeys {Key' : Type*} (f : Key → Key')
    (xs : List (Key × ℕ)) : total (mapKeys f xs) = total xs := by
  simp [total_eq_sum, mapKeys, List.map_map, Function.comp_def]

omit [DecidableEq Key] in
/-- Injective relabelling preserves distinct stage keys. -/
theorem nodup_mapKeys {Key' : Type*} {f : Key → Key'} (hf : Function.Injective f)
    {xs : List (Key × ℕ)} (hkeys : (xs.map Prod.fst).Nodup) :
    ((mapKeys f xs).map Prod.fst).Nodup := by
  simpa [mapKeys, List.map_map, Function.comp_def] using hkeys.map hf

@[simp] theorem start_mapKeys {Key' : Type*} [DecidableEq Key']
    {f : Key → Key'} (hf : Function.Injective f) (xs : List (Key × ℕ)) (q : Key) :
    start (mapKeys f xs) (f q) = start xs q := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨k, n⟩
    simpa [mapKeys, start, hf.eq_iff] using congrArg (fun t => if q = k then 0 else n + t) ih

@[simp] theorem finish_mapKeys {Key' : Type*} [DecidableEq Key']
    {f : Key → Key'} (hf : Function.Injective f) (xs : List (Key × ℕ)) (q : Key) :
    finish (mapKeys f xs) (f q) = finish xs q := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨k, n⟩
    simpa [mapKeys, finish, hf.eq_iff] using congrArg (fun t => if q = k then n else n + t) ih

@[simp] theorem duration_mapKeys {Key' : Type*} [DecidableEq Key']
    {f : Key → Key'} (hf : Function.Injective f) (xs : List (Key × ℕ)) (q : Key) :
    duration (mapKeys f xs) (f q) = duration xs q := by
  simp only [← finish_sub_start, finish_mapKeys hf, start_mapKeys hf]

/-- The length chunks of an actual finite list of labelled payloads. -/
def chunksOfPayloads {Payload Atom : Type*} (expand : Payload → List Atom)
    (xs : List (Key × Payload)) : List (Key × ℕ) :=
  xs.map fun p => (p.1, (expand p.2).length)

omit [DecidableEq Key] in
@[simp] theorem keys_chunksOfPayloads {Payload Atom : Type*} (expand : Payload → List Atom)
    (xs : List (Key × Payload)) :
    (chunksOfPayloads expand xs).map Prod.fst = xs.map Prod.fst := by
  simp [chunksOfPayloads, List.map_map, Function.comp_def]

omit [DecidableEq Key] in
@[simp] theorem total_chunksOfPayloads {Payload Atom : Type*} (expand : Payload → List Atom)
    (xs : List (Key × Payload)) :
    total (chunksOfPayloads expand xs) = (xs.flatMap fun p => expand p.2).length := by
  simp [chunksOfPayloads, total_eq_sum, List.length_flatMap, List.map_map, Function.comp_def]

/-- A uniquely labelled payload is an actual contiguous segment of the
flattened execution, with the start and length furnished by the assembled clock.
This identifies the actual execution segment, not merely its tick count. -/
theorem exists_payload_decomposition {Payload Atom : Type*}
    (expand : Payload → List Atom) {xs : List (Key × Payload)}
    (hkeys : (xs.map Prod.fst).Nodup) {q : Key} {p : Payload}
    (hmem : (q, p) ∈ xs) :
    ∃ before after : List Atom,
      xs.flatMap (fun x => expand x.2) = before ++ expand p ++ after ∧
      start (chunksOfPayloads expand xs) q = before.length ∧
      finish (chunksOfPayloads expand xs) q - start (chunksOfPayloads expand xs) q =
        (expand p).length := by
  have hdur : duration (chunksOfPayloads expand xs) q = (expand p).length :=
    duration_eq_of_mem (by simpa using hkeys)
      (List.mem_map.mpr ⟨(q, p), hmem, rfl⟩)
  obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hmem
  have hnot : q ∉ pre.map Prod.fst := by
    have hd : ((pre.map Prod.fst) ++ q :: post.map Prod.fst).Nodup := by simpa using hkeys
    have hn := (List.nodup_cons.mp (List.nodup_middle.mp hd)).1
    exact fun h => hn (List.mem_append_left _ h)
  refine ⟨pre.flatMap (fun x => expand x.2), post.flatMap (fun x => expand x.2),
    by simp, ?_, ?_⟩
  · have heq : chunksOfPayloads expand (pre ++ (q, p) :: post) =
        chunksOfPayloads expand pre ++
          (q, (expand p).length) :: chunksOfPayloads expand post := by
      simp [chunksOfPayloads]
    rw [heq, start_append_of_not_mem (by simpa using hnot)]
    simp [start, chunksOfPayloads, List.map_map, Function.comp_def]
  · simpa only [finish_sub_start] using hdur

/-- Complete stage-clock constructor. Only volume inequalities and the sum of
listed durations at each address are supplied; all interval and tick-partition
obligations follow from the finite ordered chunk list. -/
def toClock {B J : ℕ} {rho a C P : ℝ}
    (xs : List ((List (Fin B) × Fin J) × ℕ))
    (hkeys : (xs.map Prod.fst).Nodup)
    (V : List (Fin B) → ℝ)
    (hV : ∀ w, 0 ≤ V w)
    (hchildren : ∀ w, ∑ b : Fin B, V (w ++ [b]) ≤ rho * V w)
    (hroot : V [] ≤ C * P)
    (hbudget : ∀ w, ((∑ j : Fin J, duration xs (w, j) : ℕ) : ℝ) ≤ a * V w) :
    ContractingStageClock B J rho a C P (total xs) where
  V := V
  label := label xs
  A := fun w j => start xs (w, j)
  E := fun w j => finish xs (w, j)
  nonneg := hV
  children := hchildren
  root := hroot
  ordered := fun w j => start_le_finish xs (w, j)
  bounded := fun w j => finish_le_total xs (w, j)
  partition := fun w j t => partition hkeys (w, j) t
  budget := fun w => by simpa only [finish_sub_start] using hbudget w

end CascadeObstruction.StageClockAssembly
