import TransposeFollowup.MatchingXorStream
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup

/-! Word boundaries in the matching stream are semantic bookkeeping only.
The native controller acts on individual bits and repeated row flags. -/
namespace TransposeFollowup.ExpanderShearRowStream
open MatchingXorStream
set_option autoImplicit false

abbrev Word (W : ℕ) := Fin W → Bool

def wordXor {W : ℕ} (a b : Word W) : Word W := fun w => (a w).xor (b w)

def records {W : ℕ} (xs : List (Bool × Word W)) : List Record :=
  xs.flatMap (fun p => tagged p.1 (List.ofFn p.2))

def rawWords {W : ℕ} (xs : List (Word W)) : List Bool := xs.flatMap List.ofFn

def applyRows {W : ℕ} (as : List (Word W)) : List (Bool × Word W) → List (Word W)
  | [] => []
  | (false,b)::bs => b::applyRows as bs
  | (true,b)::bs => wordXor (as.headD (fun _ => false)) b::applyRows as.tail bs

def selectedRows {W : ℕ} (xs : List (Bool × Word W)) : List (Word W) :=
  xs.filterMap (fun p => if p.1 then some p.2 else none)

theorem selected_append (xs ys : List Record) :
    selected (xs ++ ys) = selected xs ++ selected ys := by
  simp [selected]

theorem selected_records {W : ℕ} (xs : List (Bool × Word W)) :
    selected (records xs) = rawWords (selectedRows xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨tag,b⟩
    change selected (tagged tag (List.ofFn b) ++ records xs) = _
    rw [selected_append, selected_tagged, ih]
    cases tag <;> simp [selectedRows, rawWords]

theorem apply_false_append (as bs : List Bool) (tail : List Record) :
    MatchingXorStream.apply as (tagged false bs ++ tail) =
      bs ++ MatchingXorStream.apply as tail := by
  induction bs <;> simp_all [tagged]

theorem apply_true_append (a b as : List Bool) (tail : List Record) (h : a.length = b.length) :
    MatchingXorStream.apply (a ++ as) (tagged true b ++ tail) =
      List.zipWith Bool.xor a b ++ MatchingXorStream.apply as tail := by
  induction b generalizing a with
  | nil => have ha : a = [] := by simpa using h
           simp [ha, tagged]
  | cons c cs ih =>
    cases a with
    | nil => simp at h
    | cons d ds =>
      have hh : ds.length = cs.length := by simpa using h
      simpa [tagged] using congrArg (List.cons (d.xor c)) (ih ds hh)

theorem zipWith_words {W : ℕ} (a b : Word W) :
    List.zipWith Bool.xor (List.ofFn a) (List.ofFn b) = List.ofFn (wordXor a b) := by
  induction W with
  | zero => simp
  | succ W ih =>
    simp only [List.ofFn_succ, List.zipWith_cons_cons]
    apply congrArg (List.cons ((a 0).xor (b 0)))
    exact ih (fun i => a i.succ) (fun i => b i.succ)

theorem apply_records {W : ℕ} (as : List (Word W)) (bs : List (Bool × Word W))
    (h : as.length = (selectedRows bs).length) :
    MatchingXorStream.apply (rawWords as) (records bs) = rawWords (applyRows as bs) := by
  induction bs generalizing as with
  | nil => simp [records, rawWords, applyRows]
  | cons b bs ih =>
    rcases b with ⟨tag,b⟩
    cases tag with
    | false =>
      have hh : as.length = (selectedRows bs).length := h
      simp only [records, List.flatMap_cons]
      rw [apply_false_append]
      change List.ofFn b ++ MatchingXorStream.apply (rawWords as) (records bs) = _
      rw [ih as hh]
      rfl
    | true =>
      cases as with
      | nil => simp [selectedRows] at h
      | cons a as =>
        have hh : as.length = (selectedRows bs).length := by simpa [selectedRows] using h
        simp only [rawWords, records, List.flatMap_cons]
        rw [apply_true_append _ _ _ _ (by simp)]
        change List.zipWith Bool.xor (List.ofFn a) (List.ofFn b) ++
            MatchingXorStream.apply (rawWords as) (records bs) = _
        rw [ih as hh]
        simp [applyRows, rawWords, zipWith_words]

/-- Pair source and target rows in their stream order. -/
def pairSource {ι : Type*} [DecidableEq ι] : List ι → List ι → ι → Option ι
  | i::is, j::js, t => if t=j then some i else pairSource is js t
  | _, _, _ => none

theorem pairSource_none {ι : Type*} [DecidableEq ι] (is js : List ι) (t : ι)
    (h : t ∉ js) : pairSource is js t = none := by
  induction js generalizing is with
  | nil => cases is <;> rfl
  | cons j js ih =>
    cases is with
    | nil => rfl
    | cons i is =>
      have ht : t ≠ j := fun he => h (he ▸ List.mem_cons_self)
      simp only [pairSource, ht, ite_false]
      exact ih is (fun hm => h (List.mem_cons_of_mem j hm))

def pairedUpdate {ι : Type*} [DecidableEq ι] {W : ℕ}
    (is js : List ι) (A B : ι → Word W) (j : ι) : Word W :=
  match pairSource is js j with
  | none => B j
  | some i => wordXor (A i) (B j)

/-- The row-level stream pairs precisely the corresponding selected rows. -/
theorem applyRows_eq_paired {ι : Type*} [DecidableEq ι] {W : ℕ}
    (is js : List ι) (hj : js.Nodup) (tag : ι → Bool) (A B : ι → Word W)
    (hlen : is.length = (js.filter tag).length) :
    applyRows (is.map A) (js.map (fun j => (tag j, B j))) =
      js.map (pairedUpdate is (js.filter tag) A B) := by
  induction js generalizing is with
  | nil => simp [applyRows]
  | cons j js ih =>
    obtain ⟨hjnot, hj⟩ := List.nodup_cons.mp hj
    cases ht : tag j with
    | false =>
      have hh : is.length = (js.filter tag).length := by simpa [ht] using hlen
      have hn : pairSource is (js.filter tag) j = none :=
        pairSource_none _ _ _ (fun h => hjnot (List.mem_of_mem_filter h))
      simp only [List.map_cons, ht, applyRows, List.filter_cons, Bool.false_eq_true,
        ↓reduceIte]
      rw [ih is hj hh]
      simp [pairedUpdate, hn]
    | true =>
      cases is with
      | nil => simp [ht] at hlen
      | cons i is =>
        have hh : is.length = (js.filter tag).length := by simpa [ht] using hlen
        simp only [List.map_cons, applyRows, List.headD_cons, List.tail_cons,
          List.filter_cons, ht, ↓reduceIte]
        rw [ih is hj hh]
        congr 1
        · simp [pairedUpdate, pairSource]
        · apply List.map_congr_left
          intro t hmem
          have hne : t ≠ j := fun he => hjnot (he ▸ hmem)
          simp [pairedUpdate, pairSource, hne]

theorem selectedRows_map {ι : Type*} {W : ℕ} (js : List ι)
    (tag : ι → Bool) (A : ι → Word W) :
    selectedRows (js.map (fun j => (tag j, A j))) = (js.filter tag).map A := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    have hi := ih
    simp only [selectedRows, List.filterMap_map] at hi
    cases ht : tag j <;> simp [selectedRows, ht] <;> exact hi

@[simp] theorem rawWords_length {W : ℕ} (xs : List (Word W)) :
    (rawWords xs).length = xs.length * W := by
  induction xs <;> simp_all [rawWords, Nat.add_mul, add_comm]

theorem pairSource_some_iff {ι : Type*} [DecidableEq ι] (is js : List ι)
    (hj : js.Nodup) (j i : ι) :
    pairSource is js j = some i ↔ (j, i) ∈ js.zip is := by
  induction js generalizing is with
  | nil => cases is <;> simp [pairSource]
  | cons k ks ih =>
    obtain ⟨hk, hks⟩ := List.nodup_cons.mp hj
    cases is with
    | nil => simp [pairSource]
    | cons l ls =>
      by_cases he : j = k
      · subst j
        have hn : (k, i) ∉ ks.zip ls := fun h => hk (List.of_mem_zip h).1
        simp [pairSource, hn, eq_comm]
      · simp [pairSource, he, ih ls hks]

theorem values_records {W : ℕ} (xs : List (Bool × Word W)) :
    values (records xs) = rawWords (xs.map Prod.snd) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    change values (tagged p.1 (List.ofFn p.2) ++ records xs) = _
    rw [show values (tagged p.1 (List.ofFn p.2) ++ records xs) =
      values (tagged p.1 (List.ofFn p.2)) ++ values (records xs) by simp [values]]
    rw [values_tagged, ih]
    rfl

theorem tags_records {W : ℕ} (xs : List (Bool × Word W)) :
    tags (records xs) = xs.flatMap (fun p => List.replicate W p.1) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    change tags (tagged p.1 (List.ofFn p.2) ++ records xs) = _
    rw [show tags (tagged p.1 (List.ofFn p.2) ++ records xs) =
      tags (tagged p.1 (List.ofFn p.2)) ++ tags (records xs) by simp [tags]]
    rw [tags_tagged, ih]
    simp

end TransposeFollowup.ExpanderShearRowStream
