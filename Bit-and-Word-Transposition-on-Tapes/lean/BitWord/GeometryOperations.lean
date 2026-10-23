import BitWord.GeometryRotations
import BitWord.GeometryScales

namespace BitWord.Geometry

/-- Extend a finite entry permutation by the identity outside its domain. -/
def finiteAct {n : ℕ} (e : Equiv.Perm (Fin n)) (x : ℕ) : ℕ :=
  if h : x < n then (e ⟨x, h⟩).val else x

@[simp] theorem finiteAct_lt {n x : ℕ} (e : Equiv.Perm (Fin n)) (h : x < n) :
    finiteAct e x < n := by simp only [finiteAct, dite_eq_left h]; exact (e ⟨x, h⟩).isLt

@[simp] theorem finiteAct_symm_apply {n : ℕ} (e : Equiv.Perm (Fin n)) (x : ℕ) :
    finiteAct e.symm (finiteAct e x) = x := by
  by_cases h : x < n
  · simp only [finiteAct, dite_eq_left h, dite_eq_left (e ⟨x, h⟩).isLt]
    change (e.symm (e ⟨x, h⟩)).val = x
    simp
  · simp [finiteAct, h]

def oriented {α : Type*} (e : Equiv.Perm α) (back : Bool) : Equiv.Perm α :=
  if back then e.symm else e

@[simp] theorem oriented_false {α : Type*} (e : Equiv.Perm α) : oriented e false = e := rfl
@[simp] theorem oriented_true {α : Type*} (e : Equiv.Perm α) : oriented e true = e.symm := rfl
@[simp] theorem oriented_symm {α : Type*} (e : Equiv.Perm α) (back : Bool) :
    oriented e.symm back = oriented e (!back) := by cases back <;> rfl

/-- Exact permitted operations within a contiguous block. Entry permutations
are arbitrary public permutations, with arbitrary positive widths/counts. -/
inductive BlockOperation where
  | entries (width count : ℕ) (width_pos : 0 < width) (count_pos : 0 < count)
      (permutation : Equiv.Perm (Fin count))
  | rotate (length : ℕ) (positive : 0 < length) (amount : Fin length)
  | reverse (length : ℕ) (positive : 0 < length)

namespace BlockOperation

def length : BlockOperation → ℕ
  | .entries k n _ _ _ => k * n
  | .rotate n _ _ => n
  | .reverse n _ => n

theorem length_pos (op : BlockOperation) : 0 < op.length := by
  cases op with
  | entries k n hk hn e => exact Nat.mul_pos hk hn
  | rotate n hn r => exact hn
  | reverse n hn => exact hn

/-- The inverse rotation amount, including the zero-offset case. -/
def rotationAmount {n : ℕ} (r : Fin n) (back : Bool) : ℕ :=
  if back then (n - r.val) % n else r.val

theorem rotationAmount_lt {n : ℕ} (hn : 0 < n) (r : Fin n) (back : Bool) :
    rotationAmount r back < n := by
  cases back <;> simp only [rotationAmount, Bool.false_eq_true, ↓reduceIte]
  · exact r.isLt
  · exact Nat.mod_lt _ hn

def act (op : BlockOperation) (back : Bool) (x : ℕ) : ℕ :=
  match op with
  | .entries k _ _ _ e => entryMap k (finiteAct (oriented e back)) x
  | .rotate n _ r => (x + rotationAmount r back) % n
  | .reverse n _ => n - 1 - x

/-- Only the middle-width entry blocks are marked bad. -/
def bad (op : BlockOperation) (B : ℕ) : Prop :=
  match op with
  | .entries k _ _ _ _ => BadAt B k
  | _ => False

instance (op : BlockOperation) (B : ℕ) : Decidable (op.bad B) := by
  cases op <;> simp only [bad, BadAt] <;> infer_instance

/-- The volume restriction applies only to the entry-permutation grant. -/
def Admissible : BlockOperation → Prop
  | .entries k n _ _ _ => k * n ≤ volume k
  | _ => True

theorem act_lt (op : BlockOperation) (back : Bool) {x : ℕ} (hx : x < op.length) :
    op.act back x < op.length := by
  cases op with
  | entries k n hk hn e =>
    simp only [length] at hx ⊢
    simp only [act, entryMap]
    have hd : x / k < n := (Nat.div_lt_iff_lt_mul hk).2 (by simpa [Nat.mul_comm] using hx)
    have ht := finiteAct_lt (oriented e back) hd
    have hm := Nat.mod_lt x hk
    nlinarith
  | rotate n hn r => exact Nat.mod_lt _ hn
  | reverse n hn => simp only [act, length] at *; omega

/-- Every permitted good block longer than B has at most four image bins on
an arbitrary subset of a B-bin. This proves the operation-specific part of
interval geometry, rather than including it in the operation's definition. -/
theorem good_large_image (op : BlockOperation) (had : op.Admissible)
    (back : Bool) {B j a : ℕ} (hB : 0 < B) (hgood : ¬ op.bad B)
    (hlarge : B < op.length) (S : Finset ℕ) (f : ℕ → ℕ)
    (hS : ∀ x ∈ S, j * B ≤ x ∧ x < (j + 1) * B)
    (ha : ∀ x ∈ S, a ≤ x ∧ x < a + op.length)
    (hf : ∀ x ∈ S, f x = a + op.act back (x - a)) :
    (bins B (S.image f)).card ≤ 4 := by
  cases op with
  | entries k n hk hn e =>
    have hwidth : B ≤ k := by simp only [bad, BadAt] at hgood; simp only [Admissible, length] at had hlarge; omega
    exact entry_image_bins_le_four hB hwidth S f (finiteAct (oriented e back)) hS
      (fun x hx => (ha x hx).1) hf
  | rotate n hn r =>
    exact rotate_image_bins_le_four hB hn (rotationAmount_lt hn r back) S f hS ha hf
  | reverse n hn =>
    exact (reverse_image_bins_le_two hB S f hS ha hf).trans (by decide)

end BlockOperation
end BitWord.Geometry
