import BitWord.AddressSwap
import Mathlib.Data.List.Iterate
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Defs

namespace BitWord

inductive Gate where
  | suffix (k : ℕ)
  | right
  | left
  deriving DecidableEq, Repr

/-- Source motion for a cyclic rotation of address positions to the right. -/
def rotateRight (N x : ℕ) := if x+1 < N then x+1 else 0
/-- Inverse cyclic rotation. -/
def rotateLeft (N x : ℕ) := if x = 0 then N-1 else x-1

def Gate.apply (N : ℕ) : Gate → ℕ → ℕ
  | .suffix k => suffixSwap N k
  | .right => rotateRight N
  | .left => rotateLeft N

def Gate.Legal (N : ℕ) : Gate → Prop
  | .suffix k => 2*k ≤ N
  | _ => 0 < N

def runGates (N : ℕ) (gs : List Gate) (x : ℕ) : ℕ :=
  gs.foldl (fun y g => g.apply N y) x

@[simp] theorem runGates_nil (N x : ℕ) : runGates N [] x = x := rfl
@[simp] theorem runGates_cons (N x : ℕ) (g : Gate) (gs : List Gate) :
    runGates N (g::gs) x = runGates N gs (g.apply N x) := rfl

theorem runGates_append (N x : ℕ) (a b : List Gate) :
    runGates N (a++b) x = runGates N b (runGates N a x) := by
  exact List.foldl_append

theorem Gate.apply_lt {N x : ℕ} {g : Gate} (hg : g.Legal N) (hx : x < N) :
    g.apply N x < N := by
  cases g with
  | suffix k => exact suffixSwap_lt hg hx
  | right => dsimp [Gate.apply, rotateRight]; split_ifs <;> omega
  | left => dsimp [Gate.apply, rotateLeft]; split_ifs <;> omega

theorem runGates_lt {N x : ℕ} {gs : List Gate}
    (hg : ∀ g ∈ gs, g.Legal N) (hx : x < N) : runGates N gs x < N := by
  induction gs generalizing x with
  | nil => exact hx
  | cons g gs ih =>
    exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      (Gate.apply_lt (hg g (by simp)) hx)

def fiveGates (n w : ℕ) : List Gate :=
  [.suffix n, .suffix (n-w), .suffix w, .suffix (n-w), .suffix n]

def elevenGates (h n w : ℕ) : List Gate :=
  fiveGates n w ++ [.suffix h] ++ fiveGates n w

@[simp] theorem fiveGates_length (n w : ℕ) : (fiveGates n w).length = 5 := rfl
@[simp] theorem elevenGates_length (h n w : ℕ) : (elevenGates h n w).length = 11 := rfl

theorem elevenGates_correct {h n w x : ℕ} (hn : 2*n = 2*h+w)
    (hw : 3*w ≤ n) (hx : x < 2*n) :
    runGates (2*n) (elevenGates h n w) x = headSwap h x := by
  exact elevenSuffix_eq_head hn hw hx

theorem elevenGates_legal {h n w : ℕ} (hn : 2*n = 2*h+w)
    (hw : 3*w ≤ n) : ∀ g ∈ elevenGates h n w, g.Legal (2*n) := by
  intro g hg
  simp only [elevenGates, fiveGates, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with ((rfl | rfl | rfl | rfl | rfl) | rfl) | (rfl | rfl | rfl | rfl | rfl)
  all_goals dsimp [Gate.Legal]; omega

theorem right_repeat {N x t : ℕ} (hN : 0 < N) (hx : x < N) (ht : t ≤ N) :
    runGates N (List.replicate t .right) x =
      if x+t < N then x+t else x+t-N := by
  induction t generalizing x with
  | zero => simp [runGates, hx]
  | succ t ih =>
    change runGates N (List.replicate t .right) (rotateRight N x) = _
    rw [ih (x := rotateRight N x) (Gate.apply_lt (g := .right) hN hx) (by omega)]
    unfold rotateRight
    split_ifs <;> omega

theorem left_repeat {N x t : ℕ} (hN : 0 < N) (hx : x < N) (ht : t ≤ N) :
    runGates N (List.replicate t .left) x =
      if t ≤ x then x-t else N+x-t := by
  induction t generalizing x with
  | zero => simp [runGates]
  | succ t ih =>
    change runGates N (List.replicate t .left) (rotateLeft N x) = _
    rw [ih (x := rotateLeft N x) (Gate.apply_lt (g := .left) hN hx) (by omega)]
    unfold rotateLeft
    split_ifs <;> omega

def rotationGates (h w : ℕ) : List Gate :=
  List.replicate w .right ++ [.suffix h] ++ List.replicate w .left

@[simp] theorem rotationGates_length (h w : ℕ) :
    (rotationGates h w).length = 2*w+1 := by simp [rotationGates]; omega

theorem rotationGates_legal {h w : ℕ} (hh : 0 < h) :
    ∀ g ∈ rotationGates h w, g.Legal (2*h+w) := by
  intro g hg
  simp only [rotationGates, List.mem_append, List.mem_replicate,
    List.mem_singleton] at hg
  rcases hg with ((⟨_, rfl⟩ | rfl) | ⟨_, rfl⟩)
  all_goals dsimp [Gate.Legal]; omega

theorem rotationGates_correct {h w x : ℕ} (hh : 0 < h) (hx : x < 2*h+w) :
    runGates (2*h+w) (rotationGates h w) x = headSwap h x := by
  have hN : 0 < 2*h+w := by omega
  have ht : w ≤ 2*h+w := by omega
  have hr := runGates_lt
    (N := 2*h+w) (x := x) (gs := List.replicate w .right)
    (by intro g hg; obtain ⟨_, rfl⟩ := List.mem_replicate.mp hg; exact hN) hx
  have hs := suffixSwap_lt (k := h) (by omega : 2*h ≤ 2*h+w) hr
  simp only [rotationGates, runGates_append, runGates_cons, runGates_nil,
    Gate.apply]
  rw [left_repeat hN hs ht, right_repeat hN hx ht]
  unfold suffixSwap headSwap
  split_ifs <;> omega

/-- Each legal suffix exchange is a genuine finite permutation. -/
def suffixEquiv (N k : ℕ) (hk : 2*k ≤ N) : Fin N ≃ Fin N where
  toFun x := ⟨suffixSwap N k x, suffixSwap_lt hk x.isLt⟩
  invFun x := ⟨suffixSwap N k x, suffixSwap_lt hk x.isLt⟩
  left_inv x := Fin.ext (suffixSwap_involutive hk x.isLt)
  right_inv x := Fin.ext (suffixSwap_involutive hk x.isLt)

/-- An address is indexed by positions in most-significant-first order. -/
abbrev Address (N : ℕ) := Fin N → Bool
/-- Pullback describes the new contents after moving source positions by `p`. -/
def moveAddress {N : ℕ} (p : Fin N ≃ Fin N) (a : Address N) : Address N :=
  fun i => a (p.symm i)

/-- Equality of address-position permutations gives equality on every raw bank. -/
theorem moveAddress_congr {N : ℕ} {p q : Fin N ≃ Fin N}
    (hpq : ∀ i, p i = q i) (a : Address N) : moveAddress p a = moveAddress q a := by
  have he : p = q := Equiv.ext hpq
  rw [he]

end BitWord
