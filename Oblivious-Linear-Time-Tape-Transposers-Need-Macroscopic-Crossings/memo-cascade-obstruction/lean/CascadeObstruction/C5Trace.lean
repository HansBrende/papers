import CascadeObstruction.ClockBudget
import Transpose.Statement

/-! Exact finite tick words for Cascade 5.  Repetition blocks have period one
or two; their expansion is the physical tick word, not an accelerated run. -/

namespace CascadeObstruction.C5

open Transpose

set_option autoImplicit false

structure Tick where
  input : Dir := .stay
  work0 : Dir := .stay
  work1 : Dir := .stay
  emit : Bool := false
  deriving DecidableEq, Repr

def Tick.work (x : Tick) (h : Fin 2) : Dir := if h = 0 then x.work0 else x.work1

def dirValue (d : Dir) : ℤ := d.shift 0

@[simp] theorem dirValue_left : dirValue .left = -1 := rfl
@[simp] theorem dirValue_stay : dirValue .stay = 0 := rfl
@[simp] theorem dirValue_right : dirValue .right = 1 := rfl

theorem shift_eq_add (d : Dir) (p : ℤ) : d.shift p = p + dirValue d := by
  cases d <;> simp [Dir.shift, dirValue, sub_eq_add_neg]

def Tick.move (x : Tick) (h : Fin 3) : ℤ :=
  if h = 0 then dirValue x.input else if h = 1 then dirValue x.work0
  else dirValue x.work1

/-- Cumulative movement before tick `t`, frozen after the finite word. -/
def position (xs : List Tick) (h : Fin 3) (t : ℕ) : ℤ :=
  ((xs.take t).map (fun x => x.move h)).sum

@[simp] theorem position_nil (h : Fin 3) (t : ℕ) : position [] h t = 0 := by
  simp [position]

@[simp] theorem position_zero (xs : List Tick) (h : Fin 3) : position xs h 0 = 0 := by
  simp [position]

@[simp] theorem position_cons_succ (x : Tick) (xs : List Tick) (h : Fin 3) (t : ℕ) :
    position (x :: xs) h (t + 1) = x.move h + position xs h t := by
  simp [position]

theorem position_append (xs ys : List Tick) (h : Fin 3) (t : ℕ) :
    position (xs ++ ys) h t = position xs h t + position ys h (t - xs.length) := by
  simp [position, List.take_append, List.map_append, List.sum_append]

theorem position_frozen (xs : List Tick) (h : Fin 3) {t : ℕ} (ht : xs.length ≤ t) :
    position xs h t = position xs h xs.length := by
  simp [position, List.take_of_length_le ht]

inductive Block where
  | straight (count : ℕ) (tick : Tick)
  | pairs (count : ℕ) (first second : Tick)
  deriving DecidableEq, Repr

def Block.duration : Block → ℕ
  | .straight n _ => n
  | .pairs n _ _ => 2 * n

def Block.steps : Block → List Tick
  | .straight n x => List.replicate n x
  | .pairs n x y => (List.replicate n [x, y]).flatten

@[simp] theorem Block.steps_length (b : Block) : b.steps.length = b.duration := by
  cases b <;> simp [Block.steps, Block.duration, List.length_flatten, mul_comm]

/-- Exact capped-floor displacement of a single periodic block. -/
def Block.displacement : Block → Fin 3 → ℕ → ℤ
  | .straight n x, h, t => (min t n : ℕ) * x.move h
  | .pairs n x y, h, t =>
      (min ((t + 1) / 2) n : ℕ) * x.move h + (min (t / 2) n : ℕ) * y.move h

private theorem pair_position (n : ℕ) (x y : Tick) (h : Fin 3) (t : ℕ) :
    position ((List.replicate n [x, y]).flatten) h t =
      (min ((t + 1) / 2) n : ℕ) * x.move h + (min (t / 2) n : ℕ) * y.move h := by
  induction n generalizing t with
  | zero => simp [position]
  | succ n ih =>
    rcases t with _ | t
    · simp [position]
    rcases t with _ | t
    · simp [position, List.replicate_succ]
    simp only [List.replicate_succ, List.flatten_cons, List.cons_append,
      List.nil_append, position_cons_succ, ih]
    have h₁ : min ((t + 1 + 1 + 1) / 2) (n + 1) = min ((t + 1) / 2) n + 1 := by
      omega
    have h₂ : min ((t + 1 + 1) / 2) (n + 1) = min (t / 2) n + 1 := by omega
    rw [h₁, h₂]
    push_cast
    ring

theorem Block.position_steps (b : Block) (h : Fin 3) (t : ℕ) :
    position b.steps h t = b.displacement h t := by
  cases b with
  | straight n x => simp [Block.steps, Block.displacement, position]
  | pairs n x y => exact pair_position n x y h t

def blocksDuration (bs : List Block) : ℕ := (bs.map Block.duration).sum

def expand (bs : List Block) : List Tick := bs.flatMap Block.steps

@[simp] theorem expand_length (bs : List Block) : (expand bs).length = blocksDuration bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [expand, blocksDuration]

/-- A block-by-block exact path formula; subsequent blocks start only after
the complete preceding physical block. -/
def blockPosition : List Block → Fin 3 → ℕ → ℤ
  | [], _, _ => 0
  | b :: bs, h, t => b.displacement h t + blockPosition bs h (t - b.duration)

theorem position_expand (bs : List Block) (h : Fin 3) (t : ℕ) :
    position (expand bs) h t = blockPosition bs h t := by
  induction bs generalizing t with
  | nil => simp [expand, blockPosition]
  | cons b bs ih =>
    change position (b.steps ++ expand bs) h t = _
    rw [position_append, b.position_steps, b.steps_length, ih]
    rfl

def Block.totalMove : Block → Fin 3 → ℤ
  | .straight n x, h => (n : ℤ) * x.move h
  | .pairs n x y, h => (n : ℤ) * (x.move h + y.move h)

@[simp] theorem Block.position_end (b : Block) (h : Fin 3) :
    position b.steps h b.duration = b.totalMove h := by
  rw [b.position_steps]
  cases b with
  | straight n x => simp [Block.displacement, Block.duration, Block.totalMove]
  | pairs n x y =>
    have he : (2 * n + 1) / 2 = n := by omega
    simp [Block.displacement, Block.duration, Block.totalMove, he, mul_add]

def totalMove (bs : List Block) (h : Fin 3) : ℤ := (bs.map (fun b => b.totalMove h)).sum

@[simp] theorem totalMove_nil (h : Fin 3) : totalMove [] h = 0 := rfl

@[simp] theorem totalMove_cons (b : Block) (bs : List Block) (h : Fin 3) :
    totalMove (b :: bs) h = b.totalMove h + totalMove bs h := rfl

theorem position_expand_end (bs : List Block) (h : Fin 3) :
    position (expand bs) h (blocksDuration bs) = totalMove bs h := by
  induction bs with
  | nil => simp [expand, blocksDuration, totalMove]
  | cons b bs ih =>
    change position (b.steps ++ expand bs) h (b.duration + blocksDuration bs) = _
    rw [position_append,
      position_frozen b.steps h (by simp), b.steps_length, b.position_end]
    simpa [totalMove] using congrArg (b.totalMove h + ·) ih

@[simp] theorem blocksDuration_append (xs ys : List Block) :
    blocksDuration (xs ++ ys) = blocksDuration xs + blocksDuration ys := by
  simp [blocksDuration]

@[simp] theorem totalMove_append (xs ys : List Block) (h : Fin 3) :
    totalMove (xs ++ ys) h = totalMove xs h + totalMove ys h := by
  simp [totalMove]

@[simp] theorem blocksDuration_flatten_replicate (n : ℕ) (bs : List Block) :
    blocksDuration ((List.replicate n bs).flatten) = n * blocksDuration bs := by
  induction n with
  | zero => simp [blocksDuration]
  | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem totalMove_flatten_replicate (n : ℕ) (bs : List Block) (h : Fin 3) :
    totalMove ((List.replicate n bs).flatten) h = (n : ℤ) * totalMove bs h := by
  induction n with
  | zero => simp [totalMove]
  | succ n ih => simp [List.replicate_succ, ih, add_mul, add_comm]

end CascadeObstruction.C5
