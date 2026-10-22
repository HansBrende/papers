import TransposeFollowup.ScheduledMotion
import Mathlib.Data.List.Forall2
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Shared compilation of finite words of public native schedules.
Runtime composition uses the existing paid append; semantic composition
uses mathlib's relational fold theorem. No bank semantics are assumed. -/
namespace TransposeFollowup.ScheduledWord
open Classical FixedTapeCompiler ScheduledNativeIO
set_option autoImplicit false
variable {O T M X Y : Type*}

def transform (f : O → X → X) (ops : List O) (x : X) : X :=
  ops.foldl (fun y op => f op y) x

theorem transform_rel (f : O → X → X) (g : O → Y → Y) (ops : List O) (R : X → Y → Prop)
    (x : X) (y : Y) (hxy : R x y)
    (hstep : ∀ op ∈ ops, ∀ a b, R a b → R (f op a) (g op b)) :
    R (transform f ops x) (transform g ops y) := by
  apply List.rel_foldl (P:=R) (R:=fun a b => a=b ∧ a∈ops)
  · intro a b hab u v huv
    rcases huv with ⟨rfl,hu⟩
    exact hstep u hu a b hab
  · exact hxy
  · exact List.forall₂_same.mpr (fun op hop => ⟨rfl,hop⟩)

def ticks (cost : O → ℕ) (ops : List O) : ℕ := (ops.map cost).sum

def schedule (cost : O → ℕ) (code : O → ℕ → NativeIO.Program T M)
    (idle : NativeIO.Program T M) : List O → ℕ → NativeIO.Program T M
  | [] => fun _ => idle
  | op::ops => append (code op) (schedule cost code idle ops) (cost op)

theorem schedule_active (cost : O → ℕ) (code : O → ℕ → NativeIO.Program T M)
    (idle : NativeIO.Program T M) (ops : List O) (c : NativeIO.Config T M) (i : ℕ)
    (hi : NativeIO.Active idle c) (ha : ∀ op ∈ ops, ∀ j, NativeIO.Active (code op j) c) :
    NativeIO.Active (schedule cost code idle ops i) c := by
  induction ops generalizing i with
  | nil => exact hi
  | cons op ops ih =>
    apply append_active
    · exact ha op List.mem_cons_self
    · intro j; exact ih j (fun a h => ha a (List.mem_cons_of_mem _ h))

theorem schedule_exact (cost : O → ℕ) (code : O → ℕ → NativeIO.Program T M)
    (idle : NativeIO.Program T M) (run : O → NativeIO.Config T M → NativeIO.Config T M)
    (ops : List O) (w : List Bool) (c : NativeIO.Config T M)
    (hrun : ∀ op ∈ ops, ∀ d, trajectory (code op) w d (cost op)=run op d) :
    trajectory (schedule cost code idle ops) w c (ticks cost ops)=transform run ops c := by
  induction ops generalizing c with
  | nil => rfl
  | cons op ops ih =>
    simp only [ticks,List.map_cons,List.sum_cons,schedule,append_exact,hrun op List.mem_cons_self,
      transform,List.foldl_cons]
    exact ih _ (fun a ha => hrun a (List.mem_cons_of_mem _ ha))

theorem ticks_le (cost : O → ℕ) (ops : List O) (C : ℕ) (hc : ∀ op ∈ ops, cost op≤C) :
    ticks cost ops≤C*ops.length := by
  simpa [ticks,List.sum_replicate,mul_comm] using (List.sum_le_sum (g:=fun _ => C) hc)

def path (cost : O → ℕ) (move : O → T → ℕ → ℤ) : List O → T → ℕ → ℤ
  | [],_,_ => 0
  | op::ops,t,n => move op t n+path cost move ops t (n-cost op)

theorem path_zero (cost : O → ℕ) (move : O → T → ℕ → ℤ) (ops : List O) (t : T)
    (hz : ∀ op ∈ ops, move op t 0=0) : path cost move ops t 0=0 := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    rw [path,Nat.zero_sub,hz op List.mem_cons_self,ih (fun a ha => hz a (List.mem_cons_of_mem _ ha)),zero_add]

theorem path_after (cost : O → ℕ) (move : O → T → ℕ → ℤ) (ops : List O) (t : T)
    (ha : ∀ op ∈ ops, ∀ n, cost op≤n → move op t n=0) (n : ℕ) (hn : ticks cost ops≤n) :
    path cost move ops t n=0 := by
  induction ops generalizing n with
  | nil => rfl
  | cons op ops ih =>
    change cost op+ticks cost ops≤n at hn
    rw [path,ha op List.mem_cons_self n (by omega),
      ih (fun a h => ha a (List.mem_cons_of_mem _ h)) _ (by omega),zero_add]

theorem path_frozen (cost : O → ℕ) (move : O → T → ℕ → ℤ) (ops : List O) (t : T)
    (ha : ∀ op ∈ ops, ∀ n, cost op≤n → move op t n=0) (n : ℕ) :
    path cost move ops t (min n (ticks cost ops))=path cost move ops t n := by
  by_cases hn : n≤ticks cost ops
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (by omega),path_after cost move ops t ha _ le_rfl,
      path_after cost move ops t ha n (by omega)]

theorem schedule_position (cost : O → ℕ) (code : O → ℕ → NativeIO.Program T M)
    (idle : NativeIO.Program T M) (move : O → T → ℕ → ℤ) (ops : List O)
    (w : List Bool) (c : NativeIO.Config T M) (n : ℕ) (hn : n≤ticks cost ops) (t : T)
    (hp : ∀ op ∈ ops, ∀ d m, m≤cost op → (trajectory (code op) w d m).work.pos t=d.work.pos t+move op t m)
    (hf : ∀ op ∈ ops, ∀ m, move op t (min m (cost op))=move op t m) :
    (trajectory (schedule cost code idle ops) w c n).work.pos t=c.work.pos t+path cost move ops t n := by
  induction ops generalizing c n with
  | nil => have hz : n=0 := Nat.eq_zero_of_le_zero hn; simp [hz,trajectory,path]
  | cons op ops ih =>
    have h := append_position _ _ (cost op) (ticks cost ops) w t _ _
      (hp op List.mem_cons_self)
      (fun d m hm => ih d m hm (fun a ha => hp a (List.mem_cons_of_mem _ ha))
        (fun a ha => hf a (List.mem_cons_of_mem _ ha))) c n hn
    simpa only [schedule,path,hf op List.mem_cons_self] using h

end TransposeFollowup.ScheduledWord
