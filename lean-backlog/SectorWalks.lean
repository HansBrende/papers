import Mathlib.Algebra.Group.Basic

/-!
# Algebra of mutual-helper sector walks

These identities hold in every group, without finiteness or commutativity.
They verify the algebraic reduction behind the written odd-walk counting
argument. They do not formalize the walk enumeration, capacity bound,
group structure theorem, or separator transfer.
-/

namespace LeanBacklog.SectorWalks

variable {G : Type*} [Group G]

def step (g t u : G) : G := t⁻¹ * g⁻¹ * u⁻¹

def sector (cell : G × G) : G := cell.1⁻¹ * cell.2

def move (cell : G × G) (t u : G) : G × G :=
  (cell.2 * t, cell.1 * u⁻¹)

theorem move_sector (cell : G × G) (t u : G) :
    sector (move cell t u) = step (sector cell) t u := by
  simp [sector, move, step, mul_assoc]

theorem move_reverse (cell : G × G) (t u : G) :
    move (move cell t u) u t = cell := by
  simp [move, mul_assoc]

theorem two_steps (g t u v z : G) :
    step (step g t u) v z = (v⁻¹ * u) * g * (t * z⁻¹) := by
  simp [step, mul_assoc]

theorem sandwich_eq_iff_square (g x y : G) :
    g * x * g = y ↔ (g * x) ^ 2 = y * x := by
  constructor
  · intro h
    simpa [pow_two, mul_assoc] using congrArg (fun a => a * x) h
  · intro h
    simpa [pow_two, mul_assoc] using congrArg (fun a => a * x⁻¹) h

theorem odd_step_fixed_iff_sandwich (g a b t u : G) :
    step (a * g * b) t u = g ↔ g * (u * a) * g = t⁻¹ * b⁻¹ := by
  constructor
  · intro h
    calc
      g * (u * a) * g = step (a * g * b) t u * (u * a) * g := by rw [h]
      _ = t⁻¹ * b⁻¹ := by simp [step, mul_assoc]
  · intro h
    have hg : g = (t⁻¹ * b⁻¹) * g⁻¹ * a⁻¹ * u⁻¹ := by
      calc
        g = (g * (u * a) * g) * g⁻¹ * a⁻¹ * u⁻¹ := by simp [mul_assoc]
        _ = (t⁻¹ * b⁻¹) * g⁻¹ * a⁻¹ * u⁻¹ := by rw [h]
    simpa [step, mul_assoc] using hg.symm

theorem odd_step_fixed_iff_square (g a b t u : G) :
    step (a * g * b) t u = g ↔
      (g * (u * a)) ^ 2 = (t⁻¹ * b⁻¹) * (u * a) :=
  (odd_step_fixed_iff_sandwich g a b t u).trans
    (sandwich_eq_iff_square g (u * a) (t⁻¹ * b⁻¹))

/-- The change of variables used in the elementary square-root moment count. -/
theorem equal_squares_iff_inverted (a h : G) :
    a ^ 2 = (a * h) ^ 2 ↔ a⁻¹ * h * a = h⁻¹ := by
  constructor
  · intro he
    have he' := congrArg (fun x => a⁻¹ * x * h⁻¹ * a⁻¹) he
    have hh : a * h⁻¹ * a⁻¹ = h := by
      simpa [pow_two, mul_assoc] using he'
    simpa [mul_assoc] using (congrArg (fun x => a⁻¹ * x * a) hh).symm
  · intro hh
    have hh' := congrArg (fun x => a * x * h) hh
    have hah : h * a * h = a := by simpa [mul_assoc] using hh'
    simpa [pow_two, mul_assoc] using (congrArg (fun x => a * x) hah).symm

#print axioms move_sector
#print axioms move_reverse
#print axioms two_steps
#print axioms sandwich_eq_iff_square
#print axioms odd_step_fixed_iff_sandwich
#print axioms odd_step_fixed_iff_square
#print axioms equal_squares_iff_inverted

end LeanBacklog.SectorWalks
