import SoftRecovery.Conditioning

namespace SoftRecovery

open Finset HalfRate MotionDepthCodes
set_option autoImplicit false

variable {A : Type*} [DecidableEq A]

/-- Information about the helper `e` gained by recovering `v` in context `K`. -/
def innovation (h : Finset A → ℝ) (e : A) (K : Finset A) (v : A) : ℝ :=
  mi h e (insert v K) - mi h e K

theorem innovation_nonneg {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (e : A) (K : Finset A) (v : A) : 0 ≤ innovation h e K v :=
  sub_nonneg.mpr (mi_mono hh e (subset_insert v K))

theorem increment_eq_innovation_add (h : Finset A → ℝ) (e : A) (K : Finset A) (v : A) :
    increment h K v = innovation h e K v + increment h (insert e K) v := by
  simp only [increment, innovation, mi, insert_comm e v]
  ring

/-- Exact contexts for a list of helper records; each later helper is
conditioned on precisely the earlier helpers in this list. -/
def helperInnovations (h : Finset A → ℝ) (v : A) : Finset A → List A → ℝ
  | _, [] => 0
  | K, e :: es => innovation h e K v + helperInnovations h v (insert e K) es

theorem increment_eq_helperInnovations_add (h : Finset A → ℝ) (v : A) :
    ∀ (es : List A) (K : Finset A),
      increment h K v = helperInnovations h v K es +
        increment h (es.toFinset ∪ K) v := by
  intro es
  induction es with
  | nil => intro K; simp [helperInnovations]
  | cons e es ih =>
    intro K
    have hs := increment_eq_innovation_add h e K v
    have hi := ih (insert e K)
    simp only [union_insert] at hi
    simp only [helperInnovations, List.toFinset_cons, insert_union]
    linarith

/-- A record's next use must retain the preceding context AND recovered symbol. -/
def NestedUses : Finset A → List (Finset A × A) → Prop
  | _, [] => True
  | L, (K, v) :: rest => L ⊆ K ∧ NestedUses (insert v K) rest

def innovationSum (h : Finset A → ℝ) (e : A) (uses : List (Finset A × A)) : ℝ :=
  (uses.map fun kv => innovation h e kv.1 kv.2).sum

/-- Information discarded between consecutive actual use contexts. -/
def chainLoss (h : Finset A → ℝ) : Finset A → List (Finset A × A) → ℝ
  | _, [] => 0
  | L, (K, v) :: rest => conditionalRank h L K + chainLoss h (insert v K) rest

/-- Only decreases in information about this helper are charged. This is
at most `chainLoss`, but need not decrease under further conditioning. -/
noncomputable def helperLoss (h : Finset A → ℝ) (e : A) :
    Finset A → List (Finset A × A) → ℝ
  | _, [] => 0
  | L, (K, v) :: rest => max 0 (mi h e L - mi h e K) + helperLoss h e (insert v K) rest

def endContext : Finset A → List (Finset A × A) → Finset A
  | L, [] => L
  | _, (K, v) :: rest => endContext (insert v K) rest

/-- Semantic nesting: the next context determines the preceding context and
recovered symbol. Their variable names need not occur in the next set. -/
def RetainedUses (h : Finset A → ℝ) : Finset A → List (Finset A × A) → Prop
  | _, [] => True
  | L, (K, v) :: rest => conditionalRank h L K = 0 ∧ RetainedUses h (insert v K) rest

theorem chainLoss_nonneg {h : Finset A → ℝ} (hh : IsPolymatroid h) :
    ∀ (uses : List (Finset A × A)) (L : Finset A), 0 ≤ chainLoss h L uses := by
  intro uses
  induction uses with
  | nil => intro _; exact le_rfl
  | cons kv rest ih =>
    intro L
    exact add_nonneg (conditionalRank_nonneg hh L kv.1) (ih _)

theorem chainLoss_contr_le {h : Finset A → ℝ} (hh : IsPolymatroid h) (Z : Finset A) :
    ∀ (uses : List (Finset A × A)) (L : Finset A),
      chainLoss (contr h Z) L uses ≤ chainLoss h L uses := by
  intro uses
  induction uses with
  | nil => intro _; exact le_rfl
  | cons kv rest ih =>
    intro L
    simp only [chainLoss, conditionalRank_contr]
    exact add_le_add (conditionalRank_antitone hh L subset_union_left) (ih _)

theorem NestedUses.retained (h : Finset A → ℝ) :
    ∀ {uses : List (Finset A × A)} {L : Finset A},
      NestedUses L uses → RetainedUses h L uses := by
  intro uses
  induction uses with
  | nil => intro _ _; trivial
  | cons kv rest ih =>
    intro L hn
    exact ⟨conditionalRank_of_subset h hn.1, ih hn.2⟩

theorem RetainedUses.contr {h : Finset A → ℝ} (hh : IsPolymatroid h) (Z : Finset A) :
    ∀ {uses : List (Finset A × A)} {L : Finset A},
      RetainedUses h L uses → RetainedUses (contr h Z) L uses := by
  intro uses
  induction uses with
  | nil => intro _ _; trivial
  | cons kv rest ih =>
    rcases kv with ⟨K, v⟩
    intro L hn
    refine ⟨?_, ih hn.2⟩
    rw [conditionalRank_contr]
    exact le_antisymm ((conditionalRank_antitone hh L subset_union_left).trans_eq hn.1)
      (conditionalRank_nonneg hh L (K ∪ Z))

theorem RetainedUses.loss_eq_zero {h : Finset A → ℝ} :
    ∀ {uses : List (Finset A × A)} {L : Finset A},
      RetainedUses h L uses → chainLoss h L uses = 0 := by
  intro uses
  induction uses with
  | nil => intro _ _; rfl
  | cons kv rest ih =>
    intro L hn
    simp only [chainLoss, hn.1, ih hn.2, add_zero]

theorem helperLoss_nonneg (h : Finset A → ℝ) (e : A) :
    ∀ (uses : List (Finset A × A)) (L : Finset A), 0 ≤ helperLoss h e L uses := by
  intro uses
  induction uses with
  | nil => intro _; exact le_rfl
  | cons kv rest ih =>
    intro L
    exact add_nonneg (le_max_left _ _) (ih _)

theorem helperLoss_le_chainLoss {h : Finset A → ℝ} (hh : IsPolymatroid h) (e : A) :
    ∀ (uses : List (Finset A × A)) (L : Finset A),
      helperLoss h e L uses ≤ chainLoss h L uses := by
  intro uses
  induction uses with
  | nil => intro _; exact le_rfl
  | cons kv rest ih =>
    intro L
    have hm := mi_le_add_conditionalRank hh e L kv.1
    exact add_le_add (max_le (conditionalRank_nonneg hh L kv.1) (by linarith)) (ih _)

/-- Telescoping needs only the positive drops of the helper's potential.
This algebraic bound holds even without the polymatroid axioms. -/
theorem innovations_le_helperLoss (h : Finset A → ℝ) (e : A) :
    ∀ (uses : List (Finset A × A)) (L : Finset A),
      innovationSum h e uses ≤ mi h e (endContext L uses) - mi h e L +
        helperLoss h e L uses := by
  intro uses
  induction uses with
  | nil =>
    intro L
    simp [innovationSum, endContext, helperLoss]
  | cons kv rest ih =>
    rcases kv with ⟨K, v⟩
    intro L
    have hi := ih (insert v K)
    have hm := le_max_right (0 : ℝ) (mi h e L - mi h e K)
    simp only [innovationSum, List.map_cons, List.sum_cons, innovation,
      endContext, helperLoss] at *
    linarith

theorem innovations_le_helper_capacity {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (e : A) (uses : List (Finset A × A)) (L : Finset A) :
    innovationSum h e uses ≤ h {e} - mi h e L + helperLoss h e L uses := by
  have hs := innovations_le_helperLoss h e uses L
  have hm := hh.mono (subset_insert e (endContext L uses))
  unfold mi at hs ⊢
  linarith

/-- The whole-context loss bound is a corollary of helper-specific loss. -/
theorem innovations_le_with_loss {h : Finset A → ℝ} (hh : IsPolymatroid h) (e : A)
    (uses : List (Finset A × A)) (L : Finset A) :
    innovationSum h e uses ≤ mi h e (endContext L uses) - mi h e L +
      chainLoss h L uses :=
  (innovations_le_helperLoss h e uses L).trans
    (add_le_add le_rfl (helperLoss_le_chainLoss hh e uses L))

theorem innovations_le_capacity_add_loss {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (e : A) (uses : List (Finset A × A)) (L : Finset A) :
    innovationSum h e uses ≤ h {e} - mi h e L + chainLoss h L uses := by
  exact (innovations_le_helper_capacity hh e uses L).trans
    (add_le_add le_rfl (helperLoss_le_chainLoss hh e uses L))

theorem retained_innovations_le {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (e : A) {uses : List (Finset A × A)} {L : Finset A}
    (hn : RetainedUses h L uses) :
    innovationSum h e uses ≤ h {e} - mi h e L := by
  simpa [hn.loss_eq_zero] using innovations_le_capacity_add_loss hh e uses L

/-- The original literal-nesting theorem follows from semantic retention. -/
theorem nested_innovations_le {h : Finset A → ℝ} (hh : IsPolymatroid h) (e : A)
    (uses : List (Finset A × A)) (L : Finset A) (hn : NestedUses L uses) :
    innovationSum h e uses ≤ h {e} - mi h e L :=
  retained_innovations_le hh e (hn.retained h)

theorem nested_innovations_le_capacity {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (e : A) {uses : List (Finset A × A)} (hn : NestedUses ∅ uses) :
    innovationSum h e uses ≤ h {e} := by
  simpa [mi_empty hh] using nested_innovations_le hh e uses ∅ hn

end SoftRecovery
