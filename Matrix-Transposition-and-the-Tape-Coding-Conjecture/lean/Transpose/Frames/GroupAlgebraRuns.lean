import Mathlib

/-!
# The group-algebra bound: at least `W` frame changes even when streams in different frames are combined

The group-algebra model. Each wire holds a *content*: a function from frames (an additive group
`F`) to coefficient vectors in `Fin W → ZMod 2`, i.e. a formal sum of sheared items. Events: a gate
`i ← i + j` (any `i`, `j`, no frame condition) or a *change* of wire `w` by `Δ`, which shifts its
content: new content at frame `f` is the old content at `f − Δ`. Initially wire `u` holds item `u`
at frame `S u`; at the end wire `ρ u` must hold item `u` at frame `S u + I`. Theorem: the run
contains at least `W` changes.

Potential: the span of the vectors `u ↦ (content of w at frame I + S u) u` over all wires `w`.
-/

namespace Transpose.ShearFrame.GroupAlgebra

open Module Submodule

variable {W : ℕ} {F : Type} [AddCommGroup F] [DecidableEq F]

abbrev Vec (W : ℕ) := Fin W → ZMod 2

def e (u : Fin W) : Vec W := Pi.single u 1

theorem e_linearIndependent : LinearIndependent (ZMod 2) (e (W := W)) :=
  Pi.linearIndependent_single_one (Fin W) (ZMod 2)

/-- Content of one wire: frame ↦ coefficient vector. -/
abbrev Content (W : ℕ) (F : Type) := F → Vec W

structure Cfg (W : ℕ) (F : Type) where
  row : Fin W → Content W F

inductive Event (W : ℕ) (F : Type) where
  | gate (i j : Fin W)
  | change (w : Fin W) (Δ : F)

namespace Cfg

def step (c : Cfg W F) : Event W F → Cfg W F
  | .gate i j => ⟨Function.update c.row i (c.row i + c.row j)⟩
  | .change w Δ => ⟨Function.update c.row w (fun f => c.row w (f - Δ))⟩

def run (c : Cfg W F) : List (Event W F) → Cfg W F
  | [] => c
  | ev :: evs => (c.step ev).run evs

end Cfg

def changes : List (Event W F) → ℕ
  | [] => 0
  | .change _ _ :: evs => changes evs + 1
  | .gate _ _ :: evs => changes evs

/-- The vector attached to wire `w`: coefficient of item `u` at frame `I + S u`. -/
def vecI (I : F) (S : Fin W → F) (c : Cfg W F) (w : Fin W) : Vec W :=
  fun u => c.row w (I + S u) u

noncomputable def pot (I : F) (S : Fin W → F) (c : Cfg W F) : ℕ :=
  finrank (ZMod 2) ↥(span (ZMod 2) (Set.range (vecI I S c)))

/-! ### Gates do not increase the potential -/

theorem vecI_gate (I : F) (S : Fin W → F) (c : Cfg W F) (i j : Fin W) :
    vecI I S (c.step (.gate i j)) = Function.update (vecI I S c) i (vecI I S c i + vecI I S c j) := by
  funext w u
  by_cases hw : w = i
  · subst hw
    simp [vecI, Cfg.step, Function.update_self]
  · simp [vecI, Cfg.step, Function.update_of_ne hw]

theorem span_update_add_le (v : Fin W → Vec W) (i j : Fin W) :
    span (ZMod 2) (Set.range (Function.update v i (v i + v j))) ≤ span (ZMod 2) (Set.range v) := by
  refine span_le.mpr ?_
  rintro _ ⟨w, rfl⟩
  by_cases hw : w = i
  · subst hw
    rw [Function.update_self]
    exact add_mem (subset_span ⟨w, rfl⟩) (subset_span ⟨j, rfl⟩)
  · rw [Function.update_of_ne hw]
    exact subset_span ⟨w, rfl⟩

theorem pot_gate_le (I : F) (S : Fin W → F) (c : Cfg W F) (i j : Fin W) :
    pot I S (c.step (.gate i j)) ≤ pot I S c := by
  unfold pot
  rw [vecI_gate]
  exact Submodule.finrank_mono (span_update_add_le _ _ _)

/-! ### A change raises the potential by at most one -/

theorem span_update_le (v : Fin W → Vec W) (w : Fin W) (x : Vec W) :
    span (ZMod 2) (Set.range (Function.update v w x)) ≤
      span (ZMod 2) (Set.range v) ⊔ span (ZMod 2) {x} := by
  refine span_le.mpr ?_
  rintro _ ⟨w', rfl⟩
  by_cases hw : w' = w
  · subst hw
    rw [Function.update_self]
    exact Submodule.mem_sup_right (subset_span (Set.mem_singleton _))
  · rw [Function.update_of_ne hw]
    exact Submodule.mem_sup_left (subset_span ⟨w', rfl⟩)

theorem finrank_sup_singleton_le (U : Submodule (ZMod 2) (Vec W)) (x : Vec W) :
    finrank (ZMod 2) ↥(U ⊔ span (ZMod 2) {x}) ≤ finrank (ZMod 2) ↥U + 1 := by
  calc finrank (ZMod 2) ↥(U ⊔ span (ZMod 2) {x})
      ≤ finrank (ZMod 2) ↥U + finrank (ZMod 2) ↥(span (ZMod 2) {x}) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ finrank (ZMod 2) ↥U + 1 := by
        have := finrank_span_le_card (R := ZMod 2) ({x} : Set (Vec W))
        simp at this
        omega

theorem vecI_change (I : F) (S : Fin W → F) (c : Cfg W F) (w : Fin W) (Δ : F) :
    vecI I S (c.step (.change w Δ)) =
      Function.update (vecI I S c) w (fun u => c.row w (I + S u - Δ) u) := by
  funext w' u
  by_cases hw : w' = w
  · subst hw
    simp [vecI, Cfg.step, Function.update_self]
  · simp [vecI, Cfg.step, Function.update_of_ne hw]

theorem pot_change_le (I : F) (S : Fin W → F) (c : Cfg W F) (w : Fin W) (Δ : F) :
    pot I S (c.step (.change w Δ)) ≤ pot I S c + 1 := by
  unfold pot
  rw [vecI_change]
  exact (Submodule.finrank_mono (span_update_le _ _ _)).trans (finrank_sup_singleton_le _ _)

theorem pot_run_le (I : F) (S : Fin W → F) :
    ∀ (evs : List (Event W F)) (c : Cfg W F), pot I S (c.run evs) ≤ pot I S c + changes evs
  | [], c => by simp [Cfg.run, changes]
  | .gate i j :: evs, c => by
      simp only [Cfg.run, changes]
      exact (pot_run_le I S evs _).trans (Nat.add_le_add_right (pot_gate_le I S c i j) _)
  | .change w Δ :: evs, c => by
      simp only [Cfg.run, changes]
      have h1 := pot_run_le I S evs (c.step (.change w Δ))
      have h2 := pot_change_le I S c w Δ
      omega

/-! ### Initial and final values -/

/-- Wire `u` holds item `u` at frame `S u`. -/
def init (S : Fin W → F) : Cfg W F :=
  ⟨fun u f => if f = S u then e u else 0⟩

theorem pot_init (I : F) (hI : I ≠ 0) (S : Fin W → F) : pot I S (init S) = 0 := by
  unfold pot
  have : vecI I S (init S) = fun _ => 0 := by
    funext w u
    simp only [vecI, init, Pi.zero_apply]
    by_cases hu : u = w
    · subst hu
      have : I + S u ≠ S u := by
        intro h
        exact hI (by simpa using h)
      simp [this]
    · split_ifs
      · simp [e, Pi.single_apply, hu]
      · rfl
  rw [this]
  simp

theorem pot_final (I : F) (S : Fin W → F) (ρ : Equiv.Perm (Fin W)) (c : Cfg W F)
    (hend : ∀ u, c.row (ρ u) = fun f => if f = S u + I then e u else 0) :
    pot I S c = W := by
  unfold pot
  have hv : ∀ u, vecI I S c (ρ u) = e u := by
    intro u
    funext u'
    rw [vecI, hend u]
    show (if I + S u' = S u + I then e u else 0) u' = e u u'
    by_cases hu : u' = u
    · subst hu; simp [add_comm]
    · split_ifs
      · rfl
      · simp [e, Pi.single_apply, hu]
  have hrange : Set.range (vecI I S c) = Set.range (e (W := W)) := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨ρ.symm w, ?_⟩
      rw [← hv (ρ.symm w), Equiv.apply_symm_apply]
    · rintro ⟨u, rfl⟩
      exact ⟨ρ u, hv u⟩
  rw [hrange, finrank_span_eq_card e_linearIndependent, Fintype.card_fin]

/-- **Group-algebra bound.** Any run from the initial configuration to a configuration in which
wire `ρ u` holds item `u` at frame `S u + I` (and nothing else) contains at least `W` changes. -/
theorem changes_ge_W (I : F) (hI : I ≠ 0) (S : Fin W → F) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W F))
    (hend : ∀ u, ((init S).run evs).row (ρ u) = fun f => if f = S u + I then e u else 0) :
    W ≤ changes evs := by
  have h := pot_run_le I S evs (init S)
  rw [pot_init I hI S, pot_final I S ρ _ hend] at h
  omega

/-- Cost version: with any cost ≥ 1 per change, the total cost is at least `W`. -/
theorem cost_ge_W (I : F) (hI : I ≠ 0) (S : Fin W → F) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W F))
    (hend : ∀ u, ((init S).run evs).row (ρ u) = fun f => if f = S u + I then e u else 0)
    (cost : Event W F → ℕ) (hcost : ∀ w Δ, 1 ≤ cost (.change w Δ)) :
    W ≤ (evs.map cost).sum := by
  have key : ∀ evs : List (Event W F), changes evs ≤ (evs.map cost).sum := by
    intro evs
    induction evs with
    | nil => simp [changes]
    | cons ev evs ih =>
      cases ev with
      | gate i j => simp only [changes, List.map_cons, List.sum_cons]; omega
      | change w Δ => simp only [changes, List.map_cons, List.sum_cons]; have := hcost w Δ; omega
  exact (changes_ge_W I hI S ρ evs hend).trans (key evs)

end Transpose.ShearFrame.GroupAlgebra
