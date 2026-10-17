import Mathlib

/-!
# The frame-change bound: every shear-frame gadget makes at least `W` frame changes

Abstract run model of a shear-frame gadget. `W` wires each carry a frame (any type
`F`) and an item-vector in `(Fin W → ZMod 2)`. Events are XOR gates `i ← i + j`, allowed only when
`i ≠ j` are at the same frame, and frame changes of one wire. Initially wire `u` is at frame `S u`
and holds the unit vector `e u`. At the end wire `ρ u` must be at frame `shift (S u)` and hold `e u`,
where `shift` has no fixed point (for matrices, `shift M = M + 1`). Then the run contains at least `W`
frame changes. Since every frame change costs rank ≥ 1, the gadget cost `s` is at least `W`.
-/

namespace Transpose.ShearFrame

open Module Submodule

variable {W : ℕ} {F : Type} [DecidableEq F]

abbrev Vec (W : ℕ) := Fin W → ZMod 2

/-- The unit vector of wire `u`. -/
def e (u : Fin W) : Vec W := Pi.single u 1

theorem e_linearIndependent : LinearIndependent (ZMod 2) (e (W := W)) :=
  Pi.linearIndependent_single_one (Fin W) (ZMod 2)

/-- A configuration: current frame and current vector of each wire. -/
structure Cfg (W : ℕ) (F : Type) where
  frame : Fin W → F
  vec : Fin W → Vec W

inductive Event (W : ℕ) (F : Type) where
  | gate (i j : Fin W)
  | move (w : Fin W) (f : F)

namespace Cfg

/-- Apply one event. -/
def step (c : Cfg W F) : Event W F → Cfg W F
  | .gate i j => { c with vec := Function.update c.vec i (c.vec i + c.vec j) }
  | .move w f => { c with frame := Function.update c.frame w f }

/-- A gate must touch two distinct wires at a common frame. -/
def valid (c : Cfg W F) : Event W F → Prop
  | .gate i j => i ≠ j ∧ c.frame i = c.frame j
  | .move _ _ => True

def run (c : Cfg W F) : List (Event W F) → Cfg W F
  | [] => c
  | ev :: evs => (c.step ev).run evs

def allValid (c : Cfg W F) : List (Event W F) → Prop
  | [] => True
  | ev :: evs => c.valid ev ∧ (c.step ev).allValid evs

/-- Span of the vectors on the wires currently at frame `f`. -/
noncomputable def sigma (c : Cfg W F) (f : F) : Submodule (ZMod 2) (Vec W) :=
  span (ZMod 2) (c.vec '' {w | c.frame w = f})

end Cfg

/-- Number of frame changes in an event list. -/
def moves : List (Event W F) → ℕ
  | [] => 0
  | .move _ _ :: evs => moves evs + 1
  | .gate _ _ :: evs => moves evs

/-- The items that must end at frame `f`. -/
noncomputable def target (S : Fin W → F) (shift : F → F) (f : F) : Submodule (ZMod 2) (Vec W) :=
  span (ZMod 2) (e '' {u | shift (S u) = f})

/-- The potential `Φ = Σ_f dim (Σ_f ⊓ N_f)`. -/
noncomputable def pot (S : Fin W → F) (shift : F → F) (c : Cfg W F) : ℕ :=
  ∑ f ∈ Finset.univ.image (shift ∘ S), finrank (ZMod 2) ↥(c.sigma f ⊓ target S shift f)

/-! ### Gates do not change any `sigma` -/

theorem sigma_gate (c : Cfg W F) {i j : Fin W} (hij : i ≠ j) (hf : c.frame i = c.frame j) (f : F) :
    (c.step (.gate i j)).sigma f = c.sigma f := by
  simp only [Cfg.step, Cfg.sigma]
  by_cases hi : c.frame i = f
  · have hj : c.frame j = f := hf ▸ hi
    apply le_antisymm
    · refine span_le.mpr ?_
      rintro _ ⟨w, hw, rfl⟩
      by_cases hwi : w = i
      · subst hwi
        rw [Function.update_self]
        exact add_mem (subset_span ⟨w, hw, rfl⟩) (subset_span ⟨j, hj, rfl⟩)
      · rw [Function.update_of_ne hwi]
        exact subset_span ⟨w, hw, rfl⟩
    · refine span_le.mpr ?_
      rintro _ ⟨w, hw, rfl⟩
      by_cases hwi : w = i
      · subst hwi
        have h1 : c.vec w + c.vec j ∈ span (ZMod 2)
            (Function.update c.vec w (c.vec w + c.vec j) '' {w' | c.frame w' = f}) :=
          subset_span ⟨w, hw, by rw [Function.update_self]⟩
        have h2 : c.vec j ∈ span (ZMod 2)
            (Function.update c.vec w (c.vec w + c.vec j) '' {w' | c.frame w' = f}) :=
          subset_span ⟨j, hj, by rw [Function.update_of_ne (Ne.symm hij)]⟩
        have hab : (c.vec w + c.vec j) - c.vec j = c.vec w := by abel
        have hmem := sub_mem h1 h2
        rwa [hab] at hmem
      · exact subset_span ⟨w, hw, by rw [Function.update_of_ne hwi]⟩
  · congr 1
    apply Set.image_congr
    intro w hw
    have hwi : w ≠ i := fun h => hi (h ▸ hw)
    exact Function.update_of_ne hwi _ _

/-! ### A frame change raises the potential by at most one -/

theorem finrank_inf_le_of_le {U U' N : Submodule (ZMod 2) (Vec W)} (h : U' ≤ U) :
    finrank (ZMod 2) ↥(U' ⊓ N) ≤ finrank (ZMod 2) ↥(U ⊓ N) :=
  Submodule.finrank_mono (inf_le_inf_right N h)

theorem finrank_inf_sup_singleton_le (U N : Submodule (ZMod 2) (Vec W)) (x : Vec W) :
    finrank (ZMod 2) ↥((U ⊔ span (ZMod 2) {x}) ⊓ N) ≤ finrank (ZMod 2) ↥(U ⊓ N) + 1 := by
  set A := (U ⊔ span (ZMod 2) {x}) ⊓ N with hA
  have h1 : A ⊔ U ≤ U ⊔ span (ZMod 2) {x} := sup_le inf_le_left le_sup_left
  have h2 : finrank (ZMod 2) ↥(U ⊔ span (ZMod 2) {x}) ≤ finrank (ZMod 2) ↥U + 1 := by
    calc finrank (ZMod 2) ↥(U ⊔ span (ZMod 2) {x})
        ≤ finrank (ZMod 2) ↥U + finrank (ZMod 2) ↥(span (ZMod 2) {x}) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ finrank (ZMod 2) ↥U + 1 := by
          have := finrank_span_le_card (R := ZMod 2) ({x} : Set (Vec W))
          simp at this
          omega
  have h3 : A ⊓ U = U ⊓ N := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    · exact le_inf (le_inf (inf_le_left.trans le_sup_left) inf_le_right) inf_le_left
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq A U
  have h5 : finrank (ZMod 2) ↥(A ⊔ U) ≤ finrank (ZMod 2) ↥U + 1 :=
    (Submodule.finrank_mono h1).trans h2
  rw [h3] at h4
  omega

theorem sigma_move_le (c : Cfg W F) (w : Fin W) (f₀ f : F) :
    (c.step (.move w f₀)).sigma f ≤ c.sigma f ⊔ span (ZMod 2) {c.vec w} := by
  simp only [Cfg.step, Cfg.sigma]
  refine span_le.mpr ?_
  rintro _ ⟨w', hw', rfl⟩
  by_cases hww : w' = w
  · subst hww
    exact Submodule.mem_sup_right (subset_span (Set.mem_singleton _))
  · have : c.frame w' = f := by
      simpa [Function.update_of_ne hww] using hw'
    exact Submodule.mem_sup_left (subset_span ⟨w', this, rfl⟩)

theorem sigma_move_le_of_ne (c : Cfg W F) (w : Fin W) {f₀ f : F} (hf : f ≠ f₀) :
    (c.step (.move w f₀)).sigma f ≤ c.sigma f := by
  simp only [Cfg.step, Cfg.sigma]
  refine span_le.mpr ?_
  rintro _ ⟨w', hw', rfl⟩
  by_cases hww : w' = w
  · subst hww
    simp [Function.update_self] at hw'
    exact absurd hw'.symm hf
  · have : c.frame w' = f := by
      simpa [Function.update_of_ne hww] using hw'
    exact subset_span ⟨w', this, rfl⟩

theorem pot_move_le (S : Fin W → F) (shift : F → F) (c : Cfg W F) (w : Fin W) (f₀ : F) :
    pot S shift (c.step (.move w f₀)) ≤ pot S shift c + 1 := by
  unfold pot
  have hterm : ∀ f ∈ Finset.univ.image (shift ∘ S),
      finrank (ZMod 2) ↥((c.step (.move w f₀)).sigma f ⊓ target S shift f) ≤
        finrank (ZMod 2) ↥(c.sigma f ⊓ target S shift f) + (if f = f₀ then 1 else 0) := by
    intro f _
    by_cases hf : f = f₀
    · subst hf
      rw [if_pos rfl]
      exact (finrank_inf_le_of_le (sigma_move_le c w f f)).trans
        (finrank_inf_sup_singleton_le _ _ _)
    · rw [if_neg hf, Nat.add_zero]
      exact finrank_inf_le_of_le (sigma_move_le_of_ne c w hf)
  calc ∑ f ∈ Finset.univ.image (shift ∘ S),
        finrank (ZMod 2) ↥((c.step (.move w f₀)).sigma f ⊓ target S shift f)
      ≤ ∑ f ∈ Finset.univ.image (shift ∘ S),
        (finrank (ZMod 2) ↥(c.sigma f ⊓ target S shift f) + (if f = f₀ then 1 else 0)) :=
        Finset.sum_le_sum hterm
    _ = (∑ f ∈ Finset.univ.image (shift ∘ S), finrank (ZMod 2) ↥(c.sigma f ⊓ target S shift f)) +
        ∑ f ∈ Finset.univ.image (shift ∘ S), (if f = f₀ then 1 else 0) := Finset.sum_add_distrib
    _ ≤ _ := by
        apply Nat.add_le_add_left
        rw [Finset.sum_ite_eq']
        split_ifs <;> omega

theorem pot_gate_eq (S : Fin W → F) (shift : F → F) (c : Cfg W F) {i j : Fin W}
    (hij : i ≠ j) (hf : c.frame i = c.frame j) :
    pot S shift (c.step (.gate i j)) = pot S shift c := by
  unfold pot
  apply Finset.sum_congr rfl
  intro f _
  rw [sigma_gate c hij hf f]

/-- Along a valid run the potential grows by at most the number of moves. -/
theorem pot_run_le (S : Fin W → F) (shift : F → F) :
    ∀ (evs : List (Event W F)) (c : Cfg W F), c.allValid evs →
      pot S shift (c.run evs) ≤ pot S shift c + moves evs
  | [], c, _ => by simp [Cfg.run, moves]
  | .gate i j :: evs, c, hv => by
      obtain ⟨⟨hij, hf⟩, hv'⟩ := hv
      simp only [Cfg.run, moves]
      have := pot_run_le S shift evs (c.step (.gate i j)) hv'
      rwa [pot_gate_eq S shift c hij hf] at this
  | .move w f₀ :: evs, c, hv => by
      obtain ⟨_, hv'⟩ := hv
      simp only [Cfg.run, moves]
      have h1 := pot_run_le S shift evs (c.step (.move w f₀)) hv'
      have h2 := pot_move_le S shift c w f₀
      omega

/-! ### The initial and final values of the potential -/

/-- The initial configuration: wire `u` at frame `S u` holding `e u`. -/
def init (S : Fin W → F) : Cfg W F := ⟨S, e⟩

theorem pot_init (S : Fin W → F) (shift : F → F) (hshift : ∀ f, shift f ≠ f) :
    pot S shift (init S) = 0 := by
  unfold pot
  apply Finset.sum_eq_zero
  intro f _
  have hdisj : Disjoint {u : Fin W | S u = f} {u : Fin W | shift (S u) = f} := by
    rw [Set.disjoint_left]
    intro u hu hu'
    simp only [Set.mem_setOf_eq] at hu hu'
    exact hshift f (by rw [← hu] at hu' ⊢; exact hu')
  have : (init S).sigma f ⊓ target S shift f = ⊥ := by
    have h := e_linearIndependent.disjoint_span_image (R := ZMod 2) hdisj
    exact disjoint_iff.mp h
  rw [this]
  simp

/-- At the end, wire `ρ u` sits at `shift (S u)` holding `e u`; then the potential equals `W`. -/
theorem pot_final (S : Fin W → F) (shift : F → F) (ρ : Equiv.Perm (Fin W)) (c : Cfg W F)
    (hframe : ∀ u, c.frame (ρ u) = shift (S u)) (hvec : ∀ u, c.vec (ρ u) = e u) :
    pot S shift c = W := by
  unfold pot
  have hsig : ∀ f, c.sigma f = target S shift f := by
    intro f
    unfold Cfg.sigma target
    congr 1
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨ρ.symm w, ?_, ?_⟩
      · show shift (S (ρ.symm w)) = f
        rw [← hframe (ρ.symm w), Equiv.apply_symm_apply]; exact hw
      · rw [← hvec (ρ.symm w), Equiv.apply_symm_apply]
    · rintro ⟨u, hu, rfl⟩
      exact ⟨ρ u, by show c.frame (ρ u) = f; rw [hframe]; exact hu, hvec u⟩
  have hfin : ∀ f, finrank (ZMod 2) ↥(target S shift f) =
      (Finset.univ.filter (fun u => shift (S u) = f)).card := by
    intro f
    unfold target
    have hli : LinearIndependent (ZMod 2) (e ∘ (Subtype.val : {u : Fin W // shift (S u) = f} → Fin W)) :=
      e_linearIndependent.comp _ Subtype.val_injective
    have hrange : (e (W := W)) '' {u | shift (S u) = f} =
        Set.range (e ∘ (Subtype.val : {u : Fin W // shift (S u) = f} → Fin W)) := by
      rw [Set.range_comp, Subtype.range_coe_subtype]
    rw [hrange, finrank_span_eq_card hli, Fintype.card_subtype]
  calc ∑ f ∈ Finset.univ.image (shift ∘ S), finrank (ZMod 2) ↥(c.sigma f ⊓ target S shift f)
      = ∑ f ∈ Finset.univ.image (shift ∘ S), (Finset.univ.filter (fun u => shift (S u) = f)).card := by
        apply Finset.sum_congr rfl
        intro f _
        rw [hsig f, inf_idem, hfin f]
    _ = (Finset.univ : Finset (Fin W)).card := by
        rw [Finset.card_eq_sum_card_image (shift ∘ S) Finset.univ]
        rfl
    _ = W := Finset.card_fin W

/-- **Frame-change bound.** A valid run from the initial configuration that ends with wire `ρ u`
at frame `shift (S u)` holding `e u`, for a fixed-point-free `shift`, contains at least `W` frame
changes. -/
theorem moves_ge_W (S : Fin W → F) (shift : F → F) (hshift : ∀ f, shift f ≠ f)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = shift (S u))
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u) :
    W ≤ moves evs := by
  have h1 := pot_run_le S shift evs (init S) hv
  rw [pot_init S shift hshift, pot_final S shift ρ _ hframe hvec] at h1
  omega

/-- Cost version: if every move costs at least one (e.g. the rank of a nonzero rational matrix),
the total cost is at least `W`. -/
theorem cost_ge_W (S : Fin W → F) (shift : F → F) (hshift : ∀ f, shift f ≠ f)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = shift (S u))
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (cost : Event W F → ℕ) (hcost : ∀ w f, 1 ≤ cost (.move w f)) :
    W ≤ (evs.map cost).sum := by
  have key : ∀ evs : List (Event W F), moves evs ≤ (evs.map cost).sum := by
    intro evs
    induction evs with
    | nil => simp [moves]
    | cons ev evs ih =>
      cases ev with
      | gate i j => simp only [moves, List.map_cons, List.sum_cons]; omega
      | move w f => simp only [moves, List.map_cons, List.sum_cons]; have := hcost w f; omega
  exact (moves_ge_W S shift hshift ρ evs hv hframe hvec).trans (key evs)

/-- Specialisation to matrix frames with `shift M = M + 1`. -/
theorem moves_ge_W_matrix {m : ℕ} (hm : 0 < m) (S : Fin W → Matrix (Fin m) (Fin m) ℚ)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W (Matrix (Fin m) (Fin m) ℚ)))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = S u + 1)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u) :
    W ≤ moves evs :=
  moves_ge_W S (· + 1) (fun M h => by
      have : (1 : Matrix (Fin m) (Fin m) ℚ) = 0 := by
        have h' := congrArg (· - M) h
        simpa using h'
      have h1 : (1 : Matrix (Fin m) (Fin m) ℚ) ⟨0, hm⟩ ⟨0, hm⟩ = 1 := Matrix.one_apply_eq _
      rw [this] at h1
      simp at h1) ρ evs hv hframe hvec

end Transpose.ShearFrame
