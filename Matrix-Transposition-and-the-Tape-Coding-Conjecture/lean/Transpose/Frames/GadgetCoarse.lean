import Transpose.Frames.GadgetRuns

/-!
# Coarsened potentials (the coarsening lemma)

The frame-change bound (`GadgetRuns.lean`) counts the frame changes of a run.  Its potential only
needs a target frame per item, and it survives *coarsening* the frames by an arbitrary map `π`: a
change that does not alter the `π`-class of the moved wire is invisible to the coarsened run.
Consequences:

* `vmoves_ge_W`: a valid run from `init S` ending with wire `ρ u` holding `e u` at frame `tgt u`,
  with `tgt u ≠ S u` for all `u`, makes at least `W` *visible* moves (moves that change a frame).
* `visible_ge_W_of_coarse`: for every `π : F → F'` with `π (tgt u) ≠ π (S u)` for all `u`, at least
  `W` moves change the `π`-class of the moved wire.
* `det_ne_zero_of_moves_le` (single jumps): with rational `m × m` matrix frames and targets `S u + 1`,
  a run with at most `W` moves changes every frame by a matrix of nonzero determinant;
  `rank_sum_of_moves_le`: the total rank of its jumps is at least `W * m` (the baseline cost).
-/

namespace Transpose.ShearFrame

open Module Submodule

variable {W : ℕ} {F F' : Type} [DecidableEq F] [DecidableEq F']

/-! ### The potential with an arbitrary index set and target family -/

/-- `Σ_{f ∈ fs} dim (Σ_f ⊓ N f)`. -/
noncomputable def potG (fs : Finset F) (N : F → Submodule (ZMod 2) (Vec W)) (c : Cfg W F) : ℕ :=
  ∑ f ∈ fs, finrank (ZMod 2) ↥(c.sigma f ⊓ N f)

/-- The items that must end at frame `f`, for an item-wise target map. -/
noncomputable def targetI (tgt : Fin W → F) (f : F) : Submodule (ZMod 2) (Vec W) :=
  span (ZMod 2) (e '' {u | tgt u = f})

theorem potG_move_le (fs : Finset F) (N : F → Submodule (ZMod 2) (Vec W)) (c : Cfg W F)
    (w : Fin W) (f₀ : F) :
    potG fs N (c.step (.move w f₀)) ≤ potG fs N c + 1 := by
  unfold potG
  have hterm : ∀ f ∈ fs,
      finrank (ZMod 2) ↥((c.step (.move w f₀)).sigma f ⊓ N f) ≤
        finrank (ZMod 2) ↥(c.sigma f ⊓ N f) + (if f = f₀ then 1 else 0) := by
    intro f _
    by_cases hf : f = f₀
    · subst hf
      rw [if_pos rfl]
      exact (finrank_inf_le_of_le (sigma_move_le c w f f)).trans
        (finrank_inf_sup_singleton_le _ _ _)
    · rw [if_neg hf, Nat.add_zero]
      exact finrank_inf_le_of_le (sigma_move_le_of_ne c w hf)
  calc ∑ f ∈ fs, finrank (ZMod 2) ↥((c.step (.move w f₀)).sigma f ⊓ N f)
      ≤ ∑ f ∈ fs, (finrank (ZMod 2) ↥(c.sigma f ⊓ N f) + (if f = f₀ then 1 else 0)) :=
        Finset.sum_le_sum hterm
    _ = (∑ f ∈ fs, finrank (ZMod 2) ↥(c.sigma f ⊓ N f)) + ∑ f ∈ fs, (if f = f₀ then 1 else 0) :=
        Finset.sum_add_distrib
    _ ≤ _ := by
        apply Nat.add_le_add_left
        rw [Finset.sum_ite_eq']
        split_ifs <;> omega

theorem potG_gate_eq (fs : Finset F) (N : F → Submodule (ZMod 2) (Vec W)) (c : Cfg W F)
    {i j : Fin W} (hij : i ≠ j) (hf : c.frame i = c.frame j) :
    potG fs N (c.step (.gate i j)) = potG fs N c := by
  unfold potG
  apply Finset.sum_congr rfl
  intro f _
  rw [sigma_gate c hij hf f]

/-- A move to the current frame does nothing. -/
theorem step_move_self (c : Cfg W F) (w : Fin W) {f : F} (hf : c.frame w = f) :
    c.step (.move w f) = c := by
  simp only [Cfg.step]
  rw [← hf, Function.update_eq_self]

/-- Number of *visible* moves of a run: moves that change the frame of the moved wire. -/
def vmoves : List (Event W F) → Cfg W F → ℕ
  | [], _ => 0
  | .gate i j :: evs, c => vmoves evs (c.step (.gate i j))
  | .move w f :: evs, c => vmoves evs (c.step (.move w f)) + (if c.frame w = f then 0 else 1)

/-- The jumps (old frame, new frame) of the moves of a run, in order. -/
def jumps : List (Event W F) → Cfg W F → List (F × F)
  | [], _ => []
  | .gate i j :: evs, c => jumps evs (c.step (.gate i j))
  | .move w f :: evs, c => (c.frame w, f) :: jumps evs (c.step (.move w f))

theorem jumps_length : ∀ (evs : List (Event W F)) (c : Cfg W F), (jumps evs c).length = moves evs
  | [], _ => rfl
  | .gate i j :: evs, c => by
      show (jumps evs (c.step (.gate i j))).length = moves evs
      exact jumps_length evs _
  | .move w f :: evs, c => by
      show (jumps evs (c.step (.move w f))).length + 1 = moves evs + 1
      rw [jumps_length evs _]

/-- Along a valid run the potential grows by at most the number of visible moves. -/
theorem potG_run_le (fs : Finset F) (N : F → Submodule (ZMod 2) (Vec W)) :
    ∀ (evs : List (Event W F)) (c : Cfg W F), c.allValid evs →
      potG fs N (c.run evs) ≤ potG fs N c + vmoves evs c
  | [], c, _ => by simp [Cfg.run, vmoves]
  | .gate i j :: evs, c, hv => by
      obtain ⟨⟨hij, hf⟩, hv'⟩ := hv
      simp only [Cfg.run, vmoves]
      have := potG_run_le fs N evs (c.step (.gate i j)) hv'
      rwa [potG_gate_eq fs N c hij hf] at this
  | .move w f₀ :: evs, c, hv => by
      obtain ⟨_, hv'⟩ := hv
      simp only [Cfg.run, vmoves]
      have h1 := potG_run_le fs N evs (c.step (.move w f₀)) hv'
      by_cases hf : c.frame w = f₀
      · rw [if_pos hf, Nat.add_zero]
        rw [step_move_self c w hf] at h1 ⊢
        exact h1
      · rw [if_neg hf]
        have h2 := potG_move_le fs N c w f₀
        omega

theorem potI_init (S tgt : Fin W → F) (htgt : ∀ u, tgt u ≠ S u) :
    potG (Finset.univ.image tgt) (targetI tgt) (init S) = 0 := by
  unfold potG
  apply Finset.sum_eq_zero
  intro f _
  have hdisj : Disjoint {u : Fin W | S u = f} {u : Fin W | tgt u = f} := by
    rw [Set.disjoint_left]
    intro u hu hu'
    simp only [Set.mem_setOf_eq] at hu hu'
    exact htgt u (hu'.trans hu.symm)
  have : (init S).sigma f ⊓ targetI tgt f = ⊥ := by
    have h := e_linearIndependent.disjoint_span_image (R := ZMod 2) hdisj
    exact disjoint_iff.mp h
  rw [this]
  simp

theorem potI_final (tgt : Fin W → F) (ρ : Equiv.Perm (Fin W)) (c : Cfg W F)
    (hframe : ∀ u, c.frame (ρ u) = tgt u) (hvec : ∀ u, c.vec (ρ u) = e u) :
    potG (Finset.univ.image tgt) (targetI tgt) c = W := by
  unfold potG
  have hsig : ∀ f, c.sigma f = targetI tgt f := by
    intro f
    unfold Cfg.sigma targetI
    congr 1
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨ρ.symm w, ?_, ?_⟩
      · show tgt (ρ.symm w) = f
        rw [← hframe (ρ.symm w), Equiv.apply_symm_apply]; exact hw
      · rw [← hvec (ρ.symm w), Equiv.apply_symm_apply]
    · rintro ⟨u, hu, rfl⟩
      exact ⟨ρ u, by show c.frame (ρ u) = f; rw [hframe]; exact hu, hvec u⟩
  have hfin : ∀ f, finrank (ZMod 2) ↥(targetI tgt f) =
      (Finset.univ.filter (fun u => tgt u = f)).card := by
    intro f
    unfold targetI
    have hli : LinearIndependent (ZMod 2) (e ∘ (Subtype.val : {u : Fin W // tgt u = f} → Fin W)) :=
      e_linearIndependent.comp _ Subtype.val_injective
    have hrange : (e (W := W)) '' {u | tgt u = f} =
        Set.range (e ∘ (Subtype.val : {u : Fin W // tgt u = f} → Fin W)) := by
      rw [Set.range_comp, Subtype.range_coe_subtype]
    rw [hrange, finrank_span_eq_card hli, Fintype.card_subtype]
  calc ∑ f ∈ Finset.univ.image tgt, finrank (ZMod 2) ↥(c.sigma f ⊓ targetI tgt f)
      = ∑ f ∈ Finset.univ.image tgt, (Finset.univ.filter (fun u => tgt u = f)).card := by
        apply Finset.sum_congr rfl
        intro f _
        rw [hsig f, inf_idem, hfin f]
    _ = (Finset.univ : Finset (Fin W)).card := by
        rw [Finset.card_eq_sum_card_image tgt Finset.univ]
    _ = W := Finset.card_fin W

/-- **Frame-change bound, visible-move form.** -/
theorem vmoves_ge_W (S tgt : Fin W → F) (htgt : ∀ u, tgt u ≠ S u) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u) :
    W ≤ vmoves evs (init S) := by
  have h1 := potG_run_le (Finset.univ.image tgt) (targetI tgt) evs (init S) hv
  rw [potI_init S tgt htgt, potI_final tgt ρ _ hframe hvec] at h1
  omega

/-! ### Coarsening -/

/-- Map the frames of an event. -/
def Event.map (π : F → F') : Event W F → Event W F'
  | .gate i j => .gate i j
  | .move w f => .move w (π f)

/-- Map the frames of a configuration. -/
def Cfg.map (π : F → F') (c : Cfg W F) : Cfg W F' := ⟨fun w => π (c.frame w), c.vec⟩

theorem step_map_gate (π : F → F') (c : Cfg W F) (i j : Fin W) :
    (c.map π).step (.gate i j) = (c.step (.gate i j)).map π := rfl

theorem step_map_move (π : F → F') (c : Cfg W F) (w : Fin W) (f : F) :
    (c.map π).step (.move w (π f)) = (c.step (.move w f)).map π := by
  simp only [Cfg.step, Cfg.map]
  congr 1
  funext x
  by_cases h : x = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem step_map (π : F → F') (c : Cfg W F) (ev : Event W F) :
    (c.map π).step (ev.map π) = (c.step ev).map π := by
  cases ev with
  | gate i j => exact step_map_gate π c i j
  | move w f => exact step_map_move π c w f

theorem run_map (π : F → F') : ∀ (evs : List (Event W F)) (c : Cfg W F),
    (c.map π).run (evs.map (Event.map π)) = (c.run evs).map π
  | [], _ => rfl
  | ev :: evs, c => by
      show ((c.map π).step (ev.map π)).run (evs.map (Event.map π)) = ((c.step ev).run evs).map π
      rw [step_map]
      exact run_map π evs (c.step ev)

theorem valid_map (π : F → F') (c : Cfg W F) (ev : Event W F) (h : c.valid ev) :
    (c.map π).valid (ev.map π) := by
  cases ev with
  | gate i j =>
    obtain ⟨hij, hf⟩ := h
    exact ⟨hij, by show π (c.frame i) = π (c.frame j); rw [hf]⟩
  | move w f => trivial

theorem allValid_map (π : F → F') : ∀ (evs : List (Event W F)) (c : Cfg W F),
    c.allValid evs → (c.map π).allValid (evs.map (Event.map π))
  | [], _, _ => trivial
  | ev :: evs, c, hv => by
      obtain ⟨h1, h2⟩ := hv
      show (c.map π).valid (ev.map π) ∧ ((c.map π).step (ev.map π)).allValid (evs.map (Event.map π))
      refine ⟨valid_map π c ev h1, ?_⟩
      rw [step_map]
      exact allValid_map π evs _ h2

/-- Coarsening can only hide moves. -/
theorem vmoves_map_le (π : F → F') : ∀ (evs : List (Event W F)) (c : Cfg W F),
    vmoves (evs.map (Event.map π)) (c.map π) ≤ moves evs
  | [], _ => le_refl _
  | .gate i j :: evs, c => by
      show vmoves (evs.map (Event.map π)) ((c.map π).step (.gate i j)) ≤ moves evs
      rw [step_map_gate]
      exact vmoves_map_le π evs _
  | .move w f :: evs, c => by
      show vmoves (evs.map (Event.map π)) ((c.map π).step (.move w (π f))) +
        (if (c.map π).frame w = π f then 0 else 1) ≤ moves evs + 1
      rw [step_map_move]
      have := vmoves_map_le π evs (c.step (.move w f))
      split_ifs <;> omega

/-- A jump whose endpoints have the same `π`-class is invisible after coarsening. -/
theorem vmoves_map_add_one_le (π : F → F') : ∀ (evs : List (Event W F)) (c : Cfg W F),
    (∃ p ∈ jumps evs c, π p.1 = π p.2) →
    vmoves (evs.map (Event.map π)) (c.map π) + 1 ≤ moves evs
  | [], _, h => by
      obtain ⟨p, hp, _⟩ := h
      simp [jumps] at hp
  | .gate i j :: evs, c, h => by
      obtain ⟨p, hp, hπ⟩ := h
      show vmoves (evs.map (Event.map π)) ((c.map π).step (.gate i j)) + 1 ≤ moves evs
      rw [step_map_gate]
      exact vmoves_map_add_one_le π evs _ ⟨p, hp, hπ⟩
  | .move w f :: evs, c, h => by
      obtain ⟨p, hp, hπ⟩ := h
      show vmoves (evs.map (Event.map π)) ((c.map π).step (.move w (π f))) +
        (if (c.map π).frame w = π f then 0 else 1) + 1 ≤ moves evs + 1
      rw [step_map_move]
      have hp' : p = (c.frame w, f) ∨ p ∈ jumps evs (c.step (.move w f)) := by
        simpa [jumps] using hp
      rcases hp' with rfl | hp'
      · have h1 := vmoves_map_le π evs (c.step (.move w f))
        have hif : (if (c.map π).frame w = π f then 0 else 1) = 0 := if_pos hπ
        rw [hif]
        omega
      · have h1 := vmoves_map_add_one_le π evs _ ⟨p, hp', hπ⟩
        split_ifs <;> omega

/-- **Coarsening lemma.** For any `π` separating sources from targets, at least `W` moves
change the `π`-class of the moved wire. -/
theorem visible_ge_W_of_coarse (S tgt : Fin W → F) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (π : F → F') (hπ : ∀ u, π (tgt u) ≠ π (S u)) :
    W ≤ vmoves (evs.map (Event.map π)) ((init S).map π) := by
  have hinit : (init S).map π = init (fun u => π (S u)) := rfl
  rw [hinit]
  refine vmoves_ge_W (fun u => π (S u)) (fun u => π (tgt u)) hπ ρ _ ?_ ?_ ?_
  · rw [← hinit]; exact allValid_map π evs _ hv
  · intro u
    rw [← hinit, run_map]
    show π (((init S).run evs).frame (ρ u)) = π (tgt u)
    rw [hframe]
  · intro u
    rw [← hinit, run_map]
    show ((init S).run evs).vec (ρ u) = e u
    exact hvec u

/-! ### Single jumps have full rank (coarsening lemma) -/

/-- **Coarsening lemma, single jumps.** With rational matrix frames and targets `S u + 1`, a run
with at most `W` moves changes every frame by a matrix of nonzero determinant. -/
theorem det_ne_zero_of_moves_le {m : ℕ} (S : Fin W → Matrix (Fin m) (Fin m) ℚ)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W (Matrix (Fin m) (Fin m) ℚ)))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = S u + 1)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (hW : moves evs ≤ W) :
    ∀ p ∈ jumps evs (init S), (p.2 - p.1).det ≠ 0 := by
  intro p hp hdet
  obtain ⟨l, hl, hlJ⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  let π : Matrix (Fin m) (Fin m) ℚ → (Fin m → ℚ) := fun M => Matrix.vecMul l M
  have hπ : ∀ u, π (S u + 1) ≠ π (S u) := by
    intro u h
    apply hl
    have h' : Matrix.vecMul l (S u) + l = Matrix.vecMul l (S u) + 0 := by
      rw [add_zero]
      calc Matrix.vecMul l (S u) + l = Matrix.vecMul l (S u + 1) := by
            rw [Matrix.vecMul_add, Matrix.vecMul_one]
        _ = Matrix.vecMul l (S u) := h
    exact add_left_cancel h'
  have h1 := visible_ge_W_of_coarse S (fun u => S u + 1) ρ evs hv hframe hvec π hπ
  have h2 := vmoves_map_add_one_le π evs (init S) ⟨p, hp, by
    show Matrix.vecMul l p.1 = Matrix.vecMul l p.2
    rw [Matrix.vecMul_sub, sub_eq_zero] at hlJ
    exact hlJ.symm⟩
  omega

/-- The total rank of the jumps of a run with at most `W` moves is at least `W * m`. -/
theorem rank_sum_of_moves_le {m : ℕ} (S : Fin W → Matrix (Fin m) (Fin m) ℚ)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W (Matrix (Fin m) (Fin m) ℚ)))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = S u + 1)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (hW : moves evs ≤ W) :
    W * m ≤ ((jumps evs (init S)).map (fun p => (p.2 - p.1).rank)).sum := by
  have hdet := det_ne_zero_of_moves_le S ρ evs hv hframe hvec hW
  have hrank : ∀ p ∈ jumps evs (init S), (p.2 - p.1).rank = m := by
    intro p hp
    rw [Matrix.rank_of_isUnit _ (Matrix.isUnit_iff_isUnit_det _ |>.mpr (isUnit_iff_ne_zero.mpr (hdet p hp)))]
    exact Fintype.card_fin m
  have hsum : ((jumps evs (init S)).map (fun p => (p.2 - p.1).rank)).sum =
      (jumps evs (init S)).length * m := by
    rw [List.map_congr_left hrank, List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hsum, jumps_length]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have := moves_ge_W_matrix hm S ρ evs hv hframe hvec
    exact Nat.mul_le_mul_right m this

end Transpose.ShearFrame
