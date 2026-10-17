import Transpose.Frames.GadgetCoarse

/-!
# The split invariant and the cargo rule for tight runs

Formalisation of the split invariant and the cargo rule, in the run model of `GadgetRuns.lean` /
`GadgetCoarse.lean`.

Setting: a valid run `evs` from `init S` ending with wire `ρ u` at frame `tgt u` holding `e u`,
with `tgt u ≠ S u` for all `u`.  Write, for a frame `f`,

* `N f = targetI tgt f` (items whose home is `f`) and `N' f = targetI S f` (items born at `f`),
* `Φ c = potG univ (targetI tgt) c` ("arrived") and `Ψ c = potG univ (targetI S) c` ("not departed").

Results (all for an arbitrary finite frame type `F`, unless stated otherwise):

* **Linear independence.** `linearIndependent_vec_run`: the vectors of a configuration reached by
  a valid run from `init S` are linearly independent (gates are transvections).  Hence
  `finrank (sigma c f)` is the number of wires at `f` (`finrank_sigma`), the `sigma`s of distinct
  frames are independent (`sigma_inf_sigma_eq_bot`) and `∑ f, finrank (sigma c f) = W`
  (`sum_finrank_sigma`).
* **Split invariant.** `potG_move_ge` / `potG_run_ge`: `Ψ` drops by at most one per visible move
  and is unchanged by gates and invisible moves; `potG_targetI_eq_W` / `potG_targetI_eq_zero`:
  `Φ(init) = 0`, `Φ(end) = W`, `Ψ(init) = W`, `Ψ(end) = 0`; `potG_add_potG_le`: `Φ + Ψ ≤ W`.
  `tight_potentials`: if the run has at most (hence exactly) `W` visible moves, then after any prefix
  with `t` visible moves `Φ = t` and `Ψ = W - t`; `tight_sigma_split`: then
  `sigma c f = (sigma c f ⊓ N f) ⊔ (sigma c f ⊓ N' f)` for every `f`.
* **Cargo rule.** `cargo_rule` (two classes: `tgt u` is the unique frame different from `S u`): in
  a tight run every visible move carries a vector lying in `N (destination) = N' (origin)`.
  `cargo_rule_bool` is the specialisation to `F = Bool`, `tgt u = !S u`.
-/

namespace Transpose.ShearFrame

open Module Submodule

variable {W : ℕ} {F : Type} [DecidableEq F]

/-! ### Bookkeeping: runs, validity and visible moves of concatenated event lists -/

omit [DecidableEq F] in
theorem run_append : ∀ (l₁ l₂ : List (Event W F)) (c : Cfg W F),
    c.run (l₁ ++ l₂) = (c.run l₁).run l₂
  | [], _, _ => rfl
  | ev :: l₁, l₂, c => run_append l₁ l₂ (c.step ev)

omit [DecidableEq F] in
theorem allValid_append : ∀ (l₁ l₂ : List (Event W F)) (c : Cfg W F),
    c.allValid (l₁ ++ l₂) ↔ c.allValid l₁ ∧ (c.run l₁).allValid l₂
  | [], l₂, c => by simp [Cfg.allValid, Cfg.run]
  | ev :: l₁, l₂, c => by
      show c.valid ev ∧ (c.step ev).allValid (l₁ ++ l₂) ↔
        (c.valid ev ∧ (c.step ev).allValid l₁) ∧ ((c.step ev).run l₁).allValid l₂
      rw [allValid_append l₁ l₂ (c.step ev), and_assoc]

theorem vmoves_append : ∀ (l₁ l₂ : List (Event W F)) (c : Cfg W F),
    vmoves (l₁ ++ l₂) c = vmoves l₁ c + vmoves l₂ (c.run l₁)
  | [], l₂, c => by simp [vmoves, Cfg.run]
  | .gate i j :: l₁, l₂, c => by
      show vmoves (l₁ ++ l₂) (c.step (.gate i j)) =
        vmoves l₁ (c.step (.gate i j)) + vmoves l₂ ((c.step (.gate i j)).run l₁)
      exact vmoves_append l₁ l₂ _
  | .move w f :: l₁, l₂, c => by
      show vmoves (l₁ ++ l₂) (c.step (.move w f)) + (if c.frame w = f then 0 else 1) =
        vmoves l₁ (c.step (.move w f)) + (if c.frame w = f then 0 else 1) +
          vmoves l₂ ((c.step (.move w f)).run l₁)
      rw [vmoves_append l₁ l₂ _]
      omega

/-- Visible moves are moves. -/
theorem vmoves_le_moves : ∀ (evs : List (Event W F)) (c : Cfg W F), vmoves evs c ≤ moves evs
  | [], _ => le_refl _
  | .gate i j :: evs, c => vmoves_le_moves evs (c.step (.gate i j))
  | .move w f :: evs, c => by
      show vmoves evs (c.step (.move w f)) + (if c.frame w = f then 0 else 1) ≤ moves evs + 1
      have := vmoves_le_moves evs (c.step (.move w f))
      split_ifs <;> omega

/-! ### The vectors stay linearly independent along a valid run -/

omit [DecidableEq F] in
/-- A gate `i ← i + j` is left multiplication of the matrix of vectors by a transvection. -/
theorem of_vec_gate (c : Cfg W F) (i j : Fin W) :
    Matrix.of (c.step (.gate i j)).vec =
      Matrix.transvection i j (1 : ZMod 2) * Matrix.of c.vec := by
  ext a b
  simp only [Cfg.step, Matrix.of_apply]
  by_cases ha : a = i
  · subst ha
    rw [Function.update_self, Matrix.transvection_mul_apply_same]
    simp
  · rw [Function.update_of_ne ha, Matrix.transvection_mul_apply_of_ne i j a b ha]
    simp

omit [DecidableEq F] in
theorem linearIndependent_vec_gate (c : Cfg W F) {i j : Fin W} (hij : i ≠ j)
    (h : LinearIndependent (ZMod 2) c.vec) :
    LinearIndependent (ZMod 2) (c.step (.gate i j)).vec := by
  have h1 : IsUnit (Matrix.of c.vec) :=
    (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of c.vec)).mp h
  have h2 : IsUnit (Matrix.transvection i j (1 : ZMod 2)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transvection_of_ne i j hij]
    exact isUnit_one
  have h3 : IsUnit (Matrix.of (c.step (.gate i j)).vec) := by
    rw [of_vec_gate]
    exact h2.mul h1
  exact (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of (c.step (.gate i j)).vec)).mpr h3

omit [DecidableEq F] in
theorem linearIndependent_vec_step (c : Cfg W F) (ev : Event W F) (hv : c.valid ev)
    (h : LinearIndependent (ZMod 2) c.vec) : LinearIndependent (ZMod 2) (c.step ev).vec := by
  cases ev with
  | gate i j => exact linearIndependent_vec_gate c hv.1 h
  | move w f => exact h

omit [DecidableEq F] in
theorem linearIndependent_vec_run : ∀ (evs : List (Event W F)) (c : Cfg W F), c.allValid evs →
    LinearIndependent (ZMod 2) c.vec → LinearIndependent (ZMod 2) (c.run evs).vec
  | [], _, _, h => h
  | ev :: evs, c, hv, h =>
      linearIndependent_vec_run evs (c.step ev) hv.2 (linearIndependent_vec_step c ev hv.1 h)

omit [DecidableEq F] in
/-- **Linear independence.** Along a valid run from `init S` the vectors are linearly
independent. -/
theorem linearIndependent_vec_init_run (S : Fin W → F) (evs : List (Event W F))
    (hv : (init S).allValid evs) : LinearIndependent (ZMod 2) ((init S).run evs).vec :=
  linearIndependent_vec_run evs (init S) hv e_linearIndependent

/-- The span of a linearly independent family restricted to a predicate has the obvious rank. -/
theorem finrank_span_image_of_linearIndependent {v : Fin W → Vec W}
    (hv : LinearIndependent (ZMod 2) v) (p : Fin W → Prop) [DecidablePred p] :
    finrank (ZMod 2) ↥(span (ZMod 2) (v '' {u | p u})) = (Finset.univ.filter p).card := by
  have hli : LinearIndependent (ZMod 2) (v ∘ (Subtype.val : {u : Fin W // p u} → Fin W)) :=
    hv.comp _ Subtype.val_injective
  have hrange : v '' {u | p u} = Set.range (v ∘ (Subtype.val : {u : Fin W // p u} → Fin W)) := by
    rw [Set.range_comp, Subtype.range_coe_subtype]
  rw [hrange, finrank_span_eq_card hli, Fintype.card_subtype]

theorem finrank_sigma (c : Cfg W F) (hli : LinearIndependent (ZMod 2) c.vec) (f : F) :
    finrank (ZMod 2) ↥(c.sigma f) = (Finset.univ.filter (fun w => c.frame w = f)).card :=
  finrank_span_image_of_linearIndependent hli _

theorem finrank_targetI (T : Fin W → F) (f : F) :
    finrank (ZMod 2) ↥(targetI T f) = (Finset.univ.filter (fun u => T u = f)).card :=
  finrank_span_image_of_linearIndependent e_linearIndependent _

/-- The spans at the frames partition the dimension `W`. -/
theorem sum_finrank_sigma [Fintype F] (c : Cfg W F) (hli : LinearIndependent (ZMod 2) c.vec) :
    ∑ f, finrank (ZMod 2) ↥(c.sigma f) = W := by
  rw [Finset.sum_congr rfl (fun f _ => finrank_sigma c hli f),
    ← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
  exact Finset.card_fin W

omit [DecidableEq F] in
/-- The spans at two distinct frames are independent. -/
theorem sigma_inf_sigma_eq_bot (c : Cfg W F) (hli : LinearIndependent (ZMod 2) c.vec)
    {f f' : F} (h : f ≠ f') : c.sigma f ⊓ c.sigma f' = ⊥ := by
  apply disjoint_iff.mp
  apply hli.disjoint_span_image
  rw [Set.disjoint_left]
  intro w hw hw'
  simp only [Set.mem_ofPred_eq] at hw hw'
  exact h (hw.symm.trans hw')

omit [DecidableEq F] in
/-- Two target subspaces with no common item are independent. -/
theorem targetI_inf_eq_bot (T T' : Fin W → F) {f f' : F}
    (h : ∀ u, T u = f → T' u = f' → False) : targetI T f ⊓ targetI T' f' = ⊥ := by
  apply disjoint_iff.mp
  apply e_linearIndependent.disjoint_span_image
  rw [Set.disjoint_left]
  intro u hu hu'
  simp only [Set.mem_ofPred_eq] at hu hu'
  exact h u hu hu'

/-! ### The second potential and the split invariant -/

omit [DecidableEq F] in
theorem le_sigma_move (c : Cfg W F) (w : Fin W) (f₀ f : F) :
    c.sigma f ≤ (c.step (.move w f₀)).sigma f ⊔ span (ZMod 2) {c.vec w} := by
  simp only [Cfg.step, Cfg.sigma]
  refine span_le.mpr ?_
  rintro _ ⟨w', hw', rfl⟩
  by_cases hww : w' = w
  · subst hww
    exact Submodule.mem_sup_right (subset_span (Set.mem_singleton _))
  · apply Submodule.mem_sup_left
    exact subset_span ⟨w', show Function.update c.frame w f₀ w' = f by
      rw [Function.update_of_ne hww]; exact hw', rfl⟩

omit [DecidableEq F] in
theorem le_sigma_move_of_ne (c : Cfg W F) (w : Fin W) (f₀ : F) {f : F} (hf : c.frame w ≠ f) :
    c.sigma f ≤ (c.step (.move w f₀)).sigma f := by
  simp only [Cfg.step, Cfg.sigma]
  refine span_le.mpr ?_
  rintro _ ⟨w', hw', rfl⟩
  have hww : w' ≠ w := fun h => hf (by rw [← h]; exact hw')
  exact subset_span ⟨w', show Function.update c.frame w f₀ w' = f by
    rw [Function.update_of_ne hww]; exact hw', rfl⟩

/-- A move lowers any potential by at most one. -/
theorem potG_move_ge (fs : Finset F) (N : F → Submodule (ZMod 2) (Vec W)) (c : Cfg W F)
    (w : Fin W) (f₀ : F) :
    potG fs N c ≤ potG fs N (c.step (.move w f₀)) + 1 := by
  unfold potG
  have hterm : ∀ f ∈ fs,
      finrank (ZMod 2) ↥(c.sigma f ⊓ N f) ≤
        finrank (ZMod 2) ↥((c.step (.move w f₀)).sigma f ⊓ N f) +
          (if f = c.frame w then 1 else 0) := by
    intro f _
    by_cases hf : f = c.frame w
    · rw [ite_eq_left hf]
      exact (finrank_inf_le_of_le (le_sigma_move c w f₀ f)).trans
        (finrank_inf_sup_singleton_le _ _ _)
    · rw [ite_eq_right hf, Nat.add_zero]
      exact finrank_inf_le_of_le (le_sigma_move_of_ne c w f₀ (Ne.symm hf))
  calc ∑ f ∈ fs, finrank (ZMod 2) ↥(c.sigma f ⊓ N f)
      ≤ ∑ f ∈ fs, (finrank (ZMod 2) ↥((c.step (.move w f₀)).sigma f ⊓ N f) +
          (if f = c.frame w then 1 else 0)) := Finset.sum_le_sum hterm
    _ = (∑ f ∈ fs, finrank (ZMod 2) ↥((c.step (.move w f₀)).sigma f ⊓ N f)) +
        ∑ f ∈ fs, (if f = c.frame w then 1 else 0) := Finset.sum_add_distrib
    _ ≤ _ := by
        apply Nat.add_le_add_left
        rw [Finset.sum_ite_eq']
        split_ifs <;> omega

/-- Along a valid run a potential drops by at most the number of visible moves. -/
theorem potG_run_ge (fs : Finset F) (N : F → Submodule (ZMod 2) (Vec W)) :
    ∀ (evs : List (Event W F)) (c : Cfg W F), c.allValid evs →
      potG fs N c ≤ potG fs N (c.run evs) + vmoves evs c
  | [], c, _ => by simp [Cfg.run, vmoves]
  | .gate i j :: evs, c, hv => by
      obtain ⟨⟨hij, hf⟩, hv'⟩ := hv
      simp only [Cfg.run, vmoves]
      have := potG_run_ge fs N evs (c.step (.gate i j)) hv'
      rwa [potG_gate_eq fs N c hij hf] at this
  | .move w f₀ :: evs, c, hv => by
      obtain ⟨_, hv'⟩ := hv
      simp only [Cfg.run, vmoves]
      have h1 := potG_run_ge fs N evs (c.step (.move w f₀)) hv'
      by_cases hf : c.frame w = f₀
      · rw [ite_eq_left hf, Nat.add_zero]
        rw [step_move_self c w hf] at h1 ⊢
        exact h1
      · rw [ite_eq_right hf]
        have h2 := potG_move_ge fs N c w f₀
        omega

omit [DecidableEq F] in
/-- A configuration in which wire `ρ u` sits at `T u` holding `e u` has `sigma f = targetI T f`. -/
theorem sigma_eq_targetI (T : Fin W → F) (ρ : Equiv.Perm (Fin W)) (c : Cfg W F)
    (hframe : ∀ u, c.frame (ρ u) = T u) (hvec : ∀ u, c.vec (ρ u) = e u) (f : F) :
    c.sigma f = targetI T f := by
  unfold Cfg.sigma targetI
  congr 1
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨ρ.symm w, ?_, ?_⟩
    · show T (ρ.symm w) = f
      rw [← hframe (ρ.symm w), Equiv.apply_symm_apply]; exact hw
    · rw [← hvec (ρ.symm w), Equiv.apply_symm_apply]
  · rintro ⟨u, hu, rfl⟩
    exact ⟨ρ u, by show c.frame (ρ u) = f; rw [hframe]; exact hu, hvec u⟩

/-- In such a configuration the potential with targets `T` is `W` (`Φ(end) = W`, `Ψ(init) = W`). -/
theorem potG_targetI_eq_W [Fintype F] (T : Fin W → F) (ρ : Equiv.Perm (Fin W)) (c : Cfg W F)
    (hframe : ∀ u, c.frame (ρ u) = T u) (hvec : ∀ u, c.vec (ρ u) = e u) :
    potG Finset.univ (targetI T) c = W := by
  unfold potG
  calc ∑ f, finrank (ZMod 2) ↥(c.sigma f ⊓ targetI T f)
      = ∑ f, (Finset.univ.filter (fun u => T u = f)).card := by
        apply Finset.sum_congr rfl
        intro f _
        rw [sigma_eq_targetI T ρ c hframe hvec f, inf_idem, finrank_targetI]
    _ = (Finset.univ : Finset (Fin W)).card := by
        rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
    _ = W := Finset.card_fin W

omit [DecidableEq F] in
/-- In such a configuration the potential with targets `T'` disjoint from `T` vanishes
(`Φ(init) = 0`, `Ψ(end) = 0`). -/
theorem potG_targetI_eq_zero (T T' : Fin W → F) (h : ∀ u, T' u ≠ T u) (ρ : Equiv.Perm (Fin W))
    (c : Cfg W F) (hframe : ∀ u, c.frame (ρ u) = T u) (hvec : ∀ u, c.vec (ρ u) = e u)
    (fs : Finset F) : potG fs (targetI T') c = 0 := by
  unfold potG
  apply Finset.sum_eq_zero
  intro f _
  rw [sigma_eq_targetI T ρ c hframe hvec f,
    targetI_inf_eq_bot T T' (fun u hu hu' => h u (hu'.trans hu.symm))]
  simp

theorem finrank_sup_of_inf_eq_bot (A D : Submodule (ZMod 2) (Vec W)) (h : A ⊓ D = ⊥) :
    finrank (ZMod 2) ↥(A ⊔ D) = finrank (ZMod 2) ↥A + finrank (ZMod 2) ↥D := by
  have := Submodule.finrank_sup_add_finrank_inf_eq A D
  rw [h, finrank_bot, add_zero] at this
  exact this

theorem finrank_inf_add_finrank_inf_le (U N N' : Submodule (ZMod 2) (Vec W)) (h : N ⊓ N' = ⊥) :
    finrank (ZMod 2) ↥(U ⊓ N) + finrank (ZMod 2) ↥(U ⊓ N') ≤ finrank (ZMod 2) ↥U := by
  have h2 : (U ⊓ N) ⊓ (U ⊓ N') = ⊥ := by
    rw [eq_bot_iff, ← h]
    exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  rw [← finrank_sup_of_inf_eq_bot _ _ h2]
  exact Submodule.finrank_mono (sup_le inf_le_left inf_le_left)

omit [DecidableEq F] in
/-- `Φ + Ψ ≤ Σ_f dim Σ_f` whenever the two target families are pointwise independent. -/
theorem potG_add_potG_le (fs : Finset F) (N N' : F → Submodule (ZMod 2) (Vec W))
    (h : ∀ f ∈ fs, N f ⊓ N' f = ⊥) (c : Cfg W F) :
    potG fs N c + potG fs N' c ≤ ∑ f ∈ fs, finrank (ZMod 2) ↥(c.sigma f) := by
  unfold potG
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun f hf => finrank_inf_add_finrank_inf_le _ _ _ (h f hf)

/-- `Φ + Ψ ≤ W` along a valid run from `init S`. -/
theorem potG_add_potG_le_W [Fintype F] (S tgt : Fin W → F) (htgt : ∀ u, tgt u ≠ S u)
    (evs : List (Event W F)) (hv : (init S).allValid evs) :
    potG Finset.univ (targetI tgt) ((init S).run evs) +
      potG Finset.univ (targetI S) ((init S).run evs) ≤ W := by
  exact (potG_add_potG_le _ _ _
    (fun f _ => targetI_inf_eq_bot tgt S (fun u hu hu' => htgt u (hu.trans hu'.symm))) _).trans
    (sum_finrank_sigma _ (linearIndependent_vec_init_run S evs hv)).le

/-- **Split invariant, values.** In a run with at most `W` visible moves, after a prefix
with `t` visible moves, `Φ = t` and `Ψ = W - t`. -/
theorem tight_potentials [Fintype F] (S tgt : Fin W → F) (htgt : ∀ u, tgt u ≠ S u)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (hW : vmoves evs (init S) ≤ W)
    (evs₁ evs₂ : List (Event W F)) (hsplit : evs = evs₁ ++ evs₂) :
    potG Finset.univ (targetI tgt) ((init S).run evs₁) = vmoves evs₁ (init S) ∧
    potG Finset.univ (targetI S) ((init S).run evs₁) + vmoves evs₁ (init S) = W := by
  subst hsplit
  have hv1 : (init S).allValid evs₁ := ((allValid_append _ _ _).mp hv).1
  have hv2 : ((init S).run evs₁).allValid evs₂ := ((allValid_append _ _ _).mp hv).2
  rw [vmoves_append] at hW
  rw [run_append] at hframe hvec
  have hΦ0 : potG Finset.univ (targetI tgt) (init S) = 0 :=
    potG_targetI_eq_zero S tgt htgt 1 (init S) (fun _ => rfl) (fun _ => rfl) _
  have hΦW : potG Finset.univ (targetI tgt) (((init S).run evs₁).run evs₂) = W :=
    potG_targetI_eq_W tgt ρ _ hframe hvec
  have hΨ0 : potG Finset.univ (targetI S) (((init S).run evs₁).run evs₂) = 0 :=
    potG_targetI_eq_zero tgt S (fun u => (htgt u).symm) ρ _ hframe hvec _
  have hΨW : potG Finset.univ (targetI S) (init S) = W :=
    potG_targetI_eq_W S 1 (init S) (fun _ => rfl) (fun _ => rfl)
  have a1 := potG_run_le Finset.univ (targetI tgt) evs₁ (init S) hv1
  have a2 := potG_run_le Finset.univ (targetI tgt) evs₂ _ hv2
  have b1 := potG_run_ge Finset.univ (targetI S) evs₁ (init S) hv1
  have b2 := potG_run_ge Finset.univ (targetI S) evs₂ _ hv2
  omega

/-- **Split invariant, subspaces.** In a run with at most `W` visible moves, at every
prefix and every frame `f`, `Σ_f = (Σ_f ⊓ N_f) ⊕ (Σ_f ⊓ N'_f)`. -/
theorem tight_sigma_split [Fintype F] (S tgt : Fin W → F) (htgt : ∀ u, tgt u ≠ S u)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (hW : vmoves evs (init S) ≤ W)
    (evs₁ evs₂ : List (Event W F)) (hsplit : evs = evs₁ ++ evs₂) (f : F) :
    ((init S).run evs₁).sigma f =
      (((init S).run evs₁).sigma f ⊓ targetI tgt f) ⊔
        (((init S).run evs₁).sigma f ⊓ targetI S f) := by
  obtain ⟨hΦ, hΨ⟩ := tight_potentials S tgt htgt ρ evs hv hframe hvec hW evs₁ evs₂ hsplit
  have hv1 : (init S).allValid evs₁ := ((allValid_append _ _ _).mp (hsplit ▸ hv)).1
  have hli := linearIndependent_vec_init_run S evs₁ hv1
  have hsum := sum_finrank_sigma _ hli
  have hdisj : ∀ f, targetI tgt f ⊓ targetI S f = ⊥ :=
    fun f => targetI_inf_eq_bot tgt S (fun u hu hu' => htgt u (hu.trans hu'.symm))
  have hle : ∀ f ∈ (Finset.univ : Finset F),
      finrank (ZMod 2) ↥(((init S).run evs₁).sigma f ⊓ targetI tgt f) +
        finrank (ZMod 2) ↥(((init S).run evs₁).sigma f ⊓ targetI S f) ≤
      finrank (ZMod 2) ↥(((init S).run evs₁).sigma f) :=
    fun f _ => finrank_inf_add_finrank_inf_le _ _ _ (hdisj f)
  have heq : ∑ f, (finrank (ZMod 2) ↥(((init S).run evs₁).sigma f ⊓ targetI tgt f) +
        finrank (ZMod 2) ↥(((init S).run evs₁).sigma f ⊓ targetI S f)) =
      ∑ f, finrank (ZMod 2) ↥(((init S).run evs₁).sigma f) := by
    rw [Finset.sum_add_distrib, hsum]
    unfold potG at hΦ hΨ
    omega
  have hf := (Finset.sum_eq_sum_iff_of_le hle).mp heq f (Finset.mem_univ f)
  have hAD : (((init S).run evs₁).sigma f ⊓ targetI tgt f) ⊓
      (((init S).run evs₁).sigma f ⊓ targetI S f) = ⊥ := by
    rw [eq_bot_iff, ← hdisj f]
    exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  symm
  apply Submodule.eq_of_le_of_finrank_eq (sup_le inf_le_left inf_le_left)
  rw [finrank_sup_of_inf_eq_bot _ _ hAD, hf]

/-! ### The cargo rule -/

/-- If `x ∉ U ⊔ N`, adjoining `x` to `U` does not enlarge the intersection with `N`. -/
theorem sup_span_singleton_inf_le_of_notMem (U N : Submodule (ZMod 2) (Vec W)) {x : Vec W}
    (hx : x ∉ U ⊔ N) : (U ⊔ span (ZMod 2) {x}) ⊓ N ≤ U ⊓ N := by
  intro y hy
  obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.mp hy
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hy1
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hz
  by_cases hr : r = 0
  · subst hr
    rw [zero_smul, add_zero] at hy2 ⊢
    exact Submodule.mem_inf.mpr ⟨hu, hy2⟩
  · exfalso
    apply hx
    have hx' : x = r⁻¹ • ((u + r • x) - u) := by
      rw [add_sub_cancel_left, inv_smul_smul₀ hr]
    rw [hx']
    exact Submodule.smul_mem _ _
      (sub_mem (Submodule.mem_sup_right hy2) (Submodule.mem_sup_left hu))

/-- A move whose cargo is not in `Σ_{dest} ⊔ N_{dest}` cannot raise the potential. -/
theorem potG_move_le_of_notMem (fs : Finset F) (N : F → Submodule (ZMod 2) (Vec W))
    (c : Cfg W F) (w : Fin W) (f₀ : F) (hx : c.vec w ∉ c.sigma f₀ ⊔ N f₀) :
    potG fs N (c.step (.move w f₀)) ≤ potG fs N c := by
  unfold potG
  apply Finset.sum_le_sum
  intro f _
  by_cases hf : f = f₀
  · subst hf
    exact Submodule.finrank_mono ((inf_le_inf_right _ (sigma_move_le c w f f)).trans
      (sup_span_singleton_inf_le_of_notMem _ _ hx))
  · exact finrank_inf_le_of_le (sigma_move_le_of_ne c w hf)

/-- Two classes: if `tgt u` is the unique frame different from `S u`, then the items born at `f`
are exactly the items whose home is the other frame `f'`. -/
theorem targetI_eq_of_two (S tgt : Fin W → F) (htwo : ∀ u f, f ≠ S u → tgt u = f)
    {f f' : F} (hff : f ≠ f') :
    targetI S f = targetI tgt f' := by
  have hset : {u : Fin W | S u = f} = {u | tgt u = f'} := by
    ext u
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      exact htwo u f' (fun h' => hff (h.symm.trans h'.symm))
    · intro h
      by_contra hne
      exact hff ((htwo u f (Ne.symm hne)).symm.trans h)
  unfold targetI
  rw [hset]

/-- **Cargo rule, `≤ W` form.** In a two-class run with at most `W` visible moves, the
vector carried by a visible move of wire `w` to frame `f₀` lies in `N f₀ = targetI tgt f₀`, the
items whose home is the destination (equivalently, the items born at the frame being left). -/
theorem cargo_rule_of_le [Fintype F] (S tgt : Fin W → F) (htgt : ∀ u, tgt u ≠ S u)
    (htwo : ∀ u f, f ≠ S u → tgt u = f)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (hW : vmoves evs (init S) ≤ W)
    (evs₁ evs₂ : List (Event W F)) (w : Fin W) (f₀ : F)
    (hsplit : evs = evs₁ ++ .move w f₀ :: evs₂)
    (hvis : ((init S).run evs₁).frame w ≠ f₀) :
    ((init S).run evs₁).vec w ∈ targetI tgt f₀ := by
  have hv1 : (init S).allValid evs₁ := ((allValid_append _ _ _).mp (hsplit ▸ hv)).1
  have hli : LinearIndependent (ZMod 2) ((init S).run evs₁).vec :=
    linearIndependent_vec_init_run S evs₁ hv1
  -- split invariant at the configuration before the move, at the origin and at the destination
  have hs1 := tight_sigma_split S tgt htgt ρ evs hv hframe hvec hW evs₁ (.move w f₀ :: evs₂)
    hsplit (((init S).run evs₁).frame w)
  have hs0 := tight_sigma_split S tgt htgt ρ evs hv hframe hvec hW evs₁ (.move w f₀ :: evs₂)
    hsplit f₀
  -- the potential before and after the move
  have hΦ1 := (tight_potentials S tgt htgt ρ evs hv hframe hvec hW evs₁ (.move w f₀ :: evs₂)
    hsplit).1
  have hΦ2 := (tight_potentials S tgt htgt ρ evs hv hframe hvec hW (evs₁ ++ [.move w f₀]) evs₂
    (by rw [hsplit, List.append_assoc, List.singleton_append])).1
  rw [run_append, vmoves_append] at hΦ2
  -- from now on write `c₁` for the configuration before the move
  set c₁ := (init S).run evs₁ with hc₁
  have hne : c₁.frame w ≠ f₀ := hvis
  -- the two classes swap the roles of `N` and `N'`
  have hN1 : targetI S (c₁.frame w) = targetI tgt f₀ := targetI_eq_of_two S tgt htwo hne
  have hN0 : targetI S f₀ = targetI tgt (c₁.frame w) :=
    targetI_eq_of_two S tgt htwo (Ne.symm hne)
  -- the potential rises by one at this (visible) move
  have hvm : vmoves [Event.move w f₀] c₁ = 1 := by
    simp [vmoves, hne]
  rw [hvm] at hΦ2
  have hΦ2' : potG Finset.univ (targetI tgt) (c₁.step (.move w f₀)) = vmoves evs₁ (init S) + 1 :=
    hΦ2
  have hgain : potG Finset.univ (targetI tgt) c₁ <
      potG Finset.univ (targetI tgt) (c₁.step (.move w f₀)) := by omega
  have hxmem : c₁.vec w ∈ c₁.sigma f₀ ⊔ targetI tgt f₀ := by
    by_contra h
    exact absurd (potG_move_le_of_notMem Finset.univ (targetI tgt) c₁ w f₀ h) (not_le.mpr hgain)
  -- decompose `x` at the origin: `x = a + d`, `a ∈ Σ₁ ⊓ N₁`, `d ∈ Σ₁ ⊓ N₀`
  have hx1 : c₁.vec w ∈ (c₁.sigma (c₁.frame w) ⊓ targetI tgt (c₁.frame w)) ⊔
      (c₁.sigma (c₁.frame w) ⊓ targetI tgt f₀) := by
    rw [← hN1, ← hs1]
    exact subset_span ⟨w, rfl, rfl⟩
  obtain ⟨a, ha, d, hd, hxad⟩ := Submodule.mem_sup.mp hx1
  -- decompose `x` at the destination: `x = d₀ + n₀`, `d₀ ∈ Σ₀ ⊓ N₁`, `n₀ ∈ N₀`
  have hx0 : c₁.vec w ∈ (c₁.sigma f₀ ⊓ targetI tgt (c₁.frame w)) ⊔ targetI tgt f₀ := by
    have h1 : c₁.sigma f₀ ≤ (c₁.sigma f₀ ⊓ targetI tgt (c₁.frame w)) ⊔ targetI tgt f₀ := by
      calc c₁.sigma f₀ = (c₁.sigma f₀ ⊓ targetI tgt f₀) ⊔ (c₁.sigma f₀ ⊓ targetI S f₀) := hs0
        _ = (c₁.sigma f₀ ⊓ targetI tgt f₀) ⊔ (c₁.sigma f₀ ⊓ targetI tgt (c₁.frame w)) := by
          rw [hN0]
        _ ≤ (c₁.sigma f₀ ⊓ targetI tgt (c₁.frame w)) ⊔ targetI tgt f₀ :=
          sup_le (inf_le_right.trans le_sup_right) le_sup_left
    exact (sup_le h1 le_sup_right) hxmem
  obtain ⟨d₀, hd₀, n₀, hn₀, hxdn⟩ := Submodule.mem_sup.mp hx0
  -- `a - d₀ = n₀ - d ∈ N₁ ⊓ N₀ = ⊥`
  have hN10 : targetI tgt (c₁.frame w) ⊓ targetI tgt f₀ = ⊥ :=
    targetI_inf_eq_bot tgt tgt (fun u hu hu' => hne (hu.symm.trans hu'))
  have hdiff : a - d₀ = n₀ - d := by
    have h := hxad.trans hxdn.symm
    calc a - d₀ = (a + d) - (d₀ + d) := by abel
      _ = (d₀ + n₀) - (d₀ + d) := by rw [h]
      _ = n₀ - d := by abel
  have had : a = d₀ := by
    have hmem : a - d₀ ∈ targetI tgt (c₁.frame w) ⊓ targetI tgt f₀ := by
      refine Submodule.mem_inf.mpr ⟨sub_mem (Submodule.mem_inf.mp ha).2
        (Submodule.mem_inf.mp hd₀).2, ?_⟩
      rw [hdiff]
      exact sub_mem hn₀ (Submodule.mem_inf.mp hd).2
    rw [hN10] at hmem
    exact sub_eq_zero.mp ((Submodule.mem_bot _).mp hmem)
  -- `a ∈ Σ₁ ⊓ Σ₀ = ⊥`
  have ha0 : a = 0 := by
    have hmem : a ∈ c₁.sigma (c₁.frame w) ⊓ c₁.sigma f₀ :=
      Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp ha).1, had ▸ (Submodule.mem_inf.mp hd₀).1⟩
    rw [sigma_inf_sigma_eq_bot c₁ hli hne] at hmem
    exact (Submodule.mem_bot _).mp hmem
  -- hence `x = d ∈ N₀`
  rw [← hxad, ha0, zero_add]
  exact (Submodule.mem_inf.mp hd).2

/-- **Cargo rule.** Two-class run model (`tgt u` is the unique frame other than `S u`):
in a valid run from `init S` that ends with wire `ρ u` at `tgt u` holding `e u` and makes exactly
`W` visible moves, every visible move (wire `w`, from frame `f₁ := frame w` to `f₀ ≠ f₁`) carries a
vector `x = vec w` with `x ∈ N f₀` (items whose home is the destination) and `x ∈ N' f₁` (items
born at the frame being left); the two subspaces coincide. -/
theorem cargo_rule [Fintype F] (S tgt : Fin W → F) (htgt : ∀ u, tgt u ≠ S u)
    (htwo : ∀ u f, f ≠ S u → tgt u = f)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (hW : vmoves evs (init S) = W)
    (evs₁ evs₂ : List (Event W F)) (w : Fin W) (f₀ : F)
    (hsplit : evs = evs₁ ++ .move w f₀ :: evs₂)
    (hvis : ((init S).run evs₁).frame w ≠ f₀) :
    ((init S).run evs₁).vec w ∈ targetI tgt f₀ ∧
      ((init S).run evs₁).vec w ∈ targetI S (((init S).run evs₁).frame w) := by
  have h := cargo_rule_of_le S tgt htgt htwo ρ evs hv hframe hvec hW.le evs₁ evs₂ w f₀ hsplit hvis
  refine ⟨h, ?_⟩
  rw [targetI_eq_of_two S tgt htwo hvis]
  exact h

/-- The cargo rule with the tightness hypothesis stated on all moves (`moves evs = W`, as in a
coarsened run in which every move is counted). -/
theorem cargo_rule_of_moves [Fintype F] (S tgt : Fin W → F) (htgt : ∀ u, tgt u ≠ S u)
    (htwo : ∀ u f, f ≠ S u → tgt u = f)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (hW : moves evs = W)
    (evs₁ evs₂ : List (Event W F)) (w : Fin W) (f₀ : F)
    (hsplit : evs = evs₁ ++ .move w f₀ :: evs₂)
    (hvis : ((init S).run evs₁).frame w ≠ f₀) :
    ((init S).run evs₁).vec w ∈ targetI tgt f₀ :=
  cargo_rule_of_le S tgt htgt htwo ρ evs hv hframe hvec
    ((vmoves_le_moves evs (init S)).trans hW.le) evs₁ evs₂ w f₀ hsplit hvis

/-- The cargo rule indexed by the position `i` of the move in the event list. -/
theorem cargo_rule_getElem [Fintype F] (S tgt : Fin W → F) (htgt : ∀ u, tgt u ≠ S u)
    (htwo : ∀ u f, f ≠ S u → tgt u = f)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (hW : vmoves evs (init S) = W)
    (i : ℕ) (hi : i < evs.length) (w : Fin W) (f₀ : F) (hmove : evs[i] = .move w f₀)
    (hvis : ((init S).run (evs.take i)).frame w ≠ f₀) :
    ((init S).run (evs.take i)).vec w ∈ targetI tgt f₀ :=
  cargo_rule_of_le S tgt htgt htwo ρ evs hv hframe hvec hW.le (evs.take i) (evs.drop (i + 1)) w f₀
    (by rw [← hmove, ← List.drop_eq_getElem_cons hi, List.take_append_drop]) hvis

/-- Specialisation to `F = Bool`: the frames are the two classes and `tgt u = !S u`. -/
theorem cargo_rule_bool (S : Fin W → Bool)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W Bool)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = !S u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (hW : vmoves evs (init S) = W)
    (evs₁ evs₂ : List (Event W Bool)) (w : Fin W) (f₀ : Bool)
    (hsplit : evs = evs₁ ++ .move w f₀ :: evs₂)
    (hvis : ((init S).run evs₁).frame w ≠ f₀) :
    ((init S).run evs₁).vec w ∈ targetI (fun u => !S u) f₀ :=
  (cargo_rule S (fun u => !S u) (fun u => by cases S u <;> decide)
    (fun u f h => by cases f <;> cases hS : S u <;> simp_all)
    ρ evs hv hframe hvec hW evs₁ evs₂ w f₀ hsplit hvis).1

end Transpose.ShearFrame
