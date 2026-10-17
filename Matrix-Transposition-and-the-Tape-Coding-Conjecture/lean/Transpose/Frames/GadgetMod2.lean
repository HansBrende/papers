import Transpose.Frames.GadgetCoarse

/-!
# The two-sided mod-2 bound for m = 2: gadgets with 2×2 integer frames never beat the baseline

For `2 × 2` integer frames, the six coarsenings `M ↦ λᵀ (M mod 2) μ` with `λᵀμ = 1` over `F₂`,
each separating every source from its target, see at least `W` moves each (the coarsening lemma);
a jump of rank `r` (over `ℚ`) is seen by at most `3r` of them (finite check over `F₂^{2×2}`), hence
the total rank of the jumps is at least `2W`: `two_mul_le_rank_sum`.
-/

namespace Transpose.ShearFrame

open Module Submodule Matrix

variable {W : ℕ} {F F' : Type} [DecidableEq F] [DecidableEq F']

/-- The visible moves of a coarsened run are the jumps whose endpoints differ under `π`. -/
theorem vmoves_map_eq (π : F → F') : ∀ (evs : List (Event W F)) (c : Cfg W F),
    vmoves (evs.map (Event.map π)) (c.map π) =
      ((jumps evs c).map (fun p => if π p.1 = π p.2 then 0 else 1)).sum
  | [], _ => rfl
  | .gate i j :: evs, c => by
      show vmoves (evs.map (Event.map π)) ((c.map π).step (.gate i j)) =
        ((jumps evs (c.step (.gate i j))).map (fun p => if π p.1 = π p.2 then 0 else 1)).sum
      rw [step_map_gate]
      exact vmoves_map_eq π evs _
  | .move w f :: evs, c => by
      show vmoves (evs.map (Event.map π)) ((c.map π).step (.move w (π f))) +
        (if π (c.frame w) = π f then 0 else 1) =
        (if π (c.frame w) = π f then 0 else 1) +
          ((jumps evs (c.step (.move w f))).map (fun p => if π p.1 = π p.2 then 0 else 1)).sum
      rw [step_map_move, vmoves_map_eq π evs _, Nat.add_comm]

/-- Exchanging a sum over a family with a sum over a list. -/
theorem sum_map_sum_comm {α β : Type} (g : β → α → ℕ) :
    ∀ (l : List α) (fam : List β),
      (fam.map (fun q => (l.map (g q)).sum)).sum =
        (l.map (fun p => (fam.map (fun q => g q p)).sum)).sum
  | [], fam => by simp
  | p :: l, fam => by
      simp only [List.map_cons, List.sum_cons]
      rw [← sum_map_sum_comm g l fam, ← List.sum_map_add]

/-! ### The six coarsenings and the finite check -/

/-- The pairs `(λ, μ) ∈ F₂² × F₂²` with `λ ⬝ᵥ μ = 1`. -/
def fam2 : List ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :=
  [(![1, 0], ![1, 0]), (![1, 0], ![1, 1]), (![0, 1], ![0, 1]),
   (![0, 1], ![1, 1]), (![1, 1], ![1, 0]), (![1, 1], ![0, 1])]

theorem fam2_dot : ∀ q ∈ fam2, q.1 ⬝ᵥ q.2 = 1 := by decide

theorem fam2_length : fam2.length = 6 := rfl

/-- How many of the six coarsenings see a jump `J` (mod 2). -/
def visCount (J : Matrix (Fin 2) (Fin 2) (ZMod 2)) : ℕ :=
  (fam2.map (fun q => if q.1 ⬝ᵥ (J *ᵥ q.2) = 0 then 0 else 1)).sum

/-- Rank over `F₂` of a `2 × 2` matrix, computably. -/
def r2 (J : Matrix (Fin 2) (Fin 2) (ZMod 2)) : ℕ :=
  if J = 0 then 0 else if J 0 0 * J 1 1 - J 0 1 * J 1 0 = 0 then 1 else 2

theorem visCount_le_aux : ∀ a b c d : ZMod 2,
    visCount !![a, b; c, d] ≤ 3 * r2 !![a, b; c, d] := by decide

theorem visCount_le (J : Matrix (Fin 2) (Fin 2) (ZMod 2)) : visCount J ≤ 3 * r2 J := by
  rw [Matrix.eta_fin_two J]
  exact visCount_le_aux _ _ _ _

/-! ### Rank over ℚ dominates rank mod 2 -/

/-- Reduction of integer matrices mod 2 and embedding into ℚ. -/
def red : Matrix (Fin 2) (Fin 2) ℤ →+* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  (Int.castRingHom (ZMod 2)).mapMatrix
def redQ : Matrix (Fin 2) (Fin 2) ℤ →+* Matrix (Fin 2) (Fin 2) ℚ :=
  (Int.castRingHom ℚ).mapMatrix

theorem red_apply (J : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) : red J i j = (J i j : ZMod 2) := rfl
theorem redQ_apply (J : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) : redQ J i j = (J i j : ℚ) := rfl

theorem one_le_rank_of_ne_zero (A : Matrix (Fin 2) (Fin 2) ℚ) (hA : A ≠ 0) : 1 ≤ A.rank := by
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hA (Matrix.ext h)
  have hx : A *ᵥ Pi.single j 1 ≠ 0 := by
    intro h0
    have := congrFun h0 i
    rw [Matrix.mulVec_single_one] at this
    exact hij this
  have hmem : A *ᵥ Pi.single j 1 ∈ LinearMap.range A.mulVecLin :=
    ⟨Pi.single j 1, Matrix.mulVecLin_apply _ _⟩
  unfold Matrix.rank
  calc 1 = finrank ℚ (span ℚ {A *ᵥ Pi.single j 1}) := (finrank_span_singleton hx).symm
    _ ≤ finrank ℚ (LinearMap.range A.mulVecLin) :=
        Submodule.finrank_mono ((span_singleton_le_iff_mem _ _).mpr hmem)

theorem r2_le_rank (J : Matrix (Fin 2) (Fin 2) ℤ) : r2 (red J) ≤ (redQ J).rank := by
  unfold r2
  split_ifs with h0 hdet
  · exact Nat.zero_le _
  · apply one_le_rank_of_ne_zero
    intro hQ
    apply h0
    ext i j
    have := congrFun (congrFun hQ i) j
    rw [redQ_apply] at this
    simp only [Matrix.zero_apply, Int.cast_eq_zero] at this
    rw [red_apply, this]
    simp
  · have hd : (red J).det ≠ 0 := by
      rw [Matrix.det_fin_two]
      exact hdet
    have hd' : (J.det : ZMod 2) ≠ 0 := by
      have h := RingHom.map_det (Int.castRingHom (ZMod 2)) J
      show (Int.castRingHom (ZMod 2)) J.det ≠ 0
      rw [h]
      exact hd
    have hdZ : J.det ≠ 0 := fun h => hd' (by rw [h]; simp)
    have hdQ : (redQ J).det ≠ 0 := by
      have h := RingHom.map_det (Int.castRingHom ℚ) J
      show ((Int.castRingHom ℚ).mapMatrix J).det ≠ 0
      rw [← h]
      show (J.det : ℚ) ≠ 0
      exact_mod_cast hdZ
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdQ))]
    simp

/-! ### The theorem -/

/-- The coarsening attached to a pair `(λ, μ)`. -/
def coarse2 (q : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) (M : Matrix (Fin 2) (Fin 2) ℤ) : ZMod 2 :=
  q.1 ⬝ᵥ (red M *ᵥ q.2)

theorem coarse2_sub (q : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    coarse2 q B - coarse2 q A = q.1 ⬝ᵥ (red (B - A) *ᵥ q.2) := by
  unfold coarse2
  rw [map_sub, Matrix.sub_mulVec, dotProduct_sub]

theorem coarse2_shift (q : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) (hq : q.1 ⬝ᵥ q.2 = 1)
    (M : Matrix (Fin 2) (Fin 2) ℤ) : coarse2 q (M + 1) ≠ coarse2 q M := by
  intro h
  have h1 : coarse2 q (M + 1) - coarse2 q M = 1 := by
    rw [coarse2_sub, add_sub_cancel_left, map_one, Matrix.one_mulVec, hq]
  rw [h, sub_self] at h1
  exact zero_ne_one h1

/-- **Two-sided mod-2 bound, m = 2.** With `2 × 2` integer frames and targets `S u + 1`, the
total rank (over ℚ) of the jumps of any valid run realising the permutation is at least `2W`. -/
theorem two_mul_le_rank_sum (S : Fin W → Matrix (Fin 2) (Fin 2) ℤ) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W (Matrix (Fin 2) (Fin 2) ℤ))) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = S u + 1)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u) :
    2 * W ≤ ((jumps evs (init S)).map (fun p => (redQ (p.2 - p.1)).rank)).sum := by
  set J := jumps evs (init S) with hJ
  -- each coarsening sees ≥ W jumps
  have hq : ∀ q ∈ fam2, W ≤ (J.map (fun p => if coarse2 q p.1 = coarse2 q p.2 then 0 else 1)).sum := by
    intro q hqmem
    rw [hJ, ← vmoves_map_eq]
    exact visible_ge_W_of_coarse S (fun u => S u + 1) ρ evs hv hframe hvec (coarse2 q)
      (fun u => coarse2_shift q (fam2_dot q hqmem) (S u))
  -- sum over the six coarsenings
  have hsum : 6 * W ≤ (fam2.map (fun q =>
      (J.map (fun p => if coarse2 q p.1 = coarse2 q p.2 then 0 else 1)).sum)).sum := by
    have h := List.sum_le_sum (l := fam2) (f := fun _ => W) hq
    have h6 : (fam2.map (fun _ => W)).sum = 6 * W := by simp [fam2]; omega
    rw [h6] at h
    exact h
  rw [sum_map_sum_comm] at hsum
  -- per jump: the number of coarsenings that see it is visCount of its reduction
  have hvis : ∀ p ∈ J, (fam2.map (fun q => if coarse2 q p.1 = coarse2 q p.2 then 0 else 1)).sum
      = visCount (red (p.2 - p.1)) := by
    intro p _
    unfold visCount
    congr 1
    apply List.map_congr_left
    intro q _
    apply if_congr _ rfl rfl
    rw [← coarse2_sub, sub_eq_zero, eq_comm]
  rw [List.map_congr_left hvis] at hsum
  -- and that is at most 3 × rank
  have hle : (J.map (fun p => visCount (red (p.2 - p.1)))).sum ≤
      (J.map (fun p => 3 * (redQ (p.2 - p.1)).rank)).sum := by
    apply List.sum_le_sum
    intro p _
    exact (visCount_le _).trans (Nat.mul_le_mul_left 3 (r2_le_rank _))
  rw [List.sum_map_mul_left] at hle
  omega

end Transpose.ShearFrame
