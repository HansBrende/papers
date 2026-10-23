import TransposeFollowup.AdaptiveForestRefinement
import TransposeFollowup.GraphNearCount

/-! Projected ancestor classes have bounded row volume and bounded row
pair distance. The coordinate forest need not have bounded vertex degree. -/

namespace TransposeFollowup.AdaptiveForest

open Classical
set_option autoImplicit false

variable {V W : Type*} [Fintype V] [Fintype W]

noncomputable def classImage [DecidableEq W] (label : V → V)
    (row : V → W) (a : V) : Finset W :=
  (Finset.univ.filter (fun v => label v = a)).image row

omit [Fintype W] in
@[simp] theorem mem_classImage [DecidableEq W] (label : V → V)
    (row : V → W) (a : V) (i : W) :
    i ∈ classImage label row a ↔ ∃ v, label v = a ∧ row v = i := by
  simp [classImage]

omit [Fintype V] [Fintype W] in
theorem projected_near {G : SimpleGraph V} {H : SimpleGraph W}
    (row : V → W) (hrow : ∀ {v w}, G.Adj v w → row v = row w ∨ H.Adj (row v) (row w))
    {ell : ℕ} {v w : V} (h : GraphNear G ell v w) : GraphNear H ell (row v) (row w) := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := project_walk row hrow p
  exact ⟨q, hq.trans_lt hp⟩

theorem ancestor_class_subset [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (row : V → W)
    (hrow : ∀ {v w}, G.Adj v w → row v = row w ∨ H.Adj (row v) (row w))
    {R : ℕ} (hR : 0 < R) (r : ℕ) (a : V) :
    classImage (ancestor G R r) row a ⊆ nearVertices H R (row a) := by
  intro i hi
  obtain ⟨v, hv, rfl⟩ := (mem_classImage _ _ _ _).mp hi
  apply (mem_nearVertices _ _ _ _).mpr
  have hn := projected_near row hrow (ancestor_near G R r hR v)
  rwa [hv] at hn

theorem positive_ball_card_le [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ i, H.degree i ≤ D) {R : ℕ} (hR : 0 < R) (i : W) :
    (nearVertices H R i).card ≤ D ^ R := by
  have h := nearVertices_card_le_power H D hD hdegree (R - 1) i
  have he : R - 1 + 1 = R := by omega
  rw [he] at h
  calc
    _ ≤ 2 * D ^ (R - 1) := h
    _ ≤ D * D ^ (R - 1) := Nat.mul_le_mul_right _ hD
    _ = D ^ R := by rw [← pow_succ', he]

theorem ancestor_class_card_le [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (row : V → W)
    (hrow : ∀ {v w}, G.Adj v w → row v = row w ∨ H.Adj (row v) (row w))
    (D : ℕ) (hD : 2 ≤ D) (hdegree : ∀ i, H.degree i ≤ D)
    {R : ℕ} (hR : 0 < R) (r : ℕ) (a : V) :
    (classImage (ancestor G R r) row a).card ≤ D ^ R :=
  (Finset.card_le_card (ancestor_class_subset G H row hrow hR r a)).trans
    (positive_ball_card_le H D hD hdegree hR (row a))

omit [Fintype V] [Fintype W] in
theorem ancestor_class_rows_near (G : SimpleGraph V) (H : SimpleGraph W) (row : V → W)
    (hrow : ∀ {v w}, G.Adj v w → row v = row w ∨ H.Adj (row v) (row w))
    {R : ℕ} (hR : 0 < R) {r : ℕ} {v w : V}
    (he : ancestor G R r v = ancestor G R r w) :
    GraphNear H (2 * R - 1) (row v) (row w) :=
  projected_near row hrow (same_ancestor_near G hR he)

end TransposeFollowup.AdaptiveForest
