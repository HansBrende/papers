import MergeDepth.Realization
import MergeDepth.HopFields

/-!
# Paired distances on a skeleton class and inside balls (Lemmas 4.9, 4.10, Proposition 4.11, Lemma 3.14(a))

The data of a skeleton class at scale `w` are abstract: reference walks `z c` for the input head
(`none`), the output count (`some none`) and the work heads (`some (some j)`), of length `T`; the
coarse work walks `s j = ⌊z (work j)/w⌋`, whose dependency DAG is the block DAG (Lemma 4.5(a)); a
genie `Γ` of full depth at most `D` in it; and an output time `ot r < T` for every output position
`r`, in the output block `⌊r/w⌋` (Lemma 4.5(c); the paper takes the last such time). The cone relation
(`coneRel`, Lemma 4.7) puts `p ∈ N_Γ(q)` when some `Γ`-free path of the block DAG from the output time
of `tpos q` ends at a time whose input block contains `p`.

* `realizes_cone`: **Lemma 4.9.** `N_Γ` has the realization property with `K_w = (k + 2)(2w - 1)` heads,
  one register and occupancy `w B`, `B = ∑_{h ≤ D} (k + 1)^h` (the paper: `w B + 1`).
* `skel_disjoint_paths`, `skel_disjoint_paths_transport`: **Lemma 4.10**,
  `m log₂ d ≤ w B K_w (K_w + 1) s T + 3L`, so `m ≤ A_s^{(w)} L/log₂ d` with
  `A_s^{(w)} = 2 s c w B K_w (K_w + 1) + 3` when `T ≤ c (L + 1)` (the paper:
  `4 s c (w B + 1) K_w (K_w + 4) + 3`).
* `skel_paired_packing`, `skel_self_demands`: **Proposition 4.11(a), (b).**
* `realizes_ball`, `ball_paired_packing`, `ball_self_demands`: **Lemma 3.14(a)**, the same for
  relations inside the balls `B^{D'}` of an oblivious schedule (`stepBall`), at scale `w = 1`, with
  `K = k + 2` heads and occupancy `B_{D'}` (the paper: `B_{D'} + 1` and the constants of the fifth
  paper).
-/

namespace MergeDepth

open Finset BoundedNesting DirectedRecovery

variable {k : ℕ}

theorem card_heads (w : ℕ) : Fintype.card (Tp k × Fin (2 * w - 1)) = (k + 2) * (2 * w - 1) := by
  simp [Fintype.card_prod, Fintype.card_option]

/-- The input heads start in the `2w - 1 ≤ W` cells around the input reference walk. -/
theorem nbhd_window {w W : ℕ} (hw : 1 ≤ w) (hW : 2 * w - 1 ≤ W) (z : Tp k → ℕ → ℤ)
    (h : Tp k × Fin (2 * w - 1)) (_ : h.1 = none) :
    z none 0 - ((w : ℤ) - 1) ≤ nbhd w z 0 h ∧ nbhd w z 0 h ≤ z none 0 - ((w : ℤ) - 1) + W - 1 := by
  obtain ⟨c, i⟩ := h
  simp only at *
  subst ‹c = none›
  simp only [nbhd]
  have hi := i.2
  have hW' : (2 * w - 1 : ℕ) ≤ (W : ℤ) := by exact_mod_cast hW
  have : ((2 * w - 1 : ℕ) : ℤ) = 2 * w - 1 := by omega
  constructor <;> omega

/-! ### Lemma 4.9 -/

open Classical in
/-- **The cone relation of a skeleton class** (Lemma 4.7): `p ∈ N_Γ(q)` iff some `Γ`-free path of the
block DAG from the output time of the demand `dm q` ends at a time whose input block contains `p`. -/
noncomputable def coneRel (w : ℕ) (z : Tp k → ℕ → ℤ) (T : ℕ) (Γ : Finset ℕ) {L : ℕ}
    (ot : ℕ → ℕ) (dm : Fin L → ℕ) (q : Fin L) : Finset (Fin L) :=
  univ.filter fun p => ∃ π : List ℕ,
    IsDepPath (fun j => skel w (z (some (some j)))) T (ot (dm q) :: π) ∧
      LinNet.GFree Γ (ot (dm q) :: π) ∧
      (p : ℤ) / w = z none ((ot (dm q) :: π).getLastD (ot (dm q))) / w

open Classical in
/-- **Lemma 4.9.** If `Γ` has full depth at most `D` in the block DAG, the output time of every demand
lies in its output block, and the demands `dm` are distinct, then every matching of incidences of
`N_Γ` is realized in `T` ticks by `2w - 1` heads on each of the `k + 2` tapes around the reference
walks, with one register and occupancy at most `w B`, `B = ∑_{h ≤ D} (k + 1)^h`. -/
theorem realizes_cone {w : ℕ} (hw : 1 ≤ w) {z : Tp k → ℕ → ℤ} (hz : ∀ c, IsWalk (z c))
    {T D : ℕ} {Γ : Finset ℕ}
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    {L : ℕ} (ot : ℕ → ℕ) (dm : Fin L → ℕ) (hdm : Function.Injective dm)
    (hot : ∀ q, ot (dm q) < T ∧ (dm q : ℤ) / w = z (some none) (ot (dm q)) / w) :
    Realizes (Prod.fst : Tp k × Fin (2 * w - 1) → Tp k) none (some none) 1 T
      (w * ∑ h ∈ range (D + 1), (k + 1) ^ h) (nbhd w z) (coneRel w z T Γ ot dm)
      (fun p => (p : ℤ)) (fun q => (dm q : ℤ)) := by
  intro m src dst hsrc hdst hinc
  have hmem := fun j => (mem_filter.mp (hinc j)).2
  choose π hπ hfree hin using hmem
  refine realize_paths hw hz (fun j => ot (dm (dst j))) π (fun j => (src j : ℤ))
    (fun j => (dm (dst j) : ℤ)) hπ (fun j => ?_) (fun j => (hot _).1) hin (fun j => (hot _).2)
    (fun j j' h => hsrc (Fin.ext (by simp only at h; exact_mod_cast h)))
    (fun j j' h => hdst (hdm (by simp only at h; exact_mod_cast h)))
  have := hdepth _ (hπ j) (hfree j)
  simp only [List.length_cons] at this
  omega

/-! ### Lemma 4.10 and Proposition 4.11 on a skeleton class -/

/-- The transposition demands are distinct cells of `[0, L)` that carry the rows of their sources. -/
theorem tpos_props {d b : ℕ} (hb : 1 ≤ b) :
    Function.Injective (fun q : Fin (d * d * b) => (tpos d b q : ℤ)) ∧
      (∀ q : Fin (d * d * b), 0 ≤ (tpos d b q : ℤ) ∧ (tpos d b q : ℤ) < d * (d * b : ℕ)) ∧
      ∀ q : Fin (d * d * b), (tpos d b q : ℤ) % (d * b : ℕ) / b = (q : ℤ) / (d * b : ℕ) := by
  have hb0 : 0 < b := by omega
  refine ⟨fun q q' h => ?_, fun q => ⟨by positivity, ?_⟩, fun q => ?_⟩
  · simp only [Nat.cast_inj] at h
    have := congrArg (tpos d b) h
    rw [tpos_tpos hb0 q.2, tpos_tpos hb0 q'.2] at this
    exact Fin.ext this
  · have := tpos_lt hb0 q.2
    push_cast
    have : (tpos d b q : ℤ) < (d * d * b : ℕ) := by exact_mod_cast this
    push_cast at this
    linarith
  · have := tpos_row hb0 q.2
    have h' : ((tpos d b q % (d * b) / b : ℕ) : ℤ) = ((q / (d * b) : ℕ) : ℤ) := by rw [this]
    push_cast at h'
    exact h'

/-- **Lemma 4.10 on a skeleton class.** With `K_w = (k + 2)(2w - 1)`, `B = ∑_{h ≤ D} (k + 1)^h`,
`L = d² b`, `db ≥ 2w - 1` and `d ≥ 2`: if the incidence graph of the cone relation `N_Γ` (with the
transposition demands) has `m` pairwise vertex-disjoint walks with `s` edges from `L_x` to `R_x`, then
`m log₂ d ≤ w B K_w (K_w + 1) s T + 3 L`. -/
theorem skel_disjoint_paths {w d b : ℕ} (hw : 1 ≤ w) (hd : 2 ≤ d) (hb : 1 ≤ b)
    (hdbw : 2 * w - 1 ≤ d * b) {z : Tp k → ℕ → ℤ} (hz : ∀ c, IsWalk (z c)) {T D : ℕ}
    {Γ : Finset ℕ}
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (ot : ℕ → ℕ) (hot : ∀ q : Fin (d * d * b),
      ot (tpos d b q) < T ∧ (tpos d b q : ℤ) / w = z (some none) (ot (tpos d b q)) / w)
    {I : Type*} (c : I → Fin (d * d * b))
    (p : ∀ i, (pairedIncidenceGraph (coneRel w z T Γ ot (fun q : Fin (d * d * b) => tpos d b q))).Walk
      (.inl (c i)) (.inr (c i)))
    {s : ℕ} (J : Finset I) (hlen : ∀ i ∈ J, (p i).length = s)
    (hdisj : (J : Set I).PairwiseDisjoint fun i => (p i).support.toFinset) :
    J.card * Real.logb 2 d ≤ (w * ∑ h ∈ range (D + 1), (k + 1) ^ h : ℕ) *
      ((k + 2) * (2 * w - 1) : ℕ) * (((k + 2) * (2 * w - 1) : ℕ) + 1) * s * T + 3 * (d * d * b) := by
  obtain ⟨hinj, hrange, hrow⟩ := tpos_props (d := d) hb
  have hreal := realizes_cone hw hz hdepth ot (fun q : Fin (d * d * b) => tpos d b q) (fun q q' h => hinj (by
    simp only [Nat.cast_inj]; exact h)) hot
  have h := disjoint_paths_bound hreal hd hb rfl hinj hrange (fun q => (hrow q))
    (z none 0 - ((w : ℤ) - 1)) (fun h hh => nbhd_window hw hdbw z h hh) c p J hlen hdisj
  rw [card_heads] at h
  push_cast at h ⊢
  linarith

/-- **Lemma 4.10 on a skeleton class**, in the form `HasDisjointPathTransport` of the fifth paper:
if `T ≤ c (L + 1)`, at most `A_s^{(w)} L/log₂ d` disjoint paired walks with `s` edges, where
`A_s^{(w)} = 2 s c w B K_w (K_w + 1) + 3`. -/
theorem skel_disjoint_paths_transport {w d b : ℕ} (hw : 1 ≤ w) (hd : 2 ≤ d) (hb : 1 ≤ b)
    (hdbw : 2 * w - 1 ≤ d * b) {z : Tp k → ℕ → ℤ} (hz : ∀ c, IsWalk (z c)) {T D : ℕ}
    {Γ : Finset ℕ}
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (ot : ℕ → ℕ) (hot : ∀ q : Fin (d * d * b),
      ot (tpos d b q) < T ∧ (tpos d b q : ℤ) / w = z (some none) (ot (tpos d b q)) / w)
    {c : ℝ} (hc : 0 ≤ c) (hT : (T : ℝ) ≤ c * (d * d * b + 1)) (r : ℕ) :
    HasDisjointPathTransport (coneRel w z T Γ ot (fun q : Fin (d * d * b) => tpos d b q)) r
      (fun s => (2 * s * c * (w * ∑ h ∈ range (D + 1), (k + 1) ^ h : ℕ) *
        ((k + 2) * (2 * w - 1) : ℕ) * (((k + 2) * (2 * w - 1) : ℕ) + 1) + 3) *
          ((d : ℝ) ^ 2 * b) / Real.logb 2 d) := by
  obtain ⟨hinj, hrange, hrow⟩ := tpos_props (d := d) hb
  have hreal := realizes_cone hw hz hdepth ot (fun q : Fin (d * d * b) => tpos d b q) (fun q q' h => hinj (by
    simp only [Nat.cast_inj]; exact h)) hot
  have h := disjoint_paths_transport hreal hd hb rfl hinj hrange (fun q => (hrow q))
    (z none 0 - ((w : ℤ) - 1)) (fun h hh => nbhd_window hw hdbw z h hh) hc hT r
  rw [card_heads] at h
  exact_mod_cast h

open Classical in
/-- **Proposition 4.11(a).** For `Q ⊆ [0, L)` whose induced incidence graph has maximum degree at most
`Δ`, the coordinates of `Q` with paired distance at most `r` in `E_Q` number at most
`∑_{s ≤ r odd} (s + 1) ν_r A_s^{(w)} L/log₂ d`. -/
theorem skel_paired_packing {w d b : ℕ} (hw : 1 ≤ w) (hd : 2 ≤ d) (hb : 1 ≤ b)
    (hdbw : 2 * w - 1 ≤ d * b) {z : Tp k → ℕ → ℤ} (hz : ∀ c, IsWalk (z c)) {T D : ℕ}
    {Γ : Finset ℕ}
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (ot : ℕ → ℕ) (hot : ∀ q : Fin (d * d * b),
      ot (tpos d b q) < T ∧ (tpos d b q : ℤ) / w = z (some none) (ot (tpos d b q)) / w)
    {c : ℝ} (hc : 0 ≤ c) (hT : (T : ℝ) ≤ c * (d * d * b + 1)) (Q : Finset (Fin (d * d * b)))
    (r Δ : ℕ)
    (hdeg : ∀ v, (pairedIncidenceGraph (inducedNeighborhood
      (coneRel w z T Γ ot (fun q : Fin (d * d * b) => tpos d b q)) Q)).degree v ≤ Δ) :
    ((shortPairedCoordinates (inducedNeighborhood
        (coneRel w z T Γ ot (fun q : Fin (d * d * b) => tpos d b q)) Q) r).card : ℝ) ≤
      pathPackingConstant r Δ (fun s => 2 * s * c * (w * ∑ h ∈ range (D + 1), (k + 1) ^ h : ℕ) *
        ((k + 2) * (2 * w - 1) : ℕ) * (((k + 2) * (2 * w - 1) : ℕ) + 1) + 3) *
        (((d : ℝ) ^ 2 * b) / Real.logb 2 d) := by
  obtain ⟨hinj, hrange, hrow⟩ := tpos_props (d := d) hb
  have hreal := realizes_cone hw hz hdepth ot (fun q : Fin (d * d * b) => tpos d b q) (fun q q' h => hinj (by
    simp only [Nat.cast_inj]; exact h)) hot
  have h := paired_distance_packing hreal hd hb rfl hinj hrange (fun q => (hrow q))
    (z none 0 - ((w : ℤ) - 1)) (fun h hh => nbhd_window hw hdbw z h hh) hc hT Q r Δ hdeg
  rw [card_heads] at h
  exact_mod_cast h

open Classical in
/-- **Proposition 4.11(b).** The self-demands `p ∈ N_Γ(p)` number at most `A_1^{(w)} L/log₂ d`. -/
theorem skel_self_demands {w d b : ℕ} (hw : 1 ≤ w) (hd : 2 ≤ d) (hb : 1 ≤ b)
    (hdbw : 2 * w - 1 ≤ d * b) {z : Tp k → ℕ → ℤ} (hz : ∀ c, IsWalk (z c)) {T D : ℕ}
    {Γ : Finset ℕ}
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (ot : ℕ → ℕ) (hot : ∀ q : Fin (d * d * b),
      ot (tpos d b q) < T ∧ (tpos d b q : ℤ) / w = z (some none) (ot (tpos d b q)) / w)
    {c : ℝ} (hc : 0 ≤ c) (hT : (T : ℝ) ≤ c * (d * d * b + 1)) :
    ((selfDemandCoordinates (coneRel w z T Γ ot (fun q : Fin (d * d * b) => tpos d b q))).card : ℝ) ≤
      (2 * c * (w * ∑ h ∈ range (D + 1), (k + 1) ^ h : ℕ) * ((k + 2) * (2 * w - 1) : ℕ) *
        (((k + 2) * (2 * w - 1) : ℕ) + 1) + 3) * ((d : ℝ) ^ 2 * b) / Real.logb 2 d := by
  obtain ⟨hinj, hrange, hrow⟩ := tpos_props (d := d) hb
  have hreal := realizes_cone hw hz hdepth ot (fun q : Fin (d * d * b) => tpos d b q) (fun q q' h => hinj (by
    simp only [Nat.cast_inj]; exact h)) hot
  have h := self_demands_le hreal hd hb rfl hinj hrange (fun q => (hrow q))
    (z none 0 - ((w : ℤ) - 1)) (fun h hh => nbhd_window hw hdbw z h hh) hc hT
  rw [card_heads] at h
  exact_mod_cast h

/-! ### Lemma 3.14(a): relations inside balls -/

theorem skel_one (x : ℕ → ℤ) : skel 1 x = x := funext fun t => by simp [skel]

open Classical in
/-- **Realizing relations inside balls** (the realization step of Lemma 3.14(a)). For an oblivious
schedule with head walks `z` (the input head `z none`, which reads position `j` at step `u` when
`rdStep u = some j`; the output count `z (some none)`, equal to `ℓ` at the step `tout ℓ < T` that
appends position `ℓ`; the work heads `z (some (some j))`), every relation with
`N(q) ⊆ B^{D'}(tpos q)` is realized by one head per tape with one register and occupancy
`B_{D'} = ∑_{h ≤ D'} (k + 1)^h`. -/
theorem realizes_ball {z : Tp k → ℕ → ℤ} (hz : ∀ c, IsWalk (z c)) {T D' L : ℕ}
    (rdStep : ℕ → Option (Fin L)) (hrd : ∀ u j, rdStep u = some j → z none u = j)
    (tout : ℕ → ℕ) (dm : Fin L → ℕ) (hdm : Function.Injective dm)
    (htout : ∀ q, tout (dm q) < T ∧ z (some none) (tout (dm q)) = dm q)
    (N : Fin L → Finset (Fin L))
    (hN : ∀ q, N q ⊆ stepBall (fun j => z (some (some j))) T rdStep D' (tout (dm q))) :
    Realizes (Prod.fst : Tp k × Fin (2 * 1 - 1) → Tp k) none (some none) 1 T
      (1 * ∑ h ∈ range (D' + 1), (k + 1) ^ h) (nbhd 1 z) N
      (fun p => (p : ℤ)) (fun q => (dm q : ℤ)) := by
  intro m src dst hsrc hdst hinc
  have hmem := fun j => (mem_filter.mp (hN _ (hinc j))).2
  choose π hπ hlen hrd' using hmem
  have hs : (fun j => skel 1 (z (some (some j)))) = fun j => z (some (some j)) :=
    funext fun j => skel_one _
  refine realize_paths le_rfl hz (fun j => tout (dm (dst j))) π (fun j => (src j : ℤ))
    (fun j => (dm (dst j) : ℤ)) (fun j => by simp only [Nat.cast_one]; rw [hs]; exact hπ j) hlen
    (fun j => (htout _).1) (fun j => ?_) (fun j => ?_)
    (fun j j' h => hsrc (Fin.ext (by simp only at h; exact_mod_cast h)))
    (fun j j' h => hdst (hdm (by simp only at h; exact_mod_cast h)))
  · simp only [Nat.cast_one, Int.ediv_one]
    exact (hrd _ _ (hrd' j)).symm
  · simp only [Nat.cast_one, Int.ediv_one]
    exact (htout _).2.symm

open Classical in
/-- **Lemma 3.14(a), Theorem 3.3 of the fifth paper for relations inside balls**, with
`A_s = 2 s c B_{D'} (k + 2)(k + 3) + 3`. -/
theorem ball_paired_packing {d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b) {z : Tp k → ℕ → ℤ}
    (hz : ∀ c, IsWalk (z c)) {T D' : ℕ} (rdStep : ℕ → Option (Fin (d * d * b)))
    (hrd : ∀ u j, rdStep u = some j → z none u = j) (tout : ℕ → ℕ)
    (htout : ∀ q : Fin (d * d * b), tout (tpos d b q) < T ∧ z (some none) (tout (tpos d b q)) = tpos d b q)
    (N : Fin (d * d * b) → Finset (Fin (d * d * b)))
    (hN : ∀ q, N q ⊆ stepBall (fun j => z (some (some j))) T rdStep D' (tout (tpos d b q)))
    {c : ℝ} (hc : 0 ≤ c) (hT : (T : ℝ) ≤ c * (d * d * b + 1)) (Q : Finset (Fin (d * d * b)))
    (r Δ : ℕ) (hdeg : ∀ v, (pairedIncidenceGraph (inducedNeighborhood N Q)).degree v ≤ Δ) :
    ((shortPairedCoordinates (inducedNeighborhood N Q) r).card : ℝ) ≤
      pathPackingConstant r Δ (fun s => 2 * s * c * (∑ h ∈ range (D' + 1), (k + 1) ^ h : ℕ) *
        (k + 2 : ℕ) * ((k + 2 : ℕ) + 1) + 3) * (((d : ℝ) ^ 2 * b) / Real.logb 2 d) := by
  obtain ⟨hinj, hrange, hrow⟩ := tpos_props (d := d) hb
  have hreal := realizes_ball hz rdStep hrd tout (fun q : Fin (d * d * b) => tpos d b q) (fun q q' h => hinj (by
    simp only [Nat.cast_inj]; exact h)) htout N hN
  have h := paired_distance_packing hreal hd hb rfl hinj hrange (fun q => (hrow q))
    (z none 0 - ((1 : ℤ) - 1)) (fun h hh => nbhd_window le_rfl (by have : 1 * 1 ≤ d * b := Nat.mul_le_mul (by omega) hb; omega) z h hh) hc hT Q r Δ hdeg
  rw [card_heads] at h
  simpa using h

open Classical in
/-- **Lemma 3.14(a), Corollary 3.7 of the fifth paper for relations inside balls**: at most
`(2 c B_{D'} (k + 2)(k + 3) + 3) L/log₂ d` positions `p` satisfy `p ∈ N(p)`. -/
theorem ball_self_demands {d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b) {z : Tp k → ℕ → ℤ}
    (hz : ∀ c, IsWalk (z c)) {T D' : ℕ} (rdStep : ℕ → Option (Fin (d * d * b)))
    (hrd : ∀ u j, rdStep u = some j → z none u = j) (tout : ℕ → ℕ)
    (htout : ∀ q : Fin (d * d * b), tout (tpos d b q) < T ∧ z (some none) (tout (tpos d b q)) = tpos d b q)
    (N : Fin (d * d * b) → Finset (Fin (d * d * b)))
    (hN : ∀ q, N q ⊆ stepBall (fun j => z (some (some j))) T rdStep D' (tout (tpos d b q)))
    {c : ℝ} (hc : 0 ≤ c) (hT : (T : ℝ) ≤ c * (d * d * b + 1)) :
    ((selfDemandCoordinates N).card : ℝ) ≤
      (2 * c * (∑ h ∈ range (D' + 1), (k + 1) ^ h : ℕ) * (k + 2 : ℕ) * ((k + 2 : ℕ) + 1) + 3) *
        ((d : ℝ) ^ 2 * b) / Real.logb 2 d := by
  obtain ⟨hinj, hrange, hrow⟩ := tpos_props (d := d) hb
  have hreal := realizes_ball hz rdStep hrd tout (fun q : Fin (d * d * b) => tpos d b q) (fun q q' h => hinj (by
    simp only [Nat.cast_inj]; exact h)) htout N hN
  have h := self_demands_le hreal hd hb rfl hinj hrange (fun q => (hrow q))
    (z none 0 - ((1 : ℤ) - 1)) (fun h hh => nbhd_window le_rfl (by have : 1 * 1 ≤ d * b := Nat.mul_le_mul (by omega) hb; omega) z h hh) hc hT
  rw [card_heads] at h
  simpa using h

end MergeDepth
