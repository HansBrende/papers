import MergeDepth.BallsQ91

/-!
# Lemma 4.12: a uniform half-rate bound on class relations, given binary [Q9.1]

Skeleton data at scale `w` (as in `MergeDepth.SkeletonPaired`): reference walks `z` (input head
`z none`, output count `z (some none)`, work heads `z (some (some j))`), a length `T ≤ c (L + 1)`,
`L = d² b`, a genie `Γ` of full depth at most `D` in the block DAG of the coarse work walks, and
output times `ot` in the output blocks. The cone relation `coneRel` of these data contains the
relation `N_Γ(q) = J_Γ(t̂_{tpos q})` of a skeleton class (Lemma 4.7; `coneJ_subset_coneRel_of_lt` and
`classRel_subset_coneRel` in `MergeDepth/SkeletonSE.lean`).

* `subrel_realizes`, `subrel_self_demands`, `subrel_paired_packing`, `subrel_card_le`: Lemma 4.9,
  Proposition 4.11(b), (a) and Lemma 4.7(a) for every relation `N ⊆ N_Γ` (realizations pass to
  subrelations).
* `skelRetained N ϑ = [0, L) ∖ (H_ϑ ∪ S)`: the coordinates that are neither heavy (left degree more
  than `ϑ`) nor self-demands; `degree_induced_le`: the induced relation on any subset of the
  complement of `H_ϑ` has incidence degree at most `max(B', ϑ)` when `|N(q)| ≤ B'`.
* `skel_uniform_binary`: **Lemma 4.12.** Given binary [Q9.1], for `k`, `w ≥ 1`, `D`, `c ≥ 0`,
  `0 < δ < 1`, any `ϑ ≥ w B/δ` (Lemma 4.12 takes `ϑ = ⌈w B/δ⌉`, `B = ∑_{h ≤ D} (k + 1)^h`) and `ζ > 0`,
  there is `d₀` such that for `d ≥ d₀`, every width `b ≥ 1`, all skeleton data as above and every
  relation `N ⊆ N_Γ`, every binary storage code `𝒞` for the induced relation of `N` on
  `Q = skelRetained N ϑ` has `log₂ |𝒞| ≤ (1/2 + ζ) |Q|`. No machine appears: the threshold depends
  only on `k`, `w`, `D`, `c`, `δ`, `ϑ` and `ζ`, uniformly over all machines with `k` work tapes.
-/

namespace MergeDepth

open Finset Filter BoundedNesting DirectedRecovery MotionDepthCodes

set_option autoImplicit false

variable {k : ℕ}

/-! ### Subrelations of the cone relation -/

section Subrel

variable {w d b : ℕ} {z : Tp k → ℕ → ℤ} {T D : ℕ} {Γ : Finset ℕ} {ot : ℕ → ℕ}
  {N : Fin (d * d * b) → Finset (Fin (d * d * b))}

theorem tpos_natCast_injective (hb : 1 ≤ b) :
    Function.Injective (fun q : Fin (d * d * b) => tpos d b q) := fun q q' h =>
  (tpos_props (d := d) hb).1 (by simp only [Nat.cast_inj]; exact h)

open Classical in
/-- **Lemma 4.9 for subrelations.** -/
theorem subrel_realizes (hw : 1 ≤ w) (hb : 1 ≤ b) (hz : ∀ c, IsWalk (z c))
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (hot : ∀ q : Fin (d * d * b),
      ot (tpos d b q) < T ∧ (tpos d b q : ℤ) / w = z (some none) (ot (tpos d b q)) / w)
    (hN : ∀ q, N q ⊆ coneRel w z T Γ ot (fun q : Fin (d * d * b) => tpos d b q) q) :
    Realizes (Prod.fst : Tp k × Fin (2 * w - 1) → Tp k) none (some none) 1 T
      (w * ∑ h ∈ range (D + 1), (k + 1) ^ h) (nbhd w z) N
      (fun p => (p : ℤ)) (fun q => (tpos d b q : ℤ)) :=
  (realizes_cone hw hz hdepth ot (fun q : Fin (d * d * b) => tpos d b q)
    (tpos_natCast_injective hb) hot).mono hN

open Classical in
/-- **Proposition 4.11(b) for subrelations**: at most `A₁ L/log₂ d` self-demands,
`A₁ = 2 c w B K_w (K_w + 1) + 3`. -/
theorem subrel_self_demands (hw : 1 ≤ w) (hd : 2 ≤ d) (hb : 1 ≤ b) (hdbw : 2 * w - 1 ≤ d * b)
    (hz : ∀ c, IsWalk (z c))
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (hot : ∀ q : Fin (d * d * b),
      ot (tpos d b q) < T ∧ (tpos d b q : ℤ) / w = z (some none) (ot (tpos d b q)) / w)
    (hN : ∀ q, N q ⊆ coneRel w z T Γ ot (fun q : Fin (d * d * b) => tpos d b q) q)
    {c : ℝ} (hc : 0 ≤ c) (hT : (T : ℝ) ≤ c * (d * d * b + 1)) :
    ((selfDemandCoordinates N).card : ℝ) ≤
      (2 * c * (w * ∑ h ∈ range (D + 1), (k + 1) ^ h : ℕ) * ((k + 2) * (2 * w - 1) : ℕ) *
        (((k + 2) * (2 * w - 1) : ℕ) + 1) + 3) * ((d * d * b : ℕ) / Real.logb 2 d) := by
  obtain ⟨hinj, hrange, hrow⟩ := tpos_props (d := d) hb
  have h := self_demands_le (subrel_realizes hw hb hz hdepth hot hN) hd hb rfl hinj hrange
    (fun q => hrow q) (z none 0 - ((w : ℤ) - 1)) (fun h hh => nbhd_window hw hdbw z h hh) hc hT
  rw [card_heads] at h
  have e : ((d : ℝ) ^ 2 * b) = ((d * d * b : ℕ) : ℝ) := by push_cast; ring
  rw [e] at h
  rw [mul_div_assoc] at h
  exact_mod_cast h

open Classical in
/-- **Proposition 4.11(a) for subrelations.** -/
theorem subrel_paired_packing (hw : 1 ≤ w) (hd : 2 ≤ d) (hb : 1 ≤ b) (hdbw : 2 * w - 1 ≤ d * b)
    (hz : ∀ c, IsWalk (z c))
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (hot : ∀ q : Fin (d * d * b),
      ot (tpos d b q) < T ∧ (tpos d b q : ℤ) / w = z (some none) (ot (tpos d b q)) / w)
    (hN : ∀ q, N q ⊆ coneRel w z T Γ ot (fun q : Fin (d * d * b) => tpos d b q) q)
    {c : ℝ} (hc : 0 ≤ c) (hT : (T : ℝ) ≤ c * (d * d * b + 1)) (Q : Finset (Fin (d * d * b)))
    (r Δ : ℕ) (hdeg : ∀ v, (pairedIncidenceGraph (inducedNeighborhood N Q)).degree v ≤ Δ) :
    ((shortPairedCoordinates (inducedNeighborhood N Q) r).card : ℝ) ≤
      pathPackingConstant r Δ (fun s => 2 * s * c * (w * ∑ h ∈ range (D + 1), (k + 1) ^ h : ℕ) *
        ((k + 2) * (2 * w - 1) : ℕ) * (((k + 2) * (2 * w - 1) : ℕ) + 1) + 3) *
        ((d * d * b : ℕ) / Real.logb 2 d) := by
  obtain ⟨hinj, hrange, hrow⟩ := tpos_props (d := d) hb
  have h := paired_distance_packing (subrel_realizes hw hb hz hdepth hot hN) hd hb rfl hinj hrange
    (fun q => hrow q) (z none 0 - ((w : ℤ) - 1)) (fun h hh => nbhd_window hw hdbw z h hh) hc hT Q
    r Δ hdeg
  rw [card_heads] at h
  have e : ((d : ℝ) ^ 2 * b) = ((d * d * b : ℕ) : ℝ) := by push_cast; ring
  rw [e] at h
  exact_mod_cast h

open Classical in
/-- **Lemma 4.7(a) for subrelations**: `|N(q)| ≤ w B`. -/
theorem subrel_card_le (hw : 1 ≤ w)
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (hN : ∀ q, N q ⊆ coneRel w z T Γ ot (fun q : Fin (d * d * b) => tpos d b q) q) (q : Fin (d * d * b)) :
    (N q).card ≤ w * ∑ h ∈ range (D + 1), (k + 1) ^ h :=
  (card_le_card (hN q)).trans (card_coneRel_le hw hdepth ot _ q)

end Subrel

/-! ### Degrees of induced relations -/

open Classical in
/-- On every subset `Q` of the complement of `H_ϑ`, the induced incidence graph has maximum degree
at most `max(B', ϑ)` when `|N(q)| ≤ B'` (Proposition 4.11(c) for subsets). -/
theorem degree_induced_le {V : Type*} [Fintype V] [DecidableEq V] (N : V → Finset V) {B' : ℕ}
    (ϑ : ℕ) (hN : ∀ q, (N q).card ≤ B') {Q : Finset V} (hQ : Q ⊆ (heavyCoords N ϑ)ᶜ) :
    ∀ v, (pairedIncidenceGraph (inducedNeighborhood N Q)).degree v ≤ max B' ϑ := by
  intro v
  cases v with
  | inl p =>
    rw [degree_inl]
    refine le_trans ?_ (le_max_right _ _)
    have hp : p.1 ∉ heavyCoords N ϑ := mem_compl.mp (hQ p.2)
    have hle : ¬ ϑ < (pairedIncidenceGraph N).degree (.inl p.1) := fun h =>
      hp (mem_filter.mpr ⟨mem_univ _, h⟩)
    rw [degree_inl] at hle
    refine le_trans ?_ (not_lt.mp hle)
    refine card_le_card_of_injOn Subtype.val (fun q hq => ?_) Subtype.val_injective.injOn
    have hq := (mem_filter.mp hq).2
    simp only [inducedNeighborhood, mem_subtype] at hq
    exact mem_filter.mpr ⟨mem_univ _, hq⟩
  | inr q =>
    rw [degree_inr]
    refine le_trans ?_ (le_max_left _ _)
    simp only [inducedNeighborhood]
    rw [card_subtype]
    exact (card_filter_le _ _).trans (hN q.1)

/-! ### Lemma 4.12 -/

open Classical in
/-- The retained coordinates of Lemma 4.12: neither heavy (left degree more than `ϑ`) nor
self-demands. -/
noncomputable def skelRetained {L : ℕ} (N : Fin L → Finset (Fin L)) (ϑ : ℕ) : Finset (Fin L) :=
  (heavyCoords N ϑ ∪ selfDemandCoordinates N)ᶜ

/-- **The instances of Lemma 4.12.** At `(d, b)`: `b ≥ 1`, skeleton data at scale `w` with
`T ≤ c (L + 1)` and a genie of full depth at most `D`, a relation `N` inside their cone relation,
and `Q = skelRetained N ϑ`. -/
def SkelInst (k w D : ℕ) (c : ℝ) (ϑ : ℕ) : InstFamily := fun d b Q N =>
  1 ≤ b ∧
    (∃ (z : Tp k → ℕ → ℤ) (T : ℕ) (Γ : Finset ℕ) (ot : ℕ → ℕ),
      (∀ c', IsWalk (z c')) ∧
      (∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
        π.length ≤ D + 1) ∧
      (∀ q : Fin (d * d * b),
        ot (tpos d b q) < T ∧ (tpos d b q : ℤ) / w = z (some none) (ot (tpos d b q)) / w) ∧
      (T : ℝ) ≤ c * (d * d * b + 1) ∧
      ∀ q, N q ⊆ coneRel w z T Γ ot (fun q : Fin (d * d * b) => tpos d b q) q) ∧
    Q = skelRetained N ϑ

open Classical in
/-- **The retained set is large.** `|[0, L) ∖ Q| ≤ δ L + A₁ L/log₂ d` for the instances, when
`ϑ ≥ w B/δ`, `d ≥ 2` and `db ≥ 2w - 1`. -/
theorem skelInst_compl (k : ℕ) {w D ϑ : ℕ} (hw : 1 ≤ w) {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hϑ : ((w * ∑ h ∈ range (D + 1), (k + 1) ^ h : ℕ) : ℝ) / δ ≤ ϑ) {d b : ℕ} (hd : 2 ≤ d)
    (hdbw : 2 * w - 1 ≤ d * b) (Q : Finset (Fin (d * d * b)))
    (N : Fin (d * d * b) → Finset (Fin (d * d * b))) (h : SkelInst k w D c ϑ d b Q N) :
    (Qᶜ.card : ℝ) ≤ δ * (d * d * b : ℕ) +
      (2 * c * (w * ∑ h ∈ range (D + 1), (k + 1) ^ h : ℕ) * ((k + 2) * (2 * w - 1) : ℕ) *
        (((k + 2) * (2 * w - 1) : ℕ) + 1) + 3) * ((d * d * b : ℕ) / Real.logb 2 d) := by
  obtain ⟨hb, ⟨z, T, Γ, ot, hz, hdepth, hot, hT, hN⟩, rfl⟩ := h
  have hB : 0 < w * ∑ h ∈ range (D + 1), (k + 1) ^ h :=
    Nat.mul_pos (by omega) (one_le_ballSize k D)
  have htrim := (paid_trimming N ϑ (subrel_card_le hw hdepth hN)).1
  rw [Fintype.card_fin] at htrim
  have hH := card_heavy_le (H := (heavyCoords N ϑ).card) (L := d * d * b) hδ hB hϑ htrim
  have hS := subrel_self_demands hw hd hb hdbw hz hdepth hot hN hc hT
  have hU : ((skelRetained N ϑ)ᶜ.card : ℝ) ≤
      (heavyCoords N ϑ).card + (selfDemandCoordinates N).card := by
    rw [skelRetained, compl_compl]
    exact_mod_cast card_union_le _ _
  linarith

open Classical in
/-- **Lemma 4.12 (a uniform half-rate bound on class relations), given binary [Q9.1].** Let `k`,
`w ≥ 1` and `D` be integers, `c ≥ 0`, `0 < δ < 1`, `B = ∑_{h ≤ D} (k + 1)^h`, `ϑ ≥ w B/δ` and
`ζ > 0`. There is `d₀` such that for `d ≥ d₀`, every width `b ≥ 1`, all skeleton data at scale `w`
(walks `z`, `T ≤ c (L + 1)`, a genie `Γ` of full depth at most `D` in the block DAG of the coarse
work walks, output times `ot` in the output blocks) and every relation `N` inside their cone
relation, every binary storage code `𝒞` for the induced relation of `N` on
`Q = [0, L) ∖ (H_ϑ ∪ S)` has `log₂ |𝒞| ≤ (1/2 + ζ) |Q|`. -/
theorem skel_uniform_binary (hQ : Q91Binary) (k : ℕ) {w D ϑ : ℕ} (hw : 1 ≤ w) {c δ : ℝ}
    (hc : 0 ≤ c) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hϑ : ((w * ∑ h ∈ range (D + 1), (k + 1) ^ h : ℕ) : ℝ) / δ ≤ ϑ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, 1 ≤ b → ∀ (z : Tp k → ℕ → ℤ), (∀ c', IsWalk (z c')) →
      ∀ (T : ℕ) (Γ : Finset ℕ),
      (∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
        π.length ≤ D + 1) →
      ∀ ot : ℕ → ℕ, (∀ q : Fin (d * d * b),
        ot (tpos d b q) < T ∧ (tpos d b q : ℤ) / w = z (some none) (ot (tpos d b q)) / w) →
      (T : ℝ) ≤ c * (d * d * b + 1) →
      ∀ N : Fin (d * d * b) → Finset (Fin (d * d * b)),
        (∀ q, N q ⊆ coneRel w z T Γ ot (fun q : Fin (d * d * b) => tpos d b q) q) →
      ∀ C : Finset (skelRetained N ϑ → Bool),
        IsStorageCode (inducedNeighborhood N (skelRetained N ϑ)) C →
        Real.logb 2 C.card ≤ (1 / 2 + ζ) * (skelRetained N ϑ).card := by
  set B := ∑ h ∈ range (D + 1), (k + 1) ^ h
  set A₁ : ℝ := 2 * c * (w * B : ℕ) * ((k + 2) * (2 * w - 1) : ℕ) *
    (((k + 2) * (2 * w - 1) : ℕ) + 1) + 3
  have hA₁ : 0 ≤ A₁ := by positivity
  -- `A₁ / log₂ d ≤ (1 - δ)/2` for large `d`
  have hlogt : Tendsto (fun d : ℕ => A₁ / Real.logb 2 d) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      tendsto_natCast_atTop_atTop)
  obtain ⟨d₂, hd₂⟩ := eventually_atTop.mp
    ((tendsto_order.mp hlogt).2 ((1 - δ) / 2) (by linarith))
  have hcard : ∃ d₁ : ℕ, ∀ d ≥ d₁, ∀ b Q N, SkelInst k w D c ϑ d b Q N →
      (1 - δ) / 2 * (d * d * b : ℕ) ≤ Q.card := by
    refine ⟨max d₂ (2 * w), fun d hd b Q N h => ?_⟩
    have hd2 : 2 ≤ d := by have := le_of_max_le_right hd; omega
    have hdbw : 2 * w - 1 ≤ d * b := by
      have := Nat.mul_le_mul (le_of_max_le_right hd) h.1
      omega
    have h1 := skelInst_compl k hw hc hδ hϑ hd2 hdbw Q N h
    have h2 : (Q.card : ℝ) + Qᶜ.card = (d * d * b : ℕ) := by
      rw [← Nat.cast_add, Finset.card_add_card_compl, Fintype.card_fin]
    have h3 := (hd₂ d (le_of_max_le_left hd)).le
    have hlog : 0 < Real.logb 2 d := Real.logb_pos (by norm_num) (by exact_mod_cast hd2)
    have h4 : A₁ * ((d * d * b : ℕ) / Real.logb 2 d) ≤ (1 - δ) / 2 * (d * d * b : ℕ) := by
      rw [← mul_div_assoc, div_le_iff₀ hlog]
      rw [div_le_iff₀ hlog] at h3
      have : (0 : ℝ) ≤ (d * d * b : ℕ) := Nat.cast_nonneg _
      nlinarith
    linarith
  have hdeg : ∀ d b Q N, SkelInst k w D c ϑ d b Q N →
      ∀ v, (pairedIncidenceGraph (inducedNeighborhood N Q)).degree v ≤ max (w * B) ϑ := by
    rintro d b Q N ⟨-, ⟨z, T, Γ, ot, -, hdepth, -, -, hN⟩, rfl⟩
    exact degree_induced_le N ϑ (subrel_card_le hw hdepth hN)
      (compl_subset_compl.mpr subset_union_left)
  have hshort : ∀ r : ℕ, 0 < r → ∃ (A : ℝ) (d₁ : ℕ), ∀ d ≥ d₁, ∀ b Q N,
      SkelInst k w D c ϑ d b Q N →
      ((shortPairedCoordinates (inducedNeighborhood N Q) r).card : ℝ) ≤
        A * ((d * d * b : ℕ) / Real.logb 2 d) := by
    intro r _
    refine ⟨pathPackingConstant r (max (w * B) ϑ) (fun s => 2 * s * c * (w * B : ℕ) *
      ((k + 2) * (2 * w - 1) : ℕ) * (((k + 2) * (2 * w - 1) : ℕ) + 1) + 3), 2 * w,
      fun d hd b Q N h => ?_⟩
    have hdg := hdeg d b Q N h
    obtain ⟨hb, ⟨z, T, Γ, ot, hz, hdepth, hot, hT, hN⟩, -⟩ := h
    have hd2 : 2 ≤ d := by omega
    have hdbw : 2 * w - 1 ≤ d * b := by
      have := Nat.mul_le_mul hd hb
      omega
    exact subrel_paired_packing hw hd2 hb hdbw hz hdepth hot hN hc hT Q r _ hdg
  obtain ⟨d₀, hd₀⟩ := uniform_rate_binary hQ (SkelInst k w D c ϑ) (max (w * B) ϑ)
    (κ := (1 - δ) / 2) (by linarith) (fun _ _ _ _ h => h.1) hdeg hcard hshort hζ
  exact ⟨d₀, fun d hd b hb z hz T Γ hdepth ot hot hT N hN C hC =>
    hd₀ d hd b _ N ⟨hb, ⟨z, T, Γ, ot, hz, hdepth, hot, hT, hN⟩, rfl⟩ C hC⟩

end MergeDepth
