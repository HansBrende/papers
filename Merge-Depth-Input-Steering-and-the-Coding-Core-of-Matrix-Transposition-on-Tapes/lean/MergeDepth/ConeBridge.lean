import MergeDepth.SkeletonCones
import MergeDepth.Trimming

/-!
# The cone relation of the block machine is realized (Lemmas 4.7 and 4.9)

`MergeDepth.SkeletonCones` (Lemma 4.7) states the storage-code property for the relation
`q ↦ J_Γ(that (tpos q))` of a `BlockFunDag`. If the out-edges of the block machine are the steps of the
block DAG of the coarse work walks (Lemma 4.5(a)) and the input block read at `u` lies in the block of
the input reference walk, this relation is a subrelation of `coneRel` (`coneJ_subset_coneRel`), so
Lemma 4.9 applies to it (`BlockFunDag.realizes_coneJ`), and with it Lemma 4.10 and
Proposition 4.11(a), (b) (`BlockFunDag.coneJ_paired_packing`, `BlockFunDag.coneJ_self_demands`).
-/

namespace MergeDepth

open Finset BoundedNesting DirectedRecovery

variable {k : ℕ}

/-- Realizability passes to subrelations. -/
theorem Realizes.mono {τ η V : Type*} [DecidableEq τ] {tape : η → τ} {inp out : τ}
    {ρ T κ : ℕ} {H : ℕ → η → ℤ} {N N' : V → Finset V} {ip op : V → ℤ}
    (hR : Realizes tape inp out ρ T κ H N ip op) (h : ∀ q, N' q ⊆ N q) :
    Realizes tape inp out ρ T κ H N' ip op :=
  fun m src dst hsrc hdst hinc => hR m src dst hsrc hdst fun j => h _ (hinc j)

open Classical in
/-- The cone of the block machine lies in the cone relation of the coarse walks. -/
theorem coneJ_subset_coneRel {L : ℕ} {α : Type*} (G : BlockFunDag L α) {w : ℕ}
    {z : Tp k → ℕ → ℤ} {T : ℕ} {Γ : Finset ℕ}
    (hout : ∀ t, G.out t = (range T).filter (BlockStep (fun j => skel w (z (some (some j)))) T t ·))
    (hblk : ∀ u, ∀ p ∈ G.blk u, (p : ℤ) / w = z none u / w) (ot : ℕ → ℕ) (dm : Fin L → ℕ)
    (q : Fin L) : G.coneJ Γ (ot (dm q)) ⊆ coneRel w z T Γ ot dm q := by
  classical
  intro p hp
  obtain ⟨u, hu, hpu⟩ := mem_biUnion.mp hp
  obtain ⟨π, hπ, hfree, hlast⟩ := (mem_coneV G.net).mp hu
  have hdep : ∀ t, ∀ u ∈ G.net.out t, DepStep (fun j => skel w (z (some (some j)))) T t u := by
    intro t u hu
    have : u ∈ G.out t := hu
    rw [hout t] at this
    exact (blockStep_iff _ T t u).mp (mem_filter.mp this).2
  have hπdep := isDepPath_of_paths hdep π _ hπ
  obtain ⟨π', rfl⟩ := G.net.mem_paths_head hπ
  refine mem_filter.mpr ⟨mem_univ _, π', hπdep, hfree, ?_⟩
  rw [hlast]
  exact hblk u p hpu

open Classical in
/-- **Lemma 4.9 for the block machine.** The relation `q ↦ J_Γ(that (tpos q))` of Lemma 4.7 has the
realization property, if the out-edges of the block machine are the block DAG of the coarse work
walks, its input blocks lie in the blocks of the input reference walk, `Γ` has full depth at most `D`,
and every output position `r` has its time `that r < T` in the block of the output reference walk. -/
theorem BlockFunDag.realizes_coneJ {L : ℕ} {α : Type*} (G : BlockFunDag L α) {w : ℕ} (hw : 1 ≤ w)
    {z : Tp k → ℕ → ℤ} (hz : ∀ c, IsWalk (z c)) {T D : ℕ} {Γ : Finset ℕ}
    (hout : ∀ t, G.out t = (range T).filter (BlockStep (fun j => skel w (z (some (some j)))) T t ·))
    (hblk : ∀ u, ∀ p ∈ G.blk u, (p : ℤ) / w = z none u / w)
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (that : Fin L → ℕ) (tpos : Fin L → Fin L) (htpos : Function.Injective tpos)
    (hthat : ∀ r, that r < T ∧ (r : ℤ) / w = z (some none) (that r) / w) :
    Realizes (Prod.fst : Tp k × Fin (2 * w - 1) → Tp k) none (some none) 1 T
      (w * ∑ h ∈ range (D + 1), (k + 1) ^ h) (nbhd w z) (fun q => G.coneJ Γ (that (tpos q)))
      (fun p => (p : ℤ)) (fun q => (tpos q : ℤ)) := by
  let ot : ℕ → ℕ := fun n => if h : n < L then that ⟨n, h⟩ else 0
  have hot : ∀ r : Fin L, ot r = that r := fun r => by simp [ot, r.2]
  have hreal := realizes_cone hw hz hdepth ot (fun q => (tpos q : ℕ))
    (fun q q' h => htpos (Fin.ext h)) (fun q => by rw [hot]; exact hthat (tpos q))
  refine hreal.mono fun q => ?_
  have := coneJ_subset_coneRel G (Γ := Γ) hout hblk ot (fun q => (tpos q : ℕ)) q
  rwa [hot] at this

/-- The transposition permutation of `Fin (d² b)`. -/
def tposFin {d b : ℕ} (hb : 1 ≤ b) (q : Fin (d * d * b)) : Fin (d * d * b) :=
  ⟨tpos d b q, tpos_lt (by omega) q.2⟩

theorem tposFin_injective {d b : ℕ} (hb : 1 ≤ b) : Function.Injective (tposFin (d := d) hb) := by
  intro q q' h
  have h' : tpos d b q = tpos d b q' := congrArg Fin.val h
  exact (tpos_props (d := d) hb).1 (by simp only; exact_mod_cast h')

open Classical in
/-- **Proposition 4.11(a) for the relation of Lemma 4.7.** -/
theorem BlockFunDag.coneJ_paired_packing {d b : ℕ} {α : Type*} (G : BlockFunDag (d * d * b) α)
    {w : ℕ} (hw : 1 ≤ w) (hd : 2 ≤ d) (hb : 1 ≤ b) (hdbw : 2 * w - 1 ≤ d * b)
    {z : Tp k → ℕ → ℤ} (hz : ∀ c, IsWalk (z c)) {T D : ℕ} {Γ : Finset ℕ}
    (hout : ∀ t, G.out t = (range T).filter (BlockStep (fun j => skel w (z (some (some j)))) T t ·))
    (hblk : ∀ u, ∀ p ∈ G.blk u, (p : ℤ) / w = z none u / w)
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (that : Fin (d * d * b) → ℕ)
    (hthat : ∀ r, that r < T ∧ (r : ℤ) / w = z (some none) (that r) / w)
    {c : ℝ} (hc : 0 ≤ c) (hT : (T : ℝ) ≤ c * (d * d * b + 1)) (Q : Finset (Fin (d * d * b)))
    (r Δ : ℕ) (hdeg : ∀ v, (pairedIncidenceGraph (inducedNeighborhood
      (fun q => G.coneJ Γ (that (tposFin hb q))) Q)).degree v ≤ Δ) :
    ((shortPairedCoordinates (inducedNeighborhood
        (fun q => G.coneJ Γ (that (tposFin hb q))) Q) r).card : ℝ) ≤
      pathPackingConstant r Δ (fun s => 2 * s * c * (w * ∑ h ∈ range (D + 1), (k + 1) ^ h : ℕ) *
        ((k + 2) * (2 * w - 1) : ℕ) * (((k + 2) * (2 * w - 1) : ℕ) + 1) + 3) *
        (((d : ℝ) ^ 2 * b) / Real.logb 2 d) := by
  obtain ⟨hinj, hrange, hrow⟩ := tpos_props (d := d) hb
  have hreal := G.realizes_coneJ hw hz hout hblk hdepth that (tposFin hb) (tposFin_injective hb)
    hthat
  have h := paired_distance_packing hreal hd hb rfl hinj hrange (fun q => hrow q)
    (z none 0 - ((w : ℤ) - 1)) (fun h hh => nbhd_window hw hdbw z h hh) hc hT Q r Δ hdeg
  rw [card_heads] at h
  exact_mod_cast h

open Classical in
/-- **Proposition 4.11(b) for the relation of Lemma 4.7.** -/
theorem BlockFunDag.coneJ_self_demands {d b : ℕ} {α : Type*} (G : BlockFunDag (d * d * b) α)
    {w : ℕ} (hw : 1 ≤ w) (hd : 2 ≤ d) (hb : 1 ≤ b) (hdbw : 2 * w - 1 ≤ d * b)
    {z : Tp k → ℕ → ℤ} (hz : ∀ c, IsWalk (z c)) {T D : ℕ} {Γ : Finset ℕ}
    (hout : ∀ t, G.out t = (range T).filter (BlockStep (fun j => skel w (z (some (some j)))) T t ·))
    (hblk : ∀ u, ∀ p ∈ G.blk u, (p : ℤ) / w = z none u / w)
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (that : Fin (d * d * b) → ℕ)
    (hthat : ∀ r, that r < T ∧ (r : ℤ) / w = z (some none) (that r) / w)
    {c : ℝ} (hc : 0 ≤ c) (hT : (T : ℝ) ≤ c * (d * d * b + 1)) :
    ((selfDemandCoordinates (fun q => G.coneJ Γ (that (tposFin hb q)))).card : ℝ) ≤
      (2 * c * (w * ∑ h ∈ range (D + 1), (k + 1) ^ h : ℕ) * ((k + 2) * (2 * w - 1) : ℕ) *
        (((k + 2) * (2 * w - 1) : ℕ) + 1) + 3) * ((d : ℝ) ^ 2 * b) / Real.logb 2 d := by
  obtain ⟨hinj, hrange, hrow⟩ := tpos_props (d := d) hb
  have hreal := G.realizes_coneJ hw hz hout hblk hdepth that (tposFin hb) (tposFin_injective hb)
    hthat
  have h := self_demands_le hreal hd hb rfl hinj hrange (fun q => hrow q)
    (z none 0 - ((w : ℤ) - 1)) (fun h hh => nbhd_window hw hdbw z h hh) hc hT
  rw [card_heads] at h
  exact_mod_cast h

end MergeDepth
