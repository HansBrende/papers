import MergeDepth.BlockDag
import MergeDepth.HopMachine
import MotionDepthCodes.StorageCode

/-!
# Cones on a skeleton class (Lemma 4.7)

The block machine of a skeleton class (Lemma 4.5) is a DAG on the times with out-edges to earlier
times, an input block read at every time, and block values determined, on the inputs of the class,
by the block read and the values at the out-neighbours (Lemma 4.5(b)). `BlockFunDag` records this
structure; `S` is the class.

* `card_coneV_le`: if every vertex has at most `k + 1` out-neighbours and every `Γ`-free path from
  `t` has at most `D` edges, at most `∑_{h ≤ D} (k + 1)^h` vertices end such paths (`coneV`, the set
  `C_Γ(t)`); with blocks of at most `w` cells, `J_Γ(t)` has at most `w` times as many cells
  (`card_coneJ_le`). `card_coneV_le_of_blockStep` takes the degree bound from Lemma 4.5(a) and the
  depth bound from a genie for the dependency DAG of the coarse walks, such as that of Lemma 4.6.
* `BlockFunDag.cone`: inputs of the class that agree on the revealed values and on `J_Γ(t)` give
  `t` the same value.
* `BlockFunDag.isStorageCode_fibre`: if the bit at output position `r` is a function of the value
  at a time `that r` (Lemma 4.5(c)) and equals the input bit at `tpos r` on the class, every fibre
  of the revealed word is a storage code for `N_Γ(q) = J_Γ(that (tpos q))`.
-/

namespace MergeDepth

open Finset BoundedNesting

section Reach

variable {F : Type*} [Field F] {L m : ℕ} (net : LinNet F L m)

/-- The vertices reached from `t` by paths with exactly `h` edges. -/
def reachN : ℕ → ℕ → Finset ℕ
  | t, 0 => {t}
  | t, h + 1 => (net.out t).biUnion fun s => reachN s h

theorem card_reachN_le {d : ℕ} (hdeg : ∀ u, (net.out u).card ≤ d) :
    ∀ h t, (reachN net t h).card ≤ d ^ h
  | 0, t => by simp [reachN]
  | h + 1, t => by
    simp only [reachN]
    calc ((net.out t).biUnion fun s => reachN net s h).card
        ≤ ∑ s ∈ net.out t, (reachN net s h).card := card_biUnion_le
      _ ≤ ∑ _s ∈ net.out t, d ^ h := sum_le_sum fun s _ => card_reachN_le hdeg h s
      _ = (net.out t).card * d ^ h := by rw [sum_const, smul_eq_mul]
      _ ≤ d * d ^ h := Nat.mul_le_mul_right _ (hdeg t)
      _ = d ^ (h + 1) := by rw [pow_succ, mul_comm]

theorem getLastD_mem_reachN :
    ∀ (π : List ℕ) (t : ℕ), (t :: π) ∈ net.paths t → (t :: π).getLastD t ∈ reachN net t π.length
  | [], t, _ => by simp [reachN]
  | s :: ρ, t, h => by
    obtain ⟨hs, hρ⟩ := cons_cons_mem_paths.mp h
    rw [LinNet.getLastD_cons_cons]
    simp only [List.length_cons, reachN]
    exact mem_biUnion.mpr ⟨s, hs, getLastD_mem_reachN ρ s hρ⟩

theorem getLastD_le_of_paths : ∀ t π, π ∈ net.paths t → π.getLastD t ≤ t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro π hπ
    obtain ⟨π', rfl⟩ := net.mem_paths_head hπ
    cases π' with
    | nil => simp
    | cons s ρ =>
      obtain ⟨hs, hρ⟩ := cons_cons_mem_paths.mp hπ
      rw [LinNet.getLastD_cons_cons]
      exact (ih s (net.out_lt t s hs) _ hρ).trans (net.out_lt t s hs).le

open Classical in
/-- `C_Γ(t)`: the ends of the `Γ`-free paths from `t`. -/
noncomputable def coneV (Γ : Finset ℕ) (t : ℕ) : Finset ℕ :=
  (range (t + 1)).filter fun u => ∃ π ∈ net.paths t, LinNet.GFree Γ π ∧ π.getLastD t = u

theorem mem_coneV {Γ : Finset ℕ} {t u : ℕ} :
    u ∈ coneV net Γ t ↔ ∃ π ∈ net.paths t, LinNet.GFree Γ π ∧ π.getLastD t = u := by
  classical
  simp only [coneV, mem_filter, mem_range, and_iff_right_iff_imp]
  rintro ⟨π, hπ, -, rfl⟩
  exact Nat.lt_succ_of_le (getLastD_le_of_paths net t π hπ)

theorem self_mem_coneV (Γ : Finset ℕ) (t : ℕ) : t ∈ coneV net Γ t :=
  (mem_coneV net).mpr ⟨[t], singleton_mem_paths net t, gfree_singleton Γ t, rfl⟩

theorem coneV_mono {Γ : Finset ℕ} {t s : ℕ} (hs : s ∈ net.out t) (hsΓ : s ∉ Γ) :
    coneV net Γ s ⊆ coneV net Γ t := by
  intro u hu
  obtain ⟨π, hπ, hfree, rfl⟩ := (mem_coneV net).mp hu
  obtain ⟨ρ, rfl⟩ := net.mem_paths_head hπ
  exact (mem_coneV net).mpr ⟨t :: s :: ρ, cons_cons_mem_paths.mpr ⟨hs, hπ⟩,
    gfree_cons_cons.mpr ⟨hsΓ, hfree⟩, LinNet.getLastD_cons_cons t s ρ⟩

/-- **Lemma 4.7(a), cone vertices.** -/
theorem card_coneV_le {k D : ℕ} (hdeg : ∀ u, (net.out u).card ≤ k + 1) {Γ : Finset ℕ} {t : ℕ}
    (hD : ∀ π ∈ net.paths t, LinNet.GFree Γ π → π.length ≤ D + 1) :
    (coneV net Γ t).card ≤ ∑ h ∈ range (D + 1), (k + 1) ^ h := by
  have hsub : coneV net Γ t ⊆ (range (D + 1)).biUnion (reachN net t) := by
    intro u hu
    obtain ⟨π, hπ, hfree, rfl⟩ := (mem_coneV net).mp hu
    obtain ⟨ρ, rfl⟩ := net.mem_paths_head hπ
    have hlen := hD _ hπ hfree
    simp only [List.length_cons] at hlen
    exact mem_biUnion.mpr ⟨ρ.length, mem_range.mpr (by omega), getLastD_mem_reachN net ρ t hπ⟩
  calc (coneV net Γ t).card ≤ ((range (D + 1)).biUnion (reachN net t)).card := card_le_card hsub
    _ ≤ ∑ h ∈ range (D + 1), (reachN net t h).card := card_biUnion_le
    _ ≤ ∑ h ∈ range (D + 1), (k + 1) ^ h := sum_le_sum fun h _ => card_reachN_le net hdeg h t

end Reach

/-- The block machine of a skeleton class, abstractly: a DAG on the times with out-edges to
earlier times, the input block `blk t` read at `t`, and values that are determined, on the class
`S`, by the block read and the values at the out-neighbours. -/
structure BlockFunDag (L : ℕ) (α : Type*) where
  out : ℕ → Finset ℕ
  out_lt : ∀ t, ∀ s ∈ out t, s < t
  blk : ℕ → Finset (Fin L)
  S : Set (Fin L → Bool)
  val : (Fin L → Bool) → ℕ → α
  det : ∀ X ∈ S, ∀ Y ∈ S, ∀ t, (∀ s ∈ out t, val X s = val Y s) → (∀ j ∈ blk t, X j = Y j) →
    val X t = val Y t

namespace BlockFunDag

variable {L : ℕ} {α : Type*} (G : BlockFunDag L α)

/-- The underlying network, with zero coefficients (only its edges are used). -/
def net : LinNet ℚ L 1 where
  out := G.out
  out_lt := G.out_lt
  c := fun _ => 0
  A := fun _ _ => 0
  a := fun _ => 0
  rd := fun _ => none

/-- `J_Γ(t)`: the input blocks read at the ends of the `Γ`-free paths from `t`. -/
noncomputable def coneJ (Γ : Finset ℕ) (t : ℕ) : Finset (Fin L) :=
  (coneV G.net Γ t).biUnion G.blk

/-- **Lemma 4.7(a), cone cells.** -/
theorem card_coneJ_le {k D w : ℕ} (hdeg : ∀ u, (G.out u).card ≤ k + 1)
    (hblk : ∀ u, (G.blk u).card ≤ w) {Γ : Finset ℕ} {t : ℕ}
    (hD : ∀ π ∈ G.net.paths t, LinNet.GFree Γ π → π.length ≤ D + 1) :
    (G.coneJ Γ t).card ≤ w * ∑ h ∈ range (D + 1), (k + 1) ^ h :=
  calc (G.coneJ Γ t).card ≤ ∑ u ∈ coneV G.net Γ t, (G.blk u).card := card_biUnion_le
    _ ≤ ∑ _u ∈ coneV G.net Γ t, w := sum_le_sum fun u _ => hblk u
    _ = (coneV G.net Γ t).card * w := by rw [sum_const, smul_eq_mul]
    _ ≤ (∑ h ∈ range (D + 1), (k + 1) ^ h) * w :=
        Nat.mul_le_mul_right _ (card_coneV_le G.net hdeg hD)
    _ = w * ∑ h ∈ range (D + 1), (k + 1) ^ h := mul_comm _ _

/-- **Lemma 4.7(b).** Inputs of the class with the same revealed values that agree on `J_Γ(t)` give
`t` the same value. -/
theorem cone (Γ : Finset ℕ) {X Y : Fin L → Bool} (hX : X ∈ G.S) (hY : Y ∈ G.S)
    (hΓ : ∀ v ∈ Γ, G.val X v = G.val Y v) :
    ∀ t, (∀ j ∈ G.coneJ Γ t, X j = Y j) → G.val X t = G.val Y t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    refine G.det X hX Y hY t (fun s hs => ?_) fun j hj =>
      ht j (mem_biUnion.mpr ⟨t, self_mem_coneV G.net Γ t, hj⟩)
    by_cases hsΓ : s ∈ Γ
    · exact hΓ s hsΓ
    · refine ih s (G.out_lt t s hs) fun j hj => ht j ?_
      obtain ⟨u, hu, hju⟩ := mem_biUnion.mp hj
      exact mem_biUnion.mpr ⟨u, coneV_mono G.net (t := t) hs hsΓ hu, hju⟩

/-- **Lemma 4.7(b), outputs.** If the bit at output position `r` is a function of the value at
`that r`, inputs of the class with the same revealed values that agree on `I_Γ(r) = J_Γ(that r)`
have the same output bit at `r`. -/
theorem output_eq (Γ : Finset ℕ) (that : Fin L → ℕ) (outw : (Fin L → Bool) → Fin L → Bool)
    (dec : Fin L → α → Bool) (hdec : ∀ X ∈ G.S, ∀ r, outw X r = dec r (G.val X (that r)))
    {X Y : Fin L → Bool} (hX : X ∈ G.S) (hY : Y ∈ G.S) (hΓ : ∀ v ∈ Γ, G.val X v = G.val Y v)
    (r : Fin L) (hr : ∀ j ∈ G.coneJ Γ (that r), X j = Y j) : outw X r = outw Y r := by
  rw [hdec X hX r, hdec Y hY r, G.cone Γ hX hY hΓ (that r) hr]

open Classical in
/-- The fibre of the revealed word: the inputs of the class with revealed values `g`. -/
noncomputable def fibre (Γ : Finset ℕ) (g : ℕ → α) : Finset (Fin L → Bool) :=
  univ.filter fun X => X ∈ G.S ∧ ∀ v ∈ Γ, G.val X v = g v

/-- **Lemma 4.7(c).** If the bit at output position `r` is a function of the value at `that r` and
equals the input bit at `tpos r` on the class, with `tpos` an involution, every fibre of the
revealed word is a storage code for the relation `q ↦ J_Γ(that (tpos q))`. -/
theorem isStorageCode_fibre (Γ : Finset ℕ) (that : Fin L → ℕ) (tpos : Fin L → Fin L)
    (htpos : ∀ q, tpos (tpos q) = q) (outw : (Fin L → Bool) → Fin L → Bool)
    (dec : Fin L → α → Bool) (hdec : ∀ X ∈ G.S, ∀ r, outw X r = dec r (G.val X (that r)))
    (htr : ∀ X ∈ G.S, ∀ r, outw X r = X (tpos r)) (g : ℕ → α) :
    MotionDepthCodes.IsStorageCode (fun q => G.coneJ Γ (that (tpos q))) (G.fibre Γ g) := by
  classical
  intro X hX Y hY q hq
  simp only [fibre, mem_filter, mem_univ, true_and] at hX hY
  have hΓ : ∀ v ∈ Γ, G.val X v = G.val Y v := fun v hv => (hX.2 v hv).trans (hY.2 v hv).symm
  have h := G.output_eq Γ that outw dec hdec hX.1 hY.1 hΓ (tpos q) hq
  rwa [htr X hX.1, htr Y hY.1, htpos] at h

end BlockFunDag

open Classical in
/-- **Lemma 4.7(a) on the block DAG.** If the out-edges of the block machine are the steps of the
block DAG of coarse walks `s` (Lemma 4.5(a)) and `Γ`-free dependency paths of `s` have at most
`D + 1` vertices (as for the genie of Lemma 4.6), then `C_Γ(t)` has at most
`∑_{h ≤ D} (k + 1)^h` elements and `J_Γ(t)` at most `w` times as many cells. -/
theorem card_coneV_le_of_blockStep {L k : ℕ} {α : Type*} (G : BlockFunDag L α)
    (s : Fin k → ℕ → ℤ) (T : ℕ) (hout : ∀ t, G.out t = (range T).filter (BlockStep s T t ·))
    {Γ : Finset ℕ} {D w : ℕ} (hΓ : ∀ π, IsDepPath s T π → LinNet.GFree Γ π → π.length ≤ D + 1)
    (hblk : ∀ u, (G.blk u).card ≤ w) (t : ℕ) :
    (coneV G.net Γ t).card ≤ ∑ h ∈ range (D + 1), (k + 1) ^ h ∧
      (G.coneJ Γ t).card ≤ w * ∑ h ∈ range (D + 1), (k + 1) ^ h := by
  have hdeg : ∀ u, (G.out u).card ≤ k + 1 := fun u => by
    rw [hout u]
    exact card_blockOut_le s T u
  have hdep : ∀ t, ∀ u ∈ G.net.out t, DepStep s T t u := fun t u hu => by
    have : u ∈ G.out t := hu
    rw [hout t] at this
    exact (blockStep_iff s T t u).mp (mem_filter.mp this).2
  have hD : ∀ π ∈ G.net.paths t, LinNet.GFree Γ π → π.length ≤ D + 1 := fun π hπ hfree =>
    hΓ π (isDepPath_of_paths hdep π t hπ) hfree
  exact ⟨card_coneV_le G.net hdeg hD, G.card_coneJ_le hdeg hblk hD⟩

end MergeDepth
