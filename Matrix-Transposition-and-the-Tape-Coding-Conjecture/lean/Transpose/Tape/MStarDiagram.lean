import Transpose.Tape.MStarWalk
import Transpose.Tape.CECut

/-!
# Theorem M* for code-carrying diagrams

Theorem M\* (level form (★) for interval labellings) holds for every family of time–space
diagrams whose block networks carry causal codes, with no Turing machine in sight. At sizes
`n_i → ∞`, let `D_i` be valid `k`-walk diagrams of length `T_i ≤ c L_i`, and let a causal code
solve complete exchange on a set `F_i` of inputs of co-entropy `m_i`
(`2^{L_i} ≤ 2^{m_i} |F_i|`) at the block capacities: the per-node profile (`G ≥ 1` bits per cell,
blocks of `r_i = blockSize G n_i` cells) plus `s_i` extra bits per memory edge. If
`(m_i + s_i) / L_i → 0`, then every uniform limit `P` on `[0, c₀]`, `c₀ = c G + 1`, of the rescaled
work walks (`TSDiagram.rescaled`) satisfies (★); a convergent subsequence exists, and every limit is
1-Lipschitz.

The proof is the machine-free core of `MStarWalk.lean` (`theoremMStar_walk`), fed by Discrete
Isoperimetry for codes (`isoperimetry_code`): the capacity between labels is at most
`M_b (3k r G + s) + r G Σ_t χ_t` (`sum_cross_blockCap_le`), which is the cut inequality `CutIneq`
(`cutIneq_of_solves`).

* `sum_cross_blockCap_le`, `cutIneq_of_solves`;
* `theoremMStar_diagram`: a convergent subsequence exists, and every subsequential limit is
  1-Lipschitz and satisfies (★);
* `theoremMStar_level_diagram`: (★) for a convergent family (its case `φ = id`).

Machines are the instance `runDiagram` (`MStarClass.lean`), where the extra bits are the state and
the head positions, `s = ⌈log₂(q+1)⌉ + (k+1)⌈log₂(2T+1)⌉ = o(L)`.
-/

namespace Transpose.Tape.Impl

open Transpose MeasureTheory Filter Topology TSDiagram

open scoped ENNReal

section Diagram

variable {k : ℕ} (D : TSDiagram k)

open Classical in
/-- **The capacity between labels.** At the block capacities with the per-node profile and `s`
extra bits per memory edge, the edges between different labels carry at most
`M_b s + r G (3k M_b + Σ_t χ_t)` bits, where `M_b` is the number of label changes and `χ_t` the
number of chords of tape `t` between different labels. -/
theorem sum_cross_blockCap_le {L n G s : ℕ} (hD : D.Valid L) (hr : 1 ≤ blockSize G n)
    (lab : ℕ → ℕ) :
    ∑ e ∈ (D.edges (blockSize G n)).filter (fun e => lab e.1 ≠ lab e.2),
        D.blockCap n G (fun y => ∑ t, (pairRes (blockSize G n) (D.work t) D.T y).card) s e ≤
      labelChanges lab (D.nodes (blockSize G n)) * s +
        blockSize G n * G * (3 * k * labelChanges lab (D.nodes (blockSize G n)) +
          ∑ t, (crossChords (pairRes (blockSize G n) (D.work t) D.T) lab
            (D.nodes (blockSize G n))).card) := by
  set r := blockSize G n with hrdef
  set N := D.nodes r with hN
  set Mb := labelChanges lab N with hMb
  set mem : ℕ → ℕ := fun y => ∑ t, (pairRes r (D.work t) D.T y).card with hmem
  have hh : ∀ t, UnitSteps (D.work t) := fun t => (hD.1 t).2
  have hdisj : Disjoint ((D.memEdges r).filter (fun e => lab e.1 ≠ lab e.2))
      ((D.chordEdges r).filter (fun e => lab e.1 ≠ lab e.2)) :=
    Finset.disjoint_filter_filter
      (Finset.disjoint_left.2 (fun e hm hc => not_mem_chordEdges_of_mem_memEdges D hm hc))
  rw [TSDiagram.edges, Finset.filter_union, Finset.sum_union hdisj]
  -- memory edges between labels: at most `M_b`, each at most `3k` blocks plus `s` bits
  have hres : ∀ y, mem y ≤ 3 * k := by
    intro y
    calc mem y ≤ ∑ _t : Fin k, 3 :=
          Finset.sum_le_sum (fun t _ => (pairRes_admissible (hh t) hr D.T).2 y)
      _ = 3 * k := by simp [Nat.mul_comm]
  have hcardM : ((D.memEdges r).filter (fun e => lab e.1 ≠ lab e.2)).card ≤ Mb := by
    apply Finset.card_le_card_of_injOn (fun e => e.2)
    · intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      obtain ⟨hm, hne⟩ := he
      rw [mem_memEdges] at hm
      obtain ⟨y, z⟩ := e
      simp only at hm hne ⊢
      obtain ⟨rfl, hz⟩ := hm
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Nat.add_sub_cancel]
      exact ⟨hz, by omega, fun h => hne h.symm⟩
    · intro e he e' he' hee
      rw [Finset.mem_coe, Finset.mem_filter, mem_memEdges] at he he'
      simp only at hee
      have h1 := he.1.1
      have h2 := he'.1.1
      exact Prod.ext (by omega) hee
  have h1 : ∑ e ∈ (D.memEdges r).filter (fun e => lab e.1 ≠ lab e.2), D.blockCap n G mem s e ≤
      Mb * (3 * k * (r * G) + s) := by
    calc _ ≤ ∑ _e ∈ (D.memEdges r).filter (fun e => lab e.1 ≠ lab e.2),
          (3 * k * (r * G) + s) := by
          apply Finset.sum_le_sum
          intro e he
          rw [blockCap_mem D (Finset.mem_filter.1 he).1]
          exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hres e.1)) _
      _ = ((D.memEdges r).filter (fun e => lab e.1 ≠ lab e.2)).card * (3 * k * (r * G) + s) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ Mb * (3 * k * (r * G) + s) := Nat.mul_le_mul_right _ hcardM
  -- chord edges between labels: one block per tape having the chord, and each tape has at most
  -- one chord into each node
  have hcardC : ∀ t, (((D.chordEdges r).filter (fun e => lab e.1 ≠ lab e.2)).filter
      (fun e => ∃ β : ℤ, IsChord (pairRes r (D.work t) D.T) β e.1 e.2)).card ≤
      (crossChords (pairRes r (D.work t) D.T) lab N).card := by
    intro t
    calc _ ≤ ((crossChords (pairRes r (D.work t) D.T) lab N).image Prod.fst).card := by
          apply Finset.card_le_card_of_injOn (fun e => e.2)
          · intro e he
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at he
            obtain ⟨⟨hc, hne⟩, β, hch⟩ := he
            rw [Finset.mem_coe, Finset.mem_image]
            refine ⟨(e.2, β), ?_, rfl⟩
            unfold crossChords
            rw [Finset.mem_biUnion]
            refine ⟨e.2, Finset.mem_range.2 ((mem_chordEdges D).1 hc).2.1, ?_⟩
            rw [Finset.mem_image]
            exact ⟨β, Finset.mem_filter.2 ⟨hch.2.2.1, e.1, hne, hch⟩, rfl⟩
          · intro e he e' he' hee
            rw [Finset.mem_coe, Finset.mem_filter] at he he'
            obtain ⟨-, β, hch⟩ := he
            obtain ⟨-, β', hch'⟩ := he'
            simp only at hee
            rw [← hee] at hch'
            have := (pairRes_chord_target_unique (hh t) hr D.T hch hch').2
            exact Prod.ext this hee
      _ ≤ _ := Finset.card_image_le
  have h2 : ∑ e ∈ (D.chordEdges r).filter (fun e => lab e.1 ≠ lab e.2), D.blockCap n G mem s e ≤
      r * G * ∑ t, (crossChords (pairRes r (D.work t) D.T) lab N).card := by
    calc _ = ∑ e ∈ (D.chordEdges r).filter (fun e => lab e.1 ≠ lab e.2),
          D.chordTapes r e * (r * G) := by
          apply Finset.sum_congr rfl
          intro e he
          exact blockCap_chord D (Finset.mem_filter.1 he).1
      _ = (∑ e ∈ (D.chordEdges r).filter (fun e => lab e.1 ≠ lab e.2), D.chordTapes r e) *
          (r * G) := by rw [Finset.sum_mul]
      _ = (∑ t : Fin k, (((D.chordEdges r).filter (fun e => lab e.1 ≠ lab e.2)).filter
          (fun e => ∃ β : ℤ, IsChord (pairRes r (D.work t) D.T) β e.1 e.2)).card) * (r * G) := by
          congr 1
          simp only [TSDiagram.chordTapes, Finset.card_filter]
          rw [Finset.sum_comm]
      _ ≤ (∑ t, (crossChords (pairRes r (D.work t) D.T) lab N).card) * (r * G) :=
          Nat.mul_le_mul_right _ (Finset.sum_le_sum (fun t _ => hcardC t))
      _ = r * G * ∑ t, (crossChords (pairRes r (D.work t) D.T) lab N).card := by ring
  calc _ ≤ Mb * (3 * k * (r * G) + s) +
        r * G * ∑ t, (crossChords (pairRes r (D.work t) D.T) lab N).card := Nat.add_le_add h1 h2
    _ = Mb * s + r * G * (3 * k * Mb +
        ∑ t, (crossChords (pairRes r (D.work t) D.T) lab N).card) := by ring

/-- **A code-carrying diagram satisfies the cut inequality.** Discrete Isoperimetry for codes
(`isoperimetry_code`) at the block capacities with the per-node profile and `s` extra bits per memory
edge, on a set of co-entropy `≤ D_c`. -/
theorem cutIneq_of_solves {n G s : ℕ} (hG : 1 ≤ G) (hn : 1 ≤ n)
    (hD : D.Valid (n * n * entryBits n)) {F : Set (Fin (n * n * entryBits n) → Bool)}
    {code : NetCode}
    (hsol : D.Solves n G (D.blockCap n G
      (fun y => ∑ t, (pairRes (blockSize G n) (D.work t) D.T y).card) s) F code)
    {Dc : ℕ} (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ Dc * F.ncard) :
    CutIneq n G (blockSize G n) D.T Dc s D.work := by
  intro lab m hm
  have hr := one_le_blockSize hG hn
  have h1 := isoperimetry_code D hD hr hsol hco lab m hm
  have h2 := sum_cross_blockCap_le D hD hr lab (s := s)
  have hN : D.nodes (blockSize G n) = numSlots (blockSize G n) D.T := rfl
  rw [hN] at h1 h2
  calc _ ≤ _ := h1
    _ ≤ _ := Nat.add_le_add_left h2 _
    _ = _ := by ring

end Diagram

/-! ### Theorem M* for code-carrying diagrams -/

/-- **Theorem M\* for code-carrying diagrams.** Let valid `k`-walk diagrams `D_i` of length
`≤ c L_i` carry causal codes solving complete exchange on sets of co-entropy `m_i` at the block
capacities (per-node profile, `G ≥ 1` bits per cell) plus `s_i` bits per memory edge, with
`(m_i + s_i) / L_i → 0`. Then the rescaled work walks have a uniformly convergent subsequence on
`[0, c₀]`, `c₀ = c G + 1`, and every subsequential limit is 1-Lipschitz and satisfies (★) for every
`θ`, every finite union `S` of closed intervals and every labelling `β` of `[0, c₀] ∖ S` constant on
finitely many intervals with label classes of measure `≤ θ`. This is `theoremMStar_walk` for the
diagrams' work walks, with the cut inequality from `cutIneq_of_solves`. -/
theorem theoremMStar_diagram {k G : ℕ} (hG : 1 ≤ G) {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ds : ℕ → TSDiagram k}
    {Fs : ∀ i, Set (Fin (ns i * ns i * entryBits (ns i)) → Bool)} {codes : ℕ → NetCode}
    {ms ss : ℕ → ℕ}
    (hvalid : ∀ᶠ i in atTop, (Ds i).Valid (ns i * ns i * entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, ((Ds i).T : ℝ) ≤ c * inputLength (ns i))
    (hco : ∀ᶠ i in atTop, 2 ^ (ns i * ns i * entryBits (ns i)) ≤ 2 ^ ms i * (Fs i).ncard)
    (hsol : ∀ᶠ i in atTop, (Ds i).Solves (ns i) G ((Ds i).blockCap (ns i) G
      (fun y => ∑ t, (pairRes (blockSize G (ns i)) ((Ds i).work t) (Ds i).T y).card) (ss i))
      (Fs i) (codes i))
    (hsmall : Tendsto (fun i => ((ms i : ℝ) + ss i) / inputLength (ns i)) atTop (𝓝 0)) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
        (Set.Icc 0 (c * G + 1))) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
      (∀ t, TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
        (Set.Icc 0 (c * G + 1))) →
      (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (c * G + 1))) ∧
      ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (c * G + 1) →
        (∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
        1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
          2 * k * volume (S ∩ Set.Icc 0 (c * G + 1)) := by
  obtain ⟨hsub, hlim⟩ := theoremMStar_walk hns (Ts := fun i => (Ds i).T) (Ds := ms) (ss := ss)
    (hs := fun i => (Ds i).work) (hvalid.mono fun i h t τ _ => (h.1 t).2 τ) htime
    (by
      filter_upwards [hvalid, hco, hsol, hns.eventually_ge_atTop 1] with i hv hc hso hn
      exact cutIneq_of_solves (Ds i) hG hn hv hso hc) hsmall
  exact ⟨hsub (hvalid.mono fun i h t => (h.1 t).1),
    fun φ hφ P hP => ⟨(hlim φ hφ P hP).1, (hlim φ hφ P hP).2.1⟩⟩

/-- **Theorem M\* for code-carrying diagrams** (level form, any `θ`): the case `φ = id` of
`theoremMStar_diagram`. If the rescaled work walks converge uniformly to `P` on `[0, c₀]`,
`c₀ = c G + 1`, then `1 ≤ Σ_t ∫⁻ κ_t + 2θ + 2k |S ∩ [0, c₀]|`. -/
theorem theoremMStar_level_diagram {k G : ℕ} (hG : 1 ≤ G) {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ds : ℕ → TSDiagram k}
    {Fs : ∀ i, Set (Fin (ns i * ns i * entryBits (ns i)) → Bool)} {codes : ℕ → NetCode}
    {ms ss : ℕ → ℕ}
    (hvalid : ∀ᶠ i in atTop, (Ds i).Valid (ns i * ns i * entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, ((Ds i).T : ℝ) ≤ c * inputLength (ns i))
    (hco : ∀ᶠ i in atTop, 2 ^ (ns i * ns i * entryBits (ns i)) ≤ 2 ^ ms i * (Fs i).ncard)
    (hsol : ∀ᶠ i in atTop, (Ds i).Solves (ns i) G ((Ds i).blockCap (ns i) G
      (fun y => ∑ t, (pairRes (blockSize G (ns i)) ((Ds i).work t) (Ds i).T y).card) (ss i))
      (Fs i) (codes i))
    (hsmall : Tendsto (fun i => ((ms i : ℝ) + ss i) / inputLength (ns i)) atTop (𝓝 0))
    {P : Fin k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => (Ds i).rescaled (ns i) G t) (P t) atTop
      (Set.Icc 0 (c * G + 1)))
    {θ : ℝ≥0∞} {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (c * G + 1))
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) :
    1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
      2 * k * volume (S ∩ Set.Icc 0 (c * G + 1)) :=
  ((theoremMStar_diagram hG hns hvalid htime hco hsol hsmall).2 id strictMono_id P hconv).2
    θ S β hS hβ hclass

end Transpose.Tape.Impl
