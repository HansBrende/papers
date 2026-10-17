import Transpose.Tape.Counting
import Transpose.Tape.Forest
import Transpose.Tape.DefsPP

/-!
# Theorem P′: anchored locality and the data-dependent Forest Lemma

* `locality_anchored`: the Locality Lemma for arbitrary step sets with data-dependent heads, the
  case `a = 0` of `locality_core` (`Locality.lean`) plus output lengths (`outLen_agree`).
* `eq_of_nodeCode_eq`: equal node codes give equal nodes (nodes are intervals, `convex_eq_Icc`);
  `anchor_of_codes`: equal codes anchor the two runs at a node's first step (`CfgAgree`).
* `forest_agree` and `forest_comb_agree`: the Forest Lemma of Theorem P′.
  `forest_comb_agree_on` needs correctness only on the two inputs (at the ends of their pass
  partitions), and no halting; `correct_of_transposes` (`Counting.lean`) supplies it for a
  transposer.
-/

namespace Transpose.Tape.Impl

open Transpose

variable {M : TM}

/-! ### Anchored locality -/

/-- **The Locality Lemma, anchored form**: `locality_core` with `a = 0` (every cell is blank at
time `0`), plus output lengths. -/
theorem locality_anchored {w w' : List Bool} {J : Finset ℕ} {A : Set ℕ}
    (hpred : ∀ τ ∈ J, τ ∉ A → 1 ≤ τ ∧ τ - 1 ∈ J)
    (hanchor : ∀ τ ∈ J, τ ∈ A →
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧ headSym M w τ = headSym M w' τ)
    (hread : ∀ τ ∈ J, τ ∉ A → ∀ (t : Fin M.k) (σ : ℕ),
      (IsLastVisit (fun s => workTraj M w s t) τ σ → σ ∈ J) ∧
      (IsLastVisit (fun s => workTraj M w' s t) τ σ → σ ∈ J))
    (hinput : ∀ τ ∈ J, (run M w τ).inPos = (run M w' τ).inPos →
      readInput w (run M w τ).inPos = readInput w' (run M w τ).inPos) :
    ∀ τ ∈ J, (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧
      headSym M w τ = headSym M w' τ ∧ transAt M w τ = transAt M w' τ := by
  have hc := locality_core hpred
    (fun τ hτ hA => ⟨(hanchor τ hτ hA).1, (hanchor τ hτ hA).2.1, (hanchor τ hτ hA).2.2.1,
      (hanchor τ hτ hA).2.2.2.2⟩)
    (fun τ hτ hA hwp t => by
      have e : workTraj M w τ t = workTraj M w' τ t := by simp only [workTraj, hwp]
      exact ⟨0, Nat.zero_le _, rfl,
        fun σ _ h2 h3 h4 => (hread τ hτ hA t σ).1 ⟨h2, h3, h4⟩,
        fun σ _ h2 h3 h4 => (hread τ hτ hA t σ).2 ⟨h2, h3.trans e, fun ρ h5 h6 h7 =>
          h4 ρ h5 h6 (h7.trans e.symm)⟩⟩) hinput
  have hl := outLen_agree hpred (fun τ hτ hA => (hanchor τ hτ hA).2.2.2.1)
    (fun τ hτ => (hc τ hτ).2.2.2.2)
  intro τ hτ
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc τ hτ
  exact ⟨h1, h2, h3, hl τ hτ, h4, h5⟩

/-! ### Equal codes give equal nodes -/

/-- Two intervals of steps with the same node code are equal. -/
theorem eq_of_nodeCode_eq {w w' : List Bool} {J J' : Finset ℕ} (hc : IsConvex J)
    (hc' : IsConvex J') (h : nodeCode M w J = nodeCode M w' J') : J = J' := by
  unfold nodeCode at h
  by_cases hJ : J.Nonempty
  · by_cases hJ' : J'.Nonempty
    · rw [dite_eq_left hJ, dite_eq_left hJ'] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [convex_eq_Icc hc hJ, convex_eq_Icc hc' hJ', h.1, h.2.1]
    · rw [dite_eq_left hJ, dite_eq_right hJ'] at h; exact absurd h (by simp)
  · by_cases hJ' : J'.Nonempty
    · rw [dite_eq_right hJ, dite_eq_left hJ'] at h; exact absurd h (by simp)
    · rw [Finset.not_nonempty_iff_eq_empty] at hJ hJ'; rw [hJ, hJ']

/-- Equal codes of a common nonempty node: the two runs agree at its first step. -/
theorem anchor_of_codes {w w' : List Bool} {N : Finset ℕ} (hN : N.Nonempty)
    (h1 : nodeCode M w N = nodeCode M w' N) (h2 : sideCode M w N = sideCode M w' N) :
    CfgAgree M w w' (firstStep N) ∧ headSym M w (firstStep N) = headSym M w' (firstStep N) := by
  have hfs : firstStep N = N.min' hN := by simp [firstStep, hN]
  unfold nodeCode at h1
  rw [dite_eq_left hN, dite_eq_left hN] at h1
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h1
  simp only [sideCode, Prod.mk.injEq] at h2
  rw [hfs] at h2 ⊢
  exact ⟨⟨h2.1, h1.1, h1.2.1, h1.2.2⟩, h2.2⟩

/-! ### The Forest Lemma, data-dependent form -/

/-- **The Forest Lemma of Theorem P′.** -/
theorem forest_agree {w w' : List Bool} {L T T' r : ℕ} {p p' : ℕ → ℕ}
    (hw : w.length = L) (hw' : w'.length = L)
    (hp : PassPartition M w T r p) (hp' : PassPartition M w' T' r p') {o₁ o₂ : ℕ}
    (hcode : ∀ α ∈ addresses M.k r,
      nodeCode M w (forestNode M w p o₁ o₂ α.1 α.2) =
          nodeCode M w' (forestNode M w' p' o₁ o₂ α.1 α.2) ∧
        sideCode M w (forestNode M w p o₁ o₂ α.1 α.2) =
          sideCode M w' (forestNode M w' p' o₁ o₂ α.1 α.2))
    (hinput : ∀ d ∈ readSet (inTraj M w) L (forest M w p r o₁ o₂),
      d ∈ readSet (inTraj M w') L (forest M w' p' r o₁ o₂) → nth w d = nth w' d) :
    (∀ α ∈ addresses M.k r, forestNode M w p o₁ o₂ α.1 α.2 = forestNode M w' p' o₁ o₂ α.1 α.2) ∧
    ∀ τ ∈ forest M w p r o₁ o₂,
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧
      headSym M w τ = headSym M w' τ ∧ transAt M w τ = transAt M w' τ := by
  classical
  have hnode : ∀ α ∈ addresses M.k r,
      forestNode M w p o₁ o₂ α.1 α.2 = forestNode M w' p' o₁ o₂ α.1 α.2 := fun α hα =>
    eq_of_nodeCode_eq (forestNode_inv hp hα o₁ o₂).2 (forestNode_inv hp' hα o₁ o₂).2
      (hcode α hα).1
  have hF : forest M w p r o₁ o₂ = forest M w' p' r o₁ o₂ :=
    Finset.biUnion_congr rfl (fun α hα => hnode α hα)
  refine ⟨hnode, ?_⟩
  -- the anchors: first steps of nonempty nodes
  let A : Set ℕ := {τ | ∃ α ∈ addresses M.k r, (forestNode M w p o₁ o₂ α.1 α.2).Nonempty ∧
    firstStep (forestNode M w p o₁ o₂ α.1 α.2) = τ}
  have hA : ∀ τ ∈ forest M w p r o₁ o₂, ∀ α ∈ addresses M.k r,
      firstStep (forestNode M w p o₁ o₂ α.1 α.2) = τ → τ ∈ A := by
    intro τ hτ α hα hfs
    by_cases hne : (forestNode M w p o₁ o₂ α.1 α.2).Nonempty
    · exact ⟨α, hα, hne, hfs⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have h0 : τ = 0 := by rw [← hfs, hne]; simp [firstStep]
      obtain ⟨β, hβ, hτβ⟩ := Finset.mem_biUnion.1 hτ
      refine ⟨β, hβ, ⟨τ, hτβ⟩, ?_⟩
      have := firstStep_le hτβ
      omega
  apply locality_anchored (A := A)
  · -- non-anchors have their predecessor in the forest
    intro τ hτ hτA
    have hτ0 : τ ≠ 0 := by
      intro h0
      obtain ⟨β, hβ, hτβ⟩ := Finset.mem_biUnion.1 hτ
      have := firstStep_le hτβ
      exact hτA (hA τ hτ β hβ (by omega))
    refine ⟨by omega, ?_⟩
    by_contra hprev
    have hep : τ ∈ entryPoints (forest M w p r o₁ o₂) := mem_entryPoints.2 ⟨hτ, hτ0, hprev⟩
    obtain ⟨α, hα, hfs⟩ := Finset.mem_image.1 (forest_entryPoints_subset hp o₁ o₂ hep)
    exact hτA (hA τ hτ α hα hfs)
  · -- the anchors carry equal data
    rintro τ - ⟨α, hα, hne, rfl⟩
    have h1 := (hcode α hα).1
    have h2 := (hcode α hα).2
    rw [← hnode α hα] at h1 h2
    obtain ⟨⟨hs, hi, hwp, hl⟩, hh⟩ := anchor_of_codes hne h1 h2
    exact ⟨hs, hi, hwp, hl, hh⟩
  · -- reads at non-anchors are served from within the forest
    intro τ hτ hτA t σ
    constructor
    · intro hlast
      by_contra hσ
      have hc : (t, τ) ∈ entryCells (workTraj M w) (forest M w p r o₁ o₂) :=
        mem_entryCells.2 ⟨hτ, σ, hσ, hlast⟩
      obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 (forest_entryCells_subset hp o₁ o₂ hc)
      simp only [Prod.mk.injEq] at hxe
      exact hτA (hA τ hτ x.2 (Finset.mem_product.1 hx).2 hxe.2)
    · intro hlast
      by_contra hσ
      rw [hF] at hσ
      have hc : (t, τ) ∈ entryCells (workTraj M w') (forest M w' p' r o₁ o₂) :=
        mem_entryCells.2 ⟨hF ▸ hτ, σ, hσ, hlast⟩
      obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 (forest_entryCells_subset hp' o₁ o₂ hc)
      simp only [Prod.mk.injEq] at hxe
      have hx2 := (Finset.mem_product.1 hx).2
      rw [← hnode x.2 hx2] at hxe
      exact hτA (hA τ hτ x.2 hx2 hxe.2)
  · -- the input bits at commonly read positions agree
    intro τ hτ hi
    refine readInput_eq_of_nth hw hw' fun d hd hdL => hinput d ?_ ?_
    · simp only [readSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨hdL, τ, hτ, hd.symm⟩
    · simp only [readSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨hdL, τ, hF ▸ hτ, by rw [hd]; exact hi.symm⟩

/-- **The comb is determined by the codes and the commonly read bits**, for two inputs on which
the machine is correct (it outputs the transposed encoding at the end `T`, `T'` of its pass
partition; no halting is assumed). -/
theorem forest_comb_agree_on {n b T T' r : ℕ} {w w' : List Bool} {p p' : ℕ → ℕ}
    (hcw : ∃ A : Matrix, w = encode n b A ∧ (run M w T).outRev.reverse = encode n b (transpose A))
    (hcw' : ∃ A : Matrix, w' = encode n b A ∧
      (run M w' T').outRev.reverse = encode n b (transpose A))
    (hp : PassPartition M w T r p) (hp' : PassPartition M w' T' r p') {o₁ o₂ : ℕ}
    (hcode : ∀ α ∈ addresses M.k r,
      nodeCode M w (forestNode M w p o₁ o₂ α.1 α.2) =
          nodeCode M w' (forestNode M w' p' o₁ o₂ α.1 α.2) ∧
        sideCode M w (forestNode M w p o₁ o₂ α.1 α.2) =
          sideCode M w' (forestNode M w' p' o₁ o₂ α.1 α.2))
    (hinput : ∀ d ∈ readSet (inTraj M w) (n * n * b) (forest M w p r o₁ o₂),
      d ∈ readSet (inTraj M w') (n * n * b) (forest M w' p' r o₁ o₂) → nth w d = nth w' d) :
    ∀ d ∈ combSet n b o₁ o₂, nth w d = nth w' d := by
  classical
  obtain ⟨A, rfl, hout⟩ := hcw
  obtain ⟨A', rfl, hout'⟩ := hcw'
  have hFA := forest_agree (length_of_mem_matrixInputs ⟨A, rfl⟩)
    (length_of_mem_matrixInputs ⟨A', rfl⟩) hp hp' hcode hinput
  have hF : forest M (encode n b A) p r o₁ o₂ = forest M (encode n b A') p' r o₁ o₂ :=
    Finset.biUnion_congr rfl (fun α hα => hFA.1 α hα)
  intro d hd
  simp only [combSet, Finset.mem_filter, Finset.mem_range] at hd
  obtain ⟨hdL, ho1, ho2⟩ := hd
  -- the step appending the transposed copy of `d` lies in the forest
  obtain ⟨τ, hτT, hτF, hsome, hτlen⟩ := exists_append_step_mem_forest hp ho1 ho2
    (by rw [← List.length_reverse, hout, length_encode]; exact tpos_lt hdL)
  obtain ⟨-, -, -, hl, -, htr⟩ := hFA.2 τ hτF
  have hob : outBit M (encode n b A') τ = outBit M (encode n b A) τ := by simp only [outBit, htr]
  have e1 := output_nth_eq_outBit (encode n b A) hτT hsome
  have e2 := output_nth_eq_outBit (encode n b A') (forest_subset hp' o₁ o₂ τ (hF ▸ hτF))
    (hob ▸ hsome)
  rw [hout, hτlen, nth_encode_transpose_tpos A hdL] at e1
  rw [hout', ← hl, hτlen, nth_encode_transpose_tpos A' hdL] at e2
  rw [e1, e2, hob]

/-- **The comb is determined by the codes and the commonly read bits.** -/
theorem forest_comb_agree {n b T T' r : ℕ} {w w' : List Bool} {p p' : ℕ → ℕ}
    (hcorr : Transposes M n b) (hw : w ∈ matrixInputs n b) (hw' : w' ∈ matrixInputs n b)
    (hT : HaltsAt M w T) (hT' : HaltsAt M w' T')
    (hp : PassPartition M w T r p) (hp' : PassPartition M w' T' r p') {o₁ o₂ : ℕ}
    (hcode : ∀ α ∈ addresses M.k r,
      nodeCode M w (forestNode M w p o₁ o₂ α.1 α.2) =
          nodeCode M w' (forestNode M w' p' o₁ o₂ α.1 α.2) ∧
        sideCode M w (forestNode M w p o₁ o₂ α.1 α.2) =
          sideCode M w' (forestNode M w' p' o₁ o₂ α.1 α.2))
    (hinput : ∀ d ∈ readSet (inTraj M w) (n * n * b) (forest M w p r o₁ o₂),
      d ∈ readSet (inTraj M w') (n * n * b) (forest M w' p' r o₁ o₂) → nth w d = nth w' d) :
    ∀ d ∈ combSet n b o₁ o₂, nth w d = nth w' d :=
  forest_comb_agree_on (correct_of_transposes hcorr hw hT) (correct_of_transposes hcorr hw' hT')
    hp hp' hcode hinput

end Transpose.Tape.Impl
