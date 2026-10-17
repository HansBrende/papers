import Transpose.Tape.PPrimeLocal
import Transpose.Tape.Corollaries
import Transpose.Tape.DefsTrace

/-!
# The Block Locality Lemma

* `locality_entry`: the Locality Lemma with data-dependent heads where a read may come from outside
  `J`, if the cell's content at some time `a ≤ τ` agrees and every visit during `[a, τ)`, in either
  run, lies in `J`. It is a case of `locality_core` (`Locality.lean`), plus output lengths
  (`outLen_agree`).
* `block_locality`: the Block Locality Lemma, with full head positions at the memory boundaries
  (the work-head offsets within blocks do not suffice: `block_locality_offsets_counterexample`).
  Its reads use the `y*` argument of the Charging Lemma (`entry_slot`, `Blocks.lean`): either the
  block was never resident outside `U` before the read's slot, or it entered `U` at a memory
  boundary or by a chord at some slot `z`, after which it is resident only at slots of `U`.
-/

namespace Transpose.Tape.Impl

open Transpose

variable {M : TM}

/-! ### The Locality Lemma, entry form -/

/-- **The Locality Lemma, entry form**: `locality_core` (whose read condition needs only the last
visits to lie in `J`), plus output lengths. -/
theorem locality_entry {w w' : List Bool} {J : Finset ℕ} {A : Set ℕ}
    (hpred : ∀ τ ∈ J, τ ∉ A → 1 ≤ τ ∧ τ - 1 ∈ J)
    (hanchor : ∀ τ ∈ J, τ ∈ A →
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧ headSym M w τ = headSym M w' τ)
    (hread : ∀ τ ∈ J, τ ∉ A → ∀ t : Fin M.k, ∃ a ≤ τ,
      (run M w a).work t (workTraj M w τ t) = (run M w' a).work t (workTraj M w τ t) ∧
      ∀ σ, a ≤ σ → σ < τ →
        (workTraj M w σ t = workTraj M w τ t ∨ workTraj M w' σ t = workTraj M w τ t) → σ ∈ J)
    (hinput : ∀ τ ∈ J, (run M w τ).inPos = (run M w' τ).inPos →
      readInput w (run M w τ).inPos = readInput w' (run M w τ).inPos) :
    ∀ τ ∈ J, (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧
      headSym M w τ = headSym M w' τ ∧ transAt M w τ = transAt M w' τ := by
  have hc := locality_core hpred
    (fun τ hτ hA => ⟨(hanchor τ hτ hA).1, (hanchor τ hτ hA).2.1, (hanchor τ hτ hA).2.2.1,
      (hanchor τ hτ hA).2.2.2.2⟩)
    (fun τ hτ hA _ t => by
      obtain ⟨a, ha, hc, hv⟩ := hread τ hτ hA t
      exact ⟨a, ha, hc, fun σ h1 h2 h3 _ => hv σ h1 h2 (Or.inl h3),
        fun σ h1 h2 h3 _ => hv σ h1 h2 (Or.inr h3)⟩) hinput
  have hl := outLen_agree hpred (fun τ hτ hA => (hanchor τ hτ hA).2.2.2.1)
    (fun τ hτ => (hc τ hτ).2.2.2.2)
  intro τ hτ
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc τ hτ
  exact ⟨h1, h2, h3, hl τ hτ, h4, h5⟩

/-! ### The Block Locality Lemma -/

theorem sameTrace_pairRes {n b r T : ℕ} {w w' : List Bool} (h : SameTrace M n b r T w w')
    (t : Fin M.k) {y : ℕ} (hy : y ≤ numSlots r T) :
    pairRes r (fun τ => workTraj M w τ t) T y = pairRes r (fun τ => workTraj M w' τ t) T y :=
  congrFun (congrArg Prod.fst (h y hy)) t

theorem sameTrace_srcRows {n b r T : ℕ} {w w' : List Bool} (h : SameTrace M n b r T w w')
    {y : ℕ} (hy : y ≤ numSlots r T) :
    srcRows M w n b (slotOf r T y) = srcRows M w' n b (slotOf r T y) :=
  congrArg (fun x => x.2.1) (h y hy)

theorem sameTrace_outLen {n b r T : ℕ} {w w' : List Bool} (h : SameTrace M n b r T w w')
    {y : ℕ} (hy : y ≤ numSlots r T) :
    (run M w (y * r)).outRev.length = (run M w' (y * r)).outRev.length :=
  congrArg (fun x => x.2.2) (h y hy)

/-- **The Block Locality Lemma** (with full head positions at the memory boundaries). -/
theorem block_locality {n b r T : ℕ} (hr : 1 ≤ r) {w w' : List Bool}
    (hw : w.length = n * n * b) (hw' : w'.length = n * n * b)
    (htrace : SameTrace M n b r T w w') (U : Set ℕ)
    (hmem : ∀ z ∈ memBoundaries U (numSlots r T),
      (run M w (z * r)).state = (run M w' (z * r)).state ∧
      (run M w (z * r)).inPos = (run M w' (z * r)).inPos ∧
      (run M w (z * r)).workPos = (run M w' (z * r)).workPos ∧
      ∀ (t : Fin M.k) (c : ℤ), blockOf r c ∈ pairRes r (fun τ => workTraj M w τ t) T z →
        (run M w (z * r)).work t c = (run M w' (z * r)).work t c)
    (hchord : ∀ (t : Fin M.k),
      ∀ p ∈ chordsInto (pairRes r (fun τ => workTraj M w τ t) T) U (numSlots r T),
      ∀ c : ℤ, blockOf r c = p.2 → (run M w (p.1 * r)).work t c = (run M w' (p.1 * r)).work t c)
    (hrows : ∀ d < n * n * b, d / (n * b) ∈ srcRows M w n b (slotSteps r U T) →
      nth w d = nth w' d) :
    ∀ τ ∈ slotSteps r U T,
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧
      headSym M w τ = headSym M w' τ ∧ transAt M w τ = transAt M w' τ := by
  classical
  set N := numSlots r T with hN
  set J := slotSteps r U T with hJ
  -- anchors: step `0` and the first steps of the memory boundaries
  let A : Set ℕ := {τ | τ = 0 ∨ ∃ z ∈ memBoundaries U N, τ = z * r}
  have hlt : ∀ τ ∈ J, τ < T := fun τ hτ => (mem_slotSteps.1 hτ).1
  have hslot : ∀ τ ∈ J, τ / r ∈ U := fun τ hτ => (mem_slotSteps.1 hτ).2
  have hdivN : ∀ τ, τ < T → τ / r < N := fun τ hτ => div_lt_numSlots hr hτ
  have hcur : ∀ (v : List Bool) (t : Fin M.k) (σ : ℕ), σ < T →
      blockOf r (workTraj M v σ t) ∈ pairRes r (fun τ => workTraj M v τ t) T (σ / r) :=
    fun v t σ hσ => cur_mem_pairRes (h := fun τ => workTraj M v τ t) hr hσ
  apply locality_entry (A := A)
  · -- non-anchors have their predecessor in `J`: a first step of a slot is an anchor unless the
    -- previous slot is in `U`
    intro τ hτ hτA
    have hτ0 : 1 ≤ τ := Nat.one_le_iff_ne_zero.2 fun h0 => hτA (Or.inl h0)
    refine ⟨hτ0, mem_slotSteps.2 ⟨by have := hlt τ hτ; omega, ?_⟩⟩
    by_cases hdiv : (τ - 1) / r = τ / r
    · rw [hdiv]; exact hslot τ hτ
    obtain ⟨hstart, hprev, hq⟩ := slot_start_of_div_ne hr hτ0 hdiv
    by_contra hU
    exact hτA (Or.inr ⟨τ / r, mem_memBoundaries.2 ⟨hdivN τ (hlt τ hτ), hslot τ hτ, hq,
      hprev ▸ hU⟩, hstart.symm⟩)
  · -- the anchors carry equal data
    rintro τ hτ (h0 | ⟨z, hz, rfl⟩)
    · subst h0
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · obtain ⟨hs, hi, hwp, hcont⟩ := hmem z hz
      have hzN : z < N := (mem_memBoundaries.1 hz).1
      have hzT : z * r < T := hlt _ hτ
      refine ⟨hs, hi, hwp, sameTrace_outLen htrace hzN.le, ?_⟩
      funext t
      show (run M w (z * r)).work t ((run M w (z * r)).workPos t) =
        (run M w' (z * r)).work t ((run M w' (z * r)).workPos t)
      rw [← hwp]
      apply hcont t
      have := hcur w t (z * r) hzT
      rwa [Nat.mul_div_cancel z (show 0 < r by omega)] at this
  · -- reads at non-anchors: the `y*` argument
    intro τ hτ _ t
    have hτT := hlt τ hτ
    set β := blockOf r (workTraj M w τ t) with hβ
    have hβR : β ∈ pairRes r (fun σ => workTraj M w σ t) T (τ / r) := hcur w t τ hτT
    -- every visit to the cell lies in a slot where its block is resident (in both runs)
    have hvisit : ∀ σ, σ < τ →
        (workTraj M w σ t = workTraj M w τ t ∨ workTraj M w' σ t = workTraj M w τ t) →
        β ∈ pairRes r (fun s => workTraj M w s t) T (σ / r) := by
      intro σ hστ hσ
      have hσT : σ < T := lt_trans hστ hτT
      rcases hσ with hσ | hσ
      · have := hcur w t σ hσT
        rwa [hσ] at this
      · have := hcur w' t σ hσT
        rw [hσ, ← sameTrace_pairRes htrace t (hdivN σ hσT).le] at this
        exact this
    rcases entry_slot (R := pairRes r (fun s => workTraj M w s t) T) (hdivN τ hτT) (hslot τ hτ)
      hβR with hnone | ⟨z, hzle, hzent, hzU⟩
    · refine ⟨0, Nat.zero_le _, rfl, fun σ _ hστ hσ => ?_⟩
      rw [hJ, mem_slotSteps]
      refine ⟨lt_trans hστ hτT, ?_⟩
      have hle : σ / r ≤ τ / r := Nat.div_le_div_right hστ.le
      rcases Nat.lt_or_ge (σ / r) (τ / r) with h' | h'
      · exact hnone _ h' (hvisit σ hστ hσ)
      · rw [le_antisymm hle h']; exact hslot τ hτ
    · refine ⟨z * r, le_trans (Nat.mul_le_mul_right r hzle) (Nat.div_mul_le_self τ r), ?_,
        fun σ hzσ hστ hσ => ?_⟩
      · rcases hzent with ⟨hzm, hzβ, -⟩ | hzc
        · exact (hmem z hzm).2.2.2 t _ hzβ
        · exact hchord t (z, β) hzc _ hβ.symm
      · rw [hJ, mem_slotSteps]
        refine ⟨lt_trans hστ hτT, ?_⟩
        have h1 : z ≤ σ / r := by
          rw [Nat.le_div_iff_mul_le (by omega)]; exact hzσ
        exact hzU _ h1 (Nat.div_le_div_right hστ.le) (hvisit σ hστ hσ)
  · -- input bits at commonly read positions: the read position lies in a row read during `J`
    intro τ hτ _
    refine readInput_eq_of_nth hw hw' fun d hd hdL => hrows d hdL ?_
    obtain ⟨hi, hj, ht, hdec⟩ := pos_decomp hdL
    obtain ⟨h1, h2⟩ := pos_mem_row (i := d / b / n) hj ht
    rw [← hdec] at h1 h2
    simp only [srcRows, Finset.mem_filter, Finset.mem_range]
    rw [show d / (n * b) = d / b / n by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]]
    exact ⟨hi, τ, hτ, by rw [← hd]; exact_mod_cast h1, by rw [← hd]; exact_mod_cast h2⟩

end Transpose.Tape.Impl
