import TapeStorageRates.PacketCompilerValues

/-! # Local determination on a frozen class of actual native runs -/

namespace TapeStorageRates.PacketCompiler

open Transpose Transpose.Tape MergeDepth BoundedNesting Finset

set_option autoImplicit false

theorem batchWalks_agree {s r R : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) {w v : List Bool}
    (h : ∀ b ≤ R, centres L hs M w b = centres L hs M v b) (i : Tp M.k) {t : ℕ} (ht : t<11*R) :
    batchWalks L hs M w i t = batchWalks L hs M v i t := by
  have h₀ := h (t/11) (by omega)
  have h₁ := h (t/11+1) (by omega)
  rcases i with _ | (_ | j) <;> simp only [batchWalks, sweep, h₀, h₁]

private theorem tick_eq {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) {w v : List Bool}
    (b i : ℕ) (hi : i<11)
    (hc : centres L hs M w b = centres L hs M v b)
    (hn : centres L hs M w (b+1) = centres L hs M v (b+1))
    (hI : tapeCell L none (readInput w) (batchWalks L hs M w none (11*b+i)) =
      tapeCell L none (readInput v) (batchWalks L hs M v none (11*b+i)))
    (hscan : ∀ j, memory hs w (11*b+i) j (batchWalks L hs M w (some (some j)) (11*b+i)) =
      memory hs v (11*b+i) j (batchWalks L hs M v (some (some j)) (11*b+i)))
    (hprev : ∀ b' i', i'<11 → 11*b'+i'+1 = 11*b+i →
      scratch L hs M w b' i' = scratch L hs M v b' i') :
    record L hs M w (11*b+i) = record L hs M v (11*b+i) := by
  have hscratch : scratch L hs M w b i = scratch L hs M v b i := by
    by_cases hsmall : i<4
    · cases i with
      | zero =>
        have hbdy : boundary L hs M w b = boundary L hs M v b := by
          cases b with
          | zero => simp [boundary, centres, past, run, init]
          | succ j =>
            have h := congrArg Scratch.boundary (hprev j 10 (by decide) (by omega))
            exact h
        simp [scratch, collect_zero, hbdy]
      | succ i =>
        let j : Fin 3 := ⟨i,by omega⟩
        apply scratch_read L hs M b j (hprev b i (by omega) (by omega))
        · change tapeCell L none (readInput w) (sweep (fun b => (centres L hs M w b).input) _) =
            tapeCell L none (readInput v) (sweep (fun b => (centres L hs M v b).input) _) at hI
          rw [read_address (centres L hs M w) b j Centres.input,
            read_address (centres L hs M v) b j Centres.input] at hI
          exact hI
        · funext l
          have h := hscan l
          rw [read_work L hs M w b j l, read_work L hs M v b j l] at h
          exact h
    · by_cases hfour : i=4
      · subst i; exact scratch_lookup _ _ _ _ hc hn (hprev b 3 (by decide) (by omega))
      · have h := hprev b (i-1) (by omega) (by omega)
        simpa only [scratch, ite_eq_right hsmall, ite_eq_right (by omega : ¬ i-1<4)] using h
  have hrecord : (record L hs M w (11*b+i)).scratch = (record L hs M v (11*b+i)).scratch := by
    simpa only [record_scratch_slot _ _ _ _ _ _ hi] using hscratch
  refine StepRecord.ext (congrArg Scratch.boundary hrecord) (congrArg Scratch.input hrecord)
    (congrArg Scratch.work hrecord) ?_ (congrArg Scratch.output hrecord)
  funext j
  rw [record_write_slot _ _ _ _ _ _ hi, record_write_slot _ _ _ _ _ _ hi]
  cases h : writeLane i with
  | none => exact hscan j
  | some l =>
    have h4 : ¬i<4 := by
      intro hlt
      interval_cases i <;> simp [writeLane] at h
    have hh := congrFun (congrFun (congrArg Scratch.work hscratch) l) j
    simpa only [scratch, ite_eq_right h4] using hh

/-- The actual eleven-phase records satisfy Paper 15's frozen local recurrence. The input
hypothesis describes exactly the ragged cell at one public address; `PaidInputs.input_cell_eq`
proves it for the reconstruction with a fixed tail. -/
theorem record_local {s r n R : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM)
    (w₀ : List Bool) (word : (Fin n → Fin s → Bool) → List Bool)
    (S : Finset (Fin n → Fin s → Bool))
    (hfrozen : ∀ x ∈ S, ∀ b ≤ R, centres L hs M (word x) b = centres L hs M w₀ b)
    (hinput : ∀ x ∈ S, ∀ y ∈ S, ∀ u : ℤ, (∀ j : Fin n, (j : ℤ) = u → x j = y j) →
      tapeCell L none (readInput (word x)) u = tapeCell L none (readInput (word y)) u) :
    PacketLocal (batchWalks L hs M w₀) (11*R) S (fun x => record L hs M (word x)) := by
  intro x hx y hy t ht hp hi
  let z : Fin M.k → ℕ → ℤ := fun j => batchWalks L hs M w₀ (some (some j))
  have xwalk := batchWalks_agree L hs M (hfrozen x hx)
  have ywalk := batchWalks_agree L hs M (hfrozen y hy)
  have scan : ∀ j, memory hs (word x) t j (z j t) = memory hs (word y) t j (z j t) := by
    apply read_eq_of_predecessors z (memory hs (word x)) (memory hs (word y))
      (fun _ _ => by simp [memory, mixed, run, init])
    · intro j u hu q hne
      apply memory_unchanged L hs _ j u q
      rwa [xwalk _ hu]
    · intro j u hu q hne
      apply memory_unchanged L hs _ j u q
      rwa [ywalk _ hu]
    · exact ht
    · intro u hdep j
      have h := congrFun (congrArg StepRecord.written (hp u hdep)) j
      change memory hs (word x) (u+1) j (batchWalks L hs M (word x) _ u) =
        memory hs (word y) (u+1) j (batchWalks L hs M (word y) _ u) at h
      rw [xwalk _ ((depStep_lt hdep).1.trans ht), ywalk _ ((depStep_lt hdep).1.trans ht)] at h
      exact h
  let b := t/11
  let i := t%11
  have hbi : 11*b+i=t := Nat.div_add_mod _ _
  have hi' : i<11 := Nat.mod_lt _ (by decide)
  have hb : b+1≤R := by dsimp [b]; omega
  rw [← hbi]
  apply tick_eq L hs M b i hi' ((hfrozen x hx b (by omega)).trans (hfrozen y hy b (by omega)).symm)
    ((hfrozen x hx (b+1) hb).trans (hfrozen y hy (b+1) hb).symm)
  · rw [hbi,xwalk _ ht,ywalk _ ht]
    exact hinput x hx y hy _ hi
  · intro j; rw [hbi,xwalk _ ht,ywalk _ ht]; exact scan j
  · intro b' i' hi'' he
    have hprev : 11*b'+i'+1=t := he.trans hbi
    have hh := congrArg StepRecord.scratch (hp (11*b'+i') (Or.inl ⟨hprev,ht⟩))
    simpa only [record_scratch_slot _ _ _ _ _ _ hi''] using hh

end TapeStorageRates.PacketCompiler
