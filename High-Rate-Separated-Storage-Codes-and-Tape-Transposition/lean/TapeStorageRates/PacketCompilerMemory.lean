import TapeStorageRates.PacketCompilerBatch
import TapeStorageRates.PacketCompilerSchedule
import TapeStorageRates.PacketCompilerRecord
import TapeStorageRates.FrozenPackets

/-! # Actual coarse work cells and their last writes

During writeback the right cell changes first, then the centre, then the left cell. Every other
coarse address has exactly its old symbol. In particular the next read of an address is the word
at its last visit, including ticks that write back the scanned symbol unchanged.
-/

namespace TapeStorageRates.PacketCompiler

open Transpose Transpose.Tape Transpose.Tape.Impl BoundedNesting MergeDepth Finset

set_option autoImplicit false

def workWord {M : TM} (s : ℕ) (c : Config M) (j : Fin M.k) (u : ℤ) : WorkWord M s :=
  fun i => c.work j (u*s+i.val)

theorem tapeCell_workWord {M : TM} (s : ℕ) (c : Config M) (j : Fin M.k) (u : ℤ) :
    tapeCell (workLayout s) 0 (c.work j) u = workWord s c j u := by
  funext i
  have hi : (i.val : ℤ) < s := by exact_mod_cast i.isLt
  simp [tapeCell, workLayout, workWord, add_mul, hi]

theorem workWord_outside {M : TM} {s : ℕ} (hs : 0 < s) (w : List Bool) (j : Fin M.k) (b : ℕ)
    (u : ℤ) (hfar : 1 < |u - (workLayout s).cell hs ((run M w (b*s)).workPos j)|) :
    workWord s (run M w ((b+1)*s)) j u = workWord s (run M w (b*s)) j u := by
  funext i
  let p : ℤ := u*s+i.val
  have hcell : (workLayout s).cell hs p = u := by
    apply (workLayout s).cell_eq hs <;> dsimp [p, workLayout] <;>
      have h := i.isLt <;> nlinarith
  have hw : IsWalk (fun t => (run M w t).workPos j) := by
    intro t
    change |(run M w (t+1)).workPos j - (run M w t).workPos j| ≤ 1
    rw [workPos_eq_work, workPos_eq_work]; exact (trace M w).work_isWalk j t
  apply work_eq_of_no_visit j p (by rw [Nat.add_mul]; omega)
  intro t h₀ h₁ he
  have h := hw.lip h₀
  have hdist : |(run M w t).workPos j - (run M w (b*s)).workPos j| ≤ s := by
    rw [Nat.add_mul, one_mul] at h₁
    rcases h with ⟨h,h'⟩
    change (run M w t).workPos j - (run M w (b*s)).workPos j ≤ _ at h
    change (run M w (b*s)).workPos j - (run M w t).workPos j ≤ _ at h'
    exact abs_le.2 ⟨by omega, by omega⟩
  rw [he] at hdist
  exact (not_le_of_gt hfar) (hcell ▸ (workLayout s).near_cell hs hdist)

def mixed {α : Type*} (old new : ℤ → α) (c q : ℤ) : ℕ → α
  | 0 | 1 | 2 | 3 | 4 | 5 => old q
  | 6 => if q=c+1 then new q else old q
  | 7 => if q=c+1 ∨ q=c then new q else old q
  | _ => new q

private theorem mixed_next {α : Type*} (old new : ℤ → α) (c c' q : ℤ) (i : ℕ) (hi : i < 10)
    (hfar : 1 < |q-c| → new q = old q) (h : q ≠ phaseAddress c c' i) :
    mixed old new c q (i+1) = mixed old new c q i := by
  interval_cases i <;> simp [mixed, phaseAddress] at *
  all_goals try split_ifs at *
  all_goals intros; first | rfl | omega | (apply hfar; by_contra! hb; have := abs_le.1 hb; omega)

/-- The actual work tape throughout a block. Each of its three committed words is taken from
the genuine native configuration after this batch of `s` ticks. -/
noncomputable def memory {M : TM} {s : ℕ} (hs : 0 < s) (w : List Bool) (t : ℕ) (j : Fin M.k)
    (q : ℤ) : WorkWord M s :=
  let b := t / 11
  let old := run M w (b*s)
  mixed (workWord s old j) (workWord s (run M w ((b+1)*s)) j)
    ((workLayout s).cell hs (old.workPos j)) q (t%11)

theorem memory_slot {M : TM} {s : ℕ} (hs : 0 < s) (w : List Bool) (b i : ℕ) (hi : i<11)
    (j : Fin M.k) (q : ℤ) :
    memory hs w (11*b+i) j q = mixed (workWord s (run M w (b*s)) j)
      (workWord s (run M w ((b+1)*s)) j) ((workLayout s).cell hs ((run M w (b*s)).workPos j)) q i := by
  simp [memory, show (11*b+i)/11=b by omega, show (11*b+i)%11=i by omega]

theorem memory_unchanged {M : TM} {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (w : List Bool)
    (j : Fin M.k) (t : ℕ) (q : ℤ) (hne : q ≠ batchWalks L hs M w (some (some j)) t) :
    memory hs w (t+1) j q = memory hs w t j q := by
  let b := t/11
  let i := t%11
  have hi : i<11 := Nat.mod_lt _ (by decide)
  have ht : 11*b+i=t := Nat.div_add_mod _ _
  rw [← ht, memory_slot _ _ b i hi]
  change q ≠ sweep (fun b => (centres L hs M w b).work j) t at hne
  rw [← ht, sweep_slot _ b i hi] at hne
  by_cases hend : i+1=11
  · rw [show 11*b+i+1=11*(b+1)+0 by omega, memory_slot _ _ (b+1) 0 (by decide), show i=10 by omega]
    rfl
  · rw [Nat.add_assoc, memory_slot _ _ b (i+1) (by omega)]
    exact mixed_next _ _ _ _ _ i (by omega) (workWord_outside hs w j b q) hne

private theorem unchanged_interval {α : Type*} (v : ℕ → α) {a t : ℕ} (hat : a ≤ t)
    (h : ∀ i, a ≤ i → i < t → v (i+1) = v i) : v t = v a := by
  induction t with
  | zero => have := Nat.eq_zero_of_le_zero hat; subst a; rfl
  | succ t ih =>
    by_cases ht : a ≤ t
    · exact (h t ht (Nat.lt_succ_self _)).trans (ih ht fun i hi hi' => h i hi (by omega))
    · have : a=t+1 := by omega
      rw [this]

/-- A common path of unit work heads gives the local read equality from only the record at
each actual last visit. This applies to blank initial tapes and to idle writes. -/
theorem read_eq_of_predecessors {k T : ℕ} {α : Type*} (z : Fin k → ℕ → ℤ)
    (x y : ℕ → Fin k → ℤ → α) (initial : ∀ j q, x 0 j q = y 0 j q)
    (hx : ∀ j t, t < T → ∀ q, q ≠ z j t → x (t+1) j q = x t j q)
    (hy : ∀ j t, t < T → ∀ q, q ≠ z j t → y (t+1) j q = y t j q)
    {t : ℕ} (ht : t<T)
    (hwrite : ∀ u, DepStep z T t u → ∀ j, x (u+1) j (z j u) = y (u+1) j (z j u)) (j : Fin k) :
    x t j (z j t) = y t j (z j t) := by
  let q := z j t
  by_cases h : ∃ u<t, z j u = q
  · obtain ⟨u, hu, he, hgap⟩ := exists_lastVisit (pos := z j) h
    have hdep : DepStep z T t u := by
      by_cases hd : u+1=t
      · exact Or.inl ⟨hd, ht⟩
      · apply Or.inr
        have hh : IsHop (z j) T u t := ⟨by omega, ht, he.symm,
          fun i hi => by rw [he]; exact hgap i (mem_Ioo.mp hi).1 (mem_Ioo.mp hi).2⟩
        exact mem_image.mpr ⟨(j,u,t), mem_allHops.mpr hh, rfl⟩
    have hxy := hwrite u hdep j
    rw [he] at hxy
    have X := unchanged_interval (fun i => x i j q) (show u+1≤t by omega)
      fun i hi hi' => hx j i (by omega) q (Ne.symm (hgap i (by omega) hi'))
    have Y := unchanged_interval (fun i => y i j q) (show u+1≤t by omega)
      fun i hi hi' => hy j i (by omega) q (Ne.symm (hgap i (by omega) hi'))
    exact X.trans (hxy.trans Y.symm)
  · have hne : ∀ i<t, q ≠ z j i := fun i hi e => h ⟨i,hi,e.symm⟩
    have X := unchanged_interval (fun i => x i j q) (Nat.zero_le t) fun i _ hi => hx j i (by omega) q (hne i hi)
    have Y := unchanged_interval (fun i => y i j q) (Nat.zero_le t) fun i _ hi => hy j i (by omega) q (hne i hi)
    exact X.trans ((initial j q).trans Y.symm)

end TapeStorageRates.PacketCompiler
