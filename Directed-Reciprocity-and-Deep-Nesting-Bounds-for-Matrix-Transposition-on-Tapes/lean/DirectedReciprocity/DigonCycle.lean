import DirectedReciprocity.StrideCycles
import HalfRate.Pieces

/-!
# Universal chordless digon cycle dichotomy (`Theorem DC`)

Let `H = {f 0, …, f (L - 1)}` (`L ≥ 4`) be a chordless digon cycle in a loopless `TTFree`
recovery relation `N` (in context `U` disjoint from `H`) such that each vertex `f i` has at most
one active recovery parent outside `U ∪ H`:

* If `3 ∣ L` and the outside parents form a stride-3 hub triple `w₀, w₁, w₂ ∉ U ∪ H`
  (`IsStride3Cycle N U f`), then `H` admits **no** `PieceCert N U H` over any number of records `m`
  (`not_pieceCert_of_isStride3Cycle`, from `stride3_no_pieceCert`).
* Otherwise, `H` **always** admits a `PieceCert N U H` using at most `L + 1` records (`m = 2` when
  `L = 4`, and `m = L + 1` via the Two-Sided Arc-Expansion schedule when `L ≥ 5`):
  `digonCycle_pieceCert_of_not_stride3` and `digonCycle_pieceCert_iff`.
-/

namespace DirectedReciprocity

open Finset HalfRate

section Stride3Def

variable {V : Type*} [DecidableEq V]

/-- A cycle `f : Fin L → V` has stride-3 outside hubs if `3 ∣ L` and there exist outside parents
`w : Fin 3 → V` outside `U ∪ image f` with `w (i mod 3) ∈ N (f i)` for every `i`. -/
def IsStride3Cycle (N : V → Finset V) (U : Finset V) {L : ℕ} (f : Fin L → V) : Prop :=
  3 ∣ L ∧ ∃ w : Fin 3 → V,
    (∀ r, w r ∉ U ∧ w r ∉ univ.image f) ∧
    ∀ i : Fin L, w ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩ ∈ N (f i)

theorem not_pieceCert_of_isStride3Cycle [Fintype V] {N : V → Finset V} {U : Finset V}
    {L : ℕ} (hL : 3 ≤ L) {f : Fin L → V} (hf : Function.Injective f)
    (hUH : Disjoint U (univ.image f))
    (hcyc : ∀ i : Fin L,
      f (idx (by omega) (i.val + 1)) ∈ N (f i) ∧
      f (idx (by omega) (i.val + L - 1)) ∈ N (f i))
    (hs3 : IsStride3Cycle N U f) :
    ¬ Nonempty (PieceCert N U (univ.image f)) := by
  obtain ⟨⟨k, hkL⟩, w, hw, hout⟩ := hs3
  have hk1 : 1 ≤ k := by omega
  let f' : Fin (3 * k) → V := fun i => f (i.cast hkL.symm)
  have hf' : Function.Injective f' := fun i j h => Fin.cast_injective _ (hf h)
  have himg : univ.image f' = univ.image f := by
    ext v
    simp only [mem_image, mem_univ, true_and, f']
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i.cast hkL.symm, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨i.cast hkL, by simp⟩
  rw [← himg] at hUH ⊢
  refine stride3_no_pieceCert hUH hk1 f' hf' rfl w (by simpa [himg] using hw) ?_ ?_
  · intro i
    have hc := hcyc (i.cast hkL.symm)
    have h1 : (idx (by omega) (i.val + 1) : Fin (3 * k)).cast hkL.symm =
        idx (by omega) ((i.cast hkL.symm).val + 1) := by
      apply Fin.ext; simp [idx_val, hkL]
    have h2 : (idx (by omega) (i.val + 3 * k - 1) : Fin (3 * k)).cast hkL.symm =
        idx (by omega) ((i.cast hkL.symm).val + L - 1) := by
      apply Fin.ext; simp [idx_val, hkL]
    exact ⟨by simp only [f', h1]; exact hc.1, by simp only [f', h2]; exact hc.2⟩
  · intro i
    simpa [f'] using hout (i.cast hkL.symm)

end Stride3Def

section FourCycle

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Every chordless digon `4`-cycle with `TTFree` and at most one outside parent per vertex admits
an explicit `2`-record co-supplied `PieceCert`. -/
noncomputable def digonCycle4_pieceCert {N : V → Finset V} {U : Finset V}
    (f : Fin 4 → V) (hf : Function.Injective f)
    (hTT : ∀ i : Fin 4, ∀ w, w ∉ U → w ∉ univ.image f →
      w ∈ N (f i) → w ∈ N (f (idx (by decide) (i.val + 1))) → False)
    (hno_chord : ∀ i j : Fin 4, f j ∈ N (f i) →
      j = idx (by decide) (i.val + 1) ∨ j = idx (by decide) (i.val + 3))
    (hout1 : ∀ i : Fin 4, ∀ w₁ w₂, w₁ ∈ N (f i) → w₂ ∈ N (f i) →
      w₁ ∉ U → w₁ ∉ univ.image f → w₂ ∉ U → w₂ ∉ univ.image f → w₁ = w₂) :
    PieceCert N U (univ.image f) := by
  classical
  let H := univ.image f
  let A : Finset V := {f 0, f 2}
  let B : Finset V := {f 1, f 3}
  let P2 : Fin 2 → Finset V := fun r => if r = 0 then A else B
  let par : V → Option V := outPar N (univ \ U) H
  let a : V → Fin 2 := fun v => if v ∈ A then 0 else 1
  let b : V → Fin 2 := fun v => if v ∈ A then 1 else 0
  let π : Fin 4 → Fin 4 := ![0, 2, 1, 3]
  have hπ_bij : Function.Bijective π := by decide
  let l : List V := List.ofFn (f ∘ π)
  have hfA : ∀ i : Fin 4, f i ∈ A ↔ (i = 0 ∨ i = 2) := by
    intro i
    simp only [A, mem_insert, mem_singleton, hf.eq_iff]
  have hfB : ∀ i : Fin 4, f i ∈ B ↔ (i = 1 ∨ i = 3) := by
    intro i
    simp only [B, mem_insert, mem_singleton, hf.eq_iff]
  have hAB : Disjoint A B := by
    rw [disjoint_left]
    intro v hv₁ hv₂
    obtain ⟨i, rfl⟩ : ∃ i, f i = v := by
      simp only [A, mem_insert, mem_singleton] at hv₁
      rcases hv₁ with rfl | rfl <;> exact ⟨_, rfl⟩
    rw [hfA] at hv₁; rw [hfB] at hv₂
    rcases hv₁ with rfl | rfl <;> rcases hv₂ with h | h <;> exact absurd h (by decide)
  refine
    { m := 2
      P := P2
      disj := by
        intro r₁ r₂ hne
        fin_cases r₁ <;> fin_cases r₂ <;> simp_all [P2, disjoint_comm]
      cover := by
        ext v
        simp only [P2, mem_biUnion, mem_univ, true_and, Fin.exists_fin_two, ↓reduceIte,
          show (1 : Fin 2) ≠ 0 by decide, A, B, mem_image, mem_insert, mem_singleton]
        constructor
        · rintro ((rfl | rfl) | (rfl | rfl)) <;> exact ⟨_, rfl⟩
        · rintro ⟨i, rfl⟩
          fin_cases i <;> simp
      l := l
      hl := by
        ext v
        simp only [l, List.mem_toFinset, List.mem_ofFn, Function.comp_apply, mem_image, mem_univ,
          true_and]
        exact ⟨fun ⟨j, hj⟩ => ⟨π j, hj⟩, fun ⟨i, hi⟩ =>
          let ⟨j, hj⟩ := hπ_bij.2 i
          ⟨j, hj ▸ hi⟩⟩
      a := a
      b := b
      par := par
      own := by
        intro v hv
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
        simp only [Function.comp_apply, a, P2]
        fin_cases j <;> simp [π, hfA, hfB]
      ab := by
        intro v _
        by_cases hv : v ∈ A <;> simp [a, b, hv]
      charged := ?_ }
  have hb_val : ∀ i : Fin 4, b (f i) = if (i = 0 ∨ i = 2) then 1 else 0 := by
    intro i; simp [b, hfA]
  have hb_P2 : ∀ i : Fin 4, P2 (b (f i)) = if (i = 0 ∨ i = 2) then B else A := by
    intro i; rw [hb_val]; split_ifs <;> rfl
  have hnb_opp : ∀ i : Fin 4, ∀ u ∈ N (f i), u ∈ H →
      u ∈ P2 (b (f i)) := by
    intro i u hu huH
    obtain ⟨j, -, rfl⟩ := mem_image.mp huH
    rw [hb_P2]
    rcases hno_chord i j hu with rfl | rfl <;> fin_cases i <;> simp [hfA, hfB, idx]
  have hadj4 : ∀ i₁ i₂ : Fin 4,
      (if (i₁ = 0 ∨ i₁ = 2) then (1 : Fin 2) else 0) ≠
      (if (i₂ = 0 ∨ i₂ = 2) then (1 : Fin 2) else 0) →
      i₂ = idx (by decide) (i₁.val + 1) ∨ i₁ = idx (by decide) (i₂.val + 1) := by decide
  refine relCharged_of_cosupply N U P2 b par (univ \ (U ∪ H)) l ∅ (fun _ => ∅) ?_ ?_ ?_
  · intro j hj hp
    have hj4 : j < 4 := by simpa [l] using hj
    simp only [l, List.getElem_ofFn, Function.comp_apply] at hp ⊢
    set i := π ⟨j, hj4⟩
    intro u hu
    by_cases huU : u ∈ U
    · exact mem_union_left _ huU
    · have huH : u ∈ H := outPar_none hp hu (mem_sdiff.mpr ⟨mem_univ u, huU⟩)
      exact mem_union_right _ (mem_union_right _ (hnb_opp i u hu huH))
  · intro j hj w hp
    have hj4 : j < 4 := by simpa [l] using hj
    simp only [l, List.getElem_ofFn, Function.comp_apply] at hp ⊢
    set i := π ⟨j, hj4⟩
    obtain ⟨hwN, hwU', hwH⟩ := outPar_some hp
    have hwU : w ∉ U := (mem_sdiff.mp hwU').2
    refine ⟨mem_sdiff.mpr ⟨mem_univ w, fun h => (mem_union.mp h).elim hwU hwH⟩, ?_, empty_subset _⟩
    intro u hu
    by_cases huU : u ∈ U
    · exact mem_union_left _ huU
    · by_cases huH : u ∈ H
      · exact mem_union_right _ (mem_insert_of_mem (mem_union_right _ (hnb_opp i u hu huH)))
      · have huw : u = w := hout1 i u w hu hwN huU huH hwU hwH
        subst huw
        exact mem_union_right _ (mem_insert_self _ _)
  · intro j j' hjj hj' w h1 h2
    have hj4 : j < 4 := by have : j' < l.length := hj'; simp [l] at this; omega
    have hj'4 : j' < 4 := by simpa [l] using hj'
    simp only [l, List.getElem_ofFn, Function.comp_apply] at h1 h2 ⊢
    obtain ⟨hw1, hwU', hwH⟩ := outPar_some h1
    obtain ⟨hw2, -, -⟩ := outPar_some h2
    have hwU : w ∉ U := (mem_sdiff.mp hwU').2
    set i₁ := π ⟨j, hj4⟩
    set i₂ := π ⟨j', hj'4⟩
    by_contra hne
    rw [hb_val, hb_val] at hne
    rcases hadj4 i₁ i₂ hne with hij | hji
    · rw [hij] at hw2; exact hTT i₁ w hwU hwH hw1 hw2
    · rw [hji] at hw1; exact hTT i₂ w hwU hwH hw2 hw1

end FourCycle

section Ge5Schedule

variable {V : Type*} [DecidableEq V]

/-- Two-sided arc-expansion permutation `[1, 2, 0, L - 1, L - 2, …, 4, 3]` for `L ≥ 5`. -/
def dcPerm {L : ℕ} (hL : 5 ≤ L) (j : Fin L) : Fin L :=
  if h0 : j.val = 0 then ⟨1, by omega⟩
  else if h1 : j.val = 1 then ⟨2, by omega⟩
  else if h2 : j.val = 2 then ⟨0, by omega⟩
  else ⟨L + 2 - j.val, by have := j.isLt; omega⟩

/-- Explicit inverse of `dcPerm`. -/
def dcInv {L : ℕ} (hL : 5 ≤ L) (k : Fin L) : Fin L :=
  if h0 : k.val = 0 then ⟨2, by omega⟩
  else if h1 : k.val = 1 then ⟨0, by omega⟩
  else if h2 : k.val = 2 then ⟨1, by omega⟩
  else ⟨L + 2 - k.val, by have := k.isLt; omega⟩

@[simp]
theorem dcPerm_zero {L : ℕ} (hL : 5 ≤ L) (h : 0 < L) :
    dcPerm hL ⟨0, h⟩ = ⟨1, by omega⟩ := by simp [dcPerm]

@[simp]
theorem dcPerm_one {L : ℕ} (hL : 5 ≤ L) (h : 1 < L) :
    dcPerm hL ⟨1, h⟩ = ⟨2, by omega⟩ := by simp [dcPerm]

@[simp]
theorem dcPerm_two {L : ℕ} (hL : 5 ≤ L) (h : 2 < L) :
    dcPerm hL ⟨2, h⟩ = ⟨0, by omega⟩ := by simp [dcPerm]

theorem dcPerm_of_ge3 {L : ℕ} (hL : 5 ≤ L) {j : Fin L} (hj3 : 3 ≤ j.val) :
    dcPerm hL j = ⟨L + 2 - j.val, by have := j.isLt; omega⟩ := by
  unfold dcPerm
  split_ifs <;> omega

theorem dcInv_of_ge3 {L : ℕ} (hL : 5 ≤ L) {k : Fin L} (hk3 : 3 ≤ k.val) :
    dcInv hL k = ⟨L + 2 - k.val, by have := k.isLt; omega⟩ := by
  unfold dcInv
  split_ifs <;> omega

theorem dcInv_dcPerm {L : ℕ} (hL : 5 ≤ L) (j : Fin L) :
    dcInv hL (dcPerm hL j) = j := by
  have hj := j.isLt
  rcases (show j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ 3 ≤ j.val by omega) with h0 | h1 | h2 | h3
  · rw [show j = ⟨0, by omega⟩ from Fin.ext h0]; simp [dcInv]
  · rw [show j = ⟨1, by omega⟩ from Fin.ext h1]; simp [dcInv]
  · rw [show j = ⟨2, by omega⟩ from Fin.ext h2]; simp [dcInv]
  · rw [dcPerm_of_ge3 hL h3, dcInv_of_ge3 hL (by simp; omega)]
    apply Fin.ext; simp; omega

theorem dcPerm_dcInv {L : ℕ} (hL : 5 ≤ L) (k : Fin L) :
    dcPerm hL (dcInv hL k) = k := by
  have hk := k.isLt
  rcases (show k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ 3 ≤ k.val by omega) with h0 | h1 | h2 | h3
  · rw [show k = ⟨0, by omega⟩ from Fin.ext h0]; simp [dcInv]
  · rw [show k = ⟨1, by omega⟩ from Fin.ext h1]; simp [dcInv]
  · rw [show k = ⟨2, by omega⟩ from Fin.ext h2]; simp [dcInv]
  · rw [dcInv_of_ge3 hL h3, dcPerm_of_ge3 hL (by simp; omega)]
    apply Fin.ext; simp; omega

theorem dcPerm_bijective {L : ℕ} (hL : 5 ≤ L) : Function.Bijective (dcPerm hL) :=
  ⟨Function.LeftInverse.injective (dcInv_dcPerm hL),
   Function.RightInverse.surjective (dcPerm_dcInv hL)⟩

/-- Consecutive positions `j ≥ 2` and `j + 1 < L` map to adjacent cycle vertices:
`dcPerm j = idx ((dcPerm (j + 1)) + 1)`. -/
theorem dcPerm_adj_succ {L : ℕ} (hL : 5 ≤ L) {j : ℕ} (hj2 : 2 ≤ j) (hj : j + 1 < L) :
    dcPerm hL ⟨j, by omega⟩ = idx (by omega) ((dcPerm hL ⟨j + 1, hj⟩).val + 1) := by
  rcases eq_or_lt_of_le hj2 with rfl | hgt
  · rw [dcPerm_two, dcPerm_of_ge3 hL (by simp)]
    apply Fin.ext
    simp only [idx_val]
    rw [show L + 2 - (2 + 1) + 1 = L by omega, Nat.mod_self]
  · rw [dcPerm_of_ge3 hL (by simp; omega), dcPerm_of_ge3 hL (by simp; omega)]
    apply Fin.ext
    simp only [idx_val]
    rw [show L + 2 - (j + 1) + 1 = L + 2 - j by omega, Nat.mod_eq_of_lt (by omega)]

/-- Record color assignment `Fin L → Fin (L + 1)` for `L ≥ 5`. -/
def dcCol {L : ℕ} (hL : 5 ≤ L) (op : Fin L → Option V) (k : Fin L) : Fin (L + 1) :=
  if k.val = 0 ∨ k.val = 2 then ⟨0, by omega⟩
  else if k.val = 1 then ⟨1, by omega⟩
  else if k.val = 3 then ⟨3, by omega⟩
  else if (op ⟨2, by omega⟩).isSome ∧ op (idx (by omega) (k.val + 1)) = op ⟨2, by omega⟩ then
    ⟨3, by omega⟩
  else ⟨k.val, by omega⟩

/-- Supplying record assignment `Fin L → Fin (L + 1)` for `L ≥ 5`. -/
def dcSupply {L : ℕ} (hL : 5 ≤ L) (op : Fin L → Option V) (k : Fin L) : Fin (L + 1) :=
  if k.val = 1 then ⟨0, by omega⟩
  else if k.val = 2 then ⟨3, by omega⟩
  else if k.val = 0 then dcCol hL op ⟨L - 1, by omega⟩
  else if k.val = 3 then ⟨L, by omega⟩
  else dcCol hL op ⟨k.val - 1, by omega⟩

theorem dcCol_four {L : ℕ} (hL : 5 ≤ L) {op : Fin L → Option V}
    (hrot : op ⟨2, by omega⟩ = none ∨ op ⟨2, by omega⟩ ≠ op (idx (by omega) 5)) :
    dcCol hL op ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
  unfold dcCol
  have hnot : ¬ ((op ⟨2, by omega⟩).isSome ∧ op (idx (by omega) 5) = op ⟨2, by omega⟩) := by
    rintro ⟨his, heq⟩
    rcases hrot with hnone | hne
    · rw [hnone] at his; simp at his
    · exact hne heq.symm
  simp [hnot]

theorem dcCol_ge4_val {L : ℕ} (hL : 5 ≤ L) (op : Fin L → Option V) {k : Fin L} (hk : 4 ≤ k.val) :
    (dcCol hL op k).val = 3 ∨ (dcCol hL op k).val = k.val := by
  unfold dcCol
  have h02 : ¬ (k.val = 0 ∨ k.val = 2) := by omega
  have h1 : ¬ (k.val = 1) := by omega
  have h3 : ¬ (k.val = 3) := by omega
  simp only [h02, h1, h3, ↓reduceIte]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem dcCol_eq_zero_iff {L : ℕ} (hL : 5 ≤ L) (op : Fin L → Option V) (k : Fin L) :
    dcCol hL op k = ⟨0, by omega⟩ ↔ (k.val = 0 ∨ k.val = 2) := by
  constructor
  · intro heq
    rcases (show (k.val = 0 ∨ k.val = 2) ∨ k.val = 1 ∨ k.val = 3 ∨ 4 ≤ k.val by omega) with
      h02 | h1 | h3 | h4
    · exact h02
    · unfold dcCol at heq; simp [h1] at heq
    · unfold dcCol at heq; simp [h3] at heq
    · rcases dcCol_ge4_val hL op h4 with h | h
      · rw [heq] at h; simp at h
      · rw [heq] at h; simp at h; omega
  · intro h02
    unfold dcCol; simp [h02]

theorem dcCol_ne_dcSupply {L : ℕ} (hL : 5 ≤ L) {op : Fin L → Option V}
    (hrot : op ⟨2, by omega⟩ = none ∨ op ⟨2, by omega⟩ ≠ op (idx (by omega) 5))
    (hadj_op : ∀ i : Fin L, ∀ w, op i = some w → op (idx (by omega) (i.val + 1)) ≠ some w)
    (k : Fin L) :
    dcCol hL op k ≠ dcSupply hL op k := by
  have hk := k.isLt
  rcases (show k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ 5 ≤ k.val by omega) with
    h0 | h1 | h2 | h3 | h4 | h5
  · rw [show k = ⟨0, by omega⟩ from Fin.ext h0]
    simp only [dcSupply, ↓reduceIte]
    have hc0 : (dcCol hL op ⟨0, by omega⟩).val = 0 := by simp [dcCol]
    rcases dcCol_ge4_val hL op (k := ⟨L - 1, by omega⟩) (by simp; omega) with h | h <;>
      (intro he; have hev := congrArg Fin.val he; simp at hev; rw [hc0, h] at hev; simp at hev; try omega)
  · rw [show k = ⟨1, by omega⟩ from Fin.ext h1]
    intro he; simp [dcCol, dcSupply] at he
  · rw [show k = ⟨2, by omega⟩ from Fin.ext h2]
    intro he; simp [dcCol, dcSupply] at he
  · rw [show k = ⟨3, by omega⟩ from Fin.ext h3]
    intro he
    have hval : (dcCol hL op ⟨3, by omega⟩).val = (dcSupply hL op ⟨3, by omega⟩).val :=
      congrArg Fin.val he
    simp [dcCol, dcSupply] at hval
    omega
  · rw [show k = ⟨4, by omega⟩ from Fin.ext h4]
    have hc4 := dcCol_four hL hrot
    have hs4 : dcSupply hL op ⟨4, by omega⟩ = ⟨3, by omega⟩ := by simp [dcSupply, dcCol]
    rw [hc4, hs4]; simp
  · -- `5 ≤ k.val < L`
    let k' : Fin L := ⟨k.val - 1, by omega⟩
    have hk'val : k'.val = k.val - 1 := rfl
    have hs : dcSupply hL op k = dcCol hL op k' := by
      unfold dcSupply
      simp [k', show k.val ≠ 1 by omega, show k.val ≠ 2 by omega, show k.val ≠ 0 by omega,
        show k.val ≠ 3 by omega]
    rw [hs]
    intro heq
    have hv1 := dcCol_ge4_val hL op (k := k) (by omega)
    have hv2 := dcCol_ge4_val hL op (k := k') (by omega)
    rw [hk'val] at hv2
    have hboth3 : (dcCol hL op k).val = 3 ∧ (dcCol hL op k').val = 3 := by
      rw [heq] at hv1
      rcases hv1 with h | h <;> rcases hv2 with h' | h' <;> omega
    -- Extract `op (idx (k + 1)) = op 2` and `op (idx (k' + 1)) = op 2`
    have hif1 : (op ⟨2, by omega⟩).isSome ∧ op (idx (by omega) (k.val + 1)) = op ⟨2, by omega⟩ := by
      by_contra hno
      have hval : (dcCol hL op k).val = k.val := by
        unfold dcCol
        have h02 : ¬ (k.val = 0 ∨ k.val = 2) := by omega
        have h1 : ¬ (k.val = 1) := by omega
        have h3 : ¬ (k.val = 3) := by omega
        simp only [h02, h1, h3, hno, ↓reduceIte]
      omega
    have hif2 : (op ⟨2, by omega⟩).isSome ∧ op (idx (by omega) (k'.val + 1)) = op ⟨2, by omega⟩ := by
      by_contra hno
      have hval : (dcCol hL op k').val = k'.val := by
        unfold dcCol
        have h02 : ¬ (k'.val = 0 ∨ k'.val = 2) := by omega
        have h1 : ¬ (k'.val = 1) := by omega
        have h3 : ¬ (k'.val = 3) := by omega
        simp only [h02, h1, h3, hno, ↓reduceIte]
      omega
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hif1.1
    have hk'_idx : idx (by omega) (k'.val + 1) = k := by
      apply Fin.ext
      simp only [idx_val, hk'val]
      rw [show k.val - 1 + 1 = k.val by omega, Nat.mod_eq_of_lt hk]
    have hopk : op k = some w := by
      have := hif2.2; rwa [hk'_idx, hw] at this
    have hopk1 : op (idx (by omega) (k.val + 1)) = some w := by
      have := hif1.2; rwa [hw] at this
    exact hadj_op k w hopk hopk1

theorem dcSupply_dcPerm_eq_dcCol_succ {L : ℕ} (hL : 5 ≤ L) (op : Fin L → Option V)
    {j : ℕ} (hj2 : 2 ≤ j) (hj : j + 1 < L) :
    dcSupply hL op (dcPerm hL ⟨j, by omega⟩) = dcCol hL op (dcPerm hL ⟨j + 1, hj⟩) := by
  rcases eq_or_lt_of_le hj2 with rfl | hgt
  · rw [dcPerm_two, dcPerm_of_ge3 hL (by simp)]
    simp [dcSupply, show L + 2 - (2 + 1) = L - 1 by omega]
  · rw [dcPerm_of_ge3 hL (by simp; omega), dcPerm_of_ge3 hL (by simp; omega)]
    unfold dcSupply
    simp only [show L + 2 - j ≠ 1 by omega, show L + 2 - j ≠ 2 by omega,
      show L + 2 - j ≠ 0 by omega, show L + 2 - j ≠ 3 by omega, ↓reduceIte]
    apply congrArg (dcCol hL op)
    apply Fin.ext
    simp only
    omega

/-- If `op (dcPerm j') = op 2 = some w` for `2 ≤ j' ≤ L - 2`, then `dcSupply (dcPerm j') = 3`. -/
theorem dcSupply_eq_three_of_op_eq_op2 {L : ℕ} (hL : 5 ≤ L) (op : Fin L → Option V)
    {j' : ℕ} (hj'2 : 2 ≤ j') (hj' : j' + 1 < L) {w : V}
    (hw2 : op ⟨2, by omega⟩ = some w) (hw' : op (dcPerm hL ⟨j', by omega⟩) = some w) :
    dcSupply hL op (dcPerm hL ⟨j', by omega⟩) = ⟨3, by omega⟩ := by
  rw [dcSupply_dcPerm_eq_dcCol_succ hL op hj'2 hj']
  set k := dcPerm hL ⟨j' + 1, hj'⟩
  have hk_ge3 : 3 ≤ k.val := by
    rw [show k = ⟨L + 2 - (j' + 1), by omega⟩ from dcPerm_of_ge3 hL (by simp; omega)]
    simp only; omega
  rcases eq_or_lt_of_le hk_ge3 with hk3 | hk4
  · have hkeq : k = ⟨3, by omega⟩ := Fin.ext hk3.symm
    rw [hkeq]; simp [dcCol]
  · have hadj := dcPerm_adj_succ hL hj'2 hj'
    unfold dcCol
    have hif : (op ⟨2, by omega⟩).isSome ∧ op (idx (by omega) (k.val + 1)) = op ⟨2, by omega⟩ := by
      refine ⟨by simp [hw2], ?_⟩
      rw [← hadj, hw', hw2]
    have h02 : ¬ (k.val = 0 ∨ k.val = 2) := by omega
    have h1 : ¬ (k.val = 1) := by omega
    have h3 : ¬ (k.val = 3) := by omega
    simp only [h02, h1, h3, hif.1, hif.2, and_self, ↓reduceIte]

/-- Explicit `(L + 1)`-record `PieceCert` for a rotated chordless digon cycle of length `L ≥ 5`
satisfying `op 2 = none ∨ op 2 ≠ op (idx 5)`. -/
noncomputable def digonCycleGe5_pieceCert [Fintype V] {N : V → Finset V} {U : Finset V}
    {L : ℕ} (hL : 5 ≤ L) (f : Fin L → V) (hf : Function.Injective f)
    (hTT : ∀ i : Fin L, ∀ w, w ∉ U → w ∉ univ.image f →
      w ∈ N (f i) → w ∈ N (f (idx (by omega) (i.val + 1))) → False)
    (hno_chord : ∀ i j : Fin L, f j ∈ N (f i) →
      j = idx (by omega) (i.val + 1) ∨ j = idx (by omega) (i.val + L - 1))
    (hout1 : ∀ i : Fin L, ∀ w₁ w₂, w₁ ∈ N (f i) → w₂ ∈ N (f i) →
      w₁ ∉ U → w₁ ∉ univ.image f → w₂ ∉ U → w₂ ∉ univ.image f → w₁ = w₂)
    (hrot : outPar N (univ \ U) (univ.image f) (f ⟨2, by omega⟩) = none ∨
      outPar N (univ \ U) (univ.image f) (f ⟨2, by omega⟩) ≠
        outPar N (univ \ U) (univ.image f) (f (idx (by omega) 5))) :
    PieceCert N U (univ.image f) := by
  classical
  have hL0 : 0 < L := by omega
  let H := univ.image f
  let par : V → Option V := outPar N (univ \ U) H
  let op : Fin L → Option V := fun i => par (f i)
  have hadj_op : ∀ i : Fin L, ∀ w, op i = some w → op (idx hL0 (i.val + 1)) ≠ some w := by
    intro i w h1 h2
    obtain ⟨hw1, hwU', hwH⟩ := outPar_some h1
    obtain ⟨hw2, -, -⟩ := outPar_some h2
    exact hTT i w ((mem_sdiff.mp hwU').2) hwH hw1 hw2
  haveI : Nonempty (Fin L) := ⟨⟨0, hL0⟩⟩
  let pos : V → Fin L := Function.invFun f
  have hpos_f : ∀ i : Fin L, pos (f i) = i := Function.leftInverse_invFun hf
  let a : V → Fin (L + 1) := fun v => dcCol hL op (pos v)
  let b : V → Fin (L + 1) := fun v => dcSupply hL op (pos v)
  let P : Fin (L + 1) → Finset V :=
    fun r => (univ.filter (fun i : Fin L => dcCol hL op i = r)).image f
  let g : Fin L → V := fun j => f (dcPerm hL j)
  let l : List V := List.ofFn g
  -- Cycle-neighbour step coverage at position `j`
  have cov_cyc : ∀ (j : ℕ) (hj : j < L) (s : Fin L),
      (s = idx hL0 ((dcPerm hL ⟨j, hj⟩).val + 1) ∨
       s = idx hL0 ((dcPerm hL ⟨j, hj⟩).val + L - 1)) →
      f s ∈ rev ∅ l j ∪ P (dcSupply hL op (dcPerm hL ⟨j, hj⟩)) := by
    intro j hj s hs
    have memP : ∀ k : Fin L, dcCol hL op k = dcSupply hL op (dcPerm hL ⟨j, hj⟩) →
        f k ∈ P (dcSupply hL op (dcPerm hL ⟨j, hj⟩)) :=
      fun k hk => mem_image.mpr ⟨k, mem_filter.mpr ⟨mem_univ k, hk⟩, rfl⟩
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ (3 ≤ j ∧ j + 1 < L) ∨ j = L - 1 by omega) with
      rfl | rfl | rfl | ⟨hj3, hjlt⟩ | rfl
    · -- `j = 0`, `dcPerm 0 = 1`, `s ∈ {2, 0}`, both in `P 0`
      apply mem_union_right
      rcases hs with rfl | rfl
      · refine memP _ ?_
        rw [dcPerm_zero]
        have hs2 : idx hL0 (1 + 1) = ⟨2, by omega⟩ := idx_of_lt hL0 (by omega)
        rw [hs2]; simp [dcCol, dcSupply]
      · refine memP _ ?_
        rw [dcPerm_zero]
        have hs0 : idx hL0 (1 + L - 1) = ⟨0, by omega⟩ := by
          apply Fin.ext; simp [idx_val, show 1 + L - 1 = L by omega]
        rw [hs0]; simp [dcCol, dcSupply]
    · -- `j = 1`, `dcPerm 1 = 2`, `s ∈ {3, 1}`: `1 = dcPerm 0 ∈ rev`, `3 ∈ P 3`
      rcases hs with rfl | rfl
      · apply mem_union_right
        refine memP _ ?_
        rw [dcPerm_one]
        have hs3 : idx hL0 (2 + 1) = ⟨3, by omega⟩ := idx_of_lt hL0 (by omega)
        rw [hs3]; simp [dcCol, dcSupply]
      · apply mem_union_left
        rw [dcPerm_one]
        have hs1 : idx hL0 (2 + L - 1) = dcPerm hL ⟨0, by omega⟩ := by
          rw [dcPerm_zero]
          apply Fin.ext
          simp only [idx_val]
          rw [show 2 + L - 1 = L + 1 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [hs1]
        exact mem_rev_ofFn g ⟨0, by omega⟩ (by simp)
    · -- `j = 2`, `dcPerm 2 = 0`, `s ∈ {1, L - 1}`: `1 = dcPerm 0 ∈ rev`, `L - 1 ∈ P (dcCol (L - 1))`
      rcases hs with rfl | rfl
      · apply mem_union_left
        rw [dcPerm_two]
        have hs1 : idx hL0 (0 + 1) = dcPerm hL ⟨0, by omega⟩ := by
          rw [dcPerm_zero]
          apply Fin.ext; simp [idx_val, Nat.mod_eq_of_lt (show 1 < L by omega)]
        rw [hs1]
        exact mem_rev_ofFn g ⟨0, by omega⟩ (by simp)
      · apply mem_union_right
        refine memP _ ?_
        rw [dcPerm_two]
        have hsL : idx hL0 (0 + L - 1) = ⟨L - 1, by omega⟩ := by
          rw [show 0 + L - 1 = L - 1 by omega]; exact idx_of_lt hL0 (by omega)
        rw [hsL]; simp [dcSupply]
    · -- `3 ≤ j` and `j + 1 < L`, `dcPerm j = L + 2 - j` (`4 ≤ i ≤ L - 1`)
      have hperm : dcPerm hL ⟨j, hj⟩ = ⟨L + 2 - j, by omega⟩ := dcPerm_of_ge3 hL hj3
      rcases hs with rfl | rfl
      · -- `s = idx ((L + 2 - j) + 1)`: revealed at `2` (if `j = 3`) or `j - 1` (if `j ≥ 4`)
        apply mem_union_left
        rw [hperm]
        rcases eq_or_lt_of_le hj3 with rfl | hj4
        · have hs0 : idx hL0 (L + 2 - 3 + 1) = dcPerm hL ⟨2, by omega⟩ := by
            rw [dcPerm_two]
            apply Fin.ext; simp only [idx_val]; rw [show L + 2 - 3 + 1 = L by omega, Nat.mod_self]
          rw [hs0]
          exact mem_rev_ofFn g ⟨2, by omega⟩ (by simp)
        · have hs_prev : idx hL0 (L + 2 - j + 1) = dcPerm hL ⟨j - 1, by omega⟩ := by
            rw [dcPerm_of_ge3 hL (by simp; omega)]
            apply Fin.ext
            simp only [idx_val]
            rw [show L + 2 - j + 1 = L + 2 - (j - 1) by omega, Nat.mod_eq_of_lt (by omega)]
          rw [hs_prev]
          exact mem_rev_ofFn g ⟨j - 1, by omega⟩ (by simp; omega)
      · -- `s = idx ((L + 2 - j) + L - 1) = dcPerm (j + 1)`, supplied by `dcSupply (dcPerm j)`
        apply mem_union_right
        refine memP _ ?_
        rw [dcSupply_dcPerm_eq_dcCol_succ hL op (by omega) hjlt]
        congr 1
        rw [hperm, dcPerm_of_ge3 hL (by simp; omega)]
        apply Fin.ext
        simp only [idx_val]
        rw [show L + 2 - j + L - 1 = L + (L + 2 - (j + 1)) by omega, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by omega)]
    · -- `j = L - 1`, `dcPerm (L - 1) = 3`, `s ∈ {4, 2}`: `4 = dcPerm (L - 2)` and `2 = dcPerm 1` both in `rev`!
      apply mem_union_left
      have hperm : dcPerm hL ⟨L - 1, hj⟩ = ⟨3, by omega⟩ := by
        rw [dcPerm_of_ge3 hL (by simp; omega)]
        apply Fin.ext; simp; omega
      rw [hperm] at hs
      rcases hs with rfl | rfl
      · have hs4 : idx hL0 (3 + 1) = dcPerm hL ⟨L - 2, by omega⟩ := by
          rw [dcPerm_of_ge3 hL (by simp; omega)]
          apply Fin.ext
          simp only [idx_val]
          rw [Nat.mod_eq_of_lt (show 4 < L by omega)]; omega
        rw [hs4]
        exact mem_rev_ofFn g ⟨L - 2, by omega⟩ (by simp; omega)
      · have hs2 : idx hL0 (3 + L - 1) = dcPerm hL ⟨1, by omega⟩ := by
          rw [dcPerm_one]
          apply Fin.ext
          simp only [idx_val]
          rw [show 3 + L - 1 = L + 2 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [hs2]
        exact mem_rev_ofFn g ⟨1, by omega⟩ (by simp; omega)
  refine
    { m := L + 1
      P := P
      disj := by
        intro r₁ r₂ hne
        rw [disjoint_left]
        intro v hv₁ hv₂
        simp only [P, mem_image, mem_filter, mem_univ, true_and] at hv₁ hv₂
        obtain ⟨i₁, hi₁, rfl⟩ := hv₁
        obtain ⟨i₂, hi₂, he⟩ := hv₂
        cases hf he
        exact hne (hi₁.symm.trans hi₂)
      cover := by
        ext v
        simp only [P, mem_biUnion, mem_univ, true_and, mem_image, mem_filter]
        exact ⟨fun ⟨_, i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨dcCol hL op i, i, rfl, hi⟩⟩
      l := l
      hl := by
        ext v
        simp only [l, g, List.mem_toFinset, List.mem_ofFn, mem_image, mem_univ, true_and]
        exact ⟨fun ⟨j, hj⟩ => ⟨dcPerm hL j, hj⟩, fun ⟨i, hi⟩ =>
          ⟨dcInv hL i, by rw [dcPerm_dcInv]; exact hi⟩⟩
      a := a
      b := b
      par := par
      own := by
        intro v hv
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
        simp only [g, a, hpos_f, P, mem_image, mem_filter, mem_univ, true_and]
        exact ⟨dcPerm hL j, rfl, rfl⟩
      ab := by
        intro v hv
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
        simp only [g, a, b, hpos_f]
        exact dcCol_ne_dcSupply hL hrot hadj_op (dcPerm hL j)
      charged := ?_ }
  refine relCharged_of_nested N U P b par (univ \ (U ∪ H)) l ∅ (fun _ => ∅) ?_ ?_ ?_
  · -- `par = none`
    intro j hj hp
    have hjL : j < L := by simpa [l] using hj
    simp only [l, g, List.getElem_ofFn, b, hpos_f] at hp ⊢
    intro u hu
    by_cases huU : u ∈ U
    · exact mem_union_left _ huU
    · have huH : u ∈ H := outPar_none hp hu (mem_sdiff.mpr ⟨mem_univ u, huU⟩)
      obtain ⟨s, -, rfl⟩ := mem_image.mp huH
      exact mem_union_right _ (cov_cyc j hjL s (hno_chord _ _ hu))
  · -- `par = some w`
    intro j hj w hp
    have hjL : j < L := by simpa [l] using hj
    simp only [l, g, List.getElem_ofFn, b, hpos_f] at hp ⊢
    obtain ⟨hwN, hwU', hwH⟩ := outPar_some hp
    have hwU : w ∉ U := (mem_sdiff.mp hwU').2
    refine ⟨mem_sdiff.mpr ⟨mem_univ w, fun h => (mem_union.mp h).elim hwU hwH⟩, ?_, empty_subset _⟩
    intro u hu
    by_cases huU : u ∈ U
    · exact mem_union_left _ huU
    · by_cases huH : u ∈ H
      · obtain ⟨s, -, rfl⟩ := mem_image.mp huH
        exact mem_union_right _ (mem_insert_of_mem (cov_cyc j hjL s (hno_chord _ _ hu)))
      · have huw : u = w := hout1 _ u w hu hwN huU huH hwU hwH
        subst huw
        exact mem_union_right _ (mem_insert_self _ _)
  · -- Nested supply for `j < j'` sharing `par = some w`
    intro j j' hjj hj' w hp hp'
    have hj'L : j' < L := by simpa [l] using hj'
    have hjL : j < L := lt_trans hjj hj'L
    simp only [l, g, List.getElem_ofFn, b, hpos_f] at hp hp' ⊢
    change op (dcPerm hL ⟨j, hjL⟩) = some w at hp
    change op (dcPerm hL ⟨j', hj'L⟩) = some w at hp'
    rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj2
    · -- `j = 0`: `dcPerm 0 = 1`, so `j' ≠ 1` (`dcPerm 1 = 2`) and `j' ≠ 2` (`dcPerm 2 = 0`); hence `3 ≤ j'`, and `P 0 = {f 0, f 2} ⊆ rev ∅ l j'`
      have hne1 : j' ≠ 1 := by
        rintro rfl
        have h1 : dcPerm hL ⟨0, hjL⟩ = ⟨1, by omega⟩ := dcPerm_zero hL hjL
        have h2 : dcPerm hL ⟨1, hj'L⟩ = idx hL0 (1 + 1) := by
          rw [dcPerm_one]; apply Fin.ext; simp [idx_val, Nat.mod_eq_of_lt (show 2 < L by omega)]
        rw [h1] at hp; rw [h2] at hp'
        exact hadj_op ⟨1, by omega⟩ w hp hp'
      have hne2 : j' ≠ 2 := by
        rintro rfl
        have h0 : dcPerm hL ⟨2, hj'L⟩ = ⟨0, by omega⟩ := dcPerm_two hL hj'L
        have h1 : dcPerm hL ⟨0, hjL⟩ = idx hL0 (0 + 1) := by
          rw [dcPerm_zero]; apply Fin.ext; simp [idx_val, Nat.mod_eq_of_lt (show 1 < L by omega)]
        rw [h0] at hp'; rw [h1] at hp
        exact hadj_op ⟨0, by omega⟩ w hp' hp
      have hj'3 : 3 ≤ j' := by omega
      have hsup0 : dcSupply hL op (dcPerm hL ⟨0, hjL⟩) = ⟨0, by omega⟩ := by simp [dcSupply]
      rw [hsup0]
      intro v hv
      apply mem_union_left
      simp only [P, mem_image, mem_filter, mem_univ, true_and] at hv
      obtain ⟨k, hk, rfl⟩ := hv
      rcases (dcCol_eq_zero_iff hL op k).mp hk with hk0 | hk2
      · have hkeq : f k = g ⟨2, by omega⟩ := by
          dsimp only [g]; rw [dcPerm_two]; congr 1; exact Fin.ext hk0
        rw [hkeq]
        exact mem_rev_ofFn g ⟨2, by omega⟩ (by simp; omega)
      · have hkeq : f k = g ⟨1, by omega⟩ := by
          dsimp only [g]; rw [dcPerm_one]; congr 1; exact Fin.ext hk2
        rw [hkeq]
        exact mem_rev_ofFn g ⟨1, by omega⟩ (by simp; omega)
    · -- `j = 1`: `dcPerm 1 = 2`, so `op 2 = some w`, `j' ≠ L - 1` (`dcPerm (L - 1) = 3`), and `dcSupply (dcPerm j') = 3 = dcSupply 2`
      rw [dcPerm_one] at hp
      have hj'lt : j' + 1 < L := by
        by_contra hge
        have hj'eq : j' = L - 1 := by omega
        have hperm3 : dcPerm hL ⟨j', hj'L⟩ = idx hL0 (2 + 1) := by
          rw [dcPerm_of_ge3 hL (by simp; omega)]
          apply Fin.ext
          simp only [hj'eq, idx_val]
          rw [Nat.mod_eq_of_lt (show 3 < L by omega)]; omega
        rw [hperm3] at hp'
        exact hadj_op ⟨2, by omega⟩ w hp hp'
      have hsup1 : dcSupply hL op (dcPerm hL ⟨1, hjL⟩) = ⟨3, by omega⟩ := by simp [dcSupply]
      have hsup' := dcSupply_eq_three_of_op_eq_op2 hL op (by omega) hj'lt hp hp'
      rw [hsup1, hsup']
      exact subset_union_right
    · -- `2 ≤ j < j' < L`: first rule out `j' = j + 1`
      have hnej1 : j' ≠ j + 1 := by
        rintro rfl
        have hadj := dcPerm_adj_succ hL hj2 hj'L
        rw [hadj] at hp
        exact hadj_op (dcPerm hL ⟨j + 1, hj'L⟩) w hp' hp
      have hj1lt : j + 1 < j' := by omega
      have hsupj := dcSupply_dcPerm_eq_dcCol_succ hL op hj2 (lt_trans hj1lt hj'L)
      rw [hsupj]
      set k₀ := dcPerm hL ⟨j + 1, lt_trans hj1lt hj'L⟩
      have hk₀_ge4 : 4 ≤ k₀.val := by
        rw [show k₀ = ⟨L + 2 - (j + 1), by omega⟩ from dcPerm_of_ge3 hL (by simp; omega)]
        simp only; omega
      by_cases hc3 : dcCol hL op k₀ = ⟨3, by omega⟩
      · -- `dcCol k₀ = 3` with `k₀ ≥ 4` forces `op (dcPerm j) = op 2`, hence `op 2 = some w`, and `dcSupply (dcPerm j') = 3`!
        have hif : (op ⟨2, by omega⟩).isSome ∧ op (idx hL0 (k₀.val + 1)) = op ⟨2, by omega⟩ := by
          by_contra hno
          have hval : (dcCol hL op k₀).val = k₀.val := by
            unfold dcCol
            have h02 : ¬ (k₀.val = 0 ∨ k₀.val = 2) := by omega
            have h1 : ¬ (k₀.val = 1) := by omega
            have h3 : ¬ (k₀.val = 3) := by omega
            simp only [h02, h1, h3, hno, ↓reduceIte]
          rw [hc3] at hval; simp at hval; omega
        have hadj := dcPerm_adj_succ hL hj2 (lt_trans hj1lt hj'L)
        have hop2 : op ⟨2, by omega⟩ = some w := by
          rw [← hif.2, ← hadj, hp]
        have hj'lt : j' + 1 < L := by
          by_contra hge
          have hj'eq : j' = L - 1 := by omega
          have hperm3 : dcPerm hL ⟨j', hj'L⟩ = idx hL0 (2 + 1) := by
            rw [dcPerm_of_ge3 hL (by simp; omega)]
            apply Fin.ext
            simp only [hj'eq, idx_val]
            rw [Nat.mod_eq_of_lt (show 3 < L by omega)]; omega
          rw [hperm3] at hp'
          exact hadj_op ⟨2, by omega⟩ w hop2 hp'
        rw [hc3, dcSupply_eq_three_of_op_eq_op2 hL op (by omega) hj'lt hop2 hp']
        exact subset_union_right
      · -- `dcCol k₀ ≠ 3` with `k₀ ≥ 4`, so `P (dcCol k₀) = {f k₀} = {g (j + 1)} ⊆ rev ∅ l j'`
        have hval0 : (dcCol hL op k₀).val = k₀.val := by
          rcases dcCol_ge4_val hL op hk₀_ge4 with h3 | hk
          · exact absurd (Fin.ext h3) hc3
          · exact hk
        intro v hv
        apply mem_union_left
        simp only [P, mem_image, mem_filter, mem_univ, true_and] at hv
        obtain ⟨k, hk, rfl⟩ := hv
        have hkeq : k = k₀ := by
          have hkval : (dcCol hL op k).val = k₀.val := by rw [hk, hval0]
          rcases (show (k.val = 0 ∨ k.val = 2) ∨ k.val = 1 ∨ k.val = 3 ∨ 4 ≤ k.val by omega) with
            h02 | h1 | h3 | h4
          · unfold dcCol at hkval; simp [h02] at hkval; omega
          · unfold dcCol at hkval; simp [h1] at hkval; omega
          · unfold dcCol at hkval; simp [h3] at hkval; omega
          · rcases dcCol_ge4_val hL op h4 with hc3' | hck
            · rw [hc3'] at hkval; omega
            · exact Fin.ext (hck.symm.trans hkval)
        rw [hkeq]
        exact mem_rev_ofFn g ⟨j + 1, lt_trans hj1lt hj'L⟩ hj1lt

end Ge5Schedule

section Dichotomy

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- If `¬ IsStride3Cycle N U f` on a cycle of length `L ≥ 4` with `TTFree` and at most one outside
parent per vertex, there is a position `s₀ : Fin L` where `op s₀ = none ∨ op s₀ ≠ op (idx (s₀ + 3))`. -/
theorem exists_non_stride3_pos {N : V → Finset V} {U : Finset V} {L : ℕ} (hL : 4 ≤ L)
    (f : Fin L → V)
    (hTT : ∀ i : Fin L, ∀ w, w ∉ U → w ∉ univ.image f →
      w ∈ N (f i) → w ∈ N (f (idx (by omega) (i.val + 1))) → False)
    (hnot3 : ¬ IsStride3Cycle N U f) :
    ∃ s₀ : Fin L, outPar N (univ \ U) (univ.image f) (f s₀) = none ∨
      outPar N (univ \ U) (univ.image f) (f s₀) ≠
        outPar N (univ \ U) (univ.image f) (f (idx (by omega) (s₀.val + 3))) := by
  classical
  have hL0 : 0 < L := by omega
  let H := univ.image f
  let op : Fin L → Option V := fun i => outPar N (univ \ U) H (f i)
  by_contra hall
  push Not at hall
  have hall' : ∀ s : Fin L, op s ≠ none ∧ op s = op (idx hL0 (s.val + 3)) := hall
  have his : ∀ i : Fin L, (op i).isSome := by
    intro i
    cases h : op i with
    | none => exact absurd h (hall' i).1
    | some _ => rfl
  have hstep3 : ∀ (i : Fin L) (q : ℕ), op i = op (idx hL0 (i.val + 3 * q)) := by
    intro i q
    induction q with
    | zero => rw [Nat.mul_zero, Nat.add_zero, idx_self]
    | succ q ih =>
      rw [ih, (hall' (idx hL0 (i.val + 3 * q))).2]
      apply congrArg op
      apply Fin.ext
      simp only [idx_val, Nat.mod_add_mod]
      rw [show i.val + 3 * q + 3 = i.val + 3 * (q + 1) by omega]
  have hdvd3 : 3 ∣ L := by
    by_contra hndvd
    have hop01 : op ⟨0, hL0⟩ = op (idx hL0 1) := by
      rcases (show L % 3 = 1 ∨ L % 3 = 2 by omega) with hm1 | hm2
      · have hq := hstep3 ⟨0, hL0⟩ (2 * (L / 3) + 1)
        have hidx : idx hL0 (0 + 3 * (2 * (L / 3) + 1)) = idx hL0 1 := by
          apply Fin.ext
          simp only [idx_val]
          have : 0 + 3 * (2 * (L / 3) + 1) = 1 + L * 2 := by omega
          rw [this, Nat.add_mul_mod_self_left]
        rwa [hidx] at hq
      · have hq := hstep3 ⟨0, hL0⟩ (L / 3 + 1)
        have hidx : idx hL0 (0 + 3 * (L / 3 + 1)) = idx hL0 1 := by
          apply Fin.ext
          simp only [idx_val]
          have : 0 + 3 * (L / 3 + 1) = 1 + L * 1 := by omega
          rw [this, Nat.add_mul_mod_self_left]
        rwa [hidx] at hq
    obtain ⟨w, hw0⟩ := Option.isSome_iff_exists.mp (his ⟨0, hL0⟩)
    have hw1 : op (idx hL0 1) = some w := hop01.symm.trans hw0
    obtain ⟨hwN0, hwU', hwH⟩ := outPar_some hw0
    obtain ⟨hwN1, -, -⟩ := outPar_some hw1
    exact hTT ⟨0, hL0⟩ w ((mem_sdiff.mp hwU').2) hwH hwN0 (by simpa using hwN1)
  -- Since `3 ∣ L`, `op ⟨0⟩, op ⟨1⟩, op ⟨2⟩` form a stride-3 hub triple!
  let w : Fin 3 → V := fun r => (Option.isSome_iff_exists.mp (his ⟨r.val, by omega⟩)).choose
  have hw_op : ∀ r : Fin 3, op ⟨r.val, by omega⟩ = some (w r) :=
    fun r => (Option.isSome_iff_exists.mp (his ⟨r.val, by omega⟩)).choose_spec
  apply hnot3
  refine ⟨hdvd3, w, ?_, ?_⟩
  · intro r
    obtain ⟨_, hwU', hwH⟩ := outPar_some (hw_op r)
    exact ⟨(mem_sdiff.mp hwU').2, hwH⟩
  · intro i
    have hi_eq : i = idx hL0 ((i.val % 3) + 3 * (i.val / 3)) := by
      apply Fin.ext
      simp only [idx_val]
      rw [show i.val % 3 + 3 * (i.val / 3) = i.val by omega, Nat.mod_eq_of_lt i.isLt]
    have hop_i : op i = some (w ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩) := by
      have hst := hstep3 ⟨i.val % 3, by omega⟩ (i.val / 3)
      rw [← hi_eq] at hst
      exact hst.symm.trans (hw_op ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩)
    exact (outPar_some hop_i).1

/-- **Theorem DC (sufficiency + record bound).** Every non-stride-3 chordless digon cycle of length
`L ≥ 4` (with `TTFree` and at most one active outside parent per vertex) admits a `PieceCert` with
at most `L + 1` records. -/
theorem digonCycle_pieceCert_of_not_stride3 {N : V → Finset V} {U : Finset V} {L : ℕ}
    (hL : 4 ≤ L) {f : Fin L → V} (hf : Function.Injective f)
    (hTT : ∀ i : Fin L, ∀ w, w ∉ U → w ∉ univ.image f →
      w ∈ N (f i) → w ∈ N (f (idx (by omega) (i.val + 1))) → False)
    (hno_chord : ∀ i j : Fin L, f j ∈ N (f i) →
      j = idx (by omega) (i.val + 1) ∨ j = idx (by omega) (i.val + L - 1))
    (hout1 : ∀ i : Fin L, ∀ w₁ w₂, w₁ ∈ N (f i) → w₂ ∈ N (f i) →
      w₁ ∉ U → w₁ ∉ univ.image f → w₂ ∉ U → w₂ ∉ univ.image f → w₁ = w₂)
    (hnot3 : ¬ IsStride3Cycle N U f) :
    ∃ c : PieceCert N U (univ.image f), c.m ≤ L + 1 := by
  rcases eq_or_lt_of_le hL with h4 | h5
  · subst h4
    exact ⟨digonCycle4_pieceCert f hf hTT hno_chord hout1, by simp [digonCycle4_pieceCert]⟩
  · have hL5 : 5 ≤ L := h5
    have hL0 : 0 < L := by omega
    obtain ⟨s₀, hs₀⟩ := exists_non_stride3_pos hL f hTT hnot3
    -- Rotate `f` so that `f' 2 = f s₀` and `f' (idx 5) = f (idx (s₀ + 3))`
    let sh := (s₀.val + L - 2) % L
    have hsh : sh < L := Nat.mod_lt _ hL0
    let rot : Fin L → Fin L := fun i => idx hL0 (s₀.val + L - 2 + i.val)
    let rotInv : Fin L → Fin L := fun j => idx hL0 (j.val + L - sh)
    have hrot_left : Function.LeftInverse rotInv rot := by
      intro i
      apply Fin.ext
      simp only [rot, rotInv, idx_val]
      have h1 : (s₀.val + L - 2 + i.val) % L = (sh + i.val) % L :=
        (Nat.mod_add_mod (s₀.val + L - 2) L i.val).symm
      rw [h1]
      rcases Nat.lt_or_ge (sh + i.val) L with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt, show sh + i.val + L - sh = L + i.val by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt i.isLt]
      · have hlt2 : sh + i.val - L < L := by omega
        have hmod : (sh + i.val) % L = sh + i.val - L := by
          conv_lhs => rw [show sh + i.val = L + (sh + i.val - L) by omega]
          rw [Nat.add_mod_left, Nat.mod_eq_of_lt hlt2]
        rw [hmod, show sh + i.val - L + L - sh = i.val by omega, Nat.mod_eq_of_lt i.isLt]
    have hrot_right : Function.RightInverse rotInv rot := by
      intro j
      apply Fin.ext
      simp only [rot, rotInv, idx_val]
      have h1 : (s₀.val + L - 2 + (j.val + L - sh) % L) % L = (sh + (j.val + L - sh)) % L := by
        rw [← Nat.mod_add_mod (s₀.val + L - 2) L ((j.val + L - sh) % L), Nat.add_mod_mod]
      rw [h1, show sh + (j.val + L - sh) = L + j.val by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt j.isLt]
    let f' : Fin L → V := f ∘ rot
    have hf' : Function.Injective f' := hf.comp hrot_left.injective
    have himg : univ.image f' = univ.image f := by
      ext v
      simp only [f', Function.comp_apply, mem_image, mem_univ, true_and]
      exact ⟨fun ⟨i, hi⟩ => ⟨rot i, hi⟩, fun ⟨j, hj⟩ => ⟨rotInv j, by rw [hrot_right]; exact hj⟩⟩
    have hrot_add : ∀ (i : Fin L) (d : ℕ),
        rot (idx hL0 (i.val + d)) = idx hL0 ((rot i).val + d) := by
      intro i d
      apply Fin.ext
      simp only [rot, idx_val, Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]
    have hrot2 : rot ⟨2, by omega⟩ = s₀ := by
      apply Fin.ext
      simp only [rot, idx_val]
      rw [show s₀.val + L - 2 + 2 = L + s₀.val by omega, Nat.add_mod_left, Nat.mod_eq_of_lt s₀.isLt]
    have hrot5 : rot (idx hL0 5) = idx hL0 (s₀.val + 3) := by
      have := hrot_add ⟨2, by omega⟩ 3
      rwa [hrot2] at this
    have hTT' : ∀ i : Fin L, ∀ w, w ∉ U → w ∉ univ.image f' →
        w ∈ N (f' i) → w ∈ N (f' (idx hL0 (i.val + 1))) → False := by
      intro i w hwU hwH h1 h2
      rw [himg] at hwH
      exact hTT (rot i) w hwU hwH h1 (by simpa [f', hrot_add i 1] using h2)
    have hno_chord' : ∀ i j : Fin L, f' j ∈ N (f' i) →
        j = idx hL0 (i.val + 1) ∨ j = idx hL0 (i.val + L - 1) := by
      intro i j hij
      rcases hno_chord (rot i) (rot j) hij with h1 | h2
      · left; exact hrot_left.injective (h1.trans (hrot_add i 1).symm)
      · right
        have hrot_pred : rot (idx hL0 (i.val + L - 1)) = idx hL0 ((rot i).val + L - 1) := by
          have := hrot_add i (L - 1)
          simpa only [show ∀ n : ℕ, n + (L - 1) = n + L - 1 from fun _ => by omega] using this
        exact hrot_left.injective (h2.trans hrot_pred.symm)
    have hout1' : ∀ i : Fin L, ∀ w₁ w₂, w₁ ∈ N (f' i) → w₂ ∈ N (f' i) →
        w₁ ∉ U → w₁ ∉ univ.image f' → w₂ ∉ U → w₂ ∉ univ.image f' → w₁ = w₂ := by
      intro i w₁ w₂ h1 h2 hw1U hw1H hw2U hw2H
      rw [himg] at hw1H hw2H
      exact hout1 (rot i) w₁ w₂ h1 h2 hw1U hw1H hw2U hw2H
    have hrot_cond : outPar N (univ \ U) (univ.image f') (f' ⟨2, by omega⟩) = none ∨
        outPar N (univ \ U) (univ.image f') (f' ⟨2, by omega⟩) ≠
          outPar N (univ \ U) (univ.image f') (f' (idx hL0 5)) := by
      simpa only [himg, f', Function.comp_apply, hrot2, hrot5] using hs₀
    let c := digonCycleGe5_pieceCert hL5 f' hf' hTT' hno_chord' hout1' hrot_cond
    have hm : c.m ≤ L + 1 := le_rfl
    rw [← himg]
    exact ⟨c, hm⟩

/-- **Theorem DC (universal chordless digon cycle dichotomy).** A chordless digon cycle of length
`L ≥ 4` (with `TTFree` and at most one active outside parent per vertex) is a certified piece if
and only if it is not a stride-3 cycle (`¬ IsStride3Cycle N U f`). -/
theorem digonCycle_pieceCert_iff {N : V → Finset V} {U : Finset V} {L : ℕ}
    (hL : 4 ≤ L) {f : Fin L → V} (hf : Function.Injective f) (hUH : Disjoint U (univ.image f))
    (hTT : ∀ i : Fin L, ∀ w, w ∉ U → w ∉ univ.image f →
      w ∈ N (f i) → w ∈ N (f (idx (by omega) (i.val + 1))) → False)
    (hcyc : ∀ i : Fin L,
      f (idx (by omega) (i.val + 1)) ∈ N (f i) ∧
      f (idx (by omega) (i.val + L - 1)) ∈ N (f i))
    (hno_chord : ∀ i j : Fin L, f j ∈ N (f i) →
      j = idx (by omega) (i.val + 1) ∨ j = idx (by omega) (i.val + L - 1))
    (hout1 : ∀ i : Fin L, ∀ w₁ w₂, w₁ ∈ N (f i) → w₂ ∈ N (f i) →
      w₁ ∉ U → w₁ ∉ univ.image f → w₂ ∉ U → w₂ ∉ univ.image f → w₁ = w₂) :
    Nonempty (PieceCert N U (univ.image f)) ↔ ¬ IsStride3Cycle N U f := by
  constructor
  · intro hne hs3
    exact not_pieceCert_of_isStride3Cycle (by omega) hf hUH hcyc hs3 hne
  · intro hnot3
    obtain ⟨c, _⟩ := digonCycle_pieceCert_of_not_stride3 hL hf hTT hno_chord hout1 hnot3
    exact ⟨c⟩

end Dichotomy

end DirectedReciprocity
