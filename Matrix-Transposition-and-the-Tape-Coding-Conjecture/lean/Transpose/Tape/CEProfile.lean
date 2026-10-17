import Transpose.Tape.CEEquiv
import Transpose.Tape.PopularTrace

/-!
# Stationary tapes: the memory profile is immaterial

Adding a stationary work tape to a diagram changes nothing in its block network: the nodes, edges,
sources and sinks stay the same, and there is no new chord. It adds one resident block at every
slot.
* `addTape`, `addTapes`: add one or `s` stationary work tapes.
* `solves_addTapes`: a code on a diagram is a code on the diagram with stationary tapes added.
* `robustNoCode_with_iff`: for every uniform memory profile of `m` blocks with `3k ≤ m (k + a)` for
  some `a` (e.g. `m k ≥ 3k`, or `m k = k`: `robustNoCode_with_k_iff`), "no code" is
  equivalent to `RobustNoCode_TM` with the per-node profile. This includes `m k = 3k` and
  `m k = 3k + 1`; a profile of `3k` blocks plus `O(1)` (or `O(log n)`) bits lies between these two
  for large `n`, so it is equivalent too.
* `solves_profileCap_addTapes` (TM-free): a code at the per-node blocks plus `s ≤ a r G` bits per
  memory edge is a code at the per-node profile with `a` stationary tapes added.
* `robustNoCode_bits_iff`: with `s k n ≤ C(k) n w` extra bits per memory edge (for `n ≥ 1`),
  "no code" is equivalent to `RobustNoCode_TM` (add `C(k)` stationary tapes). An instance is
  `robustNoCode_logBits_iff`, for the `O(log n)` bits `s k n = (3k + 4) w`. The plain form:
  `noCode_bits_iff` (a side channel computed by the code is free).
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-- Add a stationary work tape (at cell `0`). -/
def addTape {k : ℕ} (D : TSDiagram k) : TSDiagram (k + 1) where
  T := D.T
  work := Fin.snoc (α := fun _ => ℕ → ℤ) D.work (fun _ => 0)
  inp := D.inp
  out := D.out

/-- Add `s` stationary work tapes. -/
def addTapes {k : ℕ} (D : TSDiagram k) : (s : ℕ) → TSDiagram (k + s)
  | 0 => D
  | s + 1 => addTape (addTapes D s)

/-! ### The stationary walk -/

theorem stationary_mem {r T y : ℕ} {β : ℤ} (hβ : β ∈ pairRes r (fun _ => (0 : ℤ)) T y) :
    β = 0 := by
  obtain ⟨σ, -, rfl⟩ := mem_pairRes_curBlock hβ
  simp [curBlock, blockOf]

theorem stationary_pairRes {r T y : ℕ} (hr : 1 ≤ r) (hy : y * r < T) :
    pairRes r (fun _ => (0 : ℤ)) T y = {0} := by
  ext β
  constructor
  · intro hβ
    rw [stationary_mem hβ, Finset.mem_singleton]
  · intro hβ
    rw [Finset.mem_singleton] at hβ
    subst hβ
    have := cur_mem_pairRes (h := fun _ => (0 : ℤ)) hr hy
    rw [Nat.mul_div_cancel _ (by omega)] at this
    simpa [curBlock, blockOf] using this

theorem stationary_no_chord {r T x z : ℕ} {β : ℤ} :
    ¬ IsChord (pairRes r (fun _ => (0 : ℤ)) T) β x z := by
  rintro ⟨hxz, -, hz, hbetw⟩
  have hβ := stationary_mem hz
  subst hβ
  rw [mem_pairRes] at hz
  obtain ⟨τ, h1, h2, h3, -⟩ := hz
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; omega
    · exact h
  apply hbetw (x + 1) (by omega) hxz
  have hlt : (x + 1) * r < T := by
    have : (x + 1) * r ≤ z * r := Nat.mul_le_mul_right r (by omega)
    omega
  have := cur_mem_pairRes (h := fun _ => (0 : ℤ)) hr hlt
  rw [Nat.mul_div_cancel _ (by omega)] at this
  simpa [curBlock, blockOf] using this

/-! ### One stationary tape -/

section AddTape

variable {k : ℕ} (D : TSDiagram k)

theorem valid_addTape {L : ℕ} (hD : D.Valid L) : (addTape D).Valid L := by
  obtain ⟨hw, h2⟩ := hD
  refine ⟨fun t => ?_, h2⟩
  induction t using Fin.lastCases with
  | last => simp [addTape, UnitSteps]
  | cast t => simpa [addTape] using hw t

theorem chordEdges_addTape (r : ℕ) : (addTape D).chordEdges r = D.chordEdges r := by
  classical
  ext e
  rw [mem_chordEdges, mem_chordEdges]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨?_, ?_⟩)
  · rintro ⟨t, β, hc⟩
    induction t using Fin.lastCases with
    | last => simp [addTape] at hc; exact absurd hc stationary_no_chord
    | cast t => exact ⟨t, β, by simpa [addTape] using hc⟩
  · rintro ⟨t, β, hc⟩
    exact ⟨t.castSucc, β, by simpa [addTape] using hc⟩

theorem edges_addTape (r : ℕ) : (addTape D).edges r = D.edges r := by
  unfold TSDiagram.edges
  rw [chordEdges_addTape]
  rfl

theorem chordTapes_addTape (r : ℕ) (e : ℕ × ℕ) :
    (addTape D).chordTapes r e = D.chordTapes r e := by
  classical
  unfold TSDiagram.chordTapes
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  have hlast : ¬ ∃ β : ℤ,
      IsChord (pairRes r ((addTape D).work (Fin.last k)) (addTape D).T) β e.1 e.2 := by
    rintro ⟨β, hc⟩
    simp [addTape] at hc
    exact stationary_no_chord hc
  rw [ite_eq_right hlast, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro t _
  simp [addTape]

theorem solves_addTape {n G : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode} (h : D.Solves n G cap F code) :
    (addTape D).Solves n G cap F code := by
  unfold TSDiagram.Solves at h ⊢
  rw [edges_addTape]
  exact h

/-- The stationary tape adds one resident block at every slot. -/
theorem resSum_addTape {r y : ℕ} (hr : 1 ≤ r) (hy : y < D.nodes r) :
    ∑ t, (pairRes r ((addTape D).work t) (addTape D).T y).card =
      ∑ t, (pairRes r (D.work t) D.T y).card + 1 := by
  rw [Fin.sum_univ_castSucc]
  have hlast : (addTape D).work (Fin.last k) = fun _ => (0 : ℤ) := by simp [addTape]
  have hyT : y * r < D.T := (numSlots_spec hr).1 hy
  rw [hlast, show (addTape D).T = D.T from rfl, stationary_pairRes hr hyT, Finset.card_singleton]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  simp [addTape]

end AddTape

/-! ### Several stationary tapes -/

section AddTapes

variable {k : ℕ} (D : TSDiagram k)

theorem T_addTapes : ∀ s, (addTapes D s).T = D.T
  | 0 => rfl
  | s + 1 => T_addTapes s

theorem out_addTapes : ∀ s, (addTapes D s).out = D.out
  | 0 => rfl
  | s + 1 => out_addTapes s

theorem nodes_addTapes (r : ℕ) : ∀ s, (addTapes D s).nodes r = D.nodes r
  | 0 => rfl
  | s + 1 => nodes_addTapes r s

theorem valid_addTapes {L : ℕ} (hD : D.Valid L) : ∀ s, (addTapes D s).Valid L
  | 0 => hD
  | s + 1 => valid_addTape _ (valid_addTapes hD s)

theorem memEdges_addTapes (r : ℕ) : ∀ s, (addTapes D s).memEdges r = D.memEdges r
  | 0 => rfl
  | s + 1 => memEdges_addTapes r s

theorem chordEdges_addTapes (r : ℕ) : ∀ s, (addTapes D s).chordEdges r = D.chordEdges r
  | 0 => rfl
  | s + 1 => (chordEdges_addTape _ r).trans (chordEdges_addTapes r s)

theorem chordTapes_addTapes (r : ℕ) (e : ℕ × ℕ) :
    ∀ s, (addTapes D s).chordTapes r e = D.chordTapes r e
  | 0 => rfl
  | s + 1 => (chordTapes_addTape _ r e).trans (chordTapes_addTapes r e s)

theorem edges_addTapes (r : ℕ) : ∀ s, (addTapes D s).edges r = D.edges r
  | 0 => rfl
  | s + 1 => (edges_addTape _ r).trans (edges_addTapes r s)

theorem solves_addTapes {n G : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode} (h : D.Solves n G cap F code) :
    ∀ s, (addTapes D s).Solves n G cap F code
  | 0 => h
  | s + 1 => solves_addTape _ (solves_addTapes h s)

/-- `s` stationary tapes add `s` resident blocks at every slot. -/
theorem resSum_addTapes {r y : ℕ} (hr : 1 ≤ r) (hy : y < D.nodes r) :
    ∀ s, ∑ t, (pairRes r ((addTapes D s).work t) (addTapes D s).T y).card =
      ∑ t, (pairRes r (D.work t) D.T y).card + s
  | 0 => rfl
  | s + 1 => by
    have hy' : y < (addTapes D s).nodes r := by rw [nodes_addTapes]; exact hy
    have h1 := resSum_addTape (addTapes D s) hr hy'
    have h2 := resSum_addTapes hr hy s
    calc ∑ t, (pairRes r ((addTapes D (s + 1)).work t) (addTapes D (s + 1)).T y).card
        = ∑ t, (pairRes r ((addTapes D s).work t) (addTapes D s).T y).card + 1 := h1
      _ = ∑ t, (pairRes r (D.work t) D.T y).card + s + 1 := by rw [h2]
      _ = _ := by ring

end AddTapes

/-! ### The memory profile is immaterial -/

/-- At most `3k` blocks are resident at a slot. -/
theorem resSum_le {k : ℕ} {D : TSDiagram k} {L r : ℕ} (hD : D.Valid L) (hr : 1 ≤ r) (y : ℕ) :
    ∑ t, (pairRes r (D.work t) D.T y).card ≤ 3 * k := by
  calc ∑ t, (pairRes r (D.work t) D.T y).card ≤ ∑ _t : Fin k, 3 :=
        Finset.sum_le_sum (fun t _ => (pairRes_admissible (hD.1 t).2 hr D.T).2 _)
    _ = 3 * k := by simp [Nat.mul_comm]

/-- With `a` stationary tapes added, `a` blocks plus `s ≤ a r G` bits on top of the resident blocks
fit the per-node profile. -/
theorem blockCap_le_profileCap_addTapes {k : ℕ} {D : TSDiagram k} {n G a s : ℕ}
    (hr : 1 ≤ blockSize G n) (hs : s ≤ a * (blockSize G n * G)) (mem : ℕ → ℕ)
    (hmem : ∀ y, mem y ≤ ∑ t, (pairRes (blockSize G n) (D.work t) D.T y).card) :
    ∀ e ∈ D.edges (blockSize G n),
      D.blockCap n G mem s e ≤ (addTapes D a).profileCap n G e := by
  intro e he
  rcases Finset.mem_union.1 he with hm | hc
  · have hm' : e ∈ (addTapes D a).memEdges (blockSize G n) := by
      rw [memEdges_addTapes]; exact hm
    have hy : e.1 < D.nodes (blockSize G n) := by
      have := ((mem_memEdges D).1 hm).2
      omega
    unfold TSDiagram.profileCap
    rw [blockCap_mem D hm, blockCap_mem _ hm', Nat.add_zero, resSum_addTapes D hr hy a]
    calc mem e.1 * (blockSize G n * G) + s
        ≤ (∑ t, (pairRes (blockSize G n) (D.work t) D.T e.1).card) * (blockSize G n * G) +
            a * (blockSize G n * G) := Nat.add_le_add (Nat.mul_le_mul_right _ (hmem e.1)) hs
      _ = _ := by ring
  · have hc' : e ∈ (addTapes D a).chordEdges (blockSize G n) := by
      rw [chordEdges_addTapes]; exact hc
    unfold TSDiagram.profileCap
    rw [blockCap_chord D hc, blockCap_chord _ hc', chordTapes_addTapes]

/-- **Extra bits become stationary tapes** (TM-free). A code at the per-node blocks plus
`s ≤ a r G` bits per memory edge is a code at the per-node profile capacities of the diagram with `a`
stationary tapes added. -/
theorem solves_profileCap_addTapes {k : ℕ} {D : TSDiagram k} {n G a s : ℕ}
    (hr : 1 ≤ blockSize G n) (hs : s ≤ a * (blockSize G n * G))
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode}
    (h : D.Solves n G (D.blockCap n G
      (fun y => ∑ t, (pairRes (blockSize G n) (D.work t) D.T y).card) s) F code) :
    (addTapes D a).Solves n G ((addTapes D a).profileCap n G) F code :=
  solves_mono _ (fun e he => blockCap_le_profileCap_addTapes hr hs _ (fun _ => le_rfl) e
    (by rwa [edges_addTapes] at he)) (solves_addTapes D h a)

/-- "No code" with the per-node profile implies "no code" with any uniform profile: the `m k` uniform
blocks are the resident blocks of `m k` added stationary tapes. -/
theorem robustNoCode_with_of_robustNoCode (m : ℕ → ℕ) (h : RobustNoCode_TM) :
    RobustNoCode_TM_with m := by
  intro k G c C hG
  obtain ⟨n₀, hn₀⟩ := h (k + m k) G c C hG
  refine ⟨max n₀ 1, fun n hn D hD hT F hF code hsol => ?_⟩
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG (le_trans (le_max_right _ _) hn)
  refine hn₀ n (le_trans (le_max_left _ _) hn) (addTapes D (m k)) (valid_addTapes D hD _)
    (by rw [T_addTapes]; exact hT) F hF code
    (solves_mono _ (fun e he => ?_) (solves_addTapes D hsol (m k)))
  rw [edges_addTapes] at he
  refine le_trans (le_of_eq ?_) (blockCap_le_profileCap_addTapes hr le_rfl (fun _ => 0)
    (fun _ => Nat.zero_le _) e he)
  unfold TSDiagram.blockCap; split_ifs <;> ring

/-- "No code" with a uniform profile of `m` blocks implies "no code" with the per-node profile, as
soon as every `k` has some `a` with `3k ≤ m (k + a)` (add `a` stationary tapes). For example
`m k = k`: one block per tape. -/
theorem robustNoCode_of_robustNoCode_with {m : ℕ → ℕ} (hm : ∀ k, ∃ a, 3 * k ≤ m (k + a))
    (h : RobustNoCode_TM_with m) : RobustNoCode_TM := by
  intro k G c C hG
  obtain ⟨a, ha⟩ := hm k
  obtain ⟨n₀, hn₀⟩ := h (k + a) G c C hG
  refine ⟨max n₀ 1, fun n hn D hD hT F hF code hsol => ?_⟩
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG (le_trans (le_max_right _ _) hn)
  refine hn₀ n (le_trans (le_max_left _ _) hn) (addTapes D a) (valid_addTapes D hD a)
    (by rw [T_addTapes]; exact hT) F hF code
    (solves_mono _ (fun e he => ?_) (solves_addTapes D hsol a))
  rcases Finset.mem_union.1 he with hm' | hc'
  · have hm : e ∈ D.memEdges (blockSize G n) := by rw [memEdges_addTapes] at hm'; exact hm'
    unfold TSDiagram.profileCap
    rw [blockCap_mem D hm, blockCap_mem _ hm', Nat.add_zero, Nat.add_zero]
    exact Nat.mul_le_mul_right _ (le_trans (resSum_le hD hr e.1) ha)
  · have hc : e ∈ D.chordEdges (blockSize G n) := by rw [chordEdges_addTapes] at hc'; exact hc'
    unfold TSDiagram.profileCap
    rw [blockCap_chord D hc, blockCap_chord _ hc', chordTapes_addTapes]

/-- **The memory profile is immaterial**: for every `m` such that every `k` has some `a` with
`3k ≤ m (k + a)` (for example `m k ≥ 3k`, or one block per tape, `m k = k`), "no code" with the
uniform memory profile of `m` blocks is equivalent to `RobustNoCode_TM`. -/
theorem robustNoCode_with_iff {m : ℕ → ℕ} (hm : ∀ k, ∃ a, 3 * k ≤ m (k + a)) :
    RobustNoCode_TM_with m ↔ RobustNoCode_TM :=
  ⟨robustNoCode_of_robustNoCode_with hm, robustNoCode_with_of_robustNoCode m⟩

/-- The hypothesis of `robustNoCode_with_iff` says exactly that `m` is unbounded. -/
theorem exists_shift_iff_unbounded (m : ℕ → ℕ) :
    (∀ k, ∃ a, 3 * k ≤ m (k + a)) ↔ ∀ B, ∃ j, B ≤ m j := by
  constructor
  · intro h B
    obtain ⟨a, ha⟩ := h B
    exact ⟨B + a, by omega⟩
  · intro h k
    obtain ⟨j, hj⟩ := h (3 * k + ∑ i ∈ Finset.range k, m i + 1)
    have hjk : k ≤ j := by
      by_contra hlt
      push Not at hlt
      have : m j ≤ ∑ i ∈ Finset.range k, m i :=
        Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hlt)
      omega
    exact ⟨j - k, by rw [Nat.add_sub_cancel' hjk]; omega⟩

/-- **One block per tape** on memory edges is equivalent to the per-node profile. -/
theorem robustNoCode_with_k_iff : RobustNoCode_TM_with (fun k => k) ↔ RobustNoCode_TM :=
  robustNoCode_with_iff (fun k => ⟨2 * k, by omega⟩)

/-- **Extra bits are immaterial**: for `s k n ≤ C(k) n w` (for `n ≥ 1`), "no code" with `s k n` extra
bits per memory edge is equivalent to `RobustNoCode_TM` (add `C(k)` stationary tapes). The bound is
needed only for `n ≥ 1`: at `n = 0` the right side is `0`, while e.g. `(3k + 4) w` is not, since
`entryBits 0 = 1`. -/
theorem robustNoCode_bits_iff {s : ℕ → ℕ → ℕ}
    (hs : ∃ C : ℕ → ℕ, ∀ k n, 1 ≤ n → s k n ≤ C k * (n * entryBits n)) :
    RobustNoCode_TM_bits s ↔ RobustNoCode_TM := by
  obtain ⟨C₁, hC₁⟩ := hs
  constructor
  · intro h k G c C hG
    obtain ⟨n₀, hn₀⟩ := h k G c C hG
    refine ⟨n₀, fun n hn D hD hT F hF code hsol => hn₀ n hn D hD hT F hF code
      (solves_mono D (fun e _ => ?_) hsol)⟩
    unfold TSDiagram.profileCap TSDiagram.blockCap
    split_ifs <;> omega
  · intro h k G c C hG
    obtain ⟨n₀, hn₀⟩ := h (k + C₁ k) G c C hG
    refine ⟨max n₀ 1, fun n hn D hD hT F hF code hsol => ?_⟩
    have hr : 1 ≤ blockSize G n := one_le_blockSize hG (le_trans (le_max_right _ _) hn)
    have hsB : s k n ≤ C₁ k * (blockSize G n * G) :=
      le_trans (hC₁ k n (le_trans (le_max_right _ _) hn))
        (Nat.mul_le_mul_left _ (blockSize_mul_ge hG))
    exact hn₀ n (le_trans (le_max_left _ _) hn) (addTapes D (C₁ k)) (valid_addTapes D hD _)
      (by rw [T_addTapes]; exact hT) F hF code (solves_profileCap_addTapes hr hsB hsol)

/-- **A side channel computed by the code is free** (plain form): for `s k n ≤ C(k) n w` (for `n ≥ 1`), "no code"
for independent sources with `s k n` extra bits per memory edge is equivalent to `NoCode_TM` (add
`C(k)` stationary tapes). -/
theorem noCode_bits_iff {s : ℕ → ℕ → ℕ}
    (hs : ∃ C : ℕ → ℕ, ∀ k n, 1 ≤ n → s k n ≤ C k * (n * entryBits n)) :
    NoCode_TM_bits s ↔ NoCode_TM := by
  obtain ⟨C₁, hC₁⟩ := hs
  constructor
  · intro h k G c hG
    obtain ⟨n₀, hn₀⟩ := h k G c hG
    refine ⟨n₀, fun n hn D hD hT code hsol => hn₀ n hn D hD hT code
      (solves_mono D (fun e _ => ?_) hsol)⟩
    unfold TSDiagram.profileCap TSDiagram.blockCap
    split_ifs <;> omega
  · intro h k G c hG
    obtain ⟨n₀, hn₀⟩ := h (k + C₁ k) G c hG
    refine ⟨max n₀ 1, fun n hn D hD hT code hsol => ?_⟩
    have hr : 1 ≤ blockSize G n := one_le_blockSize hG (le_trans (le_max_right _ _) hn)
    have hsB : s k n ≤ C₁ k * (blockSize G n * G) :=
      le_trans (hC₁ k n (le_trans (le_max_right _ _) hn))
        (Nat.mul_le_mul_left _ (blockSize_mul_ge hG))
    exact hn₀ n (le_trans (le_max_left _ _) hn) (addTapes D (C₁ k)) (valid_addTapes D hD _)
      (by rw [T_addTapes]; exact hT) code (solves_profileCap_addTapes hr hsB hsol)

/-- **The `O(log n)`-bit target is equivalent**: `RobustNoCode_TM_bits` at `s k n = (3k + 4) w`, the
bits that already rule out every fixed machine directly, is equivalent to `RobustNoCode_TM`. -/
theorem robustNoCode_logBits_iff :
    RobustNoCode_TM_bits (fun k n => (3 * k + 4) * entryBits n) ↔ RobustNoCode_TM :=
  robustNoCode_bits_iff ⟨fun k => 3 * k + 4, fun _ _ hn =>
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hn)⟩

end Transpose.Tape.Impl
