import Transpose.Tape.CEProfile

/-!
# Every input row attached, without loss of generality

`sweepDiagram D r L` is `D` followed by an input sweep: from the first step of slot `⌈T/r⌉` the input
head moves to cell `0` and then across `[0, L)`; the work heads and the output schedule are unchanged.
* The original nodes keep their chords (`chord_sweep`), their sinks (`outNode_sweep`) and their source
  rows, which can only grow (`rowsAt_sweep_sub`). Every complete slot keeps its residency
  (`pairRes_sweep_eq`); if `r ∤ T`, the last original slot is completed by the sweep, so its residency
  can only grow (`pairRes_sweep_sub`).
* Every row is attached at some node (`attached_sweep`), and the length grows to at most
  `2 (T + r) + L` (`sweep_T_le`).
* A code at the profile capacities transfers (`solves_sweep`): each node masks its visible input back
  to its original rows, and the new edges carry `0`.

Hence "no code" may assume that the input walk attaches every row (`robustNoCode_iff_attached`,
stated in `Transpose/Tape/Statements/Coding.lean`), and the flow and distance forms need no
convention for rows without a source node.
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-! ### The sweep walk -/

/-- A unit-step walk from `p₀`: first to `0`, then upwards. -/
def sweep (p₀ : ℤ) (s : ℕ) : ℤ :=
  if s ≤ p₀.natAbs then (if 0 ≤ p₀ then p₀ - s else p₀ + s) else ((s - p₀.natAbs : ℕ) : ℤ)

theorem sweep_zero (p₀ : ℤ) : sweep p₀ 0 = p₀ := by
  unfold sweep; split_ifs <;> omega

theorem sweep_step (p₀ : ℤ) (s : ℕ) : |sweep p₀ (s + 1) - sweep p₀ s| ≤ 1 := by
  unfold sweep
  rw [abs_le]
  split_ifs <;> constructor <;> omega

theorem sweep_visit (p₀ : ℤ) (q : ℕ) : sweep p₀ (p₀.natAbs + q) = q := by
  unfold sweep
  split_ifs <;> omega

/-! ### The extended diagram -/

/-- `D` followed by an input sweep across `[0, L)`, starting at the first step of slot `⌈T/r⌉`. -/
def sweepDiagram {k : ℕ} (D : TSDiagram k) (r L : ℕ) : TSDiagram k where
  T := D.nodes r * r + (D.inp (D.nodes r * r)).natAbs + L
  work := D.work
  inp := fun τ => if τ < D.nodes r * r then D.inp τ
    else sweep (D.inp (D.nodes r * r)) (τ - D.nodes r * r)
  out := D.out

section Sweep

variable {k : ℕ} (D : TSDiagram k) {L r : ℕ}

theorem sweep_T_ge (hr : 1 ≤ r) : D.T ≤ (sweepDiagram D r L).T := by
  have := T_le_nodes_mul (D := D) hr
  simp only [sweepDiagram]
  omega

theorem sweep_inp_lt {τ : ℕ} (hτ : τ < D.nodes r * r) : (sweepDiagram D r L).inp τ = D.inp τ := by
  simp only [sweepDiagram, ite_eq_left hτ]

theorem valid_sweep (hD : D.Valid L) (hr : 1 ≤ r) : (sweepDiagram D r L).Valid L := by
  refine ⟨fun t => hD.1 t, ?_, ?_, hD.2.2.2.1, hD.2.2.2.2.1,
    fun τ hτ => hD.2.2.2.2.2 τ (le_trans (sweep_T_ge D hr) hτ)⟩
  · simp only [sweepDiagram]
    split_ifs with h
    · exact hD.2.1
    · have h0 : D.nodes r * r = 0 := by omega
      rw [h0, Nat.sub_self, sweep_zero]; exact hD.2.1
  · intro τ
    have hh := hD.2.2.1
    simp only [sweepDiagram]
    split_ifs with h1 h2 h2
    · exact hh τ
    · omega
    · have e : τ + 1 = D.nodes r * r := by omega
      rw [e, Nat.sub_self, sweep_zero]
      have := hh τ
      rw [e] at this
      exact this
    · have e : τ + 1 - D.nodes r * r = (τ - D.nodes r * r) + 1 := by omega
      rw [e]
      exact sweep_step _ _

theorem nodes_sweep_ge (hr : 1 ≤ r) : D.nodes r ≤ (sweepDiagram D r L).nodes r :=
  numSlots_mono r (sweep_T_ge D hr)

theorem slotOf_sweep_sub (hr : 1 ≤ r) (y : ℕ) : slotOf r D.T y ⊆ slotOf r (sweepDiagram D r L).T y := by
  intro τ hτ
  rw [mem_slotOf] at hτ ⊢
  exact ⟨hτ.1, hτ.2.1, lt_of_lt_of_le hτ.2.2 (sweep_T_ge D hr)⟩

theorem pairRes_sweep_sub (hr : 1 ≤ r) (t : Fin k) (y : ℕ) :
    pairRes r (D.work t) D.T y ⊆ pairRes r ((sweepDiagram D r L).work t) (sweepDiagram D r L).T y :=
  Finset.biUnion_subset_biUnion_of_subset_left _ (slotOf_sweep_sub D hr y)

theorem pairRes_sweep_eq (hr : 1 ≤ r) (t : Fin k) {y : ℕ} (hy : (y + 1) * r ≤ D.T) :
    pairRes r ((sweepDiagram D r L).work t) (sweepDiagram D r L).T y = pairRes r (D.work t) D.T y := by
  have : slotOf r (sweepDiagram D r L).T y = slotOf r D.T y := by
    ext τ
    rw [mem_slotOf, mem_slotOf]
    have := sweep_T_ge D (L := L) hr
    constructor
    · rintro ⟨h1, h2, -⟩; refine ⟨h1, h2, ?_⟩
      rw [Nat.add_mul, Nat.one_mul] at hy; omega
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by omega⟩
  unfold pairRes
  rw [this]
  rfl

/-- Old slots before the last one are complete. -/
theorem slot_full {y : ℕ} (hr : 1 ≤ r) (hy : y + 1 < D.nodes r) : (y + 1) * r ≤ D.T := by
  have := (numSlots_spec hr).1 hy
  omega

theorem chord_sweep (hr : 1 ≤ r) (t : Fin k) {β : ℤ} {x z : ℕ} (hz : z < D.nodes r)
    (hc : IsChord (pairRes r (D.work t) D.T) β x z) :
    IsChord (pairRes r ((sweepDiagram D r L).work t) (sweepDiagram D r L).T) β x z := by
  obtain ⟨hxz, hx, hzβ, hgap⟩ := hc
  refine ⟨hxz, ?_, pairRes_sweep_sub D hr t z hzβ, fun y h1 h2 hy => hgap y h1 h2 ?_⟩
  · rw [pairRes_sweep_eq D hr t (slot_full D hr (by omega))]; exact hx
  · rw [pairRes_sweep_eq D hr t (slot_full D hr (by omega))] at hy; exact hy

theorem memEdges_sweep_sub (hr : 1 ≤ r) : D.memEdges r ⊆ (sweepDiagram D r L).memEdges r := by
  intro e he
  rw [mem_memEdges] at he ⊢
  exact ⟨he.1, lt_of_lt_of_le he.2 (nodes_sweep_ge D hr)⟩

theorem chordEdges_sweep_sub (hr : 1 ≤ r) : D.chordEdges r ⊆ (sweepDiagram D r L).chordEdges r := by
  intro e he
  rw [mem_chordEdges] at he ⊢
  obtain ⟨h1, h2, t, β, hc⟩ := he
  exact ⟨lt_of_lt_of_le h1 (nodes_sweep_ge D hr), lt_of_lt_of_le h2 (nodes_sweep_ge D hr), t, β,
    chord_sweep D hr t h2 hc⟩

theorem edges_sweep_sub (hr : 1 ≤ r) : D.edges r ⊆ (sweepDiagram D r L).edges r :=
  Finset.union_subset_union (memEdges_sweep_sub D hr) (chordEdges_sweep_sub D hr)

theorem chordTapes_sweep_ge (hr : 1 ≤ r) {e : ℕ × ℕ} (he : e ∈ D.chordEdges r) :
    D.chordTapes r e ≤ (sweepDiagram D r L).chordTapes r e := by
  classical
  have hz := ((mem_chordEdges D).1 he).2.1
  unfold TSDiagram.chordTapes
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  obtain ⟨β, hc⟩ := ht.2
  exact ⟨ht.1, β, chord_sweep D hr t hz hc⟩

theorem rowsAt_sweep_sub (hr : 1 ≤ r) {n w : ℕ} (y : ℕ) :
    D.rowsAt n w r y ⊆ (sweepDiagram D r L).rowsAt n w r y := by
  classical
  intro i hi
  simp only [TSDiagram.rowsAt, Finset.mem_filter] at hi ⊢
  obtain ⟨hin, τ, hτ, h1, h2⟩ := hi
  have hτT : τ < D.T := (mem_slotOf.1 hτ).2.2
  have hτN : τ < D.nodes r * r := lt_of_lt_of_le hτT (T_le_nodes_mul hr)
  refine ⟨hin, τ, slotOf_sweep_sub D hr y hτ, ?_, ?_⟩
  · rw [sweep_inp_lt D hτN]; exact h1
  · rw [sweep_inp_lt D hτN]; exact h2

theorem outNode_sweep (hD : D.Valid L) (hr : 1 ≤ r) {o : ℕ} (ho : o < L) :
    (sweepDiagram D r L).outNode r o = D.outNode r o := by
  classical
  have hbig : ∀ y, D.nodes r ≤ y → ¬ D.out (y * r) ≤ o := by
    intro y hy
    have hT : D.T ≤ y * r := le_trans (T_le_nodes_mul hr) (Nat.mul_le_mul_right r hy)
    rw [hD.2.2.2.2.2 _ hT]
    omega
  have h0 : D.out (0 * r) ≤ o := by rw [Nat.zero_mul, hD.2.2.2.1]; exact Nat.zero_le _
  show Nat.findGreatest (fun y => D.out (y * r) ≤ o) ((sweepDiagram D r L).nodes r - 1) =
    Nat.findGreatest (fun y => D.out (y * r) ≤ o) (D.nodes r - 1)
  apply le_antisymm
  · have hP := Nat.findGreatest_spec (P := fun y => D.out (y * r) ≤ o) (Nat.zero_le _) h0
      (n := (sweepDiagram D r L).nodes r - 1)
    have hle : Nat.findGreatest (fun y => D.out (y * r) ≤ o) ((sweepDiagram D r L).nodes r - 1) ≤
        D.nodes r - 1 := by
      by_contra hc
      push Not at hc
      exact hbig _ (by omega) hP
    exact Nat.le_findGreatest hle hP
  · exact Nat.findGreatest_mono_right _ (by have := nodes_sweep_ge D (L := L) hr; omega)

theorem attached_sweep (hr : 1 ≤ r) {n w : ℕ} (hL : L = n * n * w) (hw : 1 ≤ w) :
    ∀ i < n, ∃ a < (sweepDiagram D r L).nodes r, i ∈ (sweepDiagram D r L).rowsAt n w r a := by
  classical
  intro i hi
  set p₀ := D.inp (D.nodes r * r) with hp₀
  set τ := D.nodes r * r + p₀.natAbs + i * n * w with hτ
  have hpL : i * n * w < L := by
    rw [hL]
    calc i * n * w < (i + 1) * n * w := by
          apply Nat.mul_lt_mul_of_pos_right _ hw
          exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ ≤ n * n * w := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hi)
  have hτT : τ < (sweepDiagram D r L).T := by simp only [sweepDiagram]; omega
  have hinp : (sweepDiagram D r L).inp τ = ((i * n * w : ℕ) : ℤ) := by
    simp only [sweepDiagram]
    rw [ite_eq_right (by omega), show τ - D.nodes r * r = p₀.natAbs + i * n * w by omega,
      sweep_visit]
  refine ⟨τ / r, div_lt_numSlots hr hτT, ?_⟩
  simp only [TSDiagram.rowsAt, Finset.mem_filter, Finset.mem_range]
  refine ⟨hi, τ, mem_slotOf_div hr hτT, ?_, ?_⟩
  · rw [hinp]
  · rw [hinp]
    have : i * n * w < (i + 1) * n * w := by
      apply Nat.mul_lt_mul_of_pos_right _ hw
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    exact_mod_cast this

theorem sweep_T_le (hD : D.Valid L) (hr : 1 ≤ r) :
    (sweepDiagram D r L).T ≤ 2 * (D.T + r) + L := by
  have h1 := nodes_mul_le (D := D) r
  have h2 := unitSteps_dist hD.2.2.1 (Nat.zero_le (D.nodes r * r))
  rw [hD.2.1, sub_zero, Nat.cast_zero, sub_zero] at h2
  have h3 : (D.inp (D.nodes r * r)).natAbs ≤ D.nodes r * r := by
    have : ((D.inp (D.nodes r * r)).natAbs : ℤ) ≤ ((D.nodes r * r : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]; exact h2
    exact_mod_cast this
  simp only [sweepDiagram]
  omega

theorem profileCap_sweep_ge {n G : ℕ} (hr : 1 ≤ blockSize G n) {e : ℕ × ℕ}
    (he : e ∈ D.edges (blockSize G n)) :
    D.profileCap n G e ≤ (sweepDiagram D (blockSize G n) L).profileCap n G e := by
  rcases Finset.mem_union.1 he with hm | hc
  · have hm' := memEdges_sweep_sub D (L := L) hr hm
    have he2 := (mem_memEdges D).1 hm
    unfold TSDiagram.profileCap
    rw [blockCap_mem D hm, blockCap_mem _ hm']
    have : ∑ t, (pairRes (blockSize G n) ((sweepDiagram D (blockSize G n) L).work t)
        (sweepDiagram D (blockSize G n) L).T e.1).card =
        ∑ t, (pairRes (blockSize G n) (D.work t) D.T e.1).card :=
      Finset.sum_congr rfl (fun t _ => by rw [pairRes_sweep_eq D hr t (slot_full D hr he2.2)])
    rw [this]
  · have hc' := chordEdges_sweep_sub D (L := L) hr hc
    unfold TSDiagram.profileCap
    rw [blockCap_chord D hc, blockCap_chord _ hc']
    exact Nat.mul_le_mul_right _ (chordTapes_sweep_ge D hr hc)

/-- The code `C` with each node's visible input masked to the rows of `D` at that node, and `0` on
the edges not in `D`. -/
noncomputable def maskCode (D : TSDiagram k) (n w r : ℕ) (C : NetCode) : NetCode where
  enc e f v := if e ∈ D.edges r then
      C.enc e f (fun d => if d / (n * w) ∈ D.rowsAt n w r e.1 then v d else false) else 0
  dec o f v :=
    C.dec o f (fun d => if d / (n * w) ∈ D.rowsAt n w r (D.outNode r o) then v d else false)

/-- **A code transfers to the swept diagram**, at the profile capacities. -/
theorem solves_sweep {n G : ℕ} (hD : D.Valid (n * n * entryBits n)) (hr : 1 ≤ blockSize G n)
    {F : Set (Fin (n * n * entryBits n) → Bool)} {C : NetCode}
    (hsol : D.Solves n G (D.profileCap n G) F C) :
    (sweepDiagram D (blockSize G n) (n * n * entryBits n)).Solves n G
      ((sweepDiagram D (blockSize G n) (n * n * entryBits n)).profileCap n G) F
      (maskCode D n (entryBits n) (blockSize G n) C) := by
  intro x hx
  -- masking recovers the original visible input
  have hmask : ∀ y, (fun d => if d / (n * entryBits n) ∈ D.rowsAt n (entryBits n) (blockSize G n) y
      then (sweepDiagram D (blockSize G n) (n * n * entryBits n)).visible n (entryBits n)
        (blockSize G n) y x d else false) =
      D.visible n (entryBits n) (blockSize G n) y x := by
    intro y
    funext d
    simp only [TSDiagram.visible]
    by_cases h1 : d / (n * entryBits n) ∈ D.rowsAt n (entryBits n) (blockSize G n) y
    · have h2 := rowsAt_sweep_sub D (L := n * n * entryBits n) hr y h1
      simp [h1, h2]
    · simp [h1]
  -- the values into every node agree
  have hin : ∀ v, (maskCode D n (entryBits n) (blockSize G n) C).inVals
      ((sweepDiagram D (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
      (fun y => (sweepDiagram D (blockSize G n) (n * n * entryBits n)).visible n (entryBits n)
        (blockSize G n) y x) v =
      C.inVals (D.edges (blockSize G n)) (fun y => D.visible n (entryBits n) (blockSize G n) y x) v := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
    funext e
    rw [inVals_eq, inVals_eq]
    by_cases hE : e ∈ D.edges (blockSize G n)
    · have hE' := edges_sweep_sub D (L := n * n * entryBits n) hr hE
      by_cases hc : e.2 = v ∧ e.1 < v
      · rw [ite_eq_left ⟨hE', hc⟩, ite_eq_left ⟨hE, hc⟩]
        show (if e ∈ D.edges (blockSize G n) then C.enc e _ _ else 0) = _
        rw [ite_eq_left hE, ih e.1 hc.2, hmask]
      · rw [ite_eq_right (fun h => hc h.2), ite_eq_right (fun h => hc h.2)]
    · rw [ite_eq_right (show ¬(e ∈ D.edges (blockSize G n) ∧ e.2 = v ∧ e.1 < v) from
        fun h => hE h.1)]
      by_cases h : e ∈ (sweepDiagram D (blockSize G n) (n * n * entryBits n)).edges (blockSize G n) ∧
          e.2 = v ∧ e.1 < v
      · rw [ite_eq_left h]
        show (if e ∈ D.edges (blockSize G n) then C.enc e _ _ else 0) = 0
        rw [ite_eq_right hE]
      · rw [ite_eq_right h]
  refine ⟨fun e he => ?_, fun d hd => ?_⟩
  · show (if e ∈ D.edges (blockSize G n) then C.enc e _ _ else 0) < _
    by_cases hE : e ∈ D.edges (blockSize G n)
    · rw [ite_eq_left hE, hin e.1, hmask]
      calc C.enc e (C.inVals (D.edges (blockSize G n))
            (fun y => D.visible n (entryBits n) (blockSize G n) y x) e.1)
            (D.visible n (entryBits n) (blockSize G n) e.1 x)
          < 2 ^ D.profileCap n G e := (hsol x hx).1 e hE
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (profileCap_sweep_ge D hr hE)
    · rw [ite_eq_right hE]; exact Nat.two_pow_pos _
  · have hs := outNode_sweep D hD hr (r := blockSize G n) (tpos_lt hd)
    show C.dec _ _ (fun d' => if d' / (n * entryBits n) ∈ D.rowsAt n (entryBits n) (blockSize G n)
      (D.outNode (blockSize G n) (tpos n (entryBits n) d)) then _ else false) = x ⟨d, hd⟩
    rw [hs, hin, hmask]
    exact (hsol x hx).2 d hd

end Sweep

/-! ### Every row attached, without loss of generality -/

/-- The sweep keeps linear time: `T ≤ c L` becomes `T ≤ (2c + 3) L`. -/
theorem sweep_T_le_mul {n c : ℕ} {k : ℕ} {D : TSDiagram k} {G : ℕ} (hG : 1 ≤ G) (hn : 1 ≤ n)
    (hD : D.Valid (n * n * entryBits n)) (hT : D.T ≤ c * (n * n * entryBits n)) :
    (sweepDiagram D (blockSize G n) (n * n * entryBits n)).T ≤ (2 * c + 3) * (n * n * entryBits n) := by
  have hr := one_le_blockSize hG hn
  have hrnw := blockSize_le (n := n) hG
  have h := sweep_T_le D hD hr
  have hnw : n * entryBits n ≤ n * n * entryBits n := by
    calc n * entryBits n = 1 * (n * entryBits n) := (Nat.one_mul _).symm
      _ ≤ n * (n * entryBits n) := Nat.mul_le_mul_right _ hn
      _ = n * n * entryBits n := by ring
  nlinarith

/-- **No code may assume every row attached.** "No code" on diagrams whose input walk attaches every
row implies "no code" on all diagrams (append an input sweep; `c` becomes `2c + 3`). -/
theorem robustNoCode_of_attached (h : RobustNoCode_TM_att) : RobustNoCode_TM := by
  intro k G c C hG
  obtain ⟨n₀, hn₀⟩ := h k G (2 * c + 3) C hG
  refine ⟨max n₀ 1, fun n hn D hD hT F hF code hsol => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hr := one_le_blockSize hG hn1
  have hw : 1 ≤ entryBits n := by unfold entryBits; omega
  exact hn₀ n (le_trans (le_max_left _ _) hn) _ (valid_sweep D hD hr)
    (sweep_T_le_mul hG hn1 hD hT) (attached_sweep D hr rfl hw) F hF _ (solves_sweep D hD hr hsol)

theorem robustNoCode_iff_attached : RobustNoCode_TM ↔ RobustNoCode_TM_att := by
  refine ⟨fun h => ?_, robustNoCode_of_attached⟩
  intro k G c C hG
  obtain ⟨n₀, hn₀⟩ := h k G c C hG
  exact ⟨n₀, fun n hn D hD hT _ F hF code => hn₀ n hn D hD hT F hF code⟩

/-- **The flow form on diagrams with every row attached is equivalent to "no code".** -/
theorem robustCE_TM_att_iff : RobustCE_TM_att ↔ RobustNoCode_TM := by
  constructor
  · intro h
    apply robustNoCode_of_attached
    intro k G c C hG
    have hE := one_le_ceE k G c hG
    obtain ⟨n₀, hn₀⟩ := h k G c C hG (1 / (ceE k G c : ℝ)) (by positivity)
    refine ⟨max n₀ (ceSize k G c C), fun n hn D hD hT hatt F hF code hsol => ?_⟩
    have hcap := capProfile_profileCap D n G
    obtain ⟨ρ, hρ⟩ := hn₀ n (le_trans (le_max_left _ _) hn) D hD hT hatt _ hcap F hF code hsol
    exact not_dist_of_gap hE (dist_gap hG (le_trans (le_max_right _ _) hn) hD hT hcap hF hsol)
      (dist_of_routes (by positivity) hρ)
  · intro h k G c C hG ε _
    obtain ⟨n₀, hn₀⟩ := h k G c C hG
    exact ⟨n₀, fun n hn D hD hT _ _ hcap F hF code hsol =>
      absurd (solves_mono D (le_profileCap D hcap) hsol) (hn₀ n hn D hD hT F hF code)⟩

end Transpose.Tape.Impl
