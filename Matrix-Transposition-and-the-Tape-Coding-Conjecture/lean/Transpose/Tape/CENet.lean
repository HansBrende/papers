import Transpose.Tape.DefsCE
import Transpose.Tape.CutTrace

/-!
# Block networks of time–space diagrams: general facts

These facts concern networks only; no Turing machine appears.
* `inVals_eq`: the unfolding of the code evaluation.
* Balls and distances: `ball_mono`, `mem_ball_of_walk`, `netDist_le_of_mem_ball`.
* `weak_duality`: a fractional routing at rate `λ` within the capacities gives
  `λ Σ_d rowDist d ≤ Σ_e cap e`.
* `cutset_bound_bitwise`: **the cut-set bound** for a set `U` of nodes. The input bits whose row is
  attached at no node of `U` and whose transposed position is decoded in `U` are decoded inside `U`
  from what enters `U` (`agree_on`), so `2^{|B_U|} |F| ≤ 2^L · 2^{Σ_{e entering U} cap e}`. Its
  entry form and Discrete Isoperimetry are in `CECut.lean`.
* `card_le_of_solves`: rows without a source node cost co-entropy (the cut `U` = all nodes).
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-! ### Code evaluation -/

theorem inVals_eq (C : NetCode) (E : Finset (ℕ × ℕ)) (vis : ℕ → ℕ → Bool) (v : ℕ) (e : ℕ × ℕ) :
    C.inVals E vis v e =
      if e ∈ E ∧ e.2 = v ∧ e.1 < v then C.enc e (C.inVals E vis e.1) (vis e.1) else 0 := by
  rw [NetCode.inVals]
  split_ifs <;> rfl

/-! ### Balls and distances -/

section Balls

variable {E : Finset (ℕ × ℕ)} {N : ℕ}

theorem ball_zero (a : ℕ) : ball E N a 0 = {a} := rfl

theorem ball_succ (a j : ℕ) : ball E N a (j + 1) = ball E N a j ∪
    (Finset.range N).filter (fun v => ∃ u ∈ ball E N a j, (u, v) ∈ E ∨ (v, u) ∈ E) := by
  classical
  simp only [ball]

theorem ball_mono_succ (a j : ℕ) : ball E N a j ⊆ ball E N a (j + 1) := by
  rw [ball_succ]; exact Finset.subset_union_left

theorem ball_mono (a : ℕ) {j j' : ℕ} (h : j ≤ j') : ball E N a j ⊆ ball E N a j' := by
  induction j', h using Nat.le_induction with
  | base => exact le_rfl
  | succ j' _ ih => exact ih.trans (ball_mono_succ a j')

theorem mem_ball_succ {a j u v : ℕ} (hu : u ∈ ball E N a j) (hv : v < N)
    (huv : (u, v) ∈ E ∨ (v, u) ∈ E) : v ∈ ball E N a (j + 1) := by
  classical
  rw [ball_succ]
  apply Finset.mem_union_right
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨hv, u, hu, huv⟩

theorem netDist_le_of_mem_ball {a s j : ℕ} (h : s ∈ ball E N a j) : netDist E N a s ≤ j := by
  classical
  unfold netDist
  rw [dite_eq_left ⟨j, h⟩]
  exact Nat.find_min' _ h

theorem mem_ball_netDist {a s : ℕ} (h : ∃ j, s ∈ ball E N a j) :
    s ∈ ball E N a (netDist E N a s) := by
  classical
  unfold netDist
  rw [dite_eq_left h]
  exact Nat.find_spec h

/-- A walk whose edges have endpoints `< N`, starting in the ball of radius `j`, ends in the ball of
radius `j +` (its number of steps). -/
theorem mem_ball_of_walk (hE : ∀ e ∈ E, e.1 < N ∧ e.2 < N) (a : ℕ) :
    ∀ (P : List ℕ) (u j : ℕ), u ∈ ball E N a j → IsWalk E (u :: P) →
      (u :: P).getLast (List.cons_ne_nil _ _) ∈ ball E N a (j + P.length)
  | [], u, j, hu, _ => by simpa using hu
  | v :: P, u, j, hu, hw => by
    unfold IsWalk at hw
    rw [List.isChain_cons_cons] at hw
    obtain ⟨huv, hw'⟩ := hw
    have hv : v < N := by
      rcases huv with h | h
      · exact (hE _ h).2
      · exact (hE _ h).1
    have hvb : v ∈ ball E N a (j + 1) := mem_ball_succ hu hv huv
    have := mem_ball_of_walk hE a P v (j + 1) hvb hw'
    rw [List.getLast_cons (List.cons_ne_nil _ _)]
    rw [show j + (v :: P).length = j + 1 + P.length by simp; ring]
    exact this

/-- Each step of a walk traverses an edge of `E`, so the walk's traversals of `E` number at least its
steps. -/
theorem length_le_traversals (E : Finset (ℕ × ℕ)) :
    ∀ (P : List ℕ) (u : ℕ), IsWalk E (u :: P) → P.length ≤ ∑ e ∈ E, traversals e (u :: P)
  | [], _, _ => by simp
  | v :: P, u, hw => by
    classical
    unfold IsWalk at hw
    rw [List.isChain_cons_cons] at hw
    obtain ⟨huv, hw'⟩ := hw
    have ih := length_le_traversals E P v hw'
    have hstep : 1 ≤ ∑ e ∈ E, (if (u, v) = e ∨ (v, u) = e then 1 else 0) := by
      rcases huv with h | h
      · exact le_trans (by simp) (Finset.single_le_sum (f := fun e =>
          if (u, v) = e ∨ (v, u) = e then 1 else 0) (fun _ _ => Nat.zero_le _) h)
      · exact le_trans (by simp) (Finset.single_le_sum (f := fun e =>
          if (u, v) = e ∨ (v, u) = e then 1 else 0) (fun _ _ => Nat.zero_le _) h)
    have e1 : ∑ e ∈ E, traversals e (u :: v :: P) =
        ∑ e ∈ E, (if (u, v) = e ∨ (v, u) = e then 1 else 0) + ∑ e ∈ E, traversals e (v :: P) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      simp only [traversals]
    rw [e1]
    simp only [List.length_cons]
    omega

end Balls

/-! ### Edges of a block network -/

section Edges

variable {k : ℕ} (D : TSDiagram k)

theorem mem_memEdges {r : ℕ} {e : ℕ × ℕ} :
    e ∈ D.memEdges r ↔ e.2 = e.1 + 1 ∧ e.1 + 1 < D.nodes r := by
  simp only [memEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨y, ⟨-, hy⟩, rfl⟩; exact ⟨rfl, hy⟩
  · rintro ⟨h1, h2⟩; exact ⟨e.1, ⟨by omega, h2⟩, by rw [Prod.ext_iff]; exact ⟨rfl, h1.symm⟩⟩

theorem mem_chordEdges {r : ℕ} {e : ℕ × ℕ} :
    e ∈ D.chordEdges r ↔ e.1 < D.nodes r ∧ e.2 < D.nodes r ∧
      ∃ (t : Fin k) (β : ℤ), IsChord (pairRes r (D.work t) D.T) β e.1 e.2 := by
  classical
  simp only [chordEdges, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  tauto

theorem not_mem_chordEdges_of_mem_memEdges {r : ℕ} {e : ℕ × ℕ} (he : e ∈ D.memEdges r) :
    e ∉ D.chordEdges r := by
  rw [mem_memEdges] at he
  rw [mem_chordEdges]
  rintro ⟨-, -, t, β, hc⟩
  have := hc.1
  omega

theorem edges_lt {r : ℕ} : ∀ e ∈ D.edges r, e.1 < D.nodes r ∧ e.2 < D.nodes r := by
  intro e he
  rcases Finset.mem_union.1 he with h | h
  · rw [mem_memEdges] at h; omega
  · rw [mem_chordEdges] at h; exact ⟨h.1, h.2.1⟩

theorem edges_fst_lt {r : ℕ} : ∀ e ∈ D.edges r, e.1 < e.2 := by
  intro e he
  rcases Finset.mem_union.1 he with h | h
  · rw [mem_memEdges] at h; omega
  · rw [mem_chordEdges] at h
    obtain ⟨-, -, t, β, hc⟩ := h
    exact lt_trans (Nat.lt_succ_self _) hc.1

end Edges

/-! ### Capacities -/

section Caps

variable {k : ℕ} (D : TSDiagram k)

/-- `Solves` is monotone in the capacities. -/
theorem solves_mono {n G : ℕ} {cap cap' : ℕ × ℕ → ℕ} {F : Set (Fin (n * n * entryBits n) → Bool)}
    {code : NetCode} (hle : ∀ e ∈ D.edges (blockSize G n), cap e ≤ cap' e)
    (h : D.Solves n G cap F code) : D.Solves n G cap' F code := by
  intro x hx
  obtain ⟨h1, h2⟩ := h x hx
  exact ⟨fun e he => lt_of_lt_of_le (h1 e he) (Nat.pow_le_pow_right (by norm_num) (hle e he)), h2⟩

theorem blockCap_mem {n G : ℕ} {mem : ℕ → ℕ} {s : ℕ} {e : ℕ × ℕ}
    (he : e ∈ D.memEdges (blockSize G n)) :
    D.blockCap n G mem s e = mem e.1 * (blockSize G n * G) + s := by
  unfold TSDiagram.blockCap
  rw [ite_eq_left he]

theorem blockCap_chord {n G : ℕ} {mem : ℕ → ℕ} {s : ℕ} {e : ℕ × ℕ}
    (he : e ∈ D.chordEdges (blockSize G n)) :
    D.blockCap n G mem s e = D.chordTapes (blockSize G n) e * (blockSize G n * G) := by
  unfold TSDiagram.blockCap
  rw [ite_eq_right (fun hm => not_mem_chordEdges_of_mem_memEdges D hm he), ite_eq_left he]

/-- The profile capacities are within the profile. -/
theorem capProfile_profileCap (n G : ℕ) : D.CapProfile n G (D.profileCap n G) :=
  ⟨fun e he => by unfold TSDiagram.profileCap; rw [blockCap_mem D he, Nat.add_zero],
    fun e he => by unfold TSDiagram.profileCap; rw [blockCap_chord D he]⟩

/-- Capacities within the profile are at most the profile capacities on every edge. -/
theorem le_profileCap {n G : ℕ} {cap : ℕ × ℕ → ℕ} (hcap : D.CapProfile n G cap) :
    ∀ e ∈ D.edges (blockSize G n), cap e ≤ D.profileCap n G e := by
  intro e he
  rcases Finset.mem_union.1 he with hm | hc
  · unfold TSDiagram.profileCap
    rw [blockCap_mem D hm, Nat.add_zero]
    exact hcap.1 e hm
  · unfold TSDiagram.profileCap
    rw [blockCap_chord D hc]
    exact hcap.2 e hc

/-- No code at the profile capacities iff no code within any capacities in the profile. -/
theorem not_solves_profileCap_iff {n G : ℕ} {F : Set (Fin (n * n * entryBits n) → Bool)}
    {code : NetCode} :
    ¬ D.Solves n G (D.profileCap n G) F code ↔
      ∀ cap : ℕ × ℕ → ℕ, D.CapProfile n G cap → ¬ D.Solves n G cap F code :=
  ⟨fun h _ hcap hs => h (solves_mono D (le_profileCap D hcap) hs),
    fun h => h _ (capProfile_profileCap D n G)⟩

end Caps

/-! ### Weak duality -/

open Classical in
theorem rowDist_eq_zero {k : ℕ} {D : TSDiagram k} {n w r d : ℕ}
    (h : ¬ ∃ a < D.nodes r, d / (n * w) ∈ D.rowsAt n w r a) : D.rowDist n w r d = 0 := by
  unfold rowDist
  rw [dite_eq_right]
  rintro ⟨a, ha⟩
  rw [Finset.mem_filter, Finset.mem_range] at ha
  exact h ⟨a, ha.1, ha.2⟩

open Classical in
theorem rowDist_le {k : ℕ} {D : TSDiagram k} {n w r d a : ℕ} (ha : a < D.nodes r)
    (hd : d / (n * w) ∈ D.rowsAt n w r a) :
    D.rowDist n w r d ≤ netDist (D.edges r) (D.nodes r) a (D.outNode r (tpos n w d)) := by
  unfold rowDist
  have hmem : a ∈ (Finset.range (D.nodes r)).filter (fun a => d / (n * w) ∈ D.rowsAt n w r a) := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨ha, hd⟩
  rw [dite_eq_left ⟨a, hmem⟩]
  exact Finset.inf'_le _ hmem

/-- **Weak duality.** -/
theorem weak_duality {k : ℕ} {D : TSDiagram k} {n G : ℕ} {cap : ℕ × ℕ → ℕ} {ρ : Routing}
    {rate : ℝ} (hρ : D.RoutesAt n G cap ρ rate) :
    rate * ((∑ d ∈ Finset.range (n * n * entryBits n),
        D.rowDist n (entryBits n) (blockSize G n) d : ℕ) : ℝ) ≤
      ∑ e ∈ D.edges (blockSize G n), (cap e : ℝ) := by
  classical
  set w := entryBits n
  set r := blockSize G n
  set E := D.edges r
  set A := (Finset.range (n * n * w)).filter (fun d => ∃ a < D.nodes r,
    d / (n * w) ∈ D.rowsAt n w r a)
  obtain ⟨hpaths, hload⟩ := hρ
  -- the sum over all bits is the sum over the commodities
  have hsplit : (∑ d ∈ Finset.range (n * n * w), D.rowDist n w r d) =
      ∑ d ∈ A, D.rowDist n w r d := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs with h
    · rfl
    · exact rowDist_eq_zero h
  -- each commodity: rate · rowDist ≤ its total traversals
  have hcomm : ∀ d ∈ A, rate * (D.rowDist n w r d : ℝ) ≤
      ∑ P ∈ ρ.paths d, ρ.wt d P * ∑ e ∈ E, (traversals e P : ℝ) := by
    intro d hd
    have hdA := (Finset.mem_filter.1 hd)
    obtain ⟨hP, hsum⟩ := hpaths d (Finset.mem_range.1 hdA.1) hdA.2
    rw [← hsum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro P hPm
    obtain ⟨hwt, hwalk, ⟨a, hhead, ha, hrow⟩, hlast⟩ := hP P hPm
    apply mul_le_mul_of_nonneg_left _ hwt
    -- the walk `P = a :: P'`
    obtain ⟨P', rfl⟩ : ∃ P', P = a :: P' := by
      cases P with
      | nil => simp at hhead
      | cons x P' => simp at hhead; exact ⟨P', by rw [hhead]⟩
    have hball := mem_ball_of_walk (edges_lt D) a P' a 0 (by simp [ball_zero]) hwalk
    rw [Nat.zero_add] at hball
    have hlast' : (a :: P').getLast (List.cons_ne_nil _ _) = D.outNode r (tpos n w d) := by
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hlast
      exact Option.some.inj hlast
    rw [hlast'] at hball
    have h1 := netDist_le_of_mem_ball hball
    have h2 := rowDist_le ha hrow
    have h3 := length_le_traversals E P' a hwalk
    have : (D.rowDist n w r d : ℝ) ≤ ((∑ e ∈ E, traversals e (a :: P') : ℕ) : ℝ) := by
      exact_mod_cast le_trans h2 (le_trans h1 h3)
    push_cast at this
    exact this
  calc rate * ((∑ d ∈ Finset.range (n * n * w), D.rowDist n w r d : ℕ) : ℝ)
      = ∑ d ∈ A, rate * (D.rowDist n w r d : ℝ) := by
        rw [hsplit]; push_cast; rw [Finset.mul_sum]
    _ ≤ ∑ d ∈ A, ∑ P ∈ ρ.paths d, ρ.wt d P * ∑ e ∈ E, (traversals e P : ℝ) :=
        Finset.sum_le_sum hcomm
    _ = ∑ e ∈ E, ∑ d ∈ A, ∑ P ∈ ρ.paths d, ρ.wt d P * (traversals e P : ℝ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro P _
        rw [Finset.mul_sum]
    _ ≤ ∑ e ∈ E, (cap e : ℝ) := Finset.sum_le_sum (fun e he => hload e he)

/-! ### The bits of a set of rows -/

open Classical in
/-- The number of bits `d < m n` whose row `d / m` lies in `S ⊆ range n` is `|S| m`. -/
theorem card_filter_row (m n : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range n) :
    ((Finset.range (n * m)).filter (fun d => d / m ∈ S)).card = S.card * m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  have : (Finset.range (n * m)).filter (fun d => d / m ∈ S) =
      (S ×ˢ Finset.range m).image (fun p => p.1 * m + p.2) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨-, hd⟩
      exact ⟨(d / m, d % m), ⟨hd, Nat.mod_lt _ hm⟩, by rw [Nat.mul_comm]; exact Nat.div_add_mod d m⟩
    · rintro ⟨⟨i, t⟩, ⟨hi, ht⟩, rfl⟩
      have hin := Finset.mem_range.1 (hS hi)
      refine ⟨?_, ?_⟩
      · calc i * m + t < i * m + m := by omega
          _ = (i + 1) * m := by ring
          _ ≤ n * m := Nat.mul_le_mul_right _ hin
      · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt ht, Nat.zero_add]
        exact hi
  rw [this, Finset.card_image_of_injOn, Finset.card_product, Finset.card_range]
  rintro ⟨i, t⟩ hp ⟨i', t'⟩ hp' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp hp'
  simp only at h
  have e1 : (i * m + t) / m = (i' * m + t') / m := by rw [h]
  have e2 : (i * m + t) % m = (i' * m + t') % m := by rw [h]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hp.2, Nat.add_comm (i' * m),
    Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hp'.2] at e1
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp.2, Nat.add_comm (i' * m),
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp'.2] at e2
  simp only [Nat.zero_add] at e1
  rw [e1, e2]

/-! ### The cut-set bound -/

section Cut

variable {k : ℕ} (D : TSDiagram k)

/-- No rows are attached beyond the last node. -/
theorem rowsAt_eq_empty {n w r y : ℕ} (hy : D.nodes r ≤ y) : D.rowsAt n w r y = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  simp only [TSDiagram.rowsAt, Finset.mem_filter] at hi
  obtain ⟨-, τ, hτ, -⟩ := hi
  rw [mem_slotOf] at hτ
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · subst h0; omega
  · have : y * r < D.T := lt_of_le_of_lt hτ.1 hτ.2.2
    rw [← numSlots_spec hr] at this
    exact absurd this (not_lt.2 hy)

/-- **Agreement inside `U`.** If two runs of a code see the same input at the nodes of `U` and carry
the same values on the edges entering `U`, they have the same values into every node of `U`. -/
theorem agree_on {C : NetCode} {E : Finset (ℕ × ℕ)} {U : Set ℕ} {vis vis' : ℕ → ℕ → Bool}
    (hvis : ∀ y ∈ U, vis y = vis' y)
    (hin : ∀ e ∈ E, e.1 ∉ U → e.2 ∈ U → C.edgeVal E vis e = C.edgeVal E vis' e) :
    ∀ y ∈ U, C.inVals E vis y = C.inVals E vis' y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  intro hy
  funext e
  rw [inVals_eq, inVals_eq]
  by_cases h : e ∈ E ∧ e.2 = y ∧ e.1 < y
  · rw [ite_eq_left h, ite_eq_left h]
    by_cases hx : e.1 ∈ U
    · rw [ih e.1 h.2.2 hx, hvis e.1 hx]
    · exact hin e h.1 hx (h.2.1 ▸ hy)
  · rw [ite_eq_right h, ite_eq_right h]

/-- **The cut-set bound, bit level** (TM-free). If a causal code solves complete exchange on `F` within
`cap`, then for every set `U` of nodes, with `B_U` the input bits whose row is attached at no node of
`U` and whose transposed position is decoded at a node of `U`,
`2^{|B_U|} |F| ≤ 2^L · 2^{Σ_{e entering U} cap e}`. Whole columns need not be produced in `U`. -/
theorem cutset_bound_bitwise {n G : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode} (hsol : D.Solves n G cap F code)
    (U : Set ℕ) [DecidablePred (· ∈ U)] :
    2 ^ ((Finset.range (n * n * entryBits n)).filter (fun d =>
        d / (n * entryBits n) ∉ D.rowsIn n (entryBits n) (blockSize G n) U ∧
        D.outNode (blockSize G n) (tpos n (entryBits n) d) ∈ U)).card * F.ncard ≤
      2 ^ (n * n * entryBits n) * 2 ^ (∑ e ∈ D.edgesInto (blockSize G n) U, cap e) := by
  classical
  set r := blockSize G n with hr
  set E := D.edges r with hE
  set src := D.rowsIn n (entryBits n) r U with hsrc
  set Ein := D.edgesInto r U with hEin
  -- cut bits and the rest
  let Pc : ℕ → Prop := fun d => d / (n * entryBits n) ∉ src ∧ D.outNode r (tpos n (entryBits n) d) ∈ U
  set B := (Finset.range (n * n * entryBits n)).filter (fun d => ¬ Pc d) with hB
  let vis : (Fin (n * n * entryBits n) → Bool) → ℕ → ℕ → Bool :=
    fun x y => D.visible n (entryBits n) r y x
  -- the map
  let φ : (Fin (n * n * entryBits n) → Bool) → ((e : Ein) → Fin (2 ^ cap e.1)) × (B → Bool) :=
    fun x => (fun e => if h : code.edgeVal E (vis x) e.1 < 2 ^ cap e.1 then ⟨_, h⟩
      else ⟨0, Nat.two_pow_pos _⟩,
      fun d => x ⟨d.1, Finset.mem_range.1 (Finset.mem_filter.1 d.2).1⟩)
  have hinj : Set.InjOn φ F := by
    intro x hx x' hx' h
    have hBx : ∀ d (hd : d < n * n * entryBits n), ¬ Pc d → x ⟨d, hd⟩ = x' ⟨d, hd⟩ := by
      intro d hd hnc
      have hdB : d ∈ B := Finset.mem_filter.2 ⟨Finset.mem_range.2 hd, hnc⟩
      exact congrFun (congrArg Prod.snd h) ⟨d, hdB⟩
    have hin : ∀ e ∈ E, e.1 ∉ U → e.2 ∈ U → code.edgeVal E (vis x) e = code.edgeVal E (vis x') e := by
      intro e he h1 h2
      have heE : e ∈ Ein := Finset.mem_filter.2 ⟨he, h1, h2⟩
      have hfin := congrFun (congrArg Prod.fst h) ⟨e, heE⟩
      have hv := congrArg Fin.val hfin
      dsimp only [φ] at hv
      rw [dite_eq_left ((hsol x hx).1 e he), dite_eq_left ((hsol x' hx').1 e he)] at hv
      exact hv
    have hvis : ∀ y ∈ U, vis x y = vis x' y := by
      intro y hy
      funext d
      simp only [vis, TSDiagram.visible]
      split_ifs with h1 h2
      · have hyN : y < D.nodes r := by
          by_contra hy'
          push Not at hy'
          rw [rowsAt_eq_empty D hy'] at h2
          simp at h2
        apply hBx d h1
        rintro ⟨hrow, -⟩
        apply hrow
        exact Finset.mem_biUnion.2 ⟨y, Finset.mem_filter.2 ⟨Finset.mem_range.2 hyN, hy⟩, h2⟩
      · rfl
      · rfl
    have hagree := agree_on (C := code) (E := E) hvis hin
    funext ⟨d, hd⟩
    by_cases hc : Pc d
    · -- a cut bit is decoded inside `U`
      have hs : D.outNode r (tpos n (entryBits n) d) ∈ U := hc.2
      have h1 := (hsol x hx).2 d hd
      have h2 := (hsol x' hx').2 d hd
      rw [← h1, ← h2]
      show code.dec _ (code.inVals E (vis x) _) (vis x _) =
        code.dec _ (code.inVals E (vis x') _) (vis x' _)
      rw [hagree _ hs, hvis _ hs]
    · exact hBx d hd hc
  -- counting
  have hcard : F.ncard ≤ 2 ^ (∑ e ∈ Ein, cap e) * 2 ^ B.card := by
    have := Set.ncard_le_ncard_of_injOn φ (t := Set.univ) (fun _ _ => Set.mem_univ _) hinj
      Set.finite_univ
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_pi,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at this
    simp only [Fintype.card_fin] at this
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_coe_sort Ein cap] at this
    exact this
  have hcut := Finset.card_filter_add_card_filter_not (s := Finset.range (n * n * entryBits n)) Pc
  rw [Finset.card_range, ← hB] at hcut
  calc 2 ^ ((Finset.range (n * n * entryBits n)).filter Pc).card * F.ncard
      ≤ 2 ^ ((Finset.range (n * n * entryBits n)).filter Pc).card *
          (2 ^ (∑ e ∈ Ein, cap e) * 2 ^ B.card) := Nat.mul_le_mul_left _ hcard
    _ = 2 ^ (((Finset.range (n * n * entryBits n)).filter Pc).card + B.card) *
          2 ^ (∑ e ∈ Ein, cap e) := by rw [pow_add]; ring
    _ = 2 ^ (n * n * entryBits n) * 2 ^ (∑ e ∈ Ein, cap e) := by rw [hcut]

end Cut

/-- **Rows without a source node cost co-entropy**: the cut-set bound for the set of all nodes, which
no edge enters. -/
theorem card_le_of_solves {k : ℕ} {D : TSDiagram k} {n G : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode} (hsol : D.Solves n G cap F code) :
    2 ^ (((Finset.range n).filter (fun i => ∀ a < D.nodes (blockSize G n),
        i ∉ D.rowsAt n (entryBits n) (blockSize G n) a)).card * (n * entryBits n)) * F.ncard ≤
      2 ^ (n * n * entryBits n) := by
  classical
  have h := cutset_bound_bitwise D hsol Set.univ
  have hE : D.edgesInto (blockSize G n) Set.univ = ∅ := by
    unfold TSDiagram.edgesInto; ext e; simp
  rw [hE, Finset.sum_empty, pow_zero, mul_one] at h
  refine le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (le_of_eq ?_))) h
  rw [← card_filter_row (n * entryBits n) n _ (Finset.filter_subset _ _),
    show n * (n * entryBits n) = n * n * entryBits n by ring]
  congr 1
  apply Finset.filter_congr
  intro d hd
  rw [Finset.mem_range] at hd
  have hnw : 0 < n * entryBits n := by
    rcases Nat.eq_zero_or_pos (n * entryBits n) with h0 | h0
    · rw [show n * n * entryBits n = n * (n * entryBits n) by ring, h0, Nat.mul_zero] at hd; omega
    · exact h0
  have hrow : d / (n * entryBits n) < n := by
    rw [Nat.div_lt_iff_lt_mul hnw]
    linarith [show n * n * entryBits n = n * (n * entryBits n) by ring]
  simp only [TSDiagram.rowsIn, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range,
    Set.mem_univ, and_true, not_exists, not_and]
  exact ⟨fun h => h.2, fun h => ⟨hrow, h⟩⟩

end Transpose.Tape.Impl
