import MergeDepth.Transport
import DirectedRecovery.PathPackingAsymptotics
import DirectedRecovery.SelfDemands

/-!
# Disjoint short paired paths and paired distances (Lemma 4.10, Proposition 4.11(a), (b))

`Realizes tape inp out ρ T κ H N ip op` is the conclusion of Lemma 4.9 for a relation `N` on
coordinates `V`: for every matching of incidences `src j ∈ N (dst j)` (with `src`, `dst` injective)
some run of `T` ticks with the fixed head schedule `H` and occupancy at most `κ` carries a label from
the input cell `ip (src j)` to the output cell `op (dst j)`. It passes to induced relations
(`Realizes.comap`).

* `disjoint_paths_sharp`, `disjoint_paths_bound`: **Lemma 4.10.** If the incidence graph of `N` has
  `m` pairwise vertex-disjoint walks with `s` edges from `L_x` to `R_x`, then
  `m log₂ d ≤ κ K (K + ρ) s T + 3 L`. The `i`th edges of the walks form a matching; the stages are
  realized forwards for even `i` and backwards for odd `i`, and the potential of `MergeDepth.Transport`
  is chained through the junctions (`pot_run` holds in both directions), so no reversed run is built
  and the cost is `s T` ticks instead of `(3a + 1) T`.
* `disjoint_paths_transport`: the same in the form `HasDisjointPathTransport` of the fifth paper,
  with `A_s = 2 s c κ K (K + ρ) + 3` when `T ≤ c (L + 1)`.
* `paired_distance_packing`, `self_demands_le`: **Proposition 4.11(a), (b)**, by the fifth paper's
  formal packing theorem `short_paired_count_log_bound` and its self-demand theorem.
-/

namespace MergeDepth

open Finset Real DirectedRecovery

variable {τ η : Type*} [DecidableEq τ] [Fintype η]

/-- **The realization property** (the conclusion of Lemma 4.9): every matching of incidences of `N`
is carried, from the input cells `ip` to the output cells `op`, by a run of `T` ticks with the head
schedule `H`, `ρ` registers and occupancy at most `κ`. -/
def Realizes {V : Type*} (tape : η → τ) (inp out : τ) (ρ T κ : ℕ) (H : ℕ → η → ℤ)
    (N : V → Finset V) (ip op : V → ℤ) : Prop :=
  ∀ (m : ℕ) (src dst : Fin m → V), Function.Injective src → Function.Injective dst →
    (∀ j, src j ∈ N (dst j)) →
    ∃ loc : ℕ → Fin m → Slot τ ρ, IsRun tape H loc T κ ∧
      (∀ j, loc 0 j = .inl (inp, ip (src j))) ∧ ∀ j, loc T j = .inl (out, op (dst j))

omit [Fintype η] in
/-- Realizability passes to relations that embed into a realized one, such as induced relations. -/
theorem Realizes.comap {V V' : Type*} {tape : η → τ} {inp out : τ} {ρ T κ : ℕ} {H : ℕ → η → ℤ}
    {N : V → Finset V} {ip op : V → ℤ} (hR : Realizes tape inp out ρ T κ H N ip op)
    (N' : V' → Finset V') (e : V' → V) (he : Function.Injective e)
    (hN : ∀ p q, p ∈ N' q → e p ∈ N (e q)) :
    Realizes tape inp out ρ T κ H N' (fun v => ip (e v)) (fun v => op (e v)) := by
  intro m src dst hsrc hdst hinc
  exact hR m (e ∘ src) (e ∘ dst) (he.comp hsrc) (he.comp hdst) fun j => hN _ _ (hinc j)

/-! ### Walks in the paired incidence graph -/

section Walks

variable {V : Type*} {N : V → Finset V}

/-- The side of a port: `true` for the left (input) ports. -/
def isLeft : V ⊕ V → Bool
  | .inl _ => true
  | .inr _ => false

theorem isLeft_ne_of_adj {u v : V ⊕ V} (h : (pairedIncidenceGraph N).Adj u v) :
    isLeft u ≠ isLeft v := by
  cases u <;> cases v <;> simp_all [pairedIncidenceGraph, isLeft]

omit [DecidableEq τ] [Fintype η] in
theorem port_eq_of_side {z z' : V ⊕ V} (hs : isLeft z = isLeft z')
    (hc : portCoordinate z = portCoordinate z') : z = z' := by
  cases z <;> cases z' <;> simp_all [isLeft, portCoordinate]

/-- Along a walk from a left port, the `n`th vertex is a left port exactly when `n` is even. -/
theorem isLeft_getVert {u : V} {v : V ⊕ V} (w : (pairedIncidenceGraph N).Walk (.inl u) v) :
    ∀ n ≤ w.length, isLeft (w.getVert n) = decide (Even n) := by
  intro n
  induction n with
  | zero => intro _; simp [SimpleGraph.Walk.getVert_zero, isLeft]
  | succ n ih =>
    intro hn
    have hadj := w.adj_getVert_succ (by omega : n < w.length)
    have h2 := isLeft_ne_of_adj hadj
    rw [ih (by omega)] at h2
    cases h : isLeft (w.getVert (n + 1)) <;> by_cases he : Even n <;>
      simp_all [Nat.even_add_one]

/-- The `n`th edge of a walk from a left port is an incidence: `y_n ∈ N(y_{n+1})` for even `n`, and
`y_{n+1} ∈ N(y_n)` for odd `n`, where `y_n` is the coordinate of the `n`th vertex. -/
theorem incidence_getVert {u : V} {v : V ⊕ V} (w : (pairedIncidenceGraph N).Walk (.inl u) v)
    {n : ℕ} (hn : n < w.length) :
    (Even n → portCoordinate (w.getVert n) ∈ N (portCoordinate (w.getVert (n + 1)))) ∧
      (¬ Even n → portCoordinate (w.getVert (n + 1)) ∈ N (portCoordinate (w.getVert n))) := by
  have hadj := w.adj_getVert_succ hn
  have h1 := isLeft_getVert w n hn.le
  have h2 := isLeft_getVert w (n + 1) hn
  have side : ∀ z : V ⊕ V, (isLeft z = true → z = .inl (portCoordinate z)) ∧
      (isLeft z = false → z = .inr (portCoordinate z)) := fun z => by
    cases z <;> simp [isLeft, portCoordinate]
  constructor
  · intro he
    have hl : w.getVert n = .inl (portCoordinate (w.getVert n)) := (side _).1 (by rw [h1]; simp [he])
    have hr : w.getVert (n + 1) = .inr (portCoordinate (w.getVert (n + 1))) :=
      (side _).2 (by rw [h2]; simp [Nat.even_add_one, he])
    rw [hl, hr] at hadj
    exact hadj
  · intro ho
    have hl : w.getVert n = .inr (portCoordinate (w.getVert n)) := (side _).2 (by rw [h1]; simp [ho])
    have hr : w.getVert (n + 1) = .inl (portCoordinate (w.getVert (n + 1))) :=
      (side _).1 (by rw [h2]; simp [Nat.even_add_one, ho])
    rw [hl, hr] at hadj
    exact hadj

end Walks

/-! ### Lemma 4.10 -/

open Classical in
/-- **Lemma 4.10, sharp form.** Let `N` be realized (`Realizes`) with input cells `ip` and distinct
output cells `op v ∈ [0, dW)`, `W = d b`, whose row `⌊(op v mod W)/b⌋` is the row `⌊ip v/W⌋`, and let
the input heads of the schedule start in `W` consecutive cells. If the paired incidence graph of `N`
has `m > 0` pairwise vertex-disjoint walks with `s` edges, each from `L_x` to `R_x`, then
`m log₂ d ≤ m log₂ 3 + m log₂ ((d + 1) d b/m) + s T K κ (K + ρ/W)`. -/
theorem disjoint_paths_sharp {V I : Type*} [DecidableEq V] {N : V → Finset V} {tape : η → τ}
    {inp out : τ} {ρ T κ : ℕ} {H : ℕ → η → ℤ} {ip op : V → ℤ}
    (hreal : Realizes tape inp out ρ T κ H N ip op) {d b W : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b)
    (hW : W = d * b) (hop : Function.Injective op) (hrange : ∀ v, 0 ≤ op v ∧ op v < d * W)
    (hrow : ∀ v, op v % W / b = ip v / W) (a : ℤ)
    (hwin : ∀ h, tape h = inp → a ≤ H 0 h ∧ H 0 h ≤ a + W - 1)
    (c : I → V) (p : ∀ i, (pairedIncidenceGraph N).Walk (.inl (c i)) (.inr (c i))) {s : ℕ}
    (J : Finset I) (hlen : ∀ i ∈ J, (p i).length = s)
    (hdisj : (J : Set I).PairwiseDisjoint fun i => (p i).support.toFinset) (hJ : 0 < J.card) :
    J.card * Real.logb 2 d ≤ J.card * Real.logb 2 3 +
      J.card * Real.logb 2 (((d + 1) * d * b : ℕ) / J.card) +
      s * T * Fintype.card η * κ * (Fintype.card η + ρ / W) := by
  have hWpos : 0 < W := by rw [hW]; positivity
  set m := J.card
  let e : Fin m ≃ J := J.equivFin.symm
  let y : ℕ → Fin m → V := fun n x => portCoordinate ((p (e x).1).getVert n)
  have hlenx : ∀ x, (p (e x).1).length = s := fun x => hlen _ (e x).2
  have hside : ∀ x n, n ≤ s → isLeft ((p (e x).1).getVert n) = decide (Even n) :=
    fun x n hn => isLeft_getVert _ n (by rw [hlenx]; exact hn)
  have hodd : ¬ Even s := by
    have x0 : Fin m := ⟨0, hJ⟩
    have := paired_walk_length_odd N _ _ (p (e x0).1)
    rw [hlenx] at this
    exact Nat.not_even_iff_odd.mpr this
  -- the coordinates at one position are distinct
  have hyinj : ∀ n ≤ s, Function.Injective (y n) := by
    intro n hn x x' hxx'
    by_contra hne
    have hne' : (e x).1 ≠ (e x').1 := fun h => hne (e.injective (Subtype.ext h))
    have hD := hdisj (e x).2 (e x').2 hne'
    have hv : (p (e x).1).getVert n = (p (e x').1).getVert n :=
      port_eq_of_side (by rw [hside x n hn, hside x' n hn]) hxx'
    refine Finset.disjoint_left.mp hD
      (List.mem_toFinset.mpr (SimpleGraph.Walk.getVert_mem_support _ n)) ?_
    rw [hv]
    exact List.mem_toFinset.mpr (SimpleGraph.Walk.getVert_mem_support _ n)
  have hy0 : ∀ x, y 0 x = c (e x).1 := fun x => by
    simp [y, SimpleGraph.Walk.getVert_zero, portCoordinate]
  have hys : ∀ x, y s x = c (e x).1 := fun x => by
    simp only [y]
    rw [← hlenx x, SimpleGraph.Walk.getVert_length]
    rfl
  -- the configurations at the junctions
  set A : Fin m → ℤ := fun x => ip (c (e x).1) / W
  set c₁ : ℝ := Fintype.card η * (κ * (Fintype.card η * W + ρ) * Real.log 2)
  let cfgH : ℕ → η → ℤ := fun n => if Even n then H 0 else H T
  let cfgL : ℕ → Fin m → Slot τ ρ := fun n x =>
    if Even n then .inl (inp, ip (y n x)) else .inl (out, op (y n x))
  have hstage : ∀ n < s, pot tape W A (cfgH (n + 1)) (cfgL (n + 1)) ≤
      pot tape W A (cfgH n) (cfgL n) + T * c₁ := by
    intro n hn
    have hinc := fun x => incidence_getVert (p (e x).1) (n := n) (by rw [hlenx]; exact hn)
    by_cases he : Even n
    · obtain ⟨loc, hrun, h0, hT⟩ := hreal m (y n) (y (n + 1)) (hyinj n hn.le) (hyinj (n + 1) hn)
        fun x => (hinc x).1 he
      have hb' := (pot_run hrun hWpos A).1
      have e0 : loc 0 = cfgL n := funext fun x => by simp [cfgL, he, h0]
      have eT : loc T = cfgL (n + 1) := funext fun x => by simp [cfgL, Nat.even_add_one, he, hT]
      have eH : cfgH n = H 0 := by simp [cfgH, he]
      have eH' : cfgH (n + 1) = H T := by simp [cfgH, Nat.even_add_one, he]
      rw [e0, eT] at hb'
      rw [eH, eH']
      exact hb'
    · obtain ⟨loc, hrun, h0, hT⟩ := hreal m (y (n + 1)) (y n) (hyinj (n + 1) hn) (hyinj n hn.le)
        fun x => (hinc x).2 he
      have hb' := (pot_run hrun hWpos A).2
      have e0 : loc 0 = cfgL (n + 1) := funext fun x => by
        simp [cfgL, Nat.even_add_one, he, h0]
      have eT : loc T = cfgL n := funext fun x => by simp [cfgL, he, hT]
      have eH : cfgH n = H T := by simp [cfgH, he]
      have eH' : cfgH (n + 1) = H 0 := by simp [cfgH, Nat.even_add_one, he]
      rw [e0, eT] at hb'
      rw [eH, eH']
      exact hb'
  have hchain : ∀ n ≤ s, pot tape W A (cfgH n) (cfgL n) ≤
      pot tape W A (cfgH 0) (cfgL 0) + n * (T * c₁) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h1 := hstage n (by omega)
      have h2 := ih (by omega)
      push_cast
      linarith
  have hfin := hchain s le_rfl
  have hc0 : cfgL 0 = fun x => (.inl (inp, ip (c (e x).1)) : Slot τ ρ) :=
    funext fun x => by simp [cfgL, hy0]
  have hcs : cfgL s = fun x => (.inl (out, op (c (e x).1)) : Slot τ ρ) :=
    funext fun x => by simp [cfgL, hodd, hys]
  have hH0 : cfgH 0 = H 0 := by simp [cfgH]
  have hHs : cfgH s = H T := by simp [cfgH, hodd]
  rw [hc0, hcs, hH0, hHs] at hfin
  have hst := pot_start_le tape hWpos (H 0) inp (fun x => ip (c (e x).1)) a hwin (ρ := ρ)
  have hcinj : Function.Injective fun x => c (e x).1 := by
    intro x x' h
    exact hyinj 0 (Nat.zero_le s) (by rw [hy0, hy0]; exact h)
  have hen := pot_end_ge tape hb hW (H T) out (fun x => op (c (e x).1)) A (hop.comp hcinj)
    (fun x => hrange _) (fun x => (hrow _).symm) (ρ := ρ)
  rw [Fintype.card_fin] at hst hen
  have key := transport_of_pot hd hb hW hJ (X := s * (T * c₁)) (by linarith)
  refine key.trans_eq ?_
  congr 1
  have hW' : (0 : ℝ) < W := by exact_mod_cast hWpos
  field_simp
  simp only [c₁]
  ring

open Classical in
/-- **Lemma 4.10.** Under the hypotheses of `disjoint_paths_sharp`, with `d ≥ 2` and `L = d² b`,
`m log₂ d ≤ κ K (K + ρ) s T + 3 L` for every `m ≥ 0`. -/
theorem disjoint_paths_bound {V I : Type*} [DecidableEq V] {N : V → Finset V} {tape : η → τ}
    {inp out : τ} {ρ T κ : ℕ} {H : ℕ → η → ℤ} {ip op : V → ℤ}
    (hreal : Realizes tape inp out ρ T κ H N ip op) {d b W : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    (hW : W = d * b) (hop : Function.Injective op) (hrange : ∀ v, 0 ≤ op v ∧ op v < d * W)
    (hrow : ∀ v, op v % W / b = ip v / W) (a : ℤ)
    (hwin : ∀ h, tape h = inp → a ≤ H 0 h ∧ H 0 h ≤ a + W - 1)
    (c : I → V) (p : ∀ i, (pairedIncidenceGraph N).Walk (.inl (c i)) (.inr (c i))) {s : ℕ}
    (J : Finset I) (hlen : ∀ i ∈ J, (p i).length = s)
    (hdisj : (J : Set I).PairwiseDisjoint fun i => (p i).support.toFinset) :
    J.card * Real.logb 2 d ≤ κ * Fintype.card η * (Fintype.card η + ρ) * s * T + 3 * (d * d * b) := by
  rcases Nat.eq_zero_or_pos J.card with hJ0 | hJ
  · rw [hJ0]; push_cast; simp only [zero_mul]; positivity
  have hs := disjoint_paths_sharp hreal (by omega) hb hW hop hrange hrow a hwin c p J hlen hdisj hJ
  -- the end cells `op (c x)`, `x ∈ J`, are distinct cells of `[0, dW)`
  have hmL : J.card ≤ d * d * b := by
    have hcJ : Set.InjOn c J := by
      intro i hi i' hi' h
      by_contra hne
      have hD := hdisj hi hi' hne
      refine Finset.disjoint_left.mp hD
        (List.mem_toFinset.mpr (p i).start_mem_support) ?_
      rw [h]
      exact List.mem_toFinset.mpr (p i').start_mem_support
    have := card_le_of_cells (ι := J) (d := d) (W := W) (fun i => op (c i.1))
      (fun i i' h => Subtype.ext (hcJ i.2 i'.2 (hop h))) (fun i => hrange _)
    rw [Fintype.card_coe, hW] at this
    linarith [mul_assoc d d b]
  have hsum := sharp_terms_le hd hb hJ hmL
  have hWpos : 0 < W := by rw [hW]; positivity
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hWpos
  have hρ : (ρ : ℝ) / W ≤ ρ := div_le_self (by positivity) hWr
  have hK : (s : ℝ) * T * Fintype.card η * κ * (Fintype.card η + ρ / W) ≤
      κ * Fintype.card η * (Fintype.card η + ρ) * s * T := by
    have : (0 : ℝ) ≤ s * T * Fintype.card η * κ := by positivity
    nlinarith
  linarith

open Classical in
/-- **Lemma 4.10, the form used by the fifth paper.** If `T ≤ c (L + 1)`, `L = d² b`, the realized
relation satisfies `HasDisjointPathTransport` with `A_s = 2 s c κ K (K + ρ) + 3`: at most
`A_s L/log₂ d` pairwise vertex-disjoint paired walks with `s` edges. -/
theorem disjoint_paths_transport {V : Type*} [Fintype V] [DecidableEq V] {N : V → Finset V}
    {tape : η → τ} {inp out : τ} {ρ T κ : ℕ} {H : ℕ → η → ℤ} {ip op : V → ℤ}
    (hreal : Realizes tape inp out ρ T κ H N ip op) {d b W : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    (hW : W = d * b) (hop : Function.Injective op) (hrange : ∀ v, 0 ≤ op v ∧ op v < d * W)
    (hrow : ∀ v, op v % W / b = ip v / W) (a : ℤ)
    (hwin : ∀ h, tape h = inp → a ≤ H 0 h ∧ H 0 h ≤ a + W - 1) {c : ℝ} (hc : 0 ≤ c)
    (hT : (T : ℝ) ≤ c * (d * d * b + 1)) (r : ℕ) :
    HasDisjointPathTransport N r (fun s => (2 * s * c * κ * Fintype.card η *
      (Fintype.card η + ρ) + 3) * ((d : ℝ) ^ 2 * b) / Real.logb 2 d) := by
  intro p _ s _ _ J hlen hdisj
  have h := disjoint_paths_bound hreal hd hb hW hop hrange hrow a hwin Subtype.val p J hlen hdisj
  have hlog : 0 < Real.logb 2 d := Real.logb_pos (by norm_num) (by exact_mod_cast hd)
  have hL : (1 : ℝ) ≤ d * d * b := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hT' : (T : ℝ) ≤ 2 * c * (d * d * b) := by nlinarith
  rw [le_div_iff₀ hlog]
  have : (κ : ℝ) * Fintype.card η * (Fintype.card η + ρ) * s * T ≤
      κ * Fintype.card η * (Fintype.card η + ρ) * s * (2 * c * (d * d * b)) :=
    mul_le_mul_of_nonneg_left hT' (by positivity)
  nlinarith

/-! ### Proposition 4.11 -/

open Classical in
/-- **Proposition 4.11(a).** For every `Q ⊆ V` whose induced incidence graph `E_Q` has maximum degree
at most `Δ`, the coordinates of `Q` whose two ports lie within distance `r` in `E_Q` number at most
`∑_{s ≤ r odd} (s + 1) ν_r A_s L/log₂ d` (`pathPackingConstant`), `A_s = 2 s c κ K (K + ρ) + 3`. -/
theorem paired_distance_packing {V : Type*} [Fintype V] [DecidableEq V] {N : V → Finset V}
    {tape : η → τ} {inp out : τ} {ρ T κ : ℕ} {H : ℕ → η → ℤ} {ip op : V → ℤ}
    (hreal : Realizes tape inp out ρ T κ H N ip op) {d b W : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    (hW : W = d * b) (hop : Function.Injective op) (hrange : ∀ v, 0 ≤ op v ∧ op v < d * W)
    (hrow : ∀ v, op v % W / b = ip v / W) (a : ℤ)
    (hwin : ∀ h, tape h = inp → a ≤ H 0 h ∧ H 0 h ≤ a + W - 1) {c : ℝ} (hc : 0 ≤ c)
    (hT : (T : ℝ) ≤ c * (d * d * b + 1)) (Q : Finset V) (r Δ : ℕ)
    (hdeg : ∀ v, (pairedIncidenceGraph (inducedNeighborhood N Q)).degree v ≤ Δ) :
    ((shortPairedCoordinates (inducedNeighborhood N Q) r).card : ℝ) ≤
      pathPackingConstant r Δ (fun s => 2 * s * c * κ * Fintype.card η *
        (Fintype.card η + ρ) + 3) * (((d : ℝ) ^ 2 * b) / Real.logb 2 d) := by
  have hreal' := hreal.comap (inducedNeighborhood N Q) Subtype.val Subtype.val_injective
    (fun p q hp => by simpa [inducedNeighborhood] using hp)
  have ht := disjoint_paths_transport hreal' hd hb hW (hop.comp Subtype.val_injective)
    (fun v => hrange v.1) (fun v => hrow v.1) a hwin hc hT r
  exact short_paired_count_log_bound (inducedNeighborhood N Q) r Δ d b _ hdeg ht

open Classical in
/-- **Proposition 4.11(b).** The self-demands `p ∈ N p` number at most `A_1 L/log₂ d`,
`A_1 = 2 c κ K (K + ρ) + 3`. -/
theorem self_demands_le {V : Type*} [Fintype V] [DecidableEq V] {N : V → Finset V}
    {tape : η → τ} {inp out : τ} {ρ T κ : ℕ} {H : ℕ → η → ℤ} {ip op : V → ℤ}
    (hreal : Realizes tape inp out ρ T κ H N ip op) {d b W : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    (hW : W = d * b) (hop : Function.Injective op) (hrange : ∀ v, 0 ≤ op v ∧ op v < d * W)
    (hrow : ∀ v, op v % W / b = ip v / W) (a : ℤ)
    (hwin : ∀ h, tape h = inp → a ≤ H 0 h ∧ H 0 h ≤ a + W - 1) {c : ℝ} (hc : 0 ≤ c)
    (hT : (T : ℝ) ≤ c * (d * d * b + 1)) :
    ((selfDemandCoordinates N).card : ℝ) ≤
      (2 * c * κ * Fintype.card η * (Fintype.card η + ρ) + 3) * ((d : ℝ) ^ 2 * b) /
        Real.logb 2 d := by
  apply self_demands_count_of_disjoint_transport N
  intro S p _ hlen hdisj
  have h := disjoint_paths_bound hreal hd hb hW hop hrange hrow a hwin (I := S) Subtype.val p
    (s := 1) univ (fun i _ => hlen i) (by simpa using hdisj)
  rw [card_univ, Fintype.card_coe] at h
  have hlog : 0 < Real.logb 2 d := Real.logb_pos (by norm_num) (by exact_mod_cast hd)
  have hL : (1 : ℝ) ≤ d * d * b := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hT' : (T : ℝ) ≤ 2 * c * (d * d * b) := by nlinarith
  rw [le_div_iff₀ hlog]
  have : (κ : ℝ) * Fintype.card η * (Fintype.card η + ρ) * (1 : ℕ) * T ≤
      κ * Fintype.card η * (Fintype.card η + ρ) * 1 * (2 * c * (d * d * b)) := by
    push_cast
    exact mul_le_mul_of_nonneg_left hT' (by positivity)
  push_cast at h this
  nlinarith

end MergeDepth
