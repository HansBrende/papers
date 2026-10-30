import MergeDepth.DeepNestingHops

/-!
# Block labels, the block-pair label on the cover, errors and service (Section 7.1)

* `potentialOf J`: the potential of a jump function (`Φ(0) = 0`, `Φ(t) - Φ(t - 1) = J(t)`;
  `potentialOf_sub_one`, `eq_potentialOf`, `potentialOf_comp_add`, `sum_Ico_eq_potentialOf`).
* **The block label `B(a, K)`** (the eighth paper's Definition 5.11) as a property of a jump function
  on the turns of `U` (`IsBlockLabel`: turn-supported, `1` at the tips, `1 + A_l` at every apex,
  `E_l + 1 - M(V^b)` at every valley, `M(V^b)` the sum of the jumps over the span of the back child,
  `periodVApices_back_child`), whose level parameters `A_l = blockA`, `E_l = blockE` (the tenth
  paper's closed forms) satisfy the recursion of Definition 5.11 (`blockParams_served`,
  `blockParams_canceller`, with `firstCanceller_spec`). **Existence and uniqueness**: the tenth paper's explicit jumps
  `blockJumps` are a block label (`blockJumps_isBlockLabel`, through `periodTurnJump_V` and
  `sum_blockJumps_span`) and every block label equals them (`IsBlockLabel.eq_blockJumps`, by
  induction on the level and the span lemma `isTurnOfLevel_ge_of_span`); so **the potential of the
  block label is the model's `blockPotential`** (`IsBlockLabel.potentialOf_eq`,
  `potentialOf_blockJumps`).
* `headPotential`: the potential `Φ_h` of head `h` carrying `B(a, K)` at its own turns;
  `blockPairLabel`: the block-pair label `G = (Φ₁ + Φ₂) mod q`, with values in `[0, q)`,
  turn-supported (`blockPairLabel_eq_of_not_turn`) and `rP`-periodic for `q ∣ r`, so a label on the
  `r`-fold cover (`blockPairLabel_add_mul`).
* `hopError G q p u = (G(u) - G(p) - 1) mod q`; **`hopError_blockPairLabel`: the model's errors
  `pairHopErr` are the errors of the block-pair label** (head `h`'s own time is real time shifted by
  `c_h`); errors are `P`-periodic (`hopError_add_mul_period`).
* `coverClassErr` (the total error of the class `(h, k)` on the `r`-fold cover), `ThetaServes`
  (total error at most `θ q n_h/(2N)`), `DoublyThetaServes`; `thetaServes_iff_mean` (mean error at
  most `θ q`), `coverClassErr_eq` (`r` times the error of one period, any window), and the bridge
  **`ThetaServes.servedOnWitness`**: a level `θ`-served for head `h` on any cover is
  `ServedOnWitness` in the model.
-/

namespace MergeDepth

open Finset DirectedReciprocity

/-! ### Potentials -/

theorem sum_Ico_split_int {M : Type*} [AddCommMonoid M] (f : ℤ → M) {a b c : ℤ} (hab : a ≤ b)
    (hbc : b ≤ c) : ∑ x ∈ Ico a c, f x = ∑ x ∈ Ico a b, f x + ∑ x ∈ Ico b c, f x := by
  rw [← Finset.Ico_union_Ico_eq_Ico hab hbc, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _)]

theorem sum_Ico_singleton_int {M : Type*} [AddCommMonoid M] (f : ℤ → M) (a : ℤ) :
    ∑ x ∈ Ico a (a + 1), f x = f a := by
  rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one (le_refl a) f]; simp

/-- The **potential** of a jump function `J : ℤ → ℤ`: `Φ(0) = 0` and `Φ(t) - Φ(t - 1) = J(t)`, that
is, `Φ(t) = ∑_{0 < τ ≤ t} J(τ)` for `t ≥ 0` and `Φ(t) = -∑_{t < τ ≤ 0} J(τ)` for `t < 0`. -/
def potentialOf (J : ℤ → ℤ) (t : ℤ) : ℤ :=
  if 0 ≤ t then ∑ τ ∈ Ico 1 (t + 1), J τ else -∑ τ ∈ Ico (t + 1) 1, J τ

theorem potentialOf_zero (J : ℤ → ℤ) : potentialOf J 0 = 0 := by simp [potentialOf]

theorem potentialOf_sub_one (J : ℤ → ℤ) (t : ℤ) : potentialOf J t - potentialOf J (t - 1) = J t := by
  unfold potentialOf
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [ite_eq_right (by omega : ¬ (0 ≤ t)), ite_eq_right (by omega : ¬ (0 ≤ t - 1)), sub_add_cancel,
      sum_Ico_split_int J (a := t) (b := t + 1) (c := 1) (by omega) (by omega),
      sum_Ico_singleton_int]
    ring
  · have h01 : ∑ x ∈ Ico (0:ℤ) 1, J x = J 0 := by simpa using sum_Ico_singleton_int J 0
    simp [h01]
  · rw [ite_eq_left ht.le, ite_eq_left (by omega : 0 ≤ t - 1), sub_add_cancel,
      ← Finset.sum_Ico_add_eq_sum_Ico_add_one (show (1 : ℤ) ≤ t by omega)]
    ring

/-- A function with `Φ(0) = 0` and increments `J` is the potential of `J`. -/
theorem eq_potentialOf {J Φ : ℤ → ℤ} (h0 : Φ 0 = 0) (hs : ∀ t, Φ t - Φ (t - 1) = J t) :
    Φ = potentialOf J := by
  have key : ∀ n : ℕ, Φ n = potentialOf J n ∧ Φ (-(n : ℤ)) = potentialOf J (-(n : ℤ)) := by
    intro n
    induction n with
    | zero => simp [h0, potentialOf_zero]
    | succ n ih =>
      have h1 := hs ((n + 1 : ℕ) : ℤ)
      have h2 := potentialOf_sub_one J ((n + 1 : ℕ) : ℤ)
      have h3 := hs (-(n : ℤ))
      have h4 := potentialOf_sub_one J (-(n : ℤ))
      rw [show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring] at h1 h2
      rw [show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by push_cast; ring] at h3 h4
      constructor <;> linarith [ih.1, ih.2]
  funext t
  rcases le_or_gt 0 t with ht | ht
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, t = n := ⟨t.toNat, by omega⟩
    exact (key n).1
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, t = -(n : ℤ) := ⟨(-t).toNat, by omega⟩
    exact (key n).2

/-- The potential of shifted jumps. -/
theorem potentialOf_comp_add (J : ℤ → ℤ) (c t : ℤ) :
    potentialOf (fun τ => J (τ + c)) t = potentialOf J (t + c) - potentialOf J c := by
  have := eq_potentialOf (J := fun τ => J (τ + c)) (Φ := fun t => potentialOf J (t + c) - potentialOf J c)
    (by simp) (fun t => by
      have := potentialOf_sub_one J (t + c)
      rw [show t + c - 1 = t - 1 + c by ring] at this
      show potentialOf J (t + c) - potentialOf J c - (potentialOf J (t - 1 + c) - potentialOf J c) =
        J (t + c)
      linarith)
  rw [← this]

/-- Telescoping: the sum of the jumps over `[a, b)` is `Φ(b - 1) - Φ(a - 1)`. -/
theorem sum_Ico_eq_potentialOf (J : ℤ → ℤ) {a b : ℤ} (hab : a ≤ b) :
    ∑ τ ∈ Ico a b, J τ = potentialOf J (b - 1) - potentialOf J (a - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show a + ((n + 1 : ℕ) : ℤ) = (a + n) + 1 by push_cast; ring,
      ← Finset.sum_Ico_add_eq_sum_Ico_add_one (show a ≤ a + n by omega), ih (by omega)]
    have := potentialOf_sub_one J (a + n)
    rw [show a + (n : ℤ) + 1 - 1 = a + n by ring]
    linarith

/-! ### The block labels on `U` (the eighth paper's Definition 5.11) -/

theorem strokeTurnJumpAux_succ (s0 m : ℕ) (cb cf : ℕ → ℤ) (i e τ : ℕ) :
    strokeTurnJumpAux s0 m cb cf i (e + 1) τ =
      if τ < scaleR s0 i then 0
      else if τ = scaleR s0 i then cb (i + 1)
      else if τ < scaleR s0 i + strokeLen s0 m (i + 1) then
        strokeTurnJumpAux s0 m cb cf (i + 1) e (τ - scaleR s0 i)
      else if τ = scaleR s0 i + strokeLen s0 m (i + 1) then
        cf (i + 1) - cb (i + 1) - strokeMass m cf (i + 1)
      else if τ < scaleR s0 i + 2 * strokeLen s0 m (i + 1) then
        strokeTurnJumpAux s0 m cb cf (i + 1) e (τ - scaleR s0 i - strokeLen s0 m (i + 1))
      else 0 := rfl

/-- The tenth paper's stroke jumps at the apex and the valley of an inner V. -/
theorem strokeTurnJumpAux_vApex {s0 m : ℕ} (hms : m ≤ s0) (cb cf : ℕ → ℤ) :
    ∀ d' i d, i + d = m → d' < d → ∀ β ∈ vApicesAux s0 m i d',
      strokeTurnJumpAux s0 m cb cf i d β = cb (i + 1 + d') ∧
      strokeTurnJumpAux s0 m cb cf i d (β + strokeLen s0 m (i + 1 + d')) =
        cf (i + 1 + d') - cb (i + 1 + d') - strokeMass m cf (i + 1 + d') := by
  intro d'
  induction d' with
  | zero =>
    intro i d hid hd β hβ
    rw [vApicesAux, mem_singleton] at hβ; subst hβ
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have hp := strokeLen_pos s0 m (i + 1)
    rw [strokeTurnJumpAux_succ, strokeTurnJumpAux_succ, add_zero]
    constructor
    · rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  | succ d' ih =>
    intro i d hid hd β hβ
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have hsp := strokeLen_succ (s0 := s0) (m := m) (i := i) (by omega) hms
    rw [vApicesAux, mem_union, mem_image, mem_image] at hβ
    rw [show i + 1 + (d' + 1) = i + 1 + 1 + d' by ring, strokeTurnJumpAux_succ, strokeTurnJumpAux_succ]
    have hR := scaleR_pos s0 (i + 1)
    rcases hβ with ⟨γ, hγ, rfl⟩ | ⟨γ, hγ, rfl⟩
    · obtain ⟨h1, h2⟩ := vApicesAux_span hms d' (i + 1) (by omega) γ hγ
      have hp := strokeLen_pos s0 m (i + 1 + 1 + d')
      obtain ⟨ih1, ih2⟩ := ih (i + 1) e (by omega) (by omega) γ hγ
      constructor
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
          show scaleR s0 i + γ - scaleR s0 i = γ by omega, ih1]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
          show scaleR s0 i + γ + strokeLen s0 m (i + 1 + 1 + d') - scaleR s0 i =
            γ + strokeLen s0 m (i + 1 + 1 + d') by omega, ih2]
    · obtain ⟨h1, h2⟩ := vApicesAux_span hms d' (i + 1) (by omega) γ hγ
      have hp := strokeLen_pos s0 m (i + 1 + 1 + d')
      obtain ⟨ih1, ih2⟩ := ih (i + 1) e (by omega) (by omega) γ hγ
      constructor
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_left (by omega),
          show scaleR s0 i + strokeLen s0 m (i + 1) + γ - scaleR s0 i - strokeLen s0 m (i + 1) = γ by
            omega, ih1]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_left (by omega),
          show scaleR s0 i + strokeLen s0 m (i + 1) + γ + strokeLen s0 m (i + 1 + 1 + d') -
            scaleR s0 i - strokeLen s0 m (i + 1) = γ + strokeLen s0 m (i + 1 + 1 + d') by omega, ih2]

/-- The tenth paper's period jumps at the apex and the valley of a level-`l` V of a period. -/
theorem periodTurnJump_V {s0 m l : ℕ} (hms : m ≤ s0) (hl1 : 1 ≤ l) (hlm : l ≤ m) (cb cf : ℕ → ℤ)
    (jTip : ℤ) {α : ℕ} (hα : α ∈ periodVApices s0 m l) :
    periodTurnJump s0 m cb cf jTip α = cb l ∧
      periodTurnJump s0 m cb cf jTip (α + strokeLen s0 m l) = cf l - cb l - strokeMass m cf l := by
  rw [periodVApices, mem_biUnion] at hα
  obtain ⟨q, hq, hα⟩ := hα; rw [mem_range] at hq
  obtain ⟨β, hβ, rfl⟩ := mem_image.mp hα
  obtain ⟨h1, h2⟩ := vApicesAux_span hms (l - 1) 0 (by omega) β hβ
  rw [show 0 + 1 + (l - 1) = l by omega] at h2
  have hpi := strokeLen_pos s0 m 0
  have hpl := strokeLen_pos s0 m l
  have hR0 := scaleR_pos s0 0
  obtain ⟨j1, j2⟩ := strokeTurnJumpAux_vApex hms cb cf (l - 1) 0 m (by omega) (by omega) β hβ
  rw [show 0 + 1 + (l - 1) = l by omega] at j1 j2
  have hmod1 : (q * strokeLen s0 m 0 + β) % strokeLen s0 m 0 = β := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hmod2 : (q * strokeLen s0 m 0 + β + strokeLen s0 m l) % strokeLen s0 m 0 =
      β + strokeLen s0 m l := by
    rw [show q * strokeLen s0 m 0 + β + strokeLen s0 m l = (β + strokeLen s0 m l) + q * strokeLen s0 m 0
      by ring, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  unfold periodTurnJump strokeTurnJump
  dsimp only
  simp only [Nat.sub_zero]
  constructor
  · rw [ite_eq_right (by interval_cases q <;> omega), hmod1,
      ite_eq_left ⟨by interval_cases q <;> omega, by omega⟩, j1]
  · rw [ite_eq_right (by interval_cases q <;> omega), hmod2,
      ite_eq_left ⟨by interval_cases q <;> omega, by omega⟩, j2]

/-- The V attached at the end of the segment of the back stroke of a V (its back child). -/
theorem vApicesAux_back_child {s0 m : ℕ} : ∀ d i, ∀ β ∈ vApicesAux s0 m i d,
    β + scaleR s0 (i + 1 + d) ∈ vApicesAux s0 m i (d + 1) := by
  intro d
  induction d with
  | zero =>
    intro i β hβ
    rw [vApicesAux, mem_singleton] at hβ; subst hβ
    rw [vApicesAux, mem_union, mem_image]
    left; exact ⟨scaleR s0 (i + 1), by simp [vApicesAux], by ring⟩
  | succ d ih =>
    intro i β hβ
    rw [vApicesAux, mem_union, mem_image, mem_image] at hβ
    rw [vApicesAux, mem_union, mem_image, mem_image]
    rcases hβ with ⟨γ, hγ, rfl⟩ | ⟨γ, hγ, rfl⟩
    · left
      exact ⟨γ + scaleR s0 (i + 1 + 1 + d), ih (i + 1) γ hγ, by
        rw [show i + 1 + (d + 1) = i + 1 + 1 + d by ring]; ring⟩
    · right
      exact ⟨γ + scaleR s0 (i + 1 + 1 + d), ih (i + 1) γ hγ, by
        rw [show i + 1 + (d + 1) = i + 1 + 1 + d by ring]; ring⟩

theorem periodVApices_back_child {s0 m l : ℕ} (hl1 : 1 ≤ l) {α : ℕ}
    (hα : α ∈ periodVApices s0 m l) : α + scaleR s0 l ∈ periodVApices s0 m (l + 1) := by
  rw [periodVApices, mem_biUnion] at hα ⊢
  obtain ⟨q, hq, hα⟩ := hα
  obtain ⟨β, hβ, rfl⟩ := mem_image.mp hα
  refine ⟨q, hq, mem_image.mpr ⟨β + scaleR s0 l, ?_, by ring⟩⟩
  have := vApicesAux_back_child (l - 1) 0 β hβ
  rwa [show 0 + 1 + (l - 1) = l by omega, show l - 1 + 1 = l + 1 - 1 by omega] at this

/-- The jumps of the block label `B(a, K)` on `U`, given explicitly by the tenth paper's library. -/
def blockJumps (s0 m a : ℕ) (K : ℤ) (t : ℤ) : ℤ :=
  periodTurnJump s0 m (pathSumBack (blockA m a K)) (pathSumFwd (blockA m a K) (blockE m a K)) 1
    (t % (dnpPeriod s0 m : ℤ)).toNat

/-- `J` is the jump function of **the block label `B(a, K)`** on `U` (the eighth paper's
Definition 5.11): it vanishes off the turns (turn-supported), is `1` at the tips, `1 + A_l` at the apex
of every V of level `l` (in every period), and `E_l + 1 - M(V^b)` at its valley, where `M(V^b)` is the
sum of the jumps over the span `[α + R_l, α + R_l + 2Π_{l+1})` of the V attached at the end of the
segment of its back stroke (`0` at level `m`). -/
structure IsBlockLabel (s0 m a : ℕ) (K : ℤ) (J : ℤ → ℤ) : Prop where
  off_turn : ∀ t, ¬ IsTurnZ (dnpWalk s0 m) t → J t = 0
  tip : ∀ t, IsTurnOfLevel s0 m t 0 → J t = 1
  apex : ∀ (l α : ℕ) (n : ℤ), 1 ≤ l → l ≤ m → α ∈ periodVApices s0 m l →
    J ((α : ℤ) + n * dnpPeriod s0 m) = 1 + blockA m a K l
  valley : ∀ (l α : ℕ) (n : ℤ), 1 ≤ l → l ≤ m → α ∈ periodVApices s0 m l →
    J ((α : ℤ) + strokeLen s0 m l + n * dnpPeriod s0 m) = blockE m a K l + 1 -
      (if l < m then ∑ τ ∈ Ico ((α : ℤ) + scaleR s0 l + n * dnpPeriod s0 m)
          ((α : ℤ) + scaleR s0 l + n * dnpPeriod s0 m + 2 * strokeLen s0 m (l + 1)), J τ else 0)

theorem blockPotential_zero (s0 m a : ℕ) (K : ℤ) : blockPotential s0 m a K 0 = 0 := by
  unfold blockPotential
  have := turnPotential_of_lt (s0 := s0) (m := m) (pathSumBack (blockA m a K))
    (pathSumFwd (blockA m a K) (blockE m a K)) 1 (t := 0) (dnpPeriod_pos s0 m)
  simp only [Nat.cast_zero] at this
  rw [this, evalPhiRec_zero]

/-- The potential of the explicit jumps is the model's `blockPotential`. -/
theorem potentialOf_blockJumps {s0 m : ℕ} (hms : m ≤ s0) (a : ℕ) (K : ℤ) :
    potentialOf (blockJumps s0 m a K) = blockPotential s0 m a K :=
  (eq_potentialOf (blockPotential_zero s0 m a K) (fun t => turnPotential_sub_one hms _ _ _ t)).symm

theorem blockJumps_add_mul_period (s0 m a : ℕ) (K t n : ℤ) :
    blockJumps s0 m a K (t + n * dnpPeriod s0 m) = blockJumps s0 m a K t := by
  unfold blockJumps; rw [Int.add_mul_emod_self_right]

/-- The jumps over the span of the back child of a level-`l` V add up to `M(V^b) = ∑_{i > l} c_f(i)`. -/
theorem sum_blockJumps_span {s0 m l : ℕ} (hms : m ≤ s0) (hl1 : 1 ≤ l) (hlm : l < m) (a : ℕ)
    (K : ℤ) {α : ℕ} (hα : α ∈ periodVApices s0 m l) (n : ℤ) :
    ∑ τ ∈ Ico ((α : ℤ) + scaleR s0 l + n * dnpPeriod s0 m)
        ((α : ℤ) + scaleR s0 l + n * dnpPeriod s0 m + 2 * strokeLen s0 m (l + 1)),
      blockJumps s0 m a K τ =
      strokeMass m (pathSumFwd (blockA m a K) (blockE m a K)) l := by
  set cb := pathSumBack (blockA m a K)
  set cf := pathSumFwd (blockA m a K) (blockE m a K)
  have hsp := strokeLen_succ (s0 := s0) (m := m) (i := l) hlm hms
  have hβ := periodVApices_back_child hl1 hα
  obtain ⟨hRβ, C, hC⟩ := evalPhiRec_parent (k := l + 1) (by omega) (by omega) hms cb cf 1 hβ
  rw [show l + 1 - 1 = l by omega, show α + scaleR s0 l - scaleR s0 l = α by omega] at hC
  have hspan := periodVApices_span_subset hl1 hlm.le hms hα
  have hRl := scaleR_pos s0 l
  have hpl : scaleR s0 l ≤ strokeLen s0 m l := by unfold strokeLen; nlinarith
  rw [sum_Ico_eq_potentialOf _ (by have := strokeLen_pos s0 m (l + 1); omega),
    potentialOf_blockJumps hms]
  unfold blockPotential
  rw [show (α : ℤ) + scaleR s0 l + n * dnpPeriod s0 m + 2 * strokeLen s0 m (l + 1) - 1 =
      ((α + (strokeLen s0 m l - 1) : ℕ) : ℤ) + n * dnpPeriod s0 m by
        push_cast [Nat.cast_sub (strokeLen_pos s0 m l)]; rw [hsp]; push_cast; ring,
    show (α : ℤ) + scaleR s0 l + n * dnpPeriod s0 m - 1 =
      ((α + (scaleR s0 l - 1) : ℕ) : ℤ) + n * dnpPeriod s0 m by
        push_cast [Nat.cast_sub hRl]; ring,
    turnPotential_add_mul_period, turnPotential_add_mul_period,
    turnPotential_of_lt _ _ _ (by omega), turnPotential_of_lt _ _ _ (by omega),
    hC _ (by omega), hC _ (by omega),
    strokePhiRec_lt_scaleR cb cf (o := scaleR s0 l - 1) hlm.le (by omega)]
  have htail := strokePhiRec_tail_fwd_chain cb cf (k := l) (l := m) (y := 1) hlm.le le_rfl hms
    (by norm_num) (Nat.one_le_iff_ne_zero.mpr (strokeLen_pos s0 m m).ne')
  have hm0 : strokePhiRec s0 m cb cf m (strokeLen s0 m m - 1) = 0 := by
    unfold strokePhiRec; rw [Nat.sub_self]; rfl
  rw [htail, hm0]
  unfold strokeMass
  ring

/-- **The explicit jumps are a block label** (existence in Definition 5.11). -/
theorem blockJumps_isBlockLabel {s0 m : ℕ} (hms : m ≤ s0) (a : ℕ) (K : ℤ) :
    IsBlockLabel s0 m a K (blockJumps s0 m a K) := by
  have hP : (0 : ℤ) < dnpPeriod s0 m := by exact_mod_cast dnpPeriod_pos s0 m
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun l α n hl1 hlm hα => ?_, fun l α n hl1 hlm hα => ?_⟩
  · by_contra hne
    exact ht ((isTurnZ_dnpWalk_iff hms t).2 (periodTurnJump_support _ _ _ hne))
  · rcases ht with ht | ⟨-, ht⟩
    · obtain ⟨l', hl', ht⟩ := mem_biUnion.mp ht
      obtain ⟨τ', -, he⟩ := mem_image.mp ht
      simp only [Prod.mk.injEq] at he
      rw [mem_Icc] at hl'; omega
    · unfold blockJumps periodTurnJump; dsimp only
      rw [ite_eq_left ht]
  · have hlt := periodVApices_lt hms hl1 hlm hα
    unfold blockJumps
    rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast
      (show α < dnpPeriod s0 m by omega)), Int.toNat_natCast,
      (periodTurnJump_V hms hl1 hlm _ _ 1 hα).1]
    rfl
  · have hlt := periodVApices_lt hms hl1 hlm hα
    have hv := (periodTurnJump_V hms hl1 hlm (pathSumBack (blockA m a K))
      (pathSumFwd (blockA m a K) (blockE m a K)) 1 hα).2
    unfold blockJumps
    rw [Int.add_mul_emod_self_right, show (α : ℤ) + strokeLen s0 m l = ((α + strokeLen s0 m l : ℕ) : ℤ)
      by push_cast; ring, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt), Int.toNat_natCast, hv]
    split_ifs with hlm'
    · have := sum_blockJumps_span hms hl1 hlm' a K hα n
      unfold blockJumps at this
      rw [this]
      unfold pathSumFwd pathSumBack; ring
    · rw [strokeMass_eq_zero _ (by omega)]
      unfold pathSumFwd pathSumBack; ring

/-- **The block label is unique**: every jump function satisfying Definition 5.11 is `blockJumps`
(induction on the level from `m` upwards, through the spans of the back children). -/
theorem IsBlockLabel.eq_blockJumps {s0 m a : ℕ} {K : ℤ} {J : ℤ → ℤ} (hms : m ≤ s0)
    (hJ : IsBlockLabel s0 m a K J) : J = blockJumps s0 m a K := by
  have hJ0 := blockJumps_isBlockLabel hms a K
  have hP : (0 : ℤ) < dnpPeriod s0 m := by exact_mod_cast dnpPeriod_pos s0 m
  -- the claim, by induction on the level from `m` upwards
  have claim : ∀ e : ℕ, ∀ τ l, m + 1 ≤ l + e → IsTurnOfLevel s0 m τ l → J τ = blockJumps s0 m a K τ := by
    intro e
    induction e with
    | zero => intro τ l hl hτ; have := hτ.le_m; omega
    | succ e ih =>
      intro τ l hl hτ
      by_cases hl' : m + 1 ≤ l + e
      · exact ih τ l hl' hτ
      have hτ' := hτ
      rcases hτ with hτ | ⟨rfl, hτ⟩
      · obtain ⟨l', hl'', hτ⟩ := mem_biUnion.mp hτ
        obtain ⟨τ'', hτ'', he⟩ := mem_image.mp hτ
        simp only [Prod.mk.injEq] at he
        obtain ⟨he1, rfl⟩ := he
        rw [mem_Icc] at hl''
        have hdec : τ = ((τ % (dnpPeriod s0 m : ℤ)).toNat : ℤ) + τ / dnpPeriod s0 m * dnpPeriod s0 m := by
          rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hP.ne')]
          linarith [Int.emod_add_mul_ediv τ (dnpPeriod s0 m)]
        rcases mem_union.mp hτ'' with hA | hV
        · rw [hdec, ← he1, hJ.apex l' τ'' _ hl''.1 hl''.2 hA, hJ0.apex l' τ'' _ hl''.1 hl''.2 hA]
        · obtain ⟨α, hα, hαe⟩ := mem_image.mp hV
          rw [hdec, ← he1, ← hαe]
          push_cast
          rw [hJ.valley l' α _ hl''.1 hl''.2 hα, hJ0.valley l' α _ hl''.1 hl''.2 hα]
          split_ifs with hlm
          · congr 1
            refine Finset.sum_congr rfl fun τ' hτ' => ?_
            rw [mem_Ico] at hτ'
            by_cases ht : IsTurnZ (dnpWalk s0 m) τ'
            · obtain ⟨l2, hl2⟩ := (isTurnZ_iff_exists_level hms τ').1 ht
              have hge := isTurnOfLevel_ge_of_span hms (by omega : 1 ≤ l' + 1) (by omega)
                (periodVApices_back_child hl''.1 hα) (τ / dnpPeriod s0 m) (τ := τ') (by push_cast; omega)
                (by push_cast; omega) hl2
              exact ih τ' l2 (by omega) hl2
            · rw [hJ.off_turn τ' ht, hJ0.off_turn τ' ht]
          · rfl
      · rw [hJ.tip τ hτ', hJ0.tip τ hτ']
  funext τ
  by_cases ht : IsTurnZ (dnpWalk s0 m) τ
  · obtain ⟨l, hl⟩ := (isTurnZ_iff_exists_level hms τ).1 ht
    exact claim (m + 1) τ l (by omega) hl
  · rw [hJ.off_turn τ ht, hJ0.off_turn τ ht]

/-- The potential of any block label `B(a, K)` on `U` is the model's `blockPotential`. -/
theorem IsBlockLabel.potentialOf_eq {s0 m a : ℕ} {K : ℤ} {J : ℤ → ℤ} (hms : m ≤ s0)
    (hJ : IsBlockLabel s0 m a K J) : potentialOf J = blockPotential s0 m a K := by
  rw [hJ.eq_blockJumps hms, potentialOf_blockJumps hms]

/-! ### The block-pair label on the cover, errors and service -/

/-- The potential `Φ_h` of head `h` carrying the block label `B(a, K)` at its own turns (the jumps
`t ↦ J(t + c_h)`, supported on the turns of head `h`), normalized by `Φ_h(0) = 0`. -/
def headPotential (s0 m : ℕ) (ξ : ℤ) (h : Bool) (a : ℕ) (K : ℤ) : ℤ → ℤ :=
  potentialOf fun t => blockJumps s0 m a K (t + headShift ξ h)

theorem headPotential_eq {s0 m : ℕ} (hms : m ≤ s0) (ξ : ℤ) (h : Bool) (a : ℕ) (K t : ℤ) :
    headPotential s0 m ξ h a K t =
      blockPotential s0 m a K (t + headShift ξ h) - blockPotential s0 m a K (headShift ξ h) := by
  unfold headPotential
  rw [potentialOf_comp_add, potentialOf_blockJumps hms]

/-- The jumps of head `h` vanish off its own turns. -/
theorem headJumps_off_turn {s0 m : ℕ} (hms : m ≤ s0) (ξ : ℤ) (h : Bool) (a : ℕ) (K : ℤ) {t : ℤ}
    (ht : ¬ IsTurnZ (headWalk s0 m ξ h) t) : blockJumps s0 m a K (t + headShift ξ h) = 0 := by
  apply (blockJumps_isBlockLabel hms a K).off_turn
  intro h'; apply ht
  rw [isTurnZ_headWalk_iff hms]
  exact (isTurnZ_iff_exists_level hms _).1 h'

/-- **The block-pair label** of `(B(a₁, K₁), B(a₂, K₂))` modulo `q` on the pair `x₁ = U`,
`x₂ = U(· + ξ)`: `G = (Φ₁ + Φ₂) mod q`, with `Φ_h` the potential of head `h` carrying `B(a_h, K_h)` at
its own turns. It is defined on `ℤ`; for `q ∣ r` it is `rP`-periodic (`blockPairLabel_add_mul`), a
label on the `r`-fold cover. -/
def blockPairLabel (s0 m a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (t : ℤ) : ℤ :=
  (headPotential s0 m ξ true a1 K1 t + headPotential s0 m ξ false a2 K2 t) % q

theorem blockPairLabel_mem (s0 m a1 a2 : ℕ) (K1 K2 : ℤ) {q : ℤ} (hq : 0 < q) (ξ t : ℤ) :
    0 ≤ blockPairLabel s0 m a1 a2 K1 K2 q ξ t ∧ blockPairLabel s0 m a1 a2 K1 K2 q ξ t < q :=
  ⟨Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq⟩

theorem headPotential_add_mul_period {s0 m : ℕ} (hms : m ≤ s0) (ξ : ℤ) (h : Bool) (a : ℕ)
    (K t n : ℤ) :
    headPotential s0 m ξ h a K (t + n * dnpPeriod s0 m) = headPotential s0 m ξ h a K t +
      n * (4 * strokeMass m (pathSumFwd (blockA m a K) (blockE m a K)) 0 + 2 * 1) := by
  rw [headPotential_eq hms, headPotential_eq hms, show t + n * dnpPeriod s0 m + headShift ξ h =
    (t + headShift ξ h) + n * dnpPeriod s0 m by ring]
  unfold blockPotential
  rw [turnPotential_add_mul_period]; ring

/-- For `q ∣ r` the block-pair label is `rP`-periodic, so it is a label on the `r`-fold cover. -/
theorem blockPairLabel_add_mul {s0 m : ℕ} (hms : m ≤ s0) (a1 a2 : ℕ) (K1 K2 : ℤ) {q : ℤ} {r : ℕ}
    (hqr : q ∣ r) (ξ t : ℤ) :
    blockPairLabel s0 m a1 a2 K1 K2 q ξ (t + r * dnpPeriod s0 m) =
      blockPairLabel s0 m a1 a2 K1 K2 q ξ t := by
  unfold blockPairLabel
  rw [headPotential_add_mul_period hms, headPotential_add_mul_period hms]
  obtain ⟨c, hc⟩ := hqr
  rw [show headPotential s0 m ξ true a1 K1 t + (r : ℤ) * (4 * strokeMass m (pathSumFwd (blockA m a1 K1)
      (blockE m a1 K1)) 0 + 2 * 1) + (headPotential s0 m ξ false a2 K2 t + (r : ℤ) *
      (4 * strokeMass m (pathSumFwd (blockA m a2 K2) (blockE m a2 K2)) 0 + 2 * 1)) =
      headPotential s0 m ξ true a1 K1 t + headPotential s0 m ξ false a2 K2 t + q * (c *
      (4 * strokeMass m (pathSumFwd (blockA m a1 K1) (blockE m a1 K1)) 0 + 2 * 1 +
      (4 * strokeMass m (pathSumFwd (blockA m a2 K2) (blockE m a2 K2)) 0 + 2 * 1))) by
    rw [hc]; ring, Int.add_mul_emod_self_left]

/-- The error `e(p, u) = (G(u) - G(p) - 1) mod q` of a hop `(p, u)` under a label `G`. -/
def hopError (G : ℤ → ℤ) (q p u : ℤ) : ℤ := (G u - G p - 1) % q

theorem emod_sub_emod_sub_one (a b q : ℤ) : (a % q - b % q - 1) % q = (a - b - 1) % q := by
  have h1 := Int.emod_add_mul_ediv a q
  have h2 := Int.emod_add_mul_ediv b q
  rw [show a % q - b % q - 1 = (a - b - 1) + q * (b / q - a / q) by linarith,
    Int.add_mul_emod_self_left]

/-- **The model's errors are the errors of the block-pair label**: for a hop `(p, u)` in real time,
its error is the model's `pairHopErr` of head `h` in the head's own time `(p + c_h, u + c_h)` (for
either head; the expression does not depend on `h`). -/
theorem hopError_blockPairLabel {s0 m : ℕ} (hms : m ≤ s0) (a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (h : Bool)
    (p u : ℤ) :
    hopError (blockPairLabel s0 m a1 a2 K1 K2 q ξ) q p u =
      pairHopErr s0 m a1 a2 K1 K2 q ξ h (p + headShift ξ h) (u + headShift ξ h) := by
  unfold hopError blockPairLabel
  rw [emod_sub_emod_sub_one, headPotential_eq hms, headPotential_eq hms, headPotential_eq hms,
    headPotential_eq hms]
  unfold pairHopErr headShift
  cases h <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero] <;> congr 1 <;> ring_nf

theorem hopError_add_mul_period {s0 m : ℕ} (hms : m ≤ s0) (a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (p u n : ℤ) :
    hopError (blockPairLabel s0 m a1 a2 K1 K2 q ξ) q (p + n * dnpPeriod s0 m) (u + n * dnpPeriod s0 m) =
      hopError (blockPairLabel s0 m a1 a2 K1 K2 q ξ) q p u := by
  unfold hopError blockPairLabel
  rw [emod_sub_emod_sub_one, emod_sub_emod_sub_one, headPotential_add_mul_period hms,
    headPotential_add_mul_period hms, headPotential_add_mul_period hms,
    headPotential_add_mul_period hms]
  congr 1; ring

theorem hopError_nonneg (G : ℤ → ℤ) {q : ℤ} (hq : 0 < q) (p u : ℤ) : 0 ≤ hopError G q p u :=
  Int.emod_nonneg _ hq.ne'

/-- The total error of the class `(h, k)` on the `r`-fold cover under the block-pair label. -/
noncomputable def coverClassErr (s0 m a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (r : ℕ) (h : Bool) (k : ℕ) : ℤ :=
  ∑ η ∈ coverClass s0 m ξ r h k, hopError (blockPairLabel s0 m a1 a2 K1 K2 q ξ) q η.1 η.2

/-- The block-pair label **`θ`-serves** level `k` for head `h` on the `r`-fold cover: the class
`(h, k)` has total error at most `θ q n_h / (2N)`, `N = m + 1`. -/
def ThetaServes (s0 m a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (r : ℕ) (θ : ℝ) (h : Bool) (k : ℕ) : Prop :=
  (coverClassErr s0 m a1 a2 K1 K2 q ξ r h k : ℝ) ≤
    θ * q * coverHopCount s0 m ξ r / (2 * ((m : ℝ) + 1))

/-- The block-pair label **doubly `θ`-serves** level `k`: it `θ`-serves it for both heads. -/
def DoublyThetaServes (s0 m a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (r : ℕ) (θ : ℝ) (k : ℕ) : Prop :=
  ThetaServes s0 m a1 a2 K1 K2 q ξ r θ true k ∧ ThetaServes s0 m a1 a2 K1 K2 q ξ r θ false k

/-- Every class has `n_h/(2N)` hops, so `θ`-service means mean error at most `θ q`. -/
theorem thetaServes_iff_mean {s0 m : ℕ} (hms : m ≤ s0) (a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (r : ℕ)
    (θ : ℝ) (h : Bool) {k : ℕ} (hk : k ≤ m) :
    ThetaServes s0 m a1 a2 K1 K2 q ξ r θ h k ↔
      (coverClassErr s0 m a1 a2 K1 K2 q ξ r h k : ℝ) ≤ θ * q * (coverClass s0 m ξ r h k).card := by
  unfold ThetaServes
  have hc := card_coverClass_mul hms ξ r h hk
  have hcR : (2 * ((m : ℝ) + 1)) * (coverClass s0 m ξ r h k).card = coverHopCount s0 m ξ r := by
    exact_mod_cast hc
  rw [← hcR, mul_div_assoc, mul_div_cancel_left₀ _ (by positivity)]

open Classical in
/-- The error of the hop of head `h` ending at `u`, counted if it lies in the class `(h, k)`. -/
noncomputable def classErrAt (s0 m a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (h : Bool) (k : ℕ) (u : ℤ) : ℤ :=
  if HeadHopLevelIs s0 m ξ h (headPrev s0 m ξ h u) u k then
    hopError (blockPairLabel s0 m a1 a2 K1 K2 q ξ) q (headPrev s0 m ξ h u) u else 0

theorem classErrAt_add_period {s0 m : ℕ} (hms : m ≤ s0) (a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (h : Bool)
    (k : ℕ) (u : ℤ) :
    classErrAt s0 m a1 a2 K1 K2 q ξ h k (u + dnpPeriod s0 m) = classErrAt s0 m a1 a2 K1 K2 q ξ h k u := by
  unfold classErrAt
  have h1 := headPrev_add_mul_period s0 m ξ h u 1
  rw [one_mul] at h1
  rw [h1]
  have h2 := headHopLevelIs_add_mul_period s0 m ξ h (headPrev s0 m ξ h u) u 1 k
  have h3 := hopError_add_mul_period hms a1 a2 K1 K2 q ξ (headPrev s0 m ξ h u) u 1
  rw [one_mul] at h2 h3
  by_cases hc : HeadHopLevelIs s0 m ξ h (headPrev s0 m ξ h u) u k
  · rw [ite_eq_left (h2.2 hc), ite_eq_left hc, h3]
  · rw [ite_eq_right (fun h' => hc (h2.1 h')), ite_eq_right hc]

theorem classErrAt_nonneg (s0 m a1 a2 : ℕ) (K1 K2 : ℤ) {q : ℤ} (hq : 0 < q) (ξ : ℤ) (h : Bool)
    (k : ℕ) (u : ℤ) : 0 ≤ classErrAt s0 m a1 a2 K1 K2 q ξ h k u := by
  unfold classErrAt; split_ifs
  · exact hopError_nonneg _ hq _ _
  · exact le_refl 0

/-- The total error of a class on the `r`-fold cover is `r` times its total error in one period. -/
theorem coverClassErr_eq {s0 m : ℕ} (hms : m ≤ s0) (a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (r : ℕ) (h : Bool)
    (k : ℕ) (t₀ : ℤ) :
    coverClassErr s0 m a1 a2 K1 K2 q ξ r h k =
      r * ∑ u ∈ Ico t₀ (t₀ + dnpPeriod s0 m), classErrAt s0 m a1 a2 K1 K2 q ξ h k u := by
  have hP : (0 : ℤ) < dnpPeriod s0 m := by exact_mod_cast dnpPeriod_pos s0 m
  have hper := classErrAt_add_period hms a1 a2 K1 K2 q ξ h k
  unfold coverClassErr
  rw [sum_coverClass, show (0 : ℤ) = 0 + 0 by ring]
  have := sum_Ico_mul_periodic (g := classErrAt s0 m a1 a2 K1 K2 q ξ h k) hP hper 0 r
  rw [zero_add] at this
  unfold classErrAt at this
  rw [zero_add, this, sum_Ico_periodic hP hper t₀, nsmul_eq_mul]
  unfold classErrAt
  rfl

/-- **`θ`-service implies the model's service on the witness hops**: a level that the block-pair
label `θ`-serves for head `h` on any cover is `ServedOnWitness` (the witness hops are hops of the
class, one period of the cover carries the `1/r` share of its error, and errors are nonnegative). -/
theorem ThetaServes.servedOnWitness {s0 m a1 a2 : ℕ} {K1 K2 q ξ : ℤ} {r : ℕ} {θ : ℝ} {h : Bool}
    {k : ℕ} (hms : m < s0) (hq : 0 < q) (hr : 0 < r)
    (hserv : ThetaServes s0 m a1 a2 K1 K2 q ξ r θ h k) :
    ServedOnWitness s0 m a1 a2 K1 K2 q ξ θ h k := by
  classical
  have hP : (0 : ℤ) < dnpPeriod s0 m := by exact_mod_cast dnpPeriod_pos s0 m
  have hcover := coverClassErr_eq hms.le a1 a2 K1 K2 q ξ r h k (-headShift ξ h)
  set c := headShift ξ h with hcdef
  set F := classErrAt s0 m a1 a2 K1 K2 q ξ h k with hFdef
  have hF0 : ∀ u, 0 ≤ F u := classErrAt_nonneg s0 m a1 a2 K1 K2 hq ξ h k
  set S := ∑ u ∈ Ico (-c) (-c + dnpPeriod s0 m), F u with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun u _ => hF0 u
  -- the witness hops carry at most `S`
  have hwit : witnessErr s0 m a1 a2 K1 K2 q ξ h k ≤ S := by
    unfold witnessErr witnessHops
    split_ifs with hk
    · have hmem : ∀ η ∈ (range 4).biUnion (family s0 m k), ∃ f < 4, η ∈ family s0 m k f := by
        intro η hη
        obtain ⟨f, hf, hη⟩ := mem_biUnion.mp hη
        exact ⟨f, mem_range.mp hf, hη⟩
      have hval : ∀ η ∈ (range 4).biUnion (family s0 m k),
          pairHopErr s0 m a1 a2 K1 K2 q ξ h η.1 η.2 = F (η.2 - c) := by
        intro η hη
        obtain ⟨f, hf, hη⟩ := hmem η hη
        have hcl := family_inHopClass hms.le hk.1 hk.2 hf hη ξ h 0
        simp only [zero_mul, add_zero] at hcl
        have hprev := hcl.1.eq_headPrev
        rw [hFdef]; unfold classErrAt
        rw [← hprev, ite_eq_left hcl.2, hopError_blockPairLabel hms.le a1 a2 K1 K2 q ξ h]
        simp only [hcdef, sub_add_cancel]
      rw [Finset.sum_congr rfl hval]
      have hinj : Set.InjOn (fun η : ℤ × ℤ => η.2 - c) ((range 4).biUnion (family s0 m k) : Set _) := by
        intro η₁ h₁ η₂ h₂ he
        simp only at he
        obtain ⟨f₁, hf₁, h₁⟩ := hmem η₁ h₁
        obtain ⟨f₂, hf₂, h₂⟩ := hmem η₂ h₂
        have e1 := (family_spec hms.le hk.1 hk.2 hf₁ h₁ 0).1
        have e2 := (family_spec hms.le hk.1 hk.2 hf₂ h₂ 0).1
        simp only [zero_mul, add_zero] at e1 e2
        have h2 : η₁.2 = η₂.2 := by linarith
        rw [h2] at e1
        exact Prod.ext (e1.eq_of_snd e2) h2
      rw [← Finset.sum_image (f := F) hinj, hSdef]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun u _ _ => hF0 u
      intro u hu
      obtain ⟨η, hη, rfl⟩ := mem_image.mp hu
      obtain ⟨f, hf, hη⟩ := hmem η hη
      have := family_snd_mem hms.le hk.1 hk.2 hη
      rw [mem_Ico]; constructor <;> linarith
    · simp only [Finset.sum_empty]; exact hS0
  clear_value S F
  unfold ThetaServes at hserv
  unfold ServedOnWitness
  rw [hcover, coverHopCount_eq] at hserv
  have hPd : ((2 * (r * dnpPeriod s0 m) : ℕ) : ℝ) =
      2 * ((r : ℝ) * (((m : ℝ) + 1) * (4 * 2 ^ s0))) := by
    unfold dnpPeriod strokeLen scaleR; simp only [Nat.sub_zero]; push_cast; ring
  rw [hPd, show (((r : ℤ) * S : ℤ) : ℝ) = (r : ℝ) * (S : ℝ) by push_cast; ring] at hserv
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hserv' : (r : ℝ) * S ≤ (r : ℝ) * (θ * q * (4 * 2 ^ s0)) := by
    calc (r : ℝ) * S ≤ θ * q * (2 * ((r : ℝ) * (((m : ℝ) + 1) * (4 * 2 ^ s0)))) / (2 * ((m : ℝ) + 1)) :=
          hserv
      _ = (r : ℝ) * (θ * q * (4 * 2 ^ s0)) := by field_simp
  have hS := le_of_mul_le_mul_left hserv' hrR
  have hwR : (witnessErr s0 m a1 a2 K1 K2 q ξ h k : ℝ) ≤ S := by exact_mod_cast hwit
  linarith

/-- The block-pair label is turn-supported: it changes only at turns of the heads. -/
theorem blockPairLabel_eq_of_not_turn {s0 m : ℕ} (hms : m ≤ s0) (a1 a2 : ℕ) (K1 K2 q ξ : ℤ) {t : ℤ}
    (h1 : ¬ IsTurnZ (headWalk s0 m ξ true) t) (h2 : ¬ IsTurnZ (headWalk s0 m ξ false) t) :
    blockPairLabel s0 m a1 a2 K1 K2 q ξ t = blockPairLabel s0 m a1 a2 K1 K2 q ξ (t - 1) := by
  unfold blockPairLabel headPotential
  have e1 := potentialOf_sub_one (fun t => blockJumps s0 m a1 K1 (t + headShift ξ true)) t
  have e2 := potentialOf_sub_one (fun t => blockJumps s0 m a2 K2 (t + headShift ξ false)) t
  rw [headJumps_off_turn hms ξ true a1 K1 h1] at e1
  rw [headJumps_off_turn hms ξ false a2 K2 h2] at e2
  congr 1; linarith

/-! ### The level parameters of `B(a, K)` (the eighth paper's Definition 5.11) -/

theorem isCanceller_iff (m a l : ℕ) : isCanceller m a l = true ↔ (m - l) % (a + 1) = a := by
  unfold isCanceller; simp

theorem mod_sub_of_le' {m l a t : ℕ} (hlm : l + t ≤ m) (ht : t ≤ (m - l) % (a + 1)) :
    (m - (l + t)) % (a + 1) = (m - l) % (a + 1) - t := by
  have h := Nat.div_add_mod (m - l) (a + 1)
  have hlt := Nat.mod_lt (m - l) (show 0 < a + 1 by omega)
  rw [show m - (l + t) = ((m - l) % (a + 1) - t) + (a + 1) * ((m - l) / (a + 1)) by omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Below a served level `l` with `j = (m - l) mod (a + 1)`, the levels `l + 1, …, l + j` are served,
and the next level `l + j + 1` is a canceller or `m + 1`: it is the first canceller below `l`. -/
theorem firstCanceller_spec {m a l : ℕ} (hl : l ≤ m) (hs : isCanceller m a l = false) :
    (∀ i, l < i → i ≤ l + (m - l) % (a + 1) → i ≤ m ∧ isCanceller m a i = false) ∧
      (l + (m - l) % (a + 1) + 1 ≤ m → isCanceller m a (l + (m - l) % (a + 1) + 1) = true) ∧
      (m < l + (m - l) % (a + 1) + 1 → l + (m - l) % (a + 1) = m) := by
  have hj : (m - l) % (a + 1) ≠ a := by
    intro h; rw [← isCanceller_iff] at h; rw [h] at hs; simp at hs
  have hlt := Nat.mod_lt (m - l) (show 0 < a + 1 by omega)
  have hle := Nat.mod_le (m - l) (a + 1)
  refine ⟨fun i h1 h2 => ⟨by omega, ?_⟩, fun h => ?_, fun h => by omega⟩
  · obtain ⟨t, rfl⟩ : ∃ t, i = l + t := ⟨i - l, by omega⟩
    rw [Bool.eq_false_iff, ne_eq, isCanceller_iff, mod_sub_of_le' (by omega) (by omega)]
    omega
  · rw [isCanceller_iff]
    obtain ⟨q, r, hqr, hr, hrdef⟩ : ∃ q r, (a + 1) * q + r = m - l ∧ r < a + 1 ∧
        r = (m - l) % (a + 1) := ⟨_, _, Nat.div_add_mod _ _, Nat.mod_lt _ (by omega), rfl⟩
    rw [← hrdef] at h ⊢
    rcases Nat.eq_zero_or_pos q with hq | hq
    · rw [hq, mul_zero, zero_add] at hqr; omega
    · have e1 : (a + 1) * (q - 1) = (a + 1) * q - (a + 1) := Nat.mul_sub_one (a + 1) q
      have e2 : a + 1 ≤ (a + 1) * q := Nat.le_mul_of_pos_right _ hq
      rw [show m - (l + r + 1) = a + (a + 1) * (q - 1) by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]

theorem sum_served_block {m a : ℕ} (K : ℤ) : ∀ j l, l ≤ m → isCanceller m a l = false →
    (m - l) % (a + 1) = j →
    ∑ i ∈ Icc (l + 1) (l + j), (blockA m a K i + blockE m a K i + 2) = ((2 : ℤ) ^ j - 1) * (2 * K + 2) := by
  intro j
  induction j with
  | zero => intro l _ _ _; simp
  | succ j ih =>
    intro l hl hs hj
    obtain ⟨hserved, -, -⟩ := firstCanceller_spec hl hs
    obtain ⟨hl1, hs1⟩ := hserved (l + 1) (by omega) (by omega)
    have hj1 : (m - (l + 1)) % (a + 1) = j := by
      rw [mod_sub_of_le' (by omega) (by omega), hj]; omega
    have hset : Icc (l + 1) (l + (j + 1)) = insert (l + 1) (Icc (l + 1 + 1) (l + 1 + j)) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hset, Finset.sum_insert (by simp), ih (l + 1) hl1 hs1 hj1, (block_served_mass m a K (l + 1) hs1).1,
      hj1]
    ring

/-- **The served levels of `B(a, K)`** satisfy Definition 5.11: `A_l = K` and
`E_l = K + ∑_{i=l+1}^{c-1} (A_i + E_i + 2)`, with `c = l + ((m - l) mod (a + 1)) + 1` the first canceller
below `l` or `m + 1` (`firstCanceller_spec`). -/
theorem blockParams_served {m a l : ℕ} (K : ℤ) (hl : l ≤ m) (hs : isCanceller m a l = false) :
    blockA m a K l = K ∧
      blockE m a K l = K + ∑ i ∈ Icc (l + 1) (l + (m - l) % (a + 1)),
        (blockA m a K i + blockE m a K i + 2) := by
  refine ⟨by simp [blockA, hs], ?_⟩
  rw [sum_served_block K _ l hl hs rfl]
  simp [blockE, hs]

/-- **The cancellers of `B(a, K)`** satisfy Definition 5.11: `A_c = 0` and `E_c = -Q_c - 2` with
`Q_c = ∑_{i=c+1}^{c'-1} (A_i + E_i + 2)`, where the levels `c + 1, …, c + a ≤ m` are served and
`c' = c + a + 1` is the next canceller below `c` or `m + 1`; and `Q_c = Q(a, K)`. -/
theorem blockParams_canceller {m a c : ℕ} (K : ℤ) (hc : c ≤ m) (hcan : isCanceller m a c = true) :
    blockA m a K c = 0 ∧
      (∀ i, c < i → i ≤ c + a → i ≤ m ∧ isCanceller m a i = false) ∧
      (c + a + 1 ≤ m → isCanceller m a (c + a + 1) = true) ∧
      (m < c + a + 1 → c + a = m) ∧
      ∑ i ∈ Icc (c + 1) (c + a), (blockA m a K i + blockE m a K i + 2) = blockQ a K ∧
      blockE m a K c = -(∑ i ∈ Icc (c + 1) (c + a), (blockA m a K i + blockE m a K i + 2)) - 2 := by
  have hres := (isCanceller_iff m a c).1 hcan
  have hlt := Nat.mod_le (m - c) (a + 1)
  have hca : c + a ≤ m := by omega
  -- the level `c + 1` is served with `a - 1` served levels below it (if `a ≥ 1`)
  have hserved : ∀ i, c < i → i ≤ c + a → i ≤ m ∧ isCanceller m a i = false := by
    intro i h1 h2
    obtain ⟨t, rfl⟩ : ∃ t, i = c + t := ⟨i - c, by omega⟩
    refine ⟨by omega, ?_⟩
    rw [Bool.eq_false_iff, ne_eq, isCanceller_iff, mod_sub_of_le' (by omega) (by omega)]
    omega
  have hsum : ∑ i ∈ Icc (c + 1) (c + a), (blockA m a K i + blockE m a K i + 2) = blockQ a K := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; simp [blockQ]
    · obtain ⟨hl1, hs1⟩ := hserved (c + 1) (by omega) (by omega)
      have hj1 : (m - (c + 1)) % (a + 1) = a - 1 := by rw [mod_sub_of_le' (by omega) (by omega), hres]
      have hset : Icc (c + 1) (c + a) = insert (c + 1) (Icc (c + 1 + 1) (c + 1 + (a - 1))) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [hset, Finset.sum_insert (by simp), sum_served_block K (a - 1) (c + 1) hl1 hs1 hj1,
        (block_served_mass m a K (c + 1) hs1).1, hj1]
      unfold blockQ
      have : (2 : ℤ) ^ a = 2 * 2 ^ (a - 1) := by rw [← pow_succ']; congr 1; omega
      rw [this]; ring
  refine ⟨by simp [blockA, hcan], hserved, fun h => ?_, fun h => by omega, hsum, ?_⟩
  · rw [isCanceller_iff]
    obtain ⟨q, r, hqr, hr, hrdef⟩ : ∃ q r, (a + 1) * q + r = m - c ∧ r < a + 1 ∧
        r = (m - c) % (a + 1) := ⟨_, _, Nat.div_add_mod _ _, Nat.mod_lt _ (by omega), rfl⟩
    rw [← hrdef] at hres
    rcases Nat.eq_zero_or_pos q with hq | hq
    · rw [hq, mul_zero, zero_add] at hqr; omega
    · have e1 : (a + 1) * (q - 1) = (a + 1) * q - (a + 1) := Nat.mul_sub_one (a + 1) q
      have e2 : a + 1 ≤ (a + 1) * q := Nat.le_mul_of_pos_right _ hq
      rw [show m - (c + a + 1) = a + (a + 1) * (q - 1) by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
  · rw [hsum]; simp [blockE, hcan]

end MergeDepth
