import HalfRate.Decomposition
import HalfRate.Pieces
import DirectedRecovery.PathPacking
import DirectedRecovery.Hyperfinite
import DirectedRecovery.StorageCode

/-!
# Paired distance, paid deletion, and the degree-three transfer

The paired incidence graph, its short pairs `b_E(K)`, paid conditioning and the paired-distance
condition for sequences are those of *Directed Recovery Structures in Tape Computations*
(`DirectedRecovery`).

* Lemma 2.1: `edist_eq_one_iff`, `edist_eq_three_iff`, `ttFree_iff_shortPaired_eq_empty`,
  `ttFree_iff_five_le_edist`. Transitive triangles are exactly the paired paths of length three.
* Corollary (paid deletion): `card_sq_le_of_paidDeletion`.
* Proposition 8.1: `card_sq_le_of_dn3`, `storageCodeRate_le_of_dn3`, `dn3_rate_eventually_le`;
  Conjecture P implies its hypothesis (`dn3_of_conjectureP`).
-/

namespace HalfRate

open Finset MotionDepthCodes DirectedRecovery Filter Topology

universe u

section Distance

variable {V : Type*} {N : V → Finset V}

/-- The paired distance of `p` is `1` exactly when `p ∈ N p`. -/
theorem edist_eq_one_iff (p : V) :
    (pairedIncidenceGraph N).edist (Sum.inl p) (Sum.inr p) = 1 ↔ p ∈ N p :=
  SimpleGraph.edist_eq_one_iff_adj

/-- A walk of length three from `L_p` to `R_p` is a transitive triangle with middle vertex `p`. -/
theorem tt_of_walk_three {p : V} (w : (pairedIncidenceGraph N).Walk (Sum.inl p) (Sum.inr p))
    (hw : w.length = 3) : ∃ x z, x ∈ N p ∧ p ∈ N z ∧ x ∈ N z := by
  have h1 := w.adj_getVert_succ (i := 0) (by omega)
  have h2 := w.adj_getVert_succ (i := 1) (by omega)
  have h3 := w.adj_getVert_succ (i := 2) (by omega)
  have e3 : w.getVert (2 + 1) = Sum.inr p := by
    rw [show 2 + 1 = w.length by omega, SimpleGraph.Walk.getVert_length]
  rw [e3] at h3
  rw [SimpleGraph.Walk.getVert_zero, zero_add] at h1
  rw [show (1 + 1 : ℕ) = 2 from rfl] at h2
  obtain ⟨a, ha⟩ : ∃ a, w.getVert 1 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, w.getVert 2 = b := ⟨_, rfl⟩
  rw [ha] at h1 h2
  rw [hb] at h2 h3
  rcases a with z | z
  · exact absurd h1 (pairedIncidenceGraph_not_adj_left_left N p z)
  rcases b with x | x
  · exact ⟨x, z, h3, h1, h2⟩
  · exact absurd h2 (pairedIncidenceGraph_not_adj_right_right N z x)

/-- A transitive triangle `x → p → z`, `x → z` gives the path `L_p, R_z, L_x, R_p`. No looplessness is
needed. -/
theorem edist_le_three_of_tt {x p z : V} (hxp : x ∈ N p) (hpz : p ∈ N z) (hxz : x ∈ N z) :
    (pairedIncidenceGraph N).edist (Sum.inl p) (Sum.inr p) ≤ 3 := by
  refine (SimpleGraph.edist_le (SimpleGraph.Walk.cons
    (show (pairedIncidenceGraph N).Adj (Sum.inl p) (Sum.inr z) from hpz)
    (SimpleGraph.Walk.cons (show (pairedIncidenceGraph N).Adj (Sum.inr z) (Sum.inl x) from hxz)
      (SimpleGraph.Walk.cons (show (pairedIncidenceGraph N).Adj (Sum.inl x) (Sum.inr p) from hxp)
        SimpleGraph.Walk.nil)))).trans ?_
  simp

/-- Paired distances between opposite ports are odd. -/
theorem odd_of_edist_eq {p q : V} {n : ℕ}
    (h : (pairedIncidenceGraph N).edist (Sum.inl p) (Sum.inr q) = n) : Odd n := by
  obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_eq_coe h
  rw [← hw]
  exact paired_walk_length_odd N p q w

/-- Without loops, every paired distance is at least three. -/
theorem three_le_edist (hloop : ∀ v, v ∉ N v) (p : V) :
    3 ≤ (pairedIncidenceGraph N).edist (Sum.inl p) (Sum.inr p) := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  rw [← hn] at hlt
  have hn3 : n < 3 := by exact_mod_cast hlt
  have hn1 : n = 1 := by obtain ⟨k, rfl⟩ := odd_of_edist_eq hn.symm; omega
  subst hn1
  exact hloop p ((edist_eq_one_iff p).mp (by rw [← hn]; rfl))

/-- **Lemma 2.1.** For a loopless relation, the paired distance of `p` is `3` exactly when `p` is
the middle vertex of a transitive triangle. -/
theorem edist_eq_three_iff (hloop : ∀ v, v ∉ N v) (p : V) :
    (pairedIncidenceGraph N).edist (Sum.inl p) (Sum.inr p) = 3 ↔
      ∃ x z, x ≠ p ∧ p ≠ z ∧ x ≠ z ∧ x ∈ N p ∧ p ∈ N z ∧ x ∈ N z := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_eq_coe (k := 3) h
    obtain ⟨x, z, hxp, hpz, hxz⟩ := tt_of_walk_three w hw
    refine ⟨x, z, ?_, ?_, ?_, hxp, hpz, hxz⟩
    · rintro rfl; exact hloop _ hxp
    · rintro rfl; exact hloop _ hpz
    · rintro rfl; exact hloop _ hxz
  · rintro ⟨x, z, -, -, -, hxp, hpz, hxz⟩
    exact le_antisymm (edist_le_three_of_tt hxp hpz hxz) (three_le_edist hloop p)

variable [Fintype V]

/-- **Lemma 2.1, short-pair form.** A loopless relation is TT-free if and only if `b_E(3) = 0`. -/
theorem ttFree_iff_shortPaired_eq_empty (hloop : ∀ v, v ∉ N v) :
    TTFree N ↔ shortPairedCoordinates N 3 = ∅ := by
  constructor
  · intro htt
    ext p
    simp only [shortPairedCoordinates, mem_filter, mem_univ, true_and, notMem_empty, iff_false]
    intro hle
    have h3 : (pairedIncidenceGraph N).edist (Sum.inl p) (Sum.inr p) = 3 :=
      le_antisymm (by exact_mod_cast hle) (three_le_edist hloop p)
    obtain ⟨x, z, hxp', hpz', hxz', hxp, hpz, hxz⟩ := (edist_eq_three_iff hloop p).mp h3
    exact htt x p z hxp' hpz' hxz' hxp hpz hxz
  · intro hE x y z _ _ _ h1 h2 h3
    have hy : y ∈ shortPairedCoordinates N 3 :=
      mem_filter.mpr ⟨mem_univ _, by exact_mod_cast edist_le_three_of_tt h1 h2 h3⟩
    rw [hE] at hy
    exact notMem_empty _ hy

/-- **Lemma 2.1, distance form.** A loopless relation is TT-free if and only if every paired
distance is at least five. -/
theorem ttFree_iff_five_le_edist (hloop : ∀ v, v ∉ N v) :
    TTFree N ↔ ∀ p, 5 ≤ (pairedIncidenceGraph N).edist (Sum.inl p) (Sum.inr p) := by
  rw [ttFree_iff_shortPaired_eq_empty hloop]
  constructor
  · intro hE p
    have hgt : ¬ (pairedIncidenceGraph N).edist (Sum.inl p) (Sum.inr p) ≤ (3 : ℕ) := fun h => by
      have hp : p ∈ shortPairedCoordinates N 3 := mem_filter.mpr ⟨mem_univ _, h⟩
      rw [hE] at hp
      exact notMem_empty _ hp
    rcases eq_or_ne ((pairedIncidenceGraph N).edist (Sum.inl p) (Sum.inr p)) ⊤ with htop | htop
    · rw [htop]; exact le_top
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← hn] at hgt ⊢
      have h3 : ¬ n ≤ 3 := fun h => hgt (by exact_mod_cast h)
      have h5 : 5 ≤ n := by obtain ⟨k, rfl⟩ := odd_of_edist_eq hn.symm; omega
      exact_mod_cast h5
  · intro h5
    ext p
    simp only [shortPairedCoordinates, mem_filter, mem_univ, true_and, notMem_empty, iff_false]
    intro hle
    have := (h5 p).trans hle
    norm_num at this

end Distance

section Paid

variable {V : Type*} [DecidableEq V] [Fintype V] {N : V → Finset V}

/-- **Corollary (paid deletion).** If `N − Z` satisfies the weighted half bound, every storage code
for `N` over a nonempty finite alphabet satisfies `|C|² ≤ |α|^(|V| + |Z|)`. -/
theorem card_sq_le_of_paidDeletion {α : Type*} [Fintype α] [Nonempty α] (Z : Finset V)
    (hZ : RateBound (inducedNeighborhood N (univ \ Z)) (1 / 2)) {C : Finset (V → α)}
    (hC : IsStorageCode N C) :
    C.card ^ 2 ≤ Fintype.card α ^ (Fintype.card V + Z.card) := by
  have ha : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hQ : Fintype.card (univ \ Z : Finset V) = Fintype.card V - Z.card := by
    rw [Fintype.card_coe, card_sdiff_of_subset (subset_univ Z), card_univ]
  have hZc : Fintype.card {v // v ∉ (univ \ Z : Finset V)} = Z.card := by
    rw [Fintype.card_subtype]
    congr 1
    ext v
    simp
  have hZle : Z.card ≤ Fintype.card V := card_le_univ Z
  have hu : ∀ D : Finset ((univ \ Z : Finset V) → α),
      IsStorageCode (inducedNeighborhood N (univ \ Z)) D →
      (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ ((Fintype.card (univ \ Z : Finset V) : ℝ) / 2) := by
    intro D hD
    have h2 : ((D.card : ℝ)) ^ 2 ≤ (Fintype.card α : ℝ) ^ Fintype.card (univ \ Z : Finset V) := by
      exact_mod_cast card_sq_le_of_rateBound_half hZ hD
    have hx : (0 : ℝ) ≤ (Fintype.card α : ℝ) ^ ((Fintype.card (univ \ Z : Finset V) : ℝ) / 2) :=
      Real.rpow_nonneg ha.le _
    have hsq : ((Fintype.card α : ℝ) ^ ((Fintype.card (univ \ Z : Finset V) : ℝ) / 2)) ^ 2 =
        (Fintype.card α : ℝ) ^ Fintype.card (univ \ Z : Finset V) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
      norm_num
    exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) hx two_ne_zero).mp (hsq ▸ h2)
  have hcb := storageCode_conditioning_bound hC (univ \ Z) ha hu
  rw [hZc, hQ] at hcb
  have key : ((C.card : ℝ)) ^ 2 ≤ (Fintype.card α : ℝ) ^ (Fintype.card V + Z.card) := by
    have hc0 : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
    calc ((C.card : ℝ)) ^ 2
        ≤ ((Fintype.card α : ℝ) ^ ((Z.card : ℝ) + ((Fintype.card V - Z.card : ℕ) : ℝ) / 2)) ^ 2 :=
          pow_le_pow_left₀ hc0 hcb 2
      _ = (Fintype.card α : ℝ) ^ (Fintype.card V + Z.card) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le, ← Real.rpow_natCast]
          congr 1
          push_cast [Nat.cast_sub hZle]
          ring
  exact_mod_cast key

end Paid

section Transfer

/-- The hypothesis of Proposition 8.1: every loopless TT-free relation in which every vertex has
at most three parents satisfies the weighted half bound. -/
def DN3 : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (M : W → Finset W),
    (∀ w, w ∉ M w) → TTFree M → (∀ w, (M w).card ≤ 3) → RateBound M (1 / 2)

/-- **Conjecture P.** Every loopless TT-free relation in which every vertex has at most three
parents has a decomposition. -/
def ConjectureP : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (M : W → Finset W),
    (∀ w, w ∉ M w) → TTFree M → (∀ w, (M w).card ≤ 3) → ∃ pcs, Decomp M ∅ pcs

/-- By Theorem D, Conjecture P gives the hypothesis of Proposition 8.1. -/
theorem dn3_of_conjectureP (h : ConjectureP.{u}) : DN3.{u} := fun W _ _ M hl ht hd => by
  obtain ⟨pcs, hD⟩ := h W M hl ht hd
  exact rateBound_of_decomp hD

variable {V : Type u} [DecidableEq V] [Fintype V] {N : V → Finset V}

/-- Deleting the short pairs `Z = b_E(3)` leaves a loopless TT-free relation. -/
theorem dn3_hyp_deleted (hdeg : ∀ v, (N v).card ≤ 3) :
    let M := inducedNeighborhood N (univ \ shortPairedCoordinates N 3)
    (∀ w, w ∉ M w) ∧ TTFree M ∧ ∀ w, (M w).card ≤ 3 := by
  intro M
  have hZ : ∀ v, v ∈ (univ \ shortPairedCoordinates N 3 : Finset V) →
      ¬ (pairedIncidenceGraph N).edist (Sum.inl v) (Sum.inr v) ≤ (3 : ℕ) := by
    intro v hv hle
    exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨mem_univ _, hle⟩)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨w, hw⟩ hmem
    have hww : w ∈ N w := by simpa [M, inducedNeighborhood] using hmem
    exact hZ w hw (by
      have := (edist_eq_one_iff (N := N) w).mpr hww
      rw [this]; norm_num)
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ _ _ _ h1 h2 h3
    have h1' : x ∈ N y := by simpa [M, inducedNeighborhood] using h1
    have h2' : y ∈ N z := by simpa [M, inducedNeighborhood] using h2
    have h3' : x ∈ N z := by simpa [M, inducedNeighborhood] using h3
    exact hZ y hy (by exact_mod_cast edist_le_three_of_tt h1' h2' h3')
  · intro w
    exact (card_subtype _ _).le.trans ((card_filter_le _ _).trans (hdeg w))

/-- **Proposition 8.1.** Under its hypothesis, every storage code on a relation in which every
vertex has at most three parents satisfies `|C|² ≤ |α|^(|V| + b_E(3))`. -/
theorem card_sq_le_of_dn3 (H : DN3.{u}) (hdeg : ∀ v, (N v).card ≤ 3) {α : Type*} [Fintype α]
    [Nonempty α] {C : Finset (V → α)} (hC : IsStorageCode N C) :
    C.card ^ 2 ≤ Fintype.card α ^ (Fintype.card V + (shortPairedCoordinates N 3).card) := by
  obtain ⟨h1, h2, h3⟩ := dn3_hyp_deleted (N := N) hdeg
  exact card_sq_le_of_paidDeletion _ (H _ _ h1 h2 h3) hC

/-- **Proposition 8.1, rate form.** The rate is at most `1/2 + b_E(3)/(2|V|)`. -/
theorem storageCodeRate_le_of_dn3 (H : DN3.{u}) (hdeg : ∀ v, (N v).card ≤ 3) {α : Type*}
    [Fintype α] (ha : 1 < (Fintype.card α : ℝ)) (hV : 0 < Fintype.card V) {C : Finset (V → α)}
    (hC : IsStorageCode N C) (hne : C.Nonempty) :
    storageCodeRate C ≤ 1 / 2 + ((shortPairedCoordinates N 3).card : ℝ) / (2 * Fintype.card V) := by
  have : Nonempty α := Fintype.card_pos_iff.mp (by exact_mod_cast (zero_lt_one.trans ha))
  have hsq := card_sq_le_of_dn3 H hdeg hC
  have hpos : (0 : ℝ) < C.card := by exact_mod_cast hne.card_pos
  have hsqR : ((C.card : ℝ)) ^ 2 ≤ (Fintype.card α : ℝ) ^ (Fintype.card V +
      (shortPairedCoordinates N 3).card) := by exact_mod_cast hsq
  have hlog := Real.log_le_log (by positivity) hsqR
  rw [Real.log_pow, Real.log_pow] at hlog
  have hla : 0 < Real.log (Fintype.card α) := Real.log_pos ha
  have hVR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV
  unfold storageCodeRate
  rw [Real.logb, div_div, div_le_iff₀ (by positivity)]
  push_cast at hlog
  have : Real.log C.card ≤
      ((Fintype.card V : ℝ) + (shortPairedCoordinates N 3).card) / 2 * Real.log (Fintype.card α) := by
    nlinarith
  rw [show (1 / 2 + ((shortPairedCoordinates N 3).card : ℝ) / (2 * Fintype.card V)) *
      (Real.log (Fintype.card α) * Fintype.card V) =
      ((Fintype.card V : ℝ) + (shortPairedCoordinates N 3).card) / 2 * Real.log (Fintype.card α) by
    field_simp]
  exact this

/-- **Proposition 8.1, asymptotic form.** Under its hypothesis, Question 9.1 of *Directed Recovery
Structures* has an affirmative answer for recovery sets of size at most three, with the
paired-distance condition used only at radius three (any sequence with
`HasPairedDistanceSeparation` satisfies `hsep`). -/
theorem dn3_rate_eventually_le (H : DN3.{u}) {W : ℕ → Type u} [∀ n, DecidableEq (W n)]
    [∀ n, Fintype (W n)] (M : (n : ℕ) → W n → Finset (W n)) (hdeg : ∀ n w, (M n w).card ≤ 3)
    (hpos : ∀ n, 0 < Fintype.card (W n))
    (hsep : Tendsto (fun n => ((shortPairedCoordinates (M n) 3).card : ℝ) / Fintype.card (W n))
      atTop (𝓝 0))
    {A : ℕ → Type*} [∀ n, Fintype (A n)] (C : (n : ℕ) → Finset (W n → A n))
    (hC : ∀ n, IsStorageCode (M n) (C n)) (hne : ∀ n, (C n).Nonempty)
    (ha : ∀ n, 1 < (Fintype.card (A n) : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, storageCodeRate (C n) ≤ 1 / 2 + ε := by
  have hsmall : ∀ᶠ n in atTop,
      ((shortPairedCoordinates (M n) 3).card : ℝ) / Fintype.card (W n) < 2 * ε :=
    (tendsto_order.mp hsep).2 (2 * ε) (by linarith)
  filter_upwards [hsmall] with n hn
  have hle := storageCodeRate_le_of_dn3 H (hdeg n) (ha n) (hpos n) (hC n) (hne n)
  have hVR : (0 : ℝ) < Fintype.card (W n) := by exact_mod_cast hpos n
  have : ((shortPairedCoordinates (M n) 3).card : ℝ) / (2 * Fintype.card (W n)) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hVR] at hn
    linarith
  linarith

/-- The paired-distance condition of *Directed Recovery Structures* gives the radius-three
hypothesis of `dn3_rate_eventually_le`. -/
theorem shortPaired_three_tendsto {W : ℕ → Type u} [∀ n, DecidableEq (W n)] [∀ n, Fintype (W n)]
    (M : (n : ℕ) → W n → Finset (W n)) (h : HasPairedDistanceSeparation M) :
    Tendsto (fun n => ((shortPairedCoordinates (M n) 3).card : ℝ) / Fintype.card (W n))
      atTop (𝓝 0) :=
  h 3 (by norm_num)

end Transfer

end HalfRate
