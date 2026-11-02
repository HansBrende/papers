import AboveHalfRate.Main

/-!
# The undirected crux

The formal part of Corollary U of the paper. Symmetrizing the descended relations of a tower of
twisted quotients (`AboveHalf.CheckSystem.symGraph`) gives simple graphs of bounded degree whose
closed walks of odd length are long, and the codes of the tower are storage codes for their
neighbourhood maps (`MotionDepthCodes.nbhd`). Blowing every vertex up into `b` non-adjacent copies
(`graphBlowUp`) turns them into binary codes on graphs with the same properties.

* `undirected_tower`: for every `K`, eventually the symmetrized graphs have degrees at most
  `2 (β - 1)` and no closed walk of odd length at most `K`, and carry a storage code of rate at
  least `ρ`;
* `undirected_tower_binary`: the same for the blow-ups, with degrees at most `b (2 (β - 1))` and
  binary codes of rate at least `ρ log₂ |𝔽| / b`.
-/

namespace AboveHalf

open Filter Finset DirectedRecovery MotionDepthCodes

set_option autoImplicit false

section GraphBlowUp

variable {V : Type*}

/-- The blow-up of a simple graph: every vertex becomes `b` non-adjacent copies, and copies of
adjacent vertices are adjacent. -/
abbrev graphBlowUp (G : SimpleGraph V) (b : ℕ) : SimpleGraph (V × Fin b) := G.comap Prod.fst

/-- Forgetting the copy index is a homomorphism from the blow-up onto the graph. -/
def graphBlowUpHom (G : SimpleGraph V) (b : ℕ) : graphBlowUp G b →g G where
  toFun := Prod.fst
  map_rel' h := h

/-- Walks of the blow-up project to walks of the same length. -/
theorem exists_walk_of_graphBlowUp (G : SimpleGraph V) {b : ℕ} {x y : V × Fin b}
    (w : (graphBlowUp G b).Walk x y) : ∃ w' : G.Walk x.1 y.1, w'.length = w.length :=
  ⟨w.map (graphBlowUpHom G b), SimpleGraph.Walk.length_map _ _⟩

variable [Fintype V]

/-- The neighbourhoods of the blow-up are those of the blown-up relation. -/
theorem nbhd_graphBlowUp (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ) (x : V × Fin b) :
    nbhd (graphBlowUp G b) x = blowUp (nbhd G) b x := by
  ext y
  simp [nbhd, blowUp]

/-- **Binary storage codes on the blow-up of a graph.** -/
theorem isStorageCode_graphBlowUp (G : SimpleGraph V) [DecidableRel G.Adj] {A : Type*} {b : ℕ}
    {C : Finset (V → A)} (hC : IsStorageCode (nbhd G) C) {ι : A → Fin b → Bool}
    (hι : Function.Injective ι) : IsStorageCode (nbhd (graphBlowUp G b)) (blowCode ι C) := by
  rw [show nbhd (graphBlowUp G b) = blowUp (nbhd G) b from funext (nbhd_graphBlowUp G b)]
  exact isStorageCode_blowCode hC hι

/-- **Degrees of the blow-up** are at most `b` times those of the graph. -/
theorem degree_graphBlowUp_le (G : SimpleGraph V) [DecidableRel G.Adj] {b Δ : ℕ}
    (hG : ∀ v, G.degree v ≤ Δ) (x : V × Fin b) : (graphBlowUp G b).degree x ≤ b * Δ := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have h : univ.filter ((graphBlowUp G b).Adj x) = nbhd (graphBlowUp G b) x := rfl
  rw [h, nbhd_graphBlowUp, blowUp, card_product, card_univ, Fintype.card_fin, mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  have hd := hG x.1
  rwa [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter] at hd

end GraphBlowUp

variable {P : Type} [DecidableEq P] {Γ : Type*} [Group Γ] [MulAction Γ P]
variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽]

section Tower

variable (S : CheckSystem P Γ 𝔽) (ball : P → Finset P)
  (hball : ∀ p x, x ∈ ball p ↔ S.dist p x ≤ S.R) {β : ℕ} (hβ : ∀ p, (ball p).card ≤ β)
  (Γs : ℕ → Subgroup Γ) [∀ n, Fintype (Quo (Γs n) P)]
  (s : ℕ → ℕ) (hdisp : ∀ n, ∀ γ ∈ Γs n, γ ≠ 1 → ∀ p, s n ≤ S.dist p (γ • p))
  (hs : Tendsto s atTop atTop)
  (hsize : Tendsto (fun n => Fintype.card (Quo (Γs n) P)) atTop atTop)
  (C : ∀ n, Submodule 𝔽 (Quo (Γs n) P → 𝔽))
  (hann : ∀ n, ∀ c ∈ C n, ∀ p,
    ∑ y ∈ (S.check p).support, S.check p y * c (proj (Γs n) y) = 0)
  {ρ : ℝ} (hdim : ∀ n, ρ * Fintype.card (Quo (Γs n) P) ≤ Module.finrank 𝔽 (C n))

omit [Fintype 𝔽] [∀ n, Fintype (Quo (Γs n) P)] in
include hdisp in
/-- Closed walks of odd length at most `K` disappear once the displacement exceeds `R K`. -/
theorem lt_length_of_odd_walk [∀ n, DecidableEq (Quo (Γs n) P)] {K n : ℕ} (hn : S.R * K < s n)
    {x : Quo (Γs n) P} (w : (S.symGraph (Γs n)).Walk x x) (hodd : Odd w.length) :
    K < w.length := by
  by_contra hle
  have h1 := S.le_mul_of_odd_walk (hdisp n) w hodd
  have h2 : S.R * w.length ≤ S.R * K := Nat.mul_le_mul_left _ (Nat.le_of_not_lt hle)
  omega

include hball hβ hdisp hs hsize hann hdim in
/-- **Corollary U, formal part.** For every `K`, eventually the symmetrized graphs of the tower
have degrees at most `2 (β - 1)` and no closed walk of odd length at most `K`, and the codes of the
tower are storage codes of rate at least `ρ` for their neighbourhood maps. -/
theorem undirected_tower [∀ n, DecidableEq (Quo (Γs n) P)]
    [∀ n, DecidableRel (S.symGraph (Γs n)).Adj] (K : ℕ) :
    ∀ᶠ n in atTop,
      (∀ x, (S.symGraph (Γs n)).degree x ≤ 2 * (β - 1)) ∧
      (∀ x (w : (S.symGraph (Γs n)).Walk x x), Odd w.length → K < w.length) ∧
      IsStorageCode (nbhd (S.symGraph (Γs n))) (wordsOf (C n)) ∧
      ρ ≤ storageCodeRate (wordsOf (C n)) := by
  classical
  filter_upwards [hs.eventually_gt_atTop (S.R * K + S.R), hsize.eventually_gt_atTop 0]
    with n hn hpos
  refine ⟨fun x => S.degree_symGraph_le ball hball hβ x, fun x w hodd =>
    lt_length_of_odd_walk S Γs s hdisp (by omega) w hodd, ?_, ?_⟩
  · exact S.isStorageCode_nbhd_symGraph (hdisp n) (by omega)
      (S.isStorageCode_qrel (wordsOf (C n)) fun c hc p => hann n c (mem_wordsOf.1 hc) p)
  · have hpos' : (0 : ℝ) < Fintype.card (Quo (Γs n) P) := by exact_mod_cast hpos
    rw [storageCodeRate_wordsOf, le_div_iff₀ hpos']
    exact hdim n

include hball hβ hdisp hs hsize hann hdim in
/-- **Corollary U, binary formal part.** With an injective encoding `ι : 𝔽 → (Fin b → Bool)`, for
every `K`, eventually the blow-ups of the symmetrized graphs have degrees at most `b (2 (β - 1))`
and no closed walk of odd length at most `K`, and carry binary storage codes of rate at least
`ρ log₂ |𝔽| / b`. -/
theorem undirected_tower_binary [∀ n, DecidableEq (Quo (Γs n) P)]
    [∀ n, DecidableRel (S.symGraph (Γs n)).Adj] {b : ℕ} (ι : 𝔽 → Fin b → Bool)
    (hι : Function.Injective ι) (K : ℕ) :
    ∀ᶠ n in atTop,
      (∀ x, (graphBlowUp (S.symGraph (Γs n)) b).degree x ≤ b * (2 * (β - 1))) ∧
      (∀ x (w : (graphBlowUp (S.symGraph (Γs n)) b).Walk x x), Odd w.length → K < w.length) ∧
      IsStorageCode (nbhd (graphBlowUp (S.symGraph (Γs n)) b)) (blowCode ι (wordsOf (C n))) ∧
      ρ * Real.logb 2 (Fintype.card 𝔽) / b ≤ storageCodeRate (blowCode ι (wordsOf (C n))) := by
  classical
  filter_upwards [undirected_tower S ball hball hβ Γs s hdisp hs hsize C hann hdim K]
    with n ⟨hdeg, hodd, hstore, hrate⟩
  refine ⟨fun x => degree_graphBlowUp_le _ hdeg x, fun x w hw => ?_,
    isStorageCode_graphBlowUp _ hstore hι, ?_⟩
  · obtain ⟨w', hw'⟩ := exists_walk_of_graphBlowUp _ w
    rw [← hw'] at hw ⊢
    exact hodd _ w' hw
  · rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      rw [Nat.cast_zero, div_zero]
      unfold storageCodeRate
      rw [Fintype.card_prod, Fintype.card_fin, mul_zero, Nat.cast_zero, div_zero]
    have hq : (1 : ℝ) < Fintype.card 𝔽 := by exact_mod_cast Fintype.one_lt_card
    have hlog : 0 < Real.logb 2 (Fintype.card 𝔽) := Real.logb_pos (by norm_num) hq
    have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
    have heq : storageCodeRate (blowCode ι (wordsOf (C n))) =
        storageCodeRate (wordsOf (C n)) * Real.logb 2 (Fintype.card 𝔽) / b := by
      unfold storageCodeRate
      rw [card_blowCode hι, Fintype.card_bool, Fintype.card_prod, Fintype.card_fin]
      have h2 : Real.logb 2 ((wordsOf (C n)).card : ℝ) =
          Real.logb (Fintype.card 𝔽) ((wordsOf (C n)).card : ℝ) * Real.logb 2 (Fintype.card 𝔽) := by
        rw [Real.logb, Real.logb, Real.logb]
        have hlogq : Real.log (Fintype.card 𝔽 : ℝ) ≠ 0 :=
          (Real.log_pos hq).ne'
        field_simp
      push_cast
      rw [h2]
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrate hlog.le) hbpos.le

end Tower

end AboveHalf
