import SourceCovers.CausalFibreMixture
import TransposeFollowup.UniformEntropy
import TransposeFollowup.ConditionalCoordinateEntropy

/-! Entropy consequences of the actual support routing. All entropies here
are in bits. Existing support and conditional-cover inequalities suffice;
no independence, causal typing or normalization is needed for this layer. -/

namespace SourceCovers.CausalGroups.Network

open LeanMachine TransposeFollowup Finset
open scoped BigOperators Classical
noncomputable section

universe u v
variable {d b h n : ℕ} {Edge : Type u} [Fintype Edge] (G : Network d b h n Edge)
variable {Helper : Type v} (C : Set (Input d b)) (Z : Input d b → Helper)

-- Match the classical helper equality used by the imported fibre sums.
local instance : DecidableEq (AttainedHelper C Z) := Classical.decEq _

/-- Sum of the groups' conditional entropies, measured in bits. -/
def conditionalGroupEntropy (p : C → ℝ) : ℝ :=
  ∑ a, conditionalObservationEntropy p (fun x : C => G.projection a x.val)
    (helperValue C Z) / Real.log 2

/-- Conditional total correlation of the whole column groups, in bits.
Together the groups determine the input, and the helper is deterministic. -/
def groupTotalCorrelation (p : C → ℝ) : ℝ :=
  G.conditionalGroupEntropy C Z p -
    (entropy p - observationEntropy p (helperValue C Z)) / Real.log 2

/-- The fibre support bounds the corresponding weighted conditional entropy.
The zero-mass case contributes zero on both sides. -/
theorem attainedWeight_mul_groupEntropy_le (p : C → ℝ) (hp : ∀ x, 0 ≤ p x)
    (z : AttainedHelper C Z) (a : Fin h) :
    attainedWeight C Z p z *
      (observationEntropy (helperConditionalWeight p (helperValue C Z) z)
        (fun x : HelperFiber (helperValue C Z) z => G.projection a x.val.val) / Real.log 2) ≤
      attainedWeight C Z p z * G.groupSupportLog (fibre C Z z.val) a := by
  classical
  by_cases hz : attainedWeight C Z p z = 0
  · simp [hz]
  have hw := attainedWeight_nonneg C Z p hp z
  let := helperFiber_nonempty_of_mass_pos p (helperValue C Z) z (lt_of_le_of_ne hw (Ne.symm hz))
  let A := Set.range (fun x : fibre C Z z.val => G.projection a x.val)
  have he := observationEntropy_le_log_support
    (Ω := HelperFiber (helperValue C Z) z) (A := G.GroupBit a → Bool)
    (helperConditionalWeight p (helperValue C Z) z)
    (helperConditionalWeight_nonneg p hp (helperValue C Z) z)
    (sum_helperConditionalWeight p (helperValue C Z) z hz)
    (fun x : HelperFiber (helperValue C Z) z => G.projection a x.val.val)
    A.toFinset (fun x => Set.mem_toFinset.mpr ⟨attainedFibreEquiv C Z z x, rfl⟩)
  apply mul_le_mul_of_nonneg_left _ hw
  unfold groupSupportLog Real.logb
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  simpa only [Set.toFinset_card] using he

/-- The entropy lower bound in Theorem Q. This stronger version allows any
nonnegative finite weights, including zero-mass fibres, without normalization. -/
theorem conditionalGroupEntropy_le_supportRoutingMass
    (p : C → ℝ) (hp : ∀ x, 0 ≤ p x) :
    G.conditionalGroupEntropy C Z p ≤ G.supportRoutingMass C Z p := by
  classical
  unfold conditionalGroupEntropy
  simp_rw [← sum_helperMass_mul_observationEntropy p hp,
    Finset.sum_div, mul_div_assoc]
  rw [sum_comm]
  apply sum_le_sum
  intro z _
  change (∑ a, attainedWeight C Z p z * _) ≤
    attainedWeight C Z p z * G.supportSum (fibre C Z z.val)
  rw [supportSum, mul_sum]
  exact sum_le_sum fun a _ => G.attainedWeight_mul_groupEntropy_le C Z p hp z a

/-- The correlation term is nonnegative even for unnormalized weights.
The existing conditional covering inequality applies because the groups
partition the raw coordinates. Empty input domains are allowed as well. -/
theorem groupTotalCorrelation_nonneg (p : C → ℝ) (hp : ∀ x, 0 ≤ p x) :
    0 ≤ G.groupTotalCorrelation C Z p := by
  cases isEmpty_or_nonempty C with
  | inl hC =>
    simp [groupTotalCorrelation, conditionalGroupEntropy, conditionalObservationEntropy,
      observationEntropy, entropy, pushforward]
  | inr hC =>
    let : Nonempty (AttainedHelper C Z) := Nonempty.map (helperValue C Z) hC
    let S (a : Fin h) : Finset (Bit d b) := univ.filter fun ξ => G.partition.group ξ.2.1 = a
    have hcover (ξ : Bit d b) : (1 : ℝ) ≤ ∑ a, if ξ ∈ S a then (1 : ℝ) else 0 := by
      simp [S, eq_comm]
    have hc := conditionalCoordinateEntropy_cover p hp (fun x : C => x.val)
      (helperValue C Z) S 1 hcover
    have he (a : Fin h) :
        conditionalCoordinateEntropy p (fun x : C => x.val) (helperValue C Z) (S a) =
          conditionalObservationEntropy p (fun x : C => G.projection a x.val)
            (helperValue C Z) := by
      apply conditionalObservationEntropy_eq_of_same_fibers p hp
      intro x y _
      rw [bitView_eq_iff]
      constructor
      · intro hxy
        funext ξ
        exact hxy ξ.val (by simpa [S] using ξ.property)
      · intro hxy ξ hξ
        exact congrFun hxy ⟨ξ, by simpa [S] using hξ⟩
    have hi : conditionalObservationEntropy p (fun x : C => x.val) (helperValue C Z) =
        entropy p - observationEntropy p (helperValue C Z) := by
      rw [conditionalObservationEntropy, observationEntropy_injective p hp _
        (fun x y hxy => Subtype.ext (congrArg Prod.snd hxy))]
    simp only [one_mul, he, hi] at hc
    unfold groupTotalCorrelation conditionalGroupEntropy
    rw [← Finset.sum_div]
    exact sub_nonneg.mpr
      (div_le_div_of_nonneg_right hc (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)

/-- Any upper bound on the group entropy gives the helper/deficit inequality,
retaining the exact total-correlation term. The budget `L` may be arbitrary. -/
theorem deficit_add_helper_ge_of_groupEntropy_le (p : C → ℝ) (L B : ℝ)
    (hB : G.conditionalGroupEntropy C Z p ≤ B) :
    L + G.groupTotalCorrelation C Z p - B ≤
      L - entropy p / Real.log 2 + observationEntropy p (helperValue C Z) / Real.log 2 := by
  unfold groupTotalCorrelation
  rw [sub_div]
  linarith

/-- The helper/deficit lower bound before the metric estimate is applied. -/
theorem deficit_add_helper_ge_support (p : C → ℝ) (hp : ∀ x, 0 ≤ p x) (L : ℝ) :
    L + G.groupTotalCorrelation C Z p - G.supportRoutingMass C Z p ≤
      L - entropy p / Real.log 2 + observationEntropy p (helperValue C Z) / Real.log 2 :=
  G.deficit_add_helper_ge_of_groupEntropy_le C Z p L _
    (G.conditionalGroupEntropy_le_supportRoutingMass C Z p hp)

end
end SourceCovers.CausalGroups.Network
