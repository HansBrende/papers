import SoftRecovery.Conditioning

namespace SoftRecovery

open Finset HalfRate MotionDepthCodes
open scoped BigOperators
set_option autoImplicit false

variable {V A E : Type*} [DecidableEq V] [DecidableEq A] [DecidableEq E]

theorem image_le_sum {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (e : E → A) (F : Finset E) : h (F.image e) ≤ ∑ a ∈ F, h {e a} := by
  simpa only [image_singleton] using (image_isPolymatroid hh e).le_sum_singleton F

theorem recovery_mono {h : Finset A → ℝ} (hh : IsPolymatroid h)
    {S T : Finset A} {v : A} (hST : S ⊆ T) (hr : increment h S v = 0) :
    increment h T v = 0 :=
  le_antisymm (hr ▸ increment_antitone hh hST v) (increment_nonneg hh T v)

/-- An actual set of records that completes recovery pays at most its entropy.
No independence or linearity assumption is made. -/
theorem recovery_increment_le {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (S F : Finset A) (v : A) (hr : increment h (S ∪ F) v = 0) :
    increment h S v ≤ h F := by
  have hs := increment_le_conditionalRank_add hh S F v
  rw [union_comm F S, hr, add_zero] at hs
  exact hs.trans (conditionalRank_le hh F S)

/-- Additional common revelations reduce conditional entropy by at most their
joint entropy, and hence by at most the sum of their actual capacities. -/
theorem conditional_drop_le {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (C Z Q : Finset A) :
    h (C ∪ Z) - h Z - h Q ≤ h (C ∪ (Z ∪ Q)) - h (Z ∪ Q) := by
  have hs := conditional_drop_le_joint hh C Z Q
  have hq := conditionalRank_le hh Q Z
  linarith

/-- The usual deficit/revelation lower bound, without an independence assumption.
`I` is the full input, `C` the selected part, `O` the rest, and `G` the paid reveal. -/
theorem conditional_lower_from_deficit {h : Finset A → ℝ} (hh : IsPolymatroid h)
    {I C O G : Finset A} (hcover : I ⊆ C ∪ O)
    {L B Δ g : ℝ} (hI : L - Δ ≤ h I) (hO : h O ≤ L - B) (hG : h G ≤ g) :
    B - (Δ + g) ≤ h (C ∪ (O ∪ G)) - h (O ∪ G) := by
  have hm := hh.mono (hcover.trans
    (union_subset_union (subset_refl C) (subset_union_left : O ⊆ O ∪ G)))
  have hs := hh.union_le O G
  linarith

variable [Fintype V]

omit [DecidableEq V] in
/-- Unused coordinate capacity after the common context and reveal. -/
def revealCredit (h : Finset A → ℝ) (f : V → A) (b : V → ℝ) (Z Q : Finset A) : ℝ :=
  ∑ v, (b v - increment h (Z ∪ Q) (f v))

omit [DecidableEq V] in
theorem revealCredit_nonneg {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (b : V → ℝ) (Z Q : Finset A)
    (hb : ∀ v, increment h Z (f v) ≤ b v) : 0 ≤ revealCredit h f b Z Q :=
  sum_nonneg fun v _ => sub_nonneg.mpr
    ((increment_antitone hh subset_union_left _).trans (hb v))

/-- Exact disclosure information and coordinate credit. Unlike the capacity
corollary, this statement requires no individual bounds on `b v`. -/
theorem capacity_bound_with_credit {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (Z Q : Finset A) (b : V → ℝ) (δ R : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z)
    (hres : (∑ v, increment h ((N v).image f ∪ (Z ∪ Q)) (f v)) ≤ R) :
    (∑ v, b v) + revealCredit h f b Z Q ≤
      2 * δ + 2 * mutualRank h (univ.image f) Q Z + R := by
  have hs := conditional_soft hh (Z ∪ Q) f hD
  simp only [revealCredit, sum_sub_distrib, mutualRank, conditionalRank, union_comm Q Z]
  linarith

/-- Convert any certified bound on local recovery uncertainty into a capacity
inequality. Only conditional singleton bounds are needed. -/
theorem capacity_bound_of_residual {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (Z Q : Finset A) (b : V → ℝ) (δ R : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (hb : ∀ v, increment h Z (f v) ≤ b v)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z)
    (hres : (∑ v, increment h ((N v).image f ∪ (Z ∪ Q)) (f v)) ≤ R) :
    (∑ v, b v) ≤ 2 * δ + 2 * conditionalRank h Q Z + R := by
  have hs := capacity_bound_with_credit hh f Z Q b δ R hD hlower hres
  have hcredit := revealCredit_nonneg hh f b Z Q hb
  have hinfo := mutualRank_le_right hh (univ.image f) Q Z
  linarith

omit [DecidableEq E] in
/-- Joint, conditional record accounting with arbitrary residual uncertainty.
No exact decoder, record independence, or linearity is required. -/
theorem mixed_record_entropy_bound {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (e : E → A) (Z : Finset A) (F : V → Finset E)
    (b : V → ℝ) (δ : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (hb : ∀ v, increment h Z (f v) ≤ b v)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z)
    (Q : Finset E) :
    (∑ v, b v) ≤ 2 * δ + 2 * conditionalRank h (Q.image e) Z +
      ∑ v, (conditionalRank h ((F v).image e) ((N v).image f ∪ (Z ∪ Q.image e)) +
        increment h ((F v).image e ∪ ((N v).image f ∪ (Z ∪ Q.image e))) (f v)) := by
  apply capacity_bound_of_residual hh f Z (Q.image e) b δ _ hD hb hlower
  exact sum_le_sum fun v _ => increment_le_conditionalRank_add hh _ _ _

/-- Mixed local/global accounting. `F v` contains actual record identities
that complete recovery at `v`; `Q` is any collection revealed globally.
The hypothesis on the initial entropy is supplied, for example, by
`conditional_lower_from_deficit` with `δ = Δ + g`. -/
theorem mixed_record_bound {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (e : E → A) (Z : Finset A) (F : V → Finset E)
    (b : V → ℝ) (c : E → ℝ) (δ : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (hb : ∀ v, h {f v} ≤ b v) (hc : ∀ a, h {e a} ≤ c a)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z)
    (hrecover : ∀ v, increment h (((N v).image f ∪ Z) ∪ (F v).image e) (f v) = 0)
    (Q : Finset E) :
    (∑ v, b v) ≤ 2 * δ + 2 * (∑ a ∈ Q, c a) +
      ∑ v, ∑ a ∈ F v \ Q, c a := by
  have hQ : h (Q.image e) ≤ ∑ a ∈ Q, c a :=
    (image_le_sum hh e Q).trans (sum_le_sum fun a _ => hc a)
  have hres : ∑ v, increment h ((N v).image f ∪ (Z ∪ Q.image e)) (f v) ≤
      ∑ v, ∑ a ∈ F v \ Q, c a := by
    apply sum_le_sum
    intro v _
    have hsubset : ((N v).image f ∪ Z) ∪ (F v).image e ⊆
        ((N v).image f ∪ (Z ∪ Q.image e)) ∪ (F v \ Q).image e := by
      have hf : F v ⊆ Q ∪ (F v \ Q) := by
        rw [union_sdiff_self_eq_union]
        exact subset_union_right
      simpa only [image_union, union_assoc] using
        union_subset_union (subset_refl ((N v).image f ∪ Z)) (image_subset_image hf)
    have hr := recovery_mono hh hsubset (hrecover v)
    exact (recovery_increment_le hh _ _ _ hr).trans
      ((image_le_sum hh e _).trans (sum_le_sum fun a _ => hc a))
  have hs := capacity_bound_of_residual hh f Z (Q.image e) b δ _ hD
    (fun v => (increment_le_singleton hh Z _).trans (hb v)) hlower hres
  have hq := conditionalRank_le hh (Q.image e) Z
  linarith

variable [Fintype E]

/-- The number of local recovery obligations using a particular actual record. -/
def multiplicity (F : V → Finset E) (a : E) : ℕ := (univ.filter fun v => a ∈ F v).card

omit [DecidableEq V] in
theorem local_bill (F : V → Finset E) (c : E → ℝ) (Q : Finset E) :
    (∑ v, ∑ a ∈ F v \ Q, c a) =
      ∑ a, if a ∈ Q then 0 else (multiplicity F a : ℝ) * c a := by
  have hrow : ∀ v, (∑ a ∈ F v \ Q, c a) =
      ∑ a, if a ∈ Q then 0 else if a ∈ F v then c a else 0 := by
    intro v
    rw [← sum_ite_mem_eq (F v \ Q) c]
    apply sum_congr rfl
    intro a _
    by_cases hq : a ∈ Q <;> simp [hq]
  simp_rw [hrow]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  by_cases ha : a ∈ Q
  · simp [ha]
  · simp only [ha, ↓reduceIte]
    rw [← sum_filter]
    simp [multiplicity]

omit [DecidableEq V] [Fintype V] in
/-- Thresholding any nonnegative integer charge count gives the coefficient
`min(2,k)`. This is exact algebra, not an optimization assumption. -/
theorem threshold_bill (k : E → ℕ) (c : E → ℝ) :
    2 * (∑ a ∈ univ.filter (fun a => 2 ≤ k a), c a) +
      (∑ a, if a ∈ univ.filter (fun a => 2 ≤ k a) then 0 else (k a : ℝ) * c a) =
      ∑ a, c a * (min 2 (k a) : ℕ) := by
  rw [sum_filter, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  by_cases hm : 2 ≤ k a
  · simp [hm, mul_comm]
  · simp [hm, Nat.min_eq_right (by omega : k a ≤ 2), mul_comm]

omit [DecidableEq V] in
theorem optimized_bill (F : V → Finset E) (c : E → ℝ) :
    2 * (∑ a ∈ univ.filter (fun a => 2 ≤ multiplicity F a), c a) +
      (∑ v, ∑ a ∈ F v \ univ.filter (fun a => 2 ≤ multiplicity F a), c a) =
      ∑ a, c a * (min 2 (multiplicity F a) : ℕ) := by
  rw [local_bill]
  exact threshold_bill (multiplicity F) c

theorem optimized_record_bound {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (e : E → A) (Z : Finset A) (F : V → Finset E)
    (b : V → ℝ) (c : E → ℝ) (δ : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (hb : ∀ v, h {f v} ≤ b v) (hc : ∀ a, h {e a} ≤ c a)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z)
    (hrecover : ∀ v, increment h (((N v).image f ∪ Z) ∪ (F v).image e) (f v) = 0) :
    (∑ v, b v) ≤ 2 * δ + ∑ a, c a * (min 2 (multiplicity F a) : ℕ) := by
  have hs := mixed_record_bound hh f e Z F b c δ hD hb hc hlower hrecover
    (univ.filter fun a => 2 ≤ multiplicity F a)
  rw [add_assoc, optimized_bill] at hs
  exact hs

end SoftRecovery
