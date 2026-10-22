import TransposeFollowup.CommutativeFiniteBoundary
import Mathlib.Data.Finset.Prod

/-! Finite almost-invariant affine-map sets. Right composition by (s,b)
sends (a,t) to (as,t+ab). First choose slopes, then a translation set for
all finitely many resulting shifts. This directly handles negative slopes
and does not use a general amenable-extension or hyperfiniteness theorem. -/
namespace TransposeFollowup.FiniteBoundary
open Classical Finset
open scoped BigOperators
set_option autoImplicit false

def affineRight (s : ℝˣ) (b : ℝ) (p : ℝˣ × ℝ) : ℝˣ × ℝ :=
  (p.1*s,p.2+(p.1 : ℝ)*b)

theorem affineRight_apply (s : ℝˣ) (b : ℝ) (p : ℝˣ × ℝ) (x : ℝ) :
    ((affineRight s b p).1 : ℝ)*x+(affineRight s b p).2=
      (p.1 : ℝ)*((s : ℝ)*x+b)+p.2 := by
  simp only [affineRight, Units.val_mul]
  ring

theorem affineRight_injective (s : ℝˣ) (b : ℝ) : Function.Injective (affineRight s b) := by
  intro p q he
  have ha : p.1=q.1 := mul_right_cancel (congrArg Prod.fst he)
  apply Prod.ext ha
  have ht := congrArg Prod.snd he
  change p.2+(p.1 : ℝ)*b=q.2+(q.1 : ℝ)*b at ht
  rw [ha] at ht
  exact add_right_cancel ht

theorem image_escape_card {α : Type*} [DecidableEq α] (F : Finset α) (f : α → α)
    (hf : Function.Injective f) :
    (F.image f \ F).card=(F.filter (fun x => f x ∉ F)).card := by
  rw [Finset.sdiff_eq_filter, Finset.filter_image, Finset.card_image_of_injective _ hf]

theorem affine_rectangle_escape_card (S : Finset ℝˣ) (T : Finset ℝ)
    (s : ℝˣ) (b : ℝ) :
    ((S ×ˢ T).image (affineRight s b) \ (S ×ˢ T)).card ≤
      (S.filter (fun a => a*s ∉ S)).card*T.card+
        ∑ a ∈ S, (T.filter (fun t => t+(a : ℝ)*b ∉ T)).card := by
  let A := (S.filter (fun a => a*s ∉ S)) ×ˢ T
  let B := S.biUnion (fun a => ({a} : Finset ℝˣ) ×ˢ
    T.filter (fun t => t+(a : ℝ)*b ∉ T))
  have hsub : ((S ×ˢ T).filter (fun p => affineRight s b p ∉ S ×ˢ T)) ⊆ A ∪ B := by
    intro p hp
    obtain ⟨hp, hout⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, ht⟩ := Finset.mem_product.mp hp
    by_cases hs : p.1*s ∈ S
    · have hb : p.2+(p.1 : ℝ)*b ∉ T := by
        intro hb
        exact hout (Finset.mem_product.mpr ⟨hs, hb⟩)
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨p.1, ha, Finset.mem_product.mpr ⟨Finset.mem_singleton_self _,
        Finset.mem_filter.mpr ⟨ht,hb⟩⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨ha,hs⟩,ht⟩)
  have hB : B.card ≤ ∑ a ∈ S, (T.filter (fun t => t+(a : ℝ)*b ∉ T)).card := by
    simpa only [B, Finset.card_product, Finset.card_singleton, one_mul] using
      (Finset.card_biUnion_le (s:=S) (t:=fun a => ({a} : Finset ℝˣ) ×ˢ
        T.filter (fun t => t+(a : ℝ)*b ∉ T)))
  calc
    _ = _ := image_escape_card (S ×ˢ T) _ (affineRight_injective s b)
    _ ≤ (A ∪ B).card := Finset.card_le_card hsub
    _ ≤ A.card+B.card := Finset.card_union_le A B
    _ ≤ _ := by simpa only [A, Finset.card_product] using Nat.add_le_add_left hB A.card

theorem exists_affine_small_boundary {ι : Type*} [Fintype ι]
    (s : ι → ℝˣ) (b : ι → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (ℝˣ × ℝ), F.Nonempty ∧ ∀ j,
      ((F.image (affineRight (s j) (b j)) \ F).card : ℝ) ≤ ε*F.card := by
  have he : 0 < ε/2 := by positivity
  obtain ⟨S,hS,hboundS⟩ := exists_small_mul_boundary s he
  obtain ⟨T,hT,hboundT⟩ := exists_small_add_boundary
    (fun p : S × ι => ((p.1.val : ℝˣ) : ℝ)*b p.2) he
  refine ⟨S ×ˢ T, hS.product hT, fun j => ?_⟩
  have hsc : ((S.filter (fun a => a*s j ∉ S)).card : ℝ) ≤ ε/2*S.card := by
    rw [← image_escape_card S (fun a => a*s j) (fun _ _ h => mul_right_cancel h)]
    exact hboundS j
  have htc (a : ℝˣ) (ha : a ∈ S) :
      ((T.filter (fun t => t+(a : ℝ)*b j ∉ T)).card : ℝ) ≤ ε/2*T.card := by
    rw [← image_escape_card T (fun t => t+(a : ℝ)*b j) (fun _ _ h => add_right_cancel h)]
    exact hboundT (⟨⟨a,ha⟩,j⟩ : S × ι)
  have hc : (((S ×ˢ T).image (affineRight (s j) (b j)) \ (S ×ˢ T)).card : ℝ) ≤
      ((S.filter (fun a => a*s j ∉ S)).card : ℝ)*T.card+
        ∑ a ∈ S, ((T.filter (fun t => t+(a : ℝ)*b j ∉ T)).card : ℝ) := by
    exact_mod_cast affine_rectangle_escape_card S T (s j) (b j)
  have hsum : (∑ a ∈ S, ((T.filter (fun t => t+(a : ℝ)*b j ∉ T)).card : ℝ)) ≤
      (S.card : ℝ)*(ε/2*T.card) := by
    calc
      _ ≤ ∑ _a ∈ S, ε/2*(T.card : ℝ) := Finset.sum_le_sum htc
      _ = _ := by simp
  have hm := mul_le_mul_of_nonneg_right hsc (Nat.cast_nonneg T.card : (0 : ℝ) ≤ T.card)
  rw [Finset.card_product, Nat.cast_mul]
  nlinarith

theorem exists_affine_small_symmetric_difference {ι : Type*} [Fintype ι]
    (s : ι → ℝˣ) (b : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : Finset (ℝˣ × ℝ), F.Nonempty ∧ ∀ j,
      let H := F.image (affineRight (s j) (b j))
      (((F ∪ H) \ (F ∩ H)).card : ℝ) ≤ δ*(F ∪ H).card := by
  obtain ⟨F,hF,hbound⟩ := exists_affine_small_boundary s b (show 0 < δ/2 by positivity)
  refine ⟨F,hF,fun j => ?_⟩
  let H := F.image (affineRight (s j) (b j))
  have hcard : H.card=F.card := Finset.card_image_of_injective _ (affineRight_injective _ _)
  have heq : (F \ H).card=(H \ F).card := Finset.card_sdiff_eq_card_sdiff_iff.mpr hcard.symm
  have hset : (F ∪ H) \ (F ∩ H)=(F \ H) ∪ (H \ F) := by ext x; simp; tauto
  have hc : ((F ∪ H) \ (F ∩ H)).card ≤ 2*(H \ F).card := by
    rw [hset]
    have h := Finset.card_union_le (F \ H) (H \ F)
    rw [heq] at h
    omega
  have hc' : (((F ∪ H) \ (F ∩ H)).card : ℝ) ≤ 2*(H \ F).card := by exact_mod_cast hc
  have hu : (F.card : ℝ) ≤ (F ∪ H).card := by
    exact_mod_cast Finset.card_le_card (Finset.subset_union_left (s₁:=F) (s₂:=H))
  have hb := hbound j
  have hm := mul_le_mul_of_nonneg_left hu hδ.le
  change (((F ∪ H) \ (F ∩ H)).card : ℝ) ≤ δ*(F ∪ H).card
  dsimp only [H] at hc'
  nlinarith

end TransposeFollowup.FiniteBoundary
