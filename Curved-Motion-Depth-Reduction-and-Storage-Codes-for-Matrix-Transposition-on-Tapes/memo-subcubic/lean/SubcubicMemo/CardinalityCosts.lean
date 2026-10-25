import SubcubicMemo.Schedules
import MotionDepthCodes.StorageCode

/-! Multiplicative ambiguity costs for arbitrary finite codes. -/

namespace SubcubicMemo

open Finset MotionDepthCodes
open scoped BigOperators

variable {V F α : Type*} [Fintype V] [DecidableEq V] [Field F] [DecidableEq F]

open Classical in
noncomputable def observations (C : Finset (V → α)) (S : Finset V) : ℕ :=
  (C.image (view S)).card

open Classical in
/-- Number of possible target symbols after the other symbols in a row are fixed. -/
noncomputable def choices (C : Finset (V → α)) (R : Finset V) (x : V) (f : V → α) : ℕ :=
  ((C.filter (fun g : V → α => ∀ y ∈ R.erase x, g y = f y)).image (fun g => g x)).card

theorem observations_mono (C : Finset (V → α)) {S T : Finset V} (hST : S ⊆ T) :
    observations C S ≤ observations C T := by
  classical
  let mask : (V → Option α) → V → Option α := fun f v => if v ∈ S then f v else none
  have heq : (C.image (view T)).image mask = C.image (view S) := by
    rw [image_image]
    congr 1
    funext f v
    by_cases hv : v ∈ S
    · simp [mask, view, hv, hST hv]
    · simp [mask, view, hv]
  unfold observations
  rw [← heq]
  exact card_image_le

@[simp] theorem observations_univ (C : Finset (V → α)) : observations C univ = C.card := by
  classical
  unfold observations
  apply card_image_of_injective
  intro f g h
  funext v
  exact (view_eq_iff univ f g).mp h v (mem_univ _)

theorem observations_step (C : Finset (V → α)) {R K : Finset V} {x : V} {L : ℕ}
    (hready : R.erase x ⊆ K) (hL : ∀ f ∈ C, choices C R x f ≤ L) :
    observations C (insert x K) ≤ L * observations C K := by
  classical
  let P := C.image (fun f => (view K f, f x))
  have hfst : P.image Prod.fst = C.image (view K) := by simp [P, image_image, Function.comp_def]
  have hcount : P.card ≤ L * observations C K := by
    have hp := card_le_mul_card_image (f := Prod.fst) P L (by
      intro a ha
      rw [hfst] at ha
      obtain ⟨f, hf, hfa⟩ := mem_image.mp ha
      apply le_trans _ (hL f hf)
      unfold choices
      apply card_le_card_of_injOn Prod.snd
      · intro p hp
        obtain ⟨hpP, hpa⟩ := mem_filter.mp hp
        obtain ⟨g, hg, hgp⟩ := mem_image.mp hpP
        refine mem_image.mpr ⟨g, mem_filter.mpr ⟨hg, ?_⟩, ?_⟩
        · intro y hy
          have hviews : view K g = view K f := by
            have heq := congrArg Prod.fst hgp
            exact heq.trans (hpa.trans hfa.symm)
          exact (view_eq_iff K g f).mp hviews y (hready hy)
        · exact congrArg Prod.snd hgp
      · intro p hp q hq hpq
        apply Prod.ext _ hpq
        exact (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm)
    simpa only [hfst, observations] using hp
  let extend : ((V → Option α) × α) → V → Option α :=
    fun p v => if v = x then some p.2 else p.1 v
  have hext : P.image extend = C.image (view (insert x K)) := by
    rw [show P = C.image (fun f => (view K f, f x)) from rfl, image_image]
    congr 1
    funext f v
    by_cases hv : v = x <;> simp [extend, view, hv]
  calc observations C (insert x K) = (P.image extend).card := by rw [hext]; rfl
    _ ≤ P.card := card_image_le
    _ ≤ _ := hcount

theorem Schedule.cardinality_directions {M : Matrix V V F} {W K : Finset V}
    {l : List (V × V)} (hl : Schedule M W K l) (C : Finset (V → α))
    (L : V → V → ℕ)
    (hL : ∀ v ∈ W, ∀ x ∈ insert v (recSet M v) ∩ W, ∀ f ∈ C,
      choices C (insert v (recSet M v) ∩ W) x f ≤ L v x) :
    observations C W ≤ observations C K * (l.map (fun e => L e.1 e.2)).prod := by
  induction hl with
  | nil hWK => simpa using observations_mono C hWK
  | @cons K v x l hv hx _ hready _ ih =>
    have hstep := observations_step C hready (hL v hv x hx)
    have hmul := Nat.mul_le_mul_right ((l.map (fun e => L e.1 e.2)).prod) hstep
    simp only [List.map_cons, List.prod_cons]
    nlinarith

/-- The finite decoder can use every center only once. Its exact product
charges the inverse fibre in the direction actually used. -/
theorem paid_cardinality_schedule {M : Matrix V V F} {G : SimpleGraph V}
    (htri : RecTriangleFree M) (hstar : ∀ v, Star M v)
    (hpat : ∀ v u, u ∈ recSet M v → G.Adj v u) :
    ∃ (B : Finset V) (l : List (V × V)), B.card ≤ G.matchingNumber ∧
      (l.map Prod.fst).Nodup ∧ ∀ (C : Finset (V → α)) (L : V → V → ℕ),
      (∀ v x, x ∈ insert v (recSet M v) → ∀ f ∈ C,
        choices C (insert v (recSet M v)) x f ≤ L v x) →
      C.card ≤ observations C B * (l.map (fun e => L e.1 e.2)).prod := by
  obtain ⟨B, l, hB, hl, hn⟩ := exists_matching_schedule htri hstar hpat
  refine ⟨B, l, hB, hn, ?_⟩
  intro C L hL
  simpa only [observations_univ] using hl.cardinality_directions C L (by
    simpa only [inter_univ, mem_univ, true_implies] using hL)

theorem observations_capacity [Fintype α] (C : Finset (V → α)) (B : Finset V) :
    observations C B ≤ Fintype.card α ^ B.card := by
  classical
  let extend : (B → α) → V → Option α :=
    fun f v => if h : v ∈ B then some (f ⟨v, h⟩) else none
  let P := C.image (fun f => fun v : B => f v)
  have heq : P.image extend = C.image (view B) := by
    rw [show P = C.image (fun f => fun v : B => f v) from rfl, image_image]
    congr 1
  calc observations C B = (P.image extend).card := by rw [heq]; rfl
    _ ≤ P.card := card_image_le
    _ ≤ Fintype.card (B → α) := card_le_univ _
    _ = _ := by simp

/-- A row-wise inverse-fibre budget is charged once, for every finite alphabet. -/
theorem paid_cardinality_matching [Fintype α] [Nonempty α]
    {M : Matrix V V F} {G : SimpleGraph V}
    (htri : RecTriangleFree M) (hstar : ∀ v, Star M v)
    (hpat : ∀ v u, u ∈ recSet M v → G.Adj v u)
    (C : Finset (V → α)) (L : V → ℕ) (hL1 : ∀ v, 1 ≤ L v)
    (hL : ∀ v x, x ∈ insert v (recSet M v) → ∀ f ∈ C,
      choices C (insert v (recSet M v)) x f ≤ L v) :
    C.card ≤ Fintype.card α ^ G.matchingNumber * ∏ v, L v := by
  obtain ⟨B, l, hB, hn, hbound⟩ := paid_cardinality_schedule (α := α) htri hstar hpat
  have hc := hbound C (fun v _ => L v) hL
  have hcap := observations_capacity C B
  have hp : (l.map (fun e => L e.1)).prod ≤ ∏ v, L v := by
    calc (l.map (fun e => L e.1)).prod = ((l.map Prod.fst).map L).prod := by
          simp [List.map_map, Function.comp_def]
      _ = ∏ v ∈ (l.map Prod.fst).toFinset, L v := (List.prod_toFinset L hn).symm
      _ ≤ ∏ v, L v := prod_le_prod_of_subset_of_one_le (subset_univ _) (fun v _ _ => hL1 v)
  have hpow : Fintype.card α ^ B.card ≤ Fintype.card α ^ G.matchingNumber :=
    Nat.pow_le_pow_right (Fintype.card_pos_iff.mpr inferInstance) hB
  exact hc.trans (Nat.mul_le_mul (hcap.trans hpow) hp)

end SubcubicMemo
