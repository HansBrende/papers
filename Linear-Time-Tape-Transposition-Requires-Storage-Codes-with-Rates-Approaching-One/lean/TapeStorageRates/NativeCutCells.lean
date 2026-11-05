import TapeStorageRates.NativeCut

/-! # Every cell of a native trace partition retains its actual code and provenance -/

namespace TapeStorageRates.NativeTypicalCut

open Finset Transpose MergeDepth DirectedRecovery MotionDepthCodes

set_option autoImplicit false
noncomputable section

variable {M : TM} {d b θ r : ℕ} {c ε : ℝ} {S : Finset (Fin (d*d*b) → Bool)}
variable (F : NativeTypicalCut M d b c ε θ r S)

open Classical in
/-- Distinct genie words actually attained on this trace, including correlations between
the values at its revealed steps. -/
def revealed := S.image fun x => fun t : F.genie => blockVal M 1 (List.ofFn x) t

/-- Genie values and the two discarded words for a single geometric choice. -/
abbrev Tag := (F.genie → BlockVal M 1) × ({i // i ∉ F.Q} → Bool) × ({i // i ∉ F.U} → Bool)

/-- The full observed word on a single trace: revealed native values and the two discarded
sets of physical input bits. Exterior words can have different types on different traces. -/
def tag (x : Fin (d*d*b) → Bool) : F.Tag :=
  ((fun t : F.genie => blockVal M 1 (List.ofFn x) t),
    outsideWord F.Q x, outsideWord F.U (restrictWord F.Q x))

/-- The code of the cell containing a given word. Keeping both restrictions explicit names
every surviving coordinate by its original bit address. -/
def code (x : Fin (d*d*b) → Bool) : Finset (F.U → Bool) := by
  classical
  exact ((S.filter fun y => F.tag y = F.tag x).image
    fun y => restrictWord F.U (restrictWord F.Q y))

theorem projected_mem {x} (hx : x∈S) : restrictWord F.U (restrictWord F.Q x) ∈ F.code x := by
  classical
  exact mem_image_of_mem _ (mem_filter.mpr ⟨hx,rfl⟩)

open Classical in
theorem code_card (x : Fin (d*d*b) → Bool) :
    (F.code x).card = (S.filter fun y => F.tag y = F.tag x).card := by
  classical
  apply card_image_of_injOn
  intro u hu v hv huv
  have ht := (mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm
  have h₁ := congrArg (fun z => z.2.1) ht
  have h₂ := congrArg (fun z => z.2.2) ht
  funext i
  by_cases hi : i ∈ F.Q
  · by_cases hj : (⟨i,hi⟩ : F.Q) ∈ F.U
    · exact congrFun huv ⟨⟨i,hi⟩,hj⟩
    · exact congrFun h₂ ⟨⟨i,hi⟩,hj⟩
  · exact congrFun h₁ ⟨i,hi⟩

/-- All words in the code extend to members of the original success set on the selected
trace, genie and exterior values. -/
theorem mem_code_iff {x : Fin (d*d*b) → Bool} {a : F.U → Bool} :
    a ∈ F.code x ↔ ∃ y ∈ S, F.tag y = F.tag x ∧
      restrictWord F.U (restrictWord F.Q y) = a := by
  classical
  simp [code, and_assoc]

/-- The induced native relation recovers on the whole cell, including on partial
correctness sets. -/
theorem storage (x : Fin (d*d*b) → Bool) :
    IsStorageCode (inducedNeighborhood (inducedNeighborhood
      (coneRel 1 (runWalks M (List.ofFn F.representative)) F.time F.genie F.outputTime
        (fun q : Fin (d*d*b) => tpos d b q)) F.Q) F.U) (F.code x) := by
  intro a ha b' hb q hq
  obtain ⟨u,hu,ht,rfl⟩ := F.mem_code_iff.mp ha
  obtain ⟨v,hv,ht',rfl⟩ := F.mem_code_iff.mp hb
  have hh := ht.trans ht'.symm
  apply F.decode u hu v hv (fun t ht => congrFun (congrArg Prod.fst hh) ⟨t,ht⟩) q.val.val
  intro i hi
  by_cases hQ : i ∈ F.Q
  · by_cases hU : (⟨i,hQ⟩ : F.Q) ∈ F.U
    · exact hq ⟨⟨i,hQ⟩,hU⟩ (mem_subtype.mpr (mem_subtype.mpr hi))
    · exact congrFun (congrArg (fun z => z.2.2) hh) ⟨⟨i,hQ⟩,hU⟩
  · exact congrFun (congrArg (fun z => z.2.1) hh) ⟨i,hQ⟩

open Classical in
theorem tag_count :
    (S.image F.tag).card ≤ F.revealed.card * 2 ^ (d*d*b - F.U.card) := by
  have hsub : S.image F.tag ⊆ F.revealed ×ˢ univ := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact mem_product.mpr ⟨mem_image_of_mem _ hx, mem_univ _⟩
  have hU : F.U.card ≤ F.Q.card := by simpa using F.U.card_le_univ
  have hQ : F.Q.card ≤ d*d*b := by simpa using F.Q.card_le_univ
  calc
    _ ≤ (F.revealed ×ˢ (univ : Finset
        (({i // i ∉ F.Q} → Bool) × ({i // i ∉ F.U} → Bool)))).card := card_le_card hsub
    _ = _ := by
      simp only [card_product, card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, ← pow_add]
      congr 2
      omega

theorem revealed_le : (F.revealed.card : ℝ) ≤ (2:ℝ) ^ (ε*(d*d*b : ℕ)) := by
  have h := card_revealed_le (M := M) (by decide : 0<1) F.genie S
  calc
    _ ≤ ((2 ^ (blockWidth M 1 * F.genie.card) : ℕ) : ℝ) := Nat.cast_le.mpr h
    _ ≤ _ := by
      simp only [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simpa only [Nat.cast_mul] using F.cost)

open Classical in
/-- Exact exponential moment of the projected deficit on this trace. All inputs in a
complete record cell have the same code. Its reciprocal cardinality sums to one over the cell. -/
theorem deficit_moment (bill : F.Tag → ℝ) :
    ∑ x ∈ S, (2:ℝ)^(((F.U.card:ℝ) - Real.logb 2 (F.code x).card) - bill (F.tag x)) =
      ∑ z ∈ S.image F.tag, (2:ℝ)^((F.U.card:ℝ)-bill z) := by
  let weight z := (2:ℝ)^((F.U.card:ℝ)-bill z) / (S.filter fun x => F.tag x=z).card
  calc
    _ = ∑ x ∈ S, weight (F.tag x) := by
      apply sum_congr rfl
      intro x hx
      have hpos : 0 < ((F.code x).card : ℝ) := by
        exact_mod_cast (show (F.code x).Nonempty from ⟨_,F.projected_mem hx⟩).card_pos
      rw [sub_right_comm, Real.rpow_sub (by norm_num : (0:ℝ)<2),
        Real.rpow_logb (by norm_num) (by norm_num) hpos, F.code_card]
    _ = ∑ z ∈ S.image F.tag, ∑ x ∈ S with F.tag x=z, weight z :=
      (sum_fiberwise_of_maps_to' (fun x hx => mem_image_of_mem F.tag hx) _).symm
    _ = _ := by
      apply sum_congr rfl
      intro z hz
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      have hpos : 0 < ((S.filter fun y => F.tag y=F.tag x).card : ℝ) := by
        exact_mod_cast (show (S.filter fun y => F.tag y=F.tag x).Nonempty from
          ⟨x,mem_filter.mpr ⟨hx,rfl⟩⟩).card_pos
      simp only [sum_const,nsmul_eq_mul,weight]
      field_simp

open Classical in
/-- Bounding the support of the two discarded bit strings by their full alphabet recovers
the usual charge for the revealed words. The moment identity retains the attained support. -/
theorem tag_weight_le (bill : ℝ) :
    ((S.image F.tag).card : ℝ) * (2:ℝ)^((F.U.card:ℝ)-bill) ≤
      (F.revealed.card : ℝ) * (2:ℝ)^((d*d*b : ℕ)-bill) := by
  have hsize : F.U.card ≤ d*d*b := by
    have h₁ := F.U.card_le_univ
    have h₂ := F.Q.card_le_univ
    simp only [Fintype.card_coe, Fintype.card_fin] at *
    omega
  calc
    _ ≤ ((F.revealed.card * 2 ^ (d*d*b - F.U.card) : ℕ) : ℝ) * (2:ℝ)^((F.U.card:ℝ)-bill) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr F.tag_count) (by positivity)
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc,
        ← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 2
      rw [Nat.cast_sub (show F.U.card ≤ d*(d*b) by simpa only [Nat.mul_assoc] using hsize)]
      push_cast
      ring

end
end TapeStorageRates.NativeTypicalCut
