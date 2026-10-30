import MergeDepth.FieldPruning
import MergeDepth.HopFields
import MergeDepth.MergeFields
import MergeDepth.HCStar
import MergeDepth.Formation

set_option autoImplicit false

/-!
# Hop charging for the field DAG of a pruning of an oblivious transposer

The results of Section 3 for function DAGs that refine the dependency DAG (`hop_charging_fields`,
`FunDag.cone`, `FunDag.isIndexCode`, `merge_reduction_fields`, `cor_HCstar_step`), applied to the
field DAG `Pr.toFunDag` of a pruning `Pr` of an oblivious transposer in the frozen model
(`ObliviousTransposer`), with the refinement hypotheses discharged by
`MergeDepth/FieldPruning.lean`: width `k + 2`, edges along dependency steps of the work walks,
input marks at the positions read, steps and fields of at most `2^β` values for `β ≥ β(M)`, and
the output decoding. The cold genie, the lineage assignment with its side condition, the
merge-depth bound and the hypothesis of Lemma 3.14(b) remain hypotheses, as in those theorems.

* `Pruning.field_cone`, `Pruning.field_isIndexCode`: Lemma 3.3(b) for the field DAG of a pruning:
  the cone lemma, and the index code of the whole steps of `Γ`, the fields of `Q` and the bits at
  `X`, with at most `β |Γ| + β |Q| + |X|` bits.
* `hop_charging_pruning`, `hop_charging_pruning_bits`: Theorem HC′(b), with the bit count
  `ε L + β (k + 2) k C (L + 1) / τ + |X|` in the second.
* `hop_charging_pruning_HC`: Theorem HC for field DAGs (formation depth, the lineage assignment of
  the copies), the variant mentioned after Remark 3.6.
* `short_paths_pruning`: the path bound of Theorem HC′ (Lemma 3.9) for field DAGs.
* `merge_reduction_pruning`: Proposition 3.20(b).
* `cor_HCstar_pruning`: Corollary HC* at one size; `cor_HCstar_frozen`: the same for a machine
  oblivious at length `L` in the frozen model (`ObliviousOn`), with `T ≤ C (L + 1)` derived from
  `TransposesAtWidth` (`haltTime_le_of_obliviousOn`); `cor_HCstar_pruning_empty`: the last sentence
  of Corollary HC* at one size (empty genie, cold genie at `(V, 1/4)` built by `cold_genie_exists`).

**A sharper charge.** The checkpoints of Lemma 3.9 can be taken among the heads of deep lineage
edges (`hop_charging_fields_heads`, `cor_HCstar_heads`, for any refinement). In a field DAG these
are symbol fields when the lineage edges are edges of the DAG, so a checkpoint costs
`⌈log₂ (g + 1)⌉` bits instead of `β` (`hop_charging_pruning_sym`, `cor_HCstar_pruning_sym`).
-/

namespace MergeDepth

open Finset Transpose Transpose.Tape BoundedNesting

/-! ### Counting code words -/

/-- A code word made of `|ι₁|` values of at most `2^β₁` values each, `|ι₂|` values of at most
`2^β₂` values each and `|ι₃|` bits takes at most `2^{β₁ |ι₁| + β₂ |ι₂| + |ι₃|}` values. -/
theorem card_image_triple_le {L β₁ β₂ : ℕ} {ι₁ ι₂ ι₃ : Type*} {α₁ : ι₁ → Type*}
    {α₂ : ι₂ → Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] [DecidableEq ι₁] [DecidableEq ι₂]
    [DecidableEq ι₃] [∀ i, DecidableEq (α₁ i)] [∀ i, DecidableEq (α₂ i)]
    (f₁ : (Fin L → Bool) → (i : ι₁) → α₁ i) (f₂ : (Fin L → Bool) → (i : ι₂) → α₂ i)
    (f₃ : (Fin L → Bool) → ι₃ → Bool) (h₁ : ∀ i, (univ.image fun w => f₁ w i).card ≤ 2 ^ β₁)
    (h₂ : ∀ i, (univ.image fun w => f₂ w i).card ≤ 2 ^ β₂) :
    (univ.image fun w => (f₁ w, f₂ w, f₃ w)).card ≤
      2 ^ (β₁ * Fintype.card ι₁ + β₂ * Fintype.card ι₂ + Fintype.card ι₃) := by
  calc (univ.image fun w => (f₁ w, f₂ w, f₃ w)).card
      ≤ ((Fintype.piFinset fun i => univ.image fun w => f₁ w i) ×ˢ
          ((Fintype.piFinset fun i => univ.image fun w => f₂ w i) ×ˢ
            (univ : Finset (ι₃ → Bool)))).card := by
        refine card_le_card fun e he => ?_
        obtain ⟨w, -, rfl⟩ := mem_image.mp he
        exact mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun i => mem_image.mpr ⟨w, mem_univ _, rfl⟩,
          mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun i => mem_image.mpr ⟨w, mem_univ _, rfl⟩,
            mem_univ _⟩⟩
    _ = (∏ i, (univ.image fun w => f₁ w i).card) *
          ((∏ i, (univ.image fun w => f₂ w i).card) * 2 ^ Fintype.card ι₃) := by
        rw [card_product, card_product, Fintype.card_piFinset, Fintype.card_piFinset, card_univ,
          Fintype.card_fun, Fintype.card_bool]
    _ ≤ (∏ _i : ι₁, 2 ^ β₁) * ((∏ _i : ι₂, 2 ^ β₂) * 2 ^ Fintype.card ι₃) := by
        gcongr with i _ i _
        · exact h₁ i
        · exact h₂ i
    _ = 2 ^ (β₁ * Fintype.card ι₁ + β₂ * Fintype.card ι₂ + Fintype.card ι₃) := by
        rw [prod_const, prod_const, card_univ, card_univ, ← pow_mul, ← pow_mul, ← pow_add,
          ← pow_add, add_assoc]

variable {M : TM}

/-- Step values take at most `2^β` values for `β ≥ β(M)`. -/
theorem card_image_stepValue_le {L β : ℕ} (hβ : valueWidth M ≤ β) (t : ℕ) :
    (univ.image fun w : Fin L → Bool => stepValue M (List.ofFn w) t).card ≤ 2 ^ β :=
  (card_le_univ _).trans ((card_value_le M).trans (Nat.pow_le_pow_right (by norm_num) hβ))

/-- Fields take at most `2^β` values for `β ≥ β(M)`. -/
theorem card_image_fieldVal_le {L β : ℕ} (hβ : valueWidth M ≤ β) (u : ℕ) :
    (univ.image fun w : Fin L → Bool => fieldVal M (List.ofFn w) u).card ≤ 2 ^ β := by
  classical
  calc (univ.image fun w : Fin L → Bool => fieldVal M (List.ofFn w) u).card
      ≤ ((univ : Finset (Value M)).image (fieldOf M (u % (M.k + 2)))).card := by
        refine card_le_card fun e he => ?_
        obtain ⟨w, -, rfl⟩ := mem_image.mp he
        exact mem_image.mpr ⟨stepValue M (List.ofFn w) (u / (M.k + 2)), mem_univ _, rfl⟩
    _ ≤ Fintype.card (Value M) := card_image_le.trans (by rw [card_univ])
    _ ≤ 2 ^ β := (card_value_le M).trans (Nat.pow_le_pow_right (by norm_num) hβ)

namespace Pruning

variable {L : ℕ} {τ₀ : Trace M.k} {T : ℕ}

theorem toFunDag_val_congr (Pr : Pruning M L τ₀ T) {w w' : Fin L → Bool} {v : ℕ}
    (h : v / (M.k + 2) < T → fieldVal M (List.ofFn w) v = fieldVal M (List.ofFn w') v) :
    Pr.toFunDag.val w v = Pr.toFunDag.val w' v := by
  by_cases hv : v / (M.k + 2) < T
  · rw [Pr.toFunDag_val_of_lt w hv, Pr.toFunDag_val_of_lt w' hv]
    exact h hv
  · rw [Pr.toFunDag_val_of_le w (not_lt.mp hv), Pr.toFunDag_val_of_le w' (not_lt.mp hv)]

/-! ### Lemma 3.3(b) for the field DAG of a pruning -/

open Classical in
/-- **Lemma 3.3(b), the cone lemma for the field DAG of a pruning.** Let `R` be a set of revealed
field nodes (for the paper's `(Γ, Q)`, `R = Γ.biUnion (fieldNodesAt k) ∪ Q`). If two inputs agree
on the revealed fields and on the positions read at the ends of the `R`-free paths from a field `u`
of a step `t < T`, the field `u` takes the same value on them. -/
theorem field_cone (Pr : Pruning M L τ₀ T) (R : Finset ℕ) {w w' : Fin L → Bool}
    (hR : ∀ v ∈ R, v / (M.k + 2) < T → fieldVal M (List.ofFn w) v = fieldVal M (List.ofFn w') v)
    {u : ℕ} (hu : u / (M.k + 2) < T) (hI : ∀ j ∈ Pr.toFunDag.coneSet R u, w j = w' j) :
    fieldVal M (List.ofFn w) u = fieldVal M (List.ofFn w') u := by
  have := Pr.toFunDag.cone R w w' (fun v hv => Pr.toFunDag_val_congr (hR v hv)) u hI
  rwa [Pr.toFunDag_val_of_lt w hu, Pr.toFunDag_val_of_lt w' hu] at this

variable {d b : ℕ}

open Classical in
/-- **Lemma 3.3(b), the index code, for the field DAG of a pruning of an oblivious transposer.**
Let `Γ` be a set of steps, `Q` a set of field nodes and `X` a set of output positions, and let the
revealed nodes be the fields of the steps of `Γ` and the nodes of `Q`. The values of the steps of
`Γ`, the fields of `Q` and the bits at the positions `tpos ℓ`, `ℓ ∈ X`, form an index code with at
most `β |Γ| + β |Q| + |X|` bits for the system that is empty at `ℓ ∈ X` and at revealed output
nodes, and is the cone set `I_{Γ,Q}(o_{t_ℓ})` of the output node of `ℓ` otherwise. -/
theorem field_isIndexCode (hM : ObliviousTransposer M d b τ₀ T)
    (Pr : Pruning M (d * d * b) τ₀ T) {β : ℕ} (hβ : valueWidth M ≤ β) (Γ Q : Finset ℕ)
    (X : Finset (Fin (d * d * b))) :
    IsIndexCode (fun w => ((fun t : Γ => stepValue M (List.ofFn w) t.1),
        (fun q : Q => fieldVal M (List.ofFn w) q.1), (fun ℓ : X => w (tposOf d b ℓ.1))))
      (fun ℓ => if ℓ ∈ X ∨ outputNodeOf τ₀ T ℓ ∈ Γ.biUnion (fieldNodesAt M.k) ∪ Q then ∅
        else Pr.toFunDag.coneSet (Γ.biUnion (fieldNodesAt M.k) ∪ Q) (outputNodeOf τ₀ T ℓ))
      (tposOf d b) ∧
    (univ.image fun w => ((fun t : Γ => stepValue M (List.ofFn w) t.1),
        (fun q : Q => fieldVal M (List.ofFn w) q.1), (fun ℓ : X => w (tposOf d b ℓ.1)))).card ≤
      2 ^ (β * Γ.card + β * Q.card + X.card) := by
  refine ⟨Pr.toFunDag.isIndexCode_of _ _ X (fun ℓ => outputNodeOf τ₀ T ℓ) (tposOf d b)
    (fun _ => decOut) (fun w ℓ => Pr.toFunDag_dec hM w ℓ) fun w w' hE => ?_, ?_⟩
  · simp only [Prod.mk.injEq] at hE
    obtain ⟨h1, h2, h3⟩ := hE
    refine ⟨fun v hv => Pr.toFunDag_val_congr fun _ => ?_, fun ℓ hℓ => congr_fun h3 ⟨ℓ, hℓ⟩⟩
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨t, ht, hvt⟩ := mem_biUnion.mp hv
      have e := mem_fieldNodesAt.mp hvt
      refine fieldVal_eq_of_stepValue M ?_
      rw [e]
      exact congr_fun h1 ⟨t, ht⟩
    · exact congr_fun h2 ⟨v, hv⟩
  · have h := card_image_triple_le (fun w (t : Γ) => stepValue M (List.ofFn w) t.1)
      (fun w (q : Q) => fieldVal M (List.ofFn w) q.1) (fun w (ℓ : X) => w (tposOf d b ℓ.1))
      (fun t => card_image_stepValue_le hβ t.1) (fun q => card_image_fieldVal_le hβ q.1)
    simp only [Fintype.card_coe] at h
    convert h

end Pruning

/-! ### Theorem HC′(b) -/

variable {d b : ℕ} {τ₀ : Trace M.k} {T : ℕ}

open Classical in
/-- **Theorem HC′(b) for the field DAG of a pruning of an oblivious transposer.** Let `ΓF` be a cold
genie at `(V, ε)` with depth `D` for the work walks of `τ₀`, fix a lineage assignment `lin` on the
field DAG whose other out-edges are dead (`hside`), and let the `ΓF`-free paths from the output node
of every position outside `X` have at most `s` deep merges. Then revealing the fields of the steps
of `ΓF`, the fields of a set `Q` with `τ |Q| ≤ (k + 2) N_R`, and the bits of the positions in `X` is
an index code with at most `2^{β |ΓF| + β |Q| + |X|}` code words, for a system contained in the
balls of radius `(s + 1) τ D` around the output steps. -/
theorem hop_charging_pruning (hM : ObliviousTransposer M d b τ₀ T)
    (Pr : Pruning M (d * d * b) τ₀ T) {V β : ℕ} (hβ : valueWidth M ≤ β) {ε : ℝ} {D : ℕ}
    {ΓF : Finset ℕ} (hcold : IsColdGenie (L := d * d * b) τ₀.work T V β ε D ΓF) (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ Pr.toFunDag.net.paths u →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) (u :: v' :: π) →
      rCount (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) (s : ℕ) (X : Finset (Fin (d * d * b)))
    (hround : ∀ ℓ ∉ X, ∀ π, π ∈ Pr.toFunDag.net.paths (outputNodeOf τ₀ T ℓ) →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) π →
      dm lin (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) false π ≤ s) :
    ∃ (Q : Finset ℕ) (I : Fin (d * d * b) → Finset (Fin (d * d * b))),
      τ * Q.card ≤ (M.k + 2) * (deepHops τ₀.work T V).card ∧
      IsIndexCode (fun w => ((fun t : ΓF => fun v : fieldNodesAt M.k t.1 => Pr.toFunDag.val w v),
        (fun q : Q => Pr.toFunDag.val w q.1), (fun ℓ : X => w (tposOf d b ℓ.1)))) I
        (tposOf d b) ∧
      (∀ ℓ, I ℓ ⊆ stepBall τ₀.work T (readPos τ₀ (d * d * b)) ((s + 1) * τ * D)
        (appendTime τ₀ T ℓ)) ∧
      (univ.image fun w => ((fun t : ΓF => fun v : fieldNodesAt M.k t.1 => Pr.toFunDag.val w v),
        (fun q : Q => Pr.toFunDag.val w q.1), (fun ℓ : X => w (tposOf d b ℓ.1)))).card ≤
        2 ^ (β * ΓF.card + β * Q.card + X.card) :=
  hop_charging_fields Pr.toFunDag (fun u => u / (M.k + 2)) (fieldNodesAt M.k)
    (fun _ _ => mem_fieldNodesAt) (fun t => (card_fieldNodesAt M.k t).le) τ₀.work
    Pr.toFunDag_edge (readPos τ₀ (d * d * b)) Pr.toFunDag_rd hcold
    (fun t _ => Pr.toFunDag_step_card hβ t) (Pr.toFunDag_field_card hβ) lin hside hτ s
    (fun ℓ => outputNodeOf τ₀ T ℓ) (fun ℓ => appendTime τ₀ T ℓ) (fun ℓ => outputNodeOf_div τ₀ T ℓ)
    (tposOf d b) (fun _ => decOut) (fun w ℓ => Pr.toFunDag_dec hM w ℓ) X hround

/-- The checkpoints of Theorem HC′ cost at most `β (k + 2) k C (L + 1) / τ` bits. -/
theorem beta_mul_card_le {β C V τ : ℕ} {Q : Finset ℕ} (hτ : 1 ≤ τ) {L : ℕ}
    (hT : T ≤ C * (L + 1)) (hQ : τ * Q.card ≤ (M.k + 2) * (deepHops τ₀.work T V).card) :
    (β * Q.card : ℝ) ≤ β * (M.k + 2) * M.k * C * (L + 1) / τ := by
  have h1 : τ * Q.card ≤ (M.k + 2) * (M.k * (C * (L + 1))) :=
    hQ.trans (Nat.mul_le_mul_left _ ((card_deepHops_le τ₀.work T V).trans
      (Nat.mul_le_mul_left _ hT)))
  have h2 : (τ * Q.card : ℝ) ≤ (M.k + 2) * (M.k * (C * (L + 1))) := by exact_mod_cast h1
  have hτ' : (0 : ℝ) < τ := by exact_mod_cast hτ
  rw [le_div_iff₀ hτ']
  have hβ0 : (0 : ℝ) ≤ β := by positivity
  nlinarith

open Classical in
/-- **Theorem HC′(b), with the bit count of the paper.** Under the hypotheses of
`hop_charging_pruning` and `T ≤ C (L + 1)`, the index code has at most
`β |ΓF| + β |Q| + |X| ≤ ε L + β (k + 2) k C (L + 1) / τ + |X|` bits. -/
theorem hop_charging_pruning_bits (hM : ObliviousTransposer M d b τ₀ T)
    (Pr : Pruning M (d * d * b) τ₀ T) {V β C : ℕ} (hβ : valueWidth M ≤ β)
    (hT : T ≤ C * (d * d * b + 1)) {ε : ℝ} {D : ℕ} {ΓF : Finset ℕ}
    (hcold : IsColdGenie (L := d * d * b) τ₀.work T V β ε D ΓF) (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ Pr.toFunDag.net.paths u →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) (u :: v' :: π) →
      rCount (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) (s : ℕ) (X : Finset (Fin (d * d * b)))
    (hround : ∀ ℓ ∉ X, ∀ π, π ∈ Pr.toFunDag.net.paths (outputNodeOf τ₀ T ℓ) →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) π →
      dm lin (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) false π ≤ s) :
    ∃ (Q : Finset ℕ) (I : Fin (d * d * b) → Finset (Fin (d * d * b))),
      IsIndexCode (fun w => ((fun t : ΓF => fun v : fieldNodesAt M.k t.1 => Pr.toFunDag.val w v),
        (fun q : Q => Pr.toFunDag.val w q.1), (fun ℓ : X => w (tposOf d b ℓ.1)))) I
        (tposOf d b) ∧
      (∀ ℓ, I ℓ ⊆ stepBall τ₀.work T (readPos τ₀ (d * d * b)) ((s + 1) * τ * D)
        (appendTime τ₀ T ℓ)) ∧
      (univ.image fun w => ((fun t : ΓF => fun v : fieldNodesAt M.k t.1 => Pr.toFunDag.val w v),
        (fun q : Q => Pr.toFunDag.val w q.1), (fun ℓ : X => w (tposOf d b ℓ.1)))).card ≤
        2 ^ (β * ΓF.card + β * Q.card + X.card) ∧
      ((β * ΓF.card + β * Q.card + X.card : ℕ) : ℝ) ≤
        ε * (d * d * b : ℕ) + β * (M.k + 2) * M.k * C * ((d * d * b : ℕ) + 1) / τ + X.card := by
  obtain ⟨Q, I, hQ, hcode, hball, himg⟩ :=
    hop_charging_pruning hM Pr hβ hcold lin hside hτ s X hround
  refine ⟨Q, I, hcode, hball, himg, ?_⟩
  have h1 := beta_mul_card_le (β := β) hτ hT hQ
  have h2 := hcold.1
  push_cast at h1 h2 ⊢
  linarith

open Classical in
/-- **Theorem HC for field DAGs** (formation depth; the direct proof after Remark 3.6 applies to
field DAGs). The conclusion of `hop_charging_pruning` holds when the `ΓF`-free paths from the output
node of every position outside `X` contain at most `s` deep formations: take the lineage
assignment of the copies (Lemma 3.11). -/
theorem hop_charging_pruning_HC (hM : ObliviousTransposer M d b τ₀ T)
    (Pr : Pruning M (d * d * b) τ₀ T) {V β : ℕ} (hβ : valueWidth M ≤ β) {ε : ℝ} {D : ℕ}
    {ΓF : Finset ℕ} (hcold : IsColdGenie (L := d * d * b) τ₀.work T V β ε D ΓF)
    {τ : ℕ} (hτ : 1 ≤ τ) (s : ℕ) (X : Finset (Fin (d * d * b)))
    (hround : ∀ ℓ ∉ X, ∀ π, π ∈ Pr.toFunDag.net.paths (outputNodeOf τ₀ T ℓ) →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) π →
      π.countP (DeepFormation Pr.toFunDag.net
        fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) ≤ s) :
    ∃ (Q : Finset ℕ) (I : Fin (d * d * b) → Finset (Fin (d * d * b))),
      τ * Q.card ≤ (M.k + 2) * (deepHops τ₀.work T V).card ∧
      IsIndexCode (fun w => ((fun t : ΓF => fun v : fieldNodesAt M.k t.1 => Pr.toFunDag.val w v),
        (fun q : Q => Pr.toFunDag.val w q.1), (fun ℓ : X => w (tposOf d b ℓ.1)))) I
        (tposOf d b) ∧
      (∀ ℓ, I ℓ ⊆ stepBall τ₀.work T (readPos τ₀ (d * d * b)) ((s + 1) * τ * D)
        (appendTime τ₀ T ℓ)) ∧
      (univ.image fun w => ((fun t : ΓF => fun v : fieldNodesAt M.k t.1 => Pr.toFunDag.val w v),
        (fun q : Q => Pr.toFunDag.val w q.1), (fun ℓ : X => w (tposOf d b ℓ.1)))).card ≤
        2 ^ (β * ΓF.card + β * Q.card + X.card) := by
  set cn := Pr.toFunDag.net
  have hlin : ∀ u v, (copyForest cn).nxt u = some v → v ∈ cn.out u := fun u v h => by
    rw [(isCopy_of_copyForest h).2]
    exact mem_singleton_self v
  have hcopy : ∀ u, IsCopy cn u → (copyForest cn).nxt u ≠ none := fun u hc => by
    obtain ⟨w, hw⟩ := card_eq_one.mp hc.1
    rw [copyForest_nxt_of_copy hc (show w ∈ cn.out u by rw [hw]; exact mem_singleton_self w)]
    simp
  refine hop_charging_pruning hM Pr hβ hcold (copyForest cn) ?_ hτ s X ?_
  · intro u v v' π hn hne hπ _
    exfalso
    obtain ⟨hv', -⟩ := cons_cons_mem_paths.mp hπ
    rw [(isCopy_of_copyForest hn).2, mem_singleton] at hv'
    exact hne hv'
  · intro ℓ hℓ π hπ hfree
    exact (dm_le_countP_deepFormation cn _ (copyForest cn) hlin hcopy hπ).trans
      (hround ℓ hℓ π hπ hfree)

/-! ### Proposition 3.20(b) -/

open Classical in
/-- **Proposition 3.20(b) for the field DAG of a pruning of an oblivious transposer.** There is a
set `Q` with `τ |Q| ≤ (k + 2) N_R` such that, for every set `Z` of field nodes meeting every path of
the merge DAG with `s + 1` vertices whose first vertex is initial, revealing the fields of the steps
of `ΓF` and the fields of `Q` and of `Z` is an index code with at most
`2^{β |ΓF| + β |Q| + β |Z|}` code words for a system inside the balls of radius `(s + 1) τ D`. -/
theorem merge_reduction_pruning (hM : ObliviousTransposer M d b τ₀ T)
    (Pr : Pruning M (d * d * b) τ₀ T) {V β : ℕ} (hβ : valueWidth M ≤ β) {ε : ℝ} {D : ℕ}
    {ΓF : Finset ℕ} (hcold : IsColdGenie (L := d * d * b) τ₀.work T V β ε D ΓF) (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ Pr.toFunDag.net.paths u →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) (u :: v' :: π) →
      rCount (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) :
    ∃ Q : Finset ℕ, τ * Q.card ≤ (M.k + 2) * (deepHops τ₀.work T V).card ∧
      ∀ (Z : Finset ℕ) (s : ℕ),
        MCut Pr.toFunDag.net (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) lin
          (ΓF.biUnion (fieldNodesAt M.k) ∪ Q)
          ((univ.image fun ℓ : Fin (d * d * b) => outputNodeOf τ₀ T ℓ).filter
            (· ∉ ΓF.biUnion (fieldNodesAt M.k) ∪ Q)) Z s →
        ∃ I : Fin (d * d * b) → Finset (Fin (d * d * b)),
          IsIndexCode (fun w => ((fun t : ΓF => fun v : fieldNodesAt M.k t.1 =>
              Pr.toFunDag.val w v),
            (fun q : Q => Pr.toFunDag.val w q.1), (fun z : Z => Pr.toFunDag.val w z.1))) I
            (tposOf d b) ∧
          (∀ ℓ, I ℓ ⊆ stepBall τ₀.work T (readPos τ₀ (d * d * b)) ((s + 1) * τ * D)
            (appendTime τ₀ T ℓ)) ∧
          (univ.image fun w => ((fun t : ΓF => fun v : fieldNodesAt M.k t.1 =>
              Pr.toFunDag.val w v),
            (fun q : Q => Pr.toFunDag.val w q.1), (fun z : Z => Pr.toFunDag.val w z.1))).card ≤
            2 ^ (β * ΓF.card + β * Q.card + β * Z.card) :=
  merge_reduction_fields Pr.toFunDag (fun u => u / (M.k + 2)) (fieldNodesAt M.k)
    (fun _ _ => mem_fieldNodesAt) (fun t => (card_fieldNodesAt M.k t).le) τ₀.work
    Pr.toFunDag_edge (readPos τ₀ (d * d * b)) Pr.toFunDag_rd hcold
    (fun t _ => Pr.toFunDag_step_card hβ t) (Pr.toFunDag_field_card hβ) lin hside hτ
    (fun ℓ => outputNodeOf τ₀ T ℓ) (fun ℓ => appendTime τ₀ T ℓ) (fun ℓ => outputNodeOf_div τ₀ T ℓ)
    (tposOf d b) (fun _ => decOut) (fun w ℓ => Pr.toFunDag_dec hM w ℓ)

/-! ### Corollary HC* at one size -/

open Classical in
/-- **Corollary HC\* at one size, for the field DAG of a pruning of an oblivious transposer.** Let
`T ≤ C (L + 1)`, `L ≥ 1`, `ΓF` a cold genie at `(V, ε)` with depth `D`, a lineage assignment with
merge depth at most `s` outside a set `X` of at most `η L` output positions, `γ = 1/2 - ε - η > 0`
and `4 β (k + 2) k C ≤ γ τ`. If every binary storage code for a relation inside the balls of radius
`(s + 1) τ D` around the output steps has at most `2^{(1/2 + γ/4) L}` elements (Lemma 3.14(b) at
this size), the hypotheses are contradictory. -/
theorem cor_HCstar_pruning (hM : ObliviousTransposer M d b τ₀ T)
    (Pr : Pruning M (d * d * b) τ₀ T) {V β C : ℕ} (hβ : valueWidth M ≤ β)
    (hT : T ≤ C * (d * d * b + 1)) (hL : 1 ≤ d * d * b) {ε η : ℝ} {D : ℕ} {ΓF : Finset ℕ}
    (hcold : IsColdGenie (L := d * d * b) τ₀.work T V β ε D ΓF) (hγ : 0 < 1 / 2 - ε - η)
    (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ Pr.toFunDag.net.paths u →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) (u :: v' :: π) →
      rCount (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) (hτbig : 4 * β * (M.k + 2) * M.k * C ≤ (1 / 2 - ε - η) * τ) (s : ℕ)
    (X : Finset (Fin (d * d * b))) (hX : (X.card : ℝ) ≤ η * (d * d * b : ℕ))
    (hround : ∀ ℓ ∉ X, ∀ π, π ∈ Pr.toFunDag.net.paths (outputNodeOf τ₀ T ℓ) →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) π →
      dm lin (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) false π ≤ s)
    (hballs : ∀ N : Fin (d * d * b) → Finset (Fin (d * d * b)),
      (∀ q, N q ⊆ stepBall τ₀.work T (readPos τ₀ (d * d * b)) ((s + 1) * τ * D)
        (appendTime τ₀ T (tposOf d b q))) →
      ∀ Cd : Finset (Fin (d * d * b) → Bool), MotionDepthCodes.IsStorageCode N Cd →
        (Cd.card : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 + (1 / 2 - ε - η) / 4) * (d * d * b : ℕ))) :
    False := by
  have hτbig' : 4 * β * ((M.k + 2 : ℕ) : ℝ) * M.k * C ≤ (1 / 2 - ε - η) * τ := by
    push_cast
    exact hτbig
  exact cor_HCstar_step Pr.toFunDag (fun u => u / (M.k + 2)) (fieldNodesAt M.k)
    (fun _ _ => mem_fieldNodesAt) (fun t => (card_fieldNodesAt M.k t).le) τ₀.work hT hL
    Pr.toFunDag_edge (readPos τ₀ (d * d * b)) Pr.toFunDag_rd hcold hγ
    (fun t _ => Pr.toFunDag_step_card hβ t) (Pr.toFunDag_field_card hβ) lin hside hτ hτbig' s
    (fun ℓ => outputNodeOf τ₀ T ℓ) (fun ℓ => appendTime τ₀ T ℓ) (fun ℓ => outputNodeOf_div τ₀ T ℓ)
    (tposOf d b) (tposOf_tposOf d b) (fun _ => decOut) (fun w ℓ => Pr.toFunDag_dec hM w ℓ) X hX
    hround hballs

/-! ### The path bound of Theorem HC′ (Lemma 3.9) -/

open Classical in
/-- **Lemma 3.9 for the field DAG of a pruning** (the path bound of Theorem HC′): there is a set `Q`
with `τ |Q| ≤ (k + 2) N_R` such that every `(ΓF, Q)`-free path with `s'` deep merges has at most
`(s' + 1) τ - 1` deep edges and at most `(s' + 1) τ D` vertices. -/
theorem short_paths_pruning {L : ℕ} (Pr : Pruning M L τ₀ T) {V β : ℕ} {ε : ℝ} {D : ℕ}
    {ΓF : Finset ℕ} (hcold : IsColdGenie (L := L) τ₀.work T V β ε D ΓF) (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ Pr.toFunDag.net.paths u →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) (u :: v' :: π) →
      rCount (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) :
    ∃ Q : Finset ℕ, τ * Q.card ≤ (M.k + 2) * (deepHops τ₀.work T V).card ∧
      ∀ t π, π ∈ Pr.toFunDag.net.paths t →
        LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k) ∪ Q) π →
        rCount (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) π + 1 ≤
          (dm lin (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) false π + 1) *
            τ ∧
        π.length ≤
          (dm lin (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) false π + 1) *
            τ * D :=
  short_paths Pr.toFunDag.net (fun u => u / (M.k + 2)) (fieldNodesAt M.k)
    (fun _ _ => mem_fieldNodesAt) (fun t => (card_fieldNodesAt M.k t).le) τ₀.work
    Pr.toFunDag_edge hcold.2 lin hside hτ

/-! ### A sharper charge: the checkpoints are symbol fields -/

/-- Symbol fields take at most `g + 1 ≤ 2^{⌈log₂ (g + 1)⌉}` values. -/
theorem Pruning.toFunDag_symbol_card {L : ℕ} (Pr : Pruning M L τ₀ T) (t : ℕ) (j : Fin M.k) :
    (univ.image fun w => Pr.toFunDag.val w (symbolNode M.k t j)).card ≤
      2 ^ Nat.clog 2 (M.g + 1) := by
  calc (univ.image fun w => Pr.toFunDag.val w (symbolNode M.k t j)).card
      ≤ (range (M.g + 1)).card := by
        refine card_le_card fun e he => ?_
        obtain ⟨w, -, rfl⟩ := mem_image.mp he
        rw [mem_range]
        by_cases ht : symbolNode M.k t j / (M.k + 2) < T
        · rw [Pr.toFunDag_val_of_lt w ht, fieldVal_symbolNode]
          exact (writtenSym M (List.ofFn w) t j).2
        · rw [Pr.toFunDag_val_of_le w (not_lt.mp ht)]
          omega
    _ = M.g + 1 := card_range _
    _ ≤ 2 ^ Nat.clog 2 (M.g + 1) := Nat.le_pow_clog (by norm_num) _

open Classical in
/-- **Theorem HC′(b) with cheap checkpoints**, for a refinement of the dependency DAG (the setting
of `hop_charging_fields`). The checkpoints `Q` can be taken among the heads of deep lineage edges
(the covering lemma applied to the deep lineage edges only, as in the paper's proof of Lemma 3.9);
so if each such head takes at most `2^βQ` values, the code has at most
`2^{β |ΓF| + βQ |Q| + |X|}` code words, with `τ |Q| ≤ m N_R` as before. -/
theorem hop_charging_fields_heads {L k : ℕ} (G : FunDag L) (st : ℕ → ℕ) (nodesAt : ℕ → Finset ℕ)
    {m : ℕ} (hnodes : ∀ u t, u ∈ nodesAt t ↔ st u = t) (hwidth : ∀ t, (nodesAt t).card ≤ m)
    (xs : Fin k → ℕ → ℤ) {T V β βQ : ℕ} (hedge : ∀ u, ∀ v ∈ G.out u, DepStep xs T (st u) (st v))
    (rdStep : ℕ → Option (Fin L)) (hrd : ∀ u j, G.rd u = some j → rdStep (st u) = some j)
    {ε : ℝ} {D : ℕ} {ΓF : Finset ℕ} (hcold : IsColdGenie (L := L) xs T V β ε D ΓF)
    (hstep : ∀ t ∈ ΓF, (univ.image fun w => fun v : nodesAt t => G.val w v).card ≤ 2 ^ β)
    (lin : Forest)
    (hhead : ∀ u v, lin.nxt u = some v → DeepStep xs T V (st u) (st v) →
      (univ.image fun w => G.val w v).card ≤ 2 ^ βQ)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ G.net.paths u →
      LinNet.GFree (ΓF.biUnion nodesAt) (u :: v' :: π) →
      rCount (fun u v => DeepStep xs T V (st u) (st v)) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) (s : ℕ) (o : Fin L → ℕ) (tout : Fin L → ℕ) (hout : ∀ ℓ, st (o ℓ) = tout ℓ)
    (tpos : Fin L → Fin L) (dec : Fin L → ℕ → Bool)
    (hdec : ∀ w ℓ, dec ℓ (G.val w (o ℓ)) = w (tpos ℓ)) (X : Finset (Fin L))
    (hround : ∀ ℓ ∉ X, ∀ π, π ∈ G.net.paths (o ℓ) → LinNet.GFree (ΓF.biUnion nodesAt) π →
      dm lin (fun u v => DeepStep xs T V (st u) (st v)) false π ≤ s) :
    ∃ (Q : Finset ℕ) (I : Fin L → Finset (Fin L)), τ * Q.card ≤ m * (deepHops xs T V).card ∧
      (∀ q ∈ Q, ∃ u, lin.nxt u = some q ∧ DeepStep xs T V (st u) (st q)) ∧
      IsIndexCode (fun w => ((fun t : ΓF => fun v : nodesAt t.1 => G.val w v),
        (fun q : Q => G.val w q.1), (fun ℓ : X => w (tpos ℓ.1)))) I tpos ∧
      (∀ ℓ, I ℓ ⊆ stepBall xs T rdStep ((s + 1) * τ * D) (tout ℓ)) ∧
      (univ.image fun w => ((fun t : ΓF => fun v : nodesAt t.1 => G.val w v),
        (fun q : Q => G.val w q.1), (fun ℓ : X => w (tpos ℓ.1)))).card ≤
        2 ^ (β * ΓF.card + βQ * Q.card + X.card) := by
  set Γ' := ΓF.biUnion nodesAt
  have hΓ' : ∀ u, u ∈ Γ' ↔ st u ∈ ΓF := fun u => by
    constructor
    · intro h
      obtain ⟨t, ht, hu⟩ := mem_biUnion.mp h
      rw [(hnodes u t).mp hu]
      exact ht
    · intro h
      exact mem_biUnion.mpr ⟨st u, h, (hnodes u (st u)).mpr rfl⟩
  set Rc : ℕ → ℕ → Prop := fun u v => DeepStep xs T V (st u) (st v)
  have hcold' : ∀ t π, π ∈ G.net.paths t → LinNet.GFree Γ' π → rCount Rc π = 0 →
      π.length ≤ D := by
    intro t π hπ hfree hR
    have := hcold.2 (π.map st) (isDepPath_map G st xs T hedge π t hπ) ((gfree_map hΓ').mp hfree)
      (by rw [← rCount_map]; exact hR)
    simpa using this
  -- the tails of the deep lineage edges, at most `m` per deep pair
  let Rset : Finset (ℕ × ℕ) := (deepHops xs T V).image fun η => (η.2.2, η.2.1)
  have hRset : ∀ a b, DeepStep xs T V a b → (a, b) ∈ Rset := by
    rintro a b ⟨η, hη, he, hl⟩
    refine mem_image.mpr ⟨η, mem_sdiff.mpr ⟨hη, hl⟩, ?_⟩
    rw [he]
  let M' : Finset ℕ :=
    ((Rset.image Prod.fst).biUnion nodesAt).filter fun u => ∃ v, lin.nxt u = some v ∧ Rc u v
  have hM' : ∀ u v, lin.nxt u = some v → Rc u v → u ∈ M' := fun u v hn hR =>
    mem_filter.mpr ⟨mem_biUnion.mpr ⟨st u, mem_image.mpr ⟨_, hRset _ _ hR, rfl⟩,
      (hnodes u (st u)).mpr rfl⟩, v, hn, hR⟩
  have hM'card : M'.card ≤ m * (deepHops xs T V).card := by
    calc M'.card ≤ ((Rset.image Prod.fst).biUnion nodesAt).card := card_filter_le _ _
      _ ≤ ∑ t ∈ Rset.image Prod.fst, (nodesAt t).card := card_biUnion_le
      _ ≤ ∑ _t ∈ Rset.image Prod.fst, m := sum_le_sum fun t _ => hwidth t
      _ = (Rset.image Prod.fst).card * m := by rw [sum_const, smul_eq_mul]
      _ ≤ (deepHops xs T V).card * m :=
          Nat.mul_le_mul_right _ (card_image_le.trans card_image_le)
      _ = m * (deepHops xs T V).card := mul_comm _ _
  obtain ⟨Q, hQh, hQ, hcov⟩ := covering lin M' hτ
  -- the checkpoints are heads of deep lineage edges
  have hQhead : ∀ q ∈ Q, ∃ u, lin.nxt u = some q ∧ DeepStep xs T V (st u) (st q) := by
    intro q hq
    obtain ⟨u, hu, hq'⟩ := mem_biUnion.mp (hQh hq)
    have hnxt : lin.nxt u = some q := by simpa using hq'
    obtain ⟨-, v, hv, hR⟩ := mem_filter.mp hu
    rw [hnxt] at hv
    obtain rfl := Option.some.inj hv
    exact ⟨u, hnxt, hR⟩
  have hQcard : ∀ q : Q, (univ.image fun w => G.val w q.1).card ≤ 2 ^ βQ := by
    intro q
    obtain ⟨u, hn, hR⟩ := hQhead q.1 q.2
    exact hhead u q.1 hn hR
  -- the index code
  set I : Fin L → Finset (Fin L) := fun ℓ =>
    if ℓ ∈ X ∨ o ℓ ∈ Γ' ∪ Q then ∅ else G.coneSet (Γ' ∪ Q) (o ℓ)
  refine ⟨Q, I, hQ.trans hM'card, hQhead, ?_, ?_, ?_⟩
  · refine G.isIndexCode_of _ (Γ' ∪ Q) X o tpos dec hdec fun w w' hE => ?_
    simp only [Prod.mk.injEq] at hE
    obtain ⟨h1, h2, h3⟩ := hE
    refine ⟨fun v hv => ?_, fun ℓ hℓ => congr_fun h3 ⟨ℓ, hℓ⟩⟩
    rcases mem_union.mp hv with hv | hv
    · have ht := (hΓ' v).mp hv
      exact congr_fun (congr_fun h1 ⟨st v, ht⟩) ⟨v, (hnodes v (st v)).mpr rfl⟩
    · exact congr_fun h2 ⟨v, hv⟩
  · intro ℓ j hj
    simp only [I] at hj
    split_ifs at hj with hX
    · simp at hj
    · push Not at hX
      obtain ⟨hℓ, -⟩ := hX
      simp only [FunDag.coneSet, mem_filter, mem_univ, true_and] at hj
      obtain ⟨π, hπ, hfree, hrdj⟩ := hj
      have hlen := length_le_of_cov G.net Rc lin Γ' D hcold' hside M' hM' hτ Q hcov hπ hfree
      have hdm : dm lin Rc false π ≤ s := hround ℓ hℓ π hπ (gfree_mono subset_union_left hfree)
      have hlen' : π.length ≤ (s + 1) * τ * D :=
        hlen.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
      obtain ⟨π', rfl⟩ := G.net.mem_paths_head hπ
      simp only [stepBall, mem_filter, mem_univ, true_and]
      refine ⟨π'.map st, ?_, ?_, ?_⟩
      · have := isDepPath_map G st xs T hedge (o ℓ :: π') (o ℓ) hπ
        simpa [hout] using this
      · simp only [List.length_map]
        simp only [List.length_cons] at hlen'
        omega
      · rw [← hout ℓ, ← List.map_cons, getLastD_map st (o ℓ :: π') (o ℓ)]
        exact hrd _ _ hrdj
  · have h := card_image_triple_le (fun w (t : ΓF) => fun v : nodesAt t.1 => G.val w v)
      (fun w (q : Q) => G.val w q.1) (fun w (ℓ : X) => w (tpos ℓ.1))
      (fun t => hstep t.1 t.2) hQcard
    simp only [Fintype.card_coe] at h
    convert h

open Classical in
/-- **Theorem HC′(b), sharpened for field DAGs.** If the lineage edges are edges of the field DAG
(as in Definition 3.12 of the paper), the checkpoints `Q` can be taken among the heads of deep
lineage edges. These are symbol fields (`toFunDag_deep_edge`), so each costs `⌈log₂ (g + 1)⌉` bits
instead of `β`: the code has at most `2^{β |ΓF| + ⌈log₂ (g + 1)⌉ |Q| + |X|}` code words, with
`τ |Q| ≤ (k + 2) N_R` as before. -/
theorem hop_charging_pruning_sym (hM : ObliviousTransposer M d b τ₀ T)
    (Pr : Pruning M (d * d * b) τ₀ T) {V β : ℕ} (hβ : valueWidth M ≤ β) {ε : ℝ} {D : ℕ}
    {ΓF : Finset ℕ} (hcold : IsColdGenie (L := d * d * b) τ₀.work T V β ε D ΓF) (lin : Forest)
    (hlin : ∀ u v, lin.nxt u = some v → v ∈ Pr.toFunDag.out u)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ Pr.toFunDag.net.paths u →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) (u :: v' :: π) →
      rCount (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) (s : ℕ) (X : Finset (Fin (d * d * b)))
    (hround : ∀ ℓ ∉ X, ∀ π, π ∈ Pr.toFunDag.net.paths (outputNodeOf τ₀ T ℓ) →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) π →
      dm lin (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) false π ≤ s) :
    ∃ (Q : Finset ℕ) (I : Fin (d * d * b) → Finset (Fin (d * d * b))),
      τ * Q.card ≤ (M.k + 2) * (deepHops τ₀.work T V).card ∧
      (∀ q ∈ Q, ∃ (t : ℕ) (j : Fin M.k), q = symbolNode M.k t j) ∧
      IsIndexCode (fun w => ((fun t : ΓF => fun v : fieldNodesAt M.k t.1 => Pr.toFunDag.val w v),
        (fun q : Q => Pr.toFunDag.val w q.1), (fun ℓ : X => w (tposOf d b ℓ.1)))) I
        (tposOf d b) ∧
      (∀ ℓ, I ℓ ⊆ stepBall τ₀.work T (readPos τ₀ (d * d * b)) ((s + 1) * τ * D)
        (appendTime τ₀ T ℓ)) ∧
      (univ.image fun w => ((fun t : ΓF => fun v : fieldNodesAt M.k t.1 => Pr.toFunDag.val w v),
        (fun q : Q => Pr.toFunDag.val w q.1), (fun ℓ : X => w (tposOf d b ℓ.1)))).card ≤
        2 ^ (β * ΓF.card + Nat.clog 2 (M.g + 1) * Q.card + X.card) := by
  -- heads of deep edges of the field DAG are symbol fields
  have hsym : ∀ u v, lin.nxt u = some v →
      DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2)) →
      ∃ (t : ℕ) (j : Fin M.k), v = symbolNode M.k t j := fun u v hn hR => by
    obtain ⟨-, j, hj⟩ := Pr.toFunDag_deep_edge (hlin u v hn) hR
    exact ⟨_, j, hj⟩
  obtain ⟨Q, I, hQ, hQhead, hcode, hball, himg⟩ := hop_charging_fields_heads Pr.toFunDag
    (fun u => u / (M.k + 2)) (fieldNodesAt M.k) (fun _ _ => mem_fieldNodesAt)
    (fun t => (card_fieldNodesAt M.k t).le) τ₀.work Pr.toFunDag_edge (readPos τ₀ (d * d * b))
    Pr.toFunDag_rd hcold (fun t _ => Pr.toFunDag_step_card hβ t) lin
    (fun u v hn hR => by
      obtain ⟨t, j, rfl⟩ := hsym u v hn hR
      exact Pr.toFunDag_symbol_card t j)
    hside hτ s (fun ℓ => outputNodeOf τ₀ T ℓ) (fun ℓ => appendTime τ₀ T ℓ)
    (fun ℓ => outputNodeOf_div τ₀ T ℓ) (tposOf d b) (fun _ => decOut)
    (fun w ℓ => Pr.toFunDag_dec hM w ℓ) X hround
  refine ⟨Q, I, hQ, fun q hq => ?_, hcode, hball, himg⟩
  obtain ⟨u, hn, hR⟩ := hQhead q hq
  exact hsym u q hn hR

open Classical in
/-- **Corollary HC\* at one size with cheap checkpoints**, for a refinement of the dependency DAG
(the setting of `cor_HCstar_step`): if every head of a deep lineage edge takes at most `2^βQ`
values, the condition `4 β m k C ≤ γ τ` of `cor_HCstar_step` can be replaced by
`4 βQ m k C ≤ γ τ`. -/
theorem cor_HCstar_heads {L k : ℕ} (G : FunDag L) (st : ℕ → ℕ) (nodesAt : ℕ → Finset ℕ) {m : ℕ}
    (hnodes : ∀ u t, u ∈ nodesAt t ↔ st u = t) (hwidth : ∀ t, (nodesAt t).card ≤ m)
    (xs : Fin k → ℕ → ℤ) {T V β βQ C : ℕ} (hT : T ≤ C * (L + 1)) (hL : 1 ≤ L)
    (hedge : ∀ u, ∀ v ∈ G.out u, DepStep xs T (st u) (st v))
    (rdStep : ℕ → Option (Fin L)) (hrd : ∀ u j, G.rd u = some j → rdStep (st u) = some j)
    {ε η : ℝ} {D : ℕ} {ΓF : Finset ℕ} (hcold : IsColdGenie (L := L) xs T V β ε D ΓF)
    (hγ : 0 < 1 / 2 - ε - η)
    (hstep : ∀ t ∈ ΓF, (univ.image fun w => fun v : nodesAt t => G.val w v).card ≤ 2 ^ β)
    (lin : Forest)
    (hhead : ∀ u v, lin.nxt u = some v → DeepStep xs T V (st u) (st v) →
      (univ.image fun w => G.val w v).card ≤ 2 ^ βQ)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ G.net.paths u →
      LinNet.GFree (ΓF.biUnion nodesAt) (u :: v' :: π) →
      rCount (fun u v => DeepStep xs T V (st u) (st v)) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) (hτbig : 4 * βQ * m * k * C ≤ (1 / 2 - ε - η) * τ) (s : ℕ)
    (o : Fin L → ℕ) (tout : Fin L → ℕ) (hout : ∀ ℓ, st (o ℓ) = tout ℓ)
    (tpos : Fin L → Fin L) (htpos : ∀ q, tpos (tpos q) = q) (dec : Fin L → ℕ → Bool)
    (hdec : ∀ w ℓ, dec ℓ (G.val w (o ℓ)) = w (tpos ℓ))
    (X : Finset (Fin L)) (hX : (X.card : ℝ) ≤ η * L)
    (hround : ∀ ℓ ∉ X, ∀ π, π ∈ G.net.paths (o ℓ) → LinNet.GFree (ΓF.biUnion nodesAt) π →
      dm lin (fun u v => DeepStep xs T V (st u) (st v)) false π ≤ s)
    (hballs : ∀ N : Fin L → Finset (Fin L),
      (∀ q, N q ⊆ stepBall xs T rdStep ((s + 1) * τ * D) (tout (tpos q))) →
      ∀ Cd : Finset (Fin L → Bool), MotionDepthCodes.IsStorageCode N Cd →
        (Cd.card : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 + (1 / 2 - ε - η) / 4) * L)) :
    False := by
  set γ := 1 / 2 - ε - η
  obtain ⟨Q, I, hQ, -, hcode, hball, himg⟩ := hop_charging_fields_heads G st nodesAt hnodes hwidth
    xs hedge rdStep hrd hcold hstep lin hhead hside hτ s o tout hout tpos dec hdec X hround
  set E := fun w : Fin L → Bool => ((fun t : ΓF => fun v : nodesAt t.1 => G.val w v),
    (fun q : Q => G.val w q.1), (fun ℓ : X => w (tpos ℓ.1)))
  set bits := β * ΓF.card + βQ * Q.card + X.card
  -- a large fibre, which is a storage code for a relation inside the balls
  obtain ⟨w₀, hw₀⟩ := exists_large_fibre_card E himg
  have hsc := isStorageCode_fibre_of_indexCode hcode htpos (E w₀)
  have hsize := hballs (fun q => I (tpos q)) (fun q => hball (tpos q)) _ hsc
  set Fb := (univ.filter fun w => E w = E w₀).card
  -- `2^L ≤ 2^bits ⋅ |fibre| ≤ 2^{bits + (1/2 + γ/4) L}`
  have h1 : (2 : ℝ) ^ (L : ℝ) ≤ (2 : ℝ) ^ ((bits : ℝ) + (1 / 2 + γ / 4) * L) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_natCast]
    calc (2 : ℝ) ^ L = ((2 ^ L : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ bits * Fb : ℕ) : ℝ) := by exact_mod_cast hw₀
      _ = (2 : ℝ) ^ bits * Fb := by push_cast; ring
      _ ≤ (2 : ℝ) ^ bits * (2 : ℝ) ^ ((1 / 2 + γ / 4) * L) := by gcongr
  have h2 : (L : ℝ) ≤ bits + (1 / 2 + γ / 4) * L :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h1
  -- the bit count of the checkpoints
  have hRcard : (τ * Q.card : ℝ) ≤ m * k * C * (L + 1) := by
    have h3 : τ * Q.card ≤ m * (k * (C * (L + 1))) :=
      hQ.trans (Nat.mul_le_mul_left _ ((card_deepHops_le xs T V).trans
        (Nat.mul_le_mul_left _ hT)))
    have : (τ * Q.card : ℝ) ≤ m * (k * (C * (L + 1))) := by exact_mod_cast h3
    linarith
  have hτ' : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hβQ : (βQ * Q.card : ℝ) ≤ γ * (L + 1) / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have hL0 : (0 : ℝ) ≤ L + 1 := by positivity
    have hβ0 : (0 : ℝ) ≤ βQ := by positivity
    have : (βQ : ℝ) * (τ * Q.card) ≤ βQ * (m * k * C * (L + 1)) :=
      mul_le_mul_of_nonneg_left hRcard hβ0
    have h4 : (4 * βQ * m * k * C : ℝ) * (L + 1) ≤ γ * τ * (L + 1) :=
      mul_le_mul_of_nonneg_right hτbig hL0
    nlinarith
  have hbits : (bits : ℝ) ≤ ε * L + γ * (L + 1) / 4 + η * L := by
    have : (bits : ℝ) = β * ΓF.card + βQ * Q.card + X.card := by push_cast [bits]; ring
    rw [this]
    linarith [hcold.1]
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have : γ * L / 2 ≤ γ / 4 := by
    simp only [γ] at h2 hbits ⊢
    nlinarith
  nlinarith

open Classical in
/-- **Corollary HC\* at one size, with the sharpened charge.** As `cor_HCstar_pruning`, for a
lineage assignment whose lineage edges are edges of the field DAG, with
`4 ⌈log₂ (g + 1)⌉ (k + 2) k C ≤ γ τ` in place of `4 β (k + 2) k C ≤ γ τ`: the checkpoints are
symbol fields (`hop_charging_pruning_sym`). -/
theorem cor_HCstar_pruning_sym (hM : ObliviousTransposer M d b τ₀ T)
    (Pr : Pruning M (d * d * b) τ₀ T) {V β C : ℕ} (hβ : valueWidth M ≤ β)
    (hT : T ≤ C * (d * d * b + 1)) (hL : 1 ≤ d * d * b) {ε η : ℝ} {D : ℕ} {ΓF : Finset ℕ}
    (hcold : IsColdGenie (L := d * d * b) τ₀.work T V β ε D ΓF) (hγ : 0 < 1 / 2 - ε - η)
    (lin : Forest) (hlin : ∀ u v, lin.nxt u = some v → v ∈ Pr.toFunDag.out u)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ Pr.toFunDag.net.paths u →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) (u :: v' :: π) →
      rCount (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ)
    (hτbig : 4 * Nat.clog 2 (M.g + 1) * (M.k + 2) * M.k * C ≤ (1 / 2 - ε - η) * τ) (s : ℕ)
    (X : Finset (Fin (d * d * b))) (hX : (X.card : ℝ) ≤ η * (d * d * b : ℕ))
    (hround : ∀ ℓ ∉ X, ∀ π, π ∈ Pr.toFunDag.net.paths (outputNodeOf τ₀ T ℓ) →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) π →
      dm lin (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) false π ≤ s)
    (hballs : ∀ N : Fin (d * d * b) → Finset (Fin (d * d * b)),
      (∀ q, N q ⊆ stepBall τ₀.work T (readPos τ₀ (d * d * b)) ((s + 1) * τ * D)
        (appendTime τ₀ T (tposOf d b q))) →
      ∀ Cd : Finset (Fin (d * d * b) → Bool), MotionDepthCodes.IsStorageCode N Cd →
        (Cd.card : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 + (1 / 2 - ε - η) / 4) * (d * d * b : ℕ))) :
    False := by
  have hτbig' : 4 * (Nat.clog 2 (M.g + 1) : ℝ) * ((M.k + 2 : ℕ) : ℝ) * M.k * C ≤
      (1 / 2 - ε - η) * τ := by
    push_cast
    exact hτbig
  exact cor_HCstar_heads Pr.toFunDag (fun u => u / (M.k + 2)) (fieldNodesAt M.k)
    (fun _ _ => mem_fieldNodesAt) (fun t => (card_fieldNodesAt M.k t).le) τ₀.work hT hL
    Pr.toFunDag_edge (readPos τ₀ (d * d * b)) Pr.toFunDag_rd hcold hγ
    (fun t _ => Pr.toFunDag_step_card hβ t) lin
    (fun u v hn hR => by
      obtain ⟨-, j, hj⟩ := Pr.toFunDag_deep_edge (hlin u v hn) hR
      rw [hj]
      exact Pr.toFunDag_symbol_card _ j)
    hside hτ hτbig' s (fun ℓ => outputNodeOf τ₀ T ℓ) (fun ℓ => appendTime τ₀ T ℓ)
    (fun ℓ => outputNodeOf_div τ₀ T ℓ) (tposOf d b) (tposOf_tposOf d b) (fun _ => decOut)
    (fun w ℓ => Pr.toFunDag_dec hM w ℓ) X hX hround hballs

/-! ### The last sentence of Corollary HC* -/

open Classical in
/-- **The last sentence of Corollary HC\*, at one size.** Let a lineage assignment for the empty
genie (no path that leaves a continuation by another out-edge contains a deep edge) give every path
of the field DAG from every output node at most `s` deep merges. If every binary storage code for a
relation inside the balls of radius `(s + 1) τ D` has at most `2^{(1/2 + 1/16) L}` elements, where
`τ = 16 β (k + 2) k C` and `D` is the depth of the cold genies at `(V, 1/4)`, the hypotheses are
contradictory. -/
theorem cor_HCstar_pruning_empty (hM : ObliviousTransposer M d b τ₀ T)
    (Pr : Pruning M (d * d * b) τ₀ T) {V β C : ℕ} (hk : 1 ≤ M.k) (hV : 1 ≤ V)
    (hβ : valueWidth M ≤ β) (hC : 1 ≤ C) (hT : T ≤ C * (d * d * b + 1)) (hL : 1 ≤ d * d * b)
    (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ Pr.toFunDag.net.paths u →
      rCount (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) (u :: v' :: π) = 0)
    (s : ℕ)
    (hround : ∀ (ℓ : Fin (d * d * b)) π, π ∈ Pr.toFunDag.net.paths (outputNodeOf τ₀ T ℓ) →
      dm lin (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) false π ≤ s)
    (hballs : ∀ N : Fin (d * d * b) → Finset (Fin (d * d * b)),
      (∀ q, N q ⊆ stepBall τ₀.work T (readPos τ₀ (d * d * b))
        ((s + 1) * (16 * β * (M.k + 2) * M.k * C) *
          (DF M.k (2 * V - 1) ((1 / 4 : ℝ) / (4 * β * C)) * ⌈4 * β * C / (1 / 4 : ℝ)⌉₊))
        (appendTime τ₀ T (tposOf d b q))) →
      ∀ Cd : Finset (Fin (d * d * b) → Bool), MotionDepthCodes.IsStorageCode N Cd →
        (Cd.card : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 + 1 / 16 : ℝ) * (d * d * b : ℕ))) :
    False := by
  have hβ1 : 1 ≤ β := le_trans (by unfold valueWidth; omega) hβ
  obtain ⟨ΓF, hcold⟩ := cold_genie_exists (L := d * d * b) hk hV hβ1 hC hL hT
    (ε := 1 / 4) (by norm_num) τ₀.work τ₀.work_isWalk
  have hτ : 1 ≤ 16 * β * (M.k + 2) * M.k * C :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hβ1) (by omega)) hk) hC
  refine cor_HCstar_pruning hM Pr hβ hT hL hcold (η := 0) (by norm_num) lin
    (fun u v v' π h1 h2 h3 _ => hside u v v' π h1 h2 h3) hτ ?_ s ∅ (by simp)
    (fun ℓ _ π hπ _ => hround ℓ π hπ) ?_
  · push_cast
    linarith
  · intro N hN Cd hCd
    have e : (1 / 2 + (1 / 2 - 1 / 4 - 0) / 4 : ℝ) = 1 / 2 + 1 / 16 := by norm_num
    rw [e]
    exact hballs N hN Cd hCd

/-! ### Oblivious transposers in the frozen model -/

/-- The halting time of a machine that is oblivious at length `L = d² b` and transposes within
`C (L + 1)` steps is at most `C (L + 1)`. -/
theorem haltTime_le_of_obliviousOn {M : TM} {d b C T : ℕ}
    (hobl : ObliviousOn M (inputsOfLength (d * d * b)) T) (htr : TransposesAtWidth M d b C) :
    T ≤ C * (d * d * b + 1) := by
  have h := (ObliviousTransposer.of_obliviousOn hobl htr (fun _ => false)).2
  have e : ⌊(C : ℝ) * (((d * d * b : ℕ) : ℝ) + 1)⌋₊ = C * (d * d * b + 1) := by
    rw [show (C : ℝ) * (((d * d * b : ℕ) : ℝ) + 1) = ((C * (d * d * b + 1) : ℕ) : ℝ) by
      push_cast; ring]
    exact Nat.floor_natCast _
  rwa [e] at h

open Classical in
/-- **Corollary HC\* at one size, in the frozen model.** `M` is oblivious at length `L = d² b` with
halting time `T` (`ObliviousOn`) and transposes `d × d` matrices with `b`-bit entries within
`C (L + 1)` steps; `τ₀` is the trace of any input. For any pruning of its field DAG, cold genie,
lineage assignment and merge-depth bound as in `cor_HCstar_pruning`, the bound of Lemma 3.14(b) at
this size is violated. -/
theorem cor_HCstar_frozen {M : TM} {d b C T : ℕ}
    (hobl : ObliviousOn M (inputsOfLength (d * d * b)) T) (htr : TransposesAtWidth M d b C)
    (w₀ : Fin (d * d * b) → Bool) {τ₀ : Trace M.k} (hτ₀ : τ₀ = trace M (List.ofFn w₀))
    (Pr : Pruning M (d * d * b) τ₀ T) {V β : ℕ} (hβ : valueWidth M ≤ β) (hL : 1 ≤ d * d * b)
    {ε η : ℝ} {D : ℕ} {ΓF : Finset ℕ}
    (hcold : IsColdGenie (L := d * d * b) τ₀.work T V β ε D ΓF) (hγ : 0 < 1 / 2 - ε - η)
    (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ Pr.toFunDag.net.paths u →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) (u :: v' :: π) →
      rCount (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) (hτbig : 4 * β * (M.k + 2) * M.k * C ≤ (1 / 2 - ε - η) * τ) (s : ℕ)
    (X : Finset (Fin (d * d * b))) (hX : (X.card : ℝ) ≤ η * (d * d * b : ℕ))
    (hround : ∀ ℓ ∉ X, ∀ π, π ∈ Pr.toFunDag.net.paths (outputNodeOf τ₀ T ℓ) →
      LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) π →
      dm lin (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) false π ≤ s)
    (hballs : ∀ N : Fin (d * d * b) → Finset (Fin (d * d * b)),
      (∀ q, N q ⊆ stepBall τ₀.work T (readPos τ₀ (d * d * b)) ((s + 1) * τ * D)
        (appendTime τ₀ T (tposOf d b q))) →
      ∀ Cd : Finset (Fin (d * d * b) → Bool), MotionDepthCodes.IsStorageCode N Cd →
        (Cd.card : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 + (1 / 2 - ε - η) / 4) * (d * d * b : ℕ))) :
    False := by
  subst hτ₀
  exact cor_HCstar_pruning (ObliviousTransposer.of_obliviousOn hobl htr w₀).1 Pr hβ
    (haltTime_le_of_obliviousOn hobl htr) hL hcold hγ lin hside hτ hτbig s X hX hround hballs

end MergeDepth
