import MergeDepth.MergeDag
import MergeDepth.HopFields

/-!
# Proposition 3.20(b): code-level depth reduction for all codes

For a function DAG refining the dependency DAG (as in Theorem HC′(b)), let `Q` be the checkpoints of
Lemma 3.9. If `Z` meets every path of the merge DAG with `s + 1` vertices whose first vertex is
initial, then revealing the steps of the cold genie, the vertices of `Q` and those of `Z` is an
index code, with at most `β |ΓF| + β |Q| + β |Z|` bits, for a system contained in the balls of
radius `(s + 1) τ D` around the output steps (`merge_reduction_fields`).
-/

namespace MergeDepth

open Finset BoundedNesting

variable {L k : ℕ}

open Classical in
/-- **Proposition 3.20(b)** for a refinement of the dependency DAG. -/
theorem merge_reduction_fields (G : FunDag L) (st : ℕ → ℕ) (nodesAt : ℕ → Finset ℕ) {m : ℕ}
    (hnodes : ∀ u t, u ∈ nodesAt t ↔ st u = t) (hwidth : ∀ t, (nodesAt t).card ≤ m)
    (xs : Fin k → ℕ → ℤ) {T V β : ℕ} (hedge : ∀ u, ∀ v ∈ G.out u, DepStep xs T (st u) (st v))
    (rdStep : ℕ → Option (Fin L)) (hrd : ∀ u j, G.rd u = some j → rdStep (st u) = some j)
    {ε : ℝ} {D : ℕ} {ΓF : Finset ℕ} (hcold : IsColdGenie (L := L) xs T V β ε D ΓF)
    (hstep : ∀ t ∈ ΓF, (univ.image fun w => fun v : nodesAt t => G.val w v).card ≤ 2 ^ β)
    (hfield : ∀ u, (univ.image fun w => G.val w u).card ≤ 2 ^ β)
    (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ G.net.paths u →
      LinNet.GFree (ΓF.biUnion nodesAt) (u :: v' :: π) →
      rCount (fun u v => DeepStep xs T V (st u) (st v)) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) (o : Fin L → ℕ) (tout : Fin L → ℕ) (hout : ∀ ℓ, st (o ℓ) = tout ℓ)
    (tpos : Fin L → Fin L) (dec : Fin L → ℕ → Bool)
    (hdec : ∀ w ℓ, dec ℓ (G.val w (o ℓ)) = w (tpos ℓ)) :
    ∃ Q : Finset ℕ, τ * Q.card ≤ m * (deepHops xs T V).card ∧
      ∀ (Z : Finset ℕ) (s : ℕ),
        MCut G.net (fun u v => DeepStep xs T V (st u) (st v)) lin (ΓF.biUnion nodesAt ∪ Q)
          ((univ.image o).filter (· ∉ ΓF.biUnion nodesAt ∪ Q)) Z s →
        ∃ I : Fin L → Finset (Fin L),
          IsIndexCode (fun w => ((fun t : ΓF => fun v : nodesAt t.1 => G.val w v),
            (fun q : Q => G.val w q.1), (fun z : Z => G.val w z.1))) I tpos ∧
          (∀ ℓ, I ℓ ⊆ stepBall xs T rdStep ((s + 1) * τ * D) (tout ℓ)) ∧
          (univ.image fun w => ((fun t : ΓF => fun v : nodesAt t.1 => G.val w v),
            (fun q : Q => G.val w q.1), (fun z : Z => G.val w z.1))).card ≤
            2 ^ (β * ΓF.card + β * Q.card + β * Z.card) := by
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
  have hcold' : ∀ t π, π ∈ G.net.paths t → LinNet.GFree Γ' π → rCount Rc π = 0 → π.length ≤ D := by
    intro t π hπ hfree hR
    have := hcold.2 (π.map st) (isDepPath_map G st xs T hedge π t hπ) ((gfree_map hΓ').mp hfree)
      (by rw [← rCount_map]; exact hR)
    simpa using this
  let Rset : Finset (ℕ × ℕ) := (deepHops xs T V).image fun η => (η.2.2, η.2.1)
  have hRset : ∀ a b, DeepStep xs T V a b → (a, b) ∈ Rset := by
    rintro a b ⟨η, hη, he, hl⟩
    refine mem_image.mpr ⟨η, mem_sdiff.mpr ⟨hη, hl⟩, ?_⟩
    rw [he]
  let M : Finset ℕ := (Rset.image Prod.fst).biUnion nodesAt
  have hM : ∀ u v, lin.nxt u = some v → Rc u v → u ∈ M := fun u v _ hR =>
    mem_biUnion.mpr ⟨st u, mem_image.mpr ⟨_, hRset _ _ hR, rfl⟩, (hnodes u (st u)).mpr rfl⟩
  have hMcard : M.card ≤ m * (deepHops xs T V).card := by
    calc M.card ≤ ∑ t ∈ Rset.image Prod.fst, (nodesAt t).card := card_biUnion_le
      _ ≤ ∑ _t ∈ Rset.image Prod.fst, m := sum_le_sum fun t _ => hwidth t
      _ = (Rset.image Prod.fst).card * m := by rw [sum_const, smul_eq_mul]
      _ ≤ (deepHops xs T V).card * m :=
          Nat.mul_le_mul_right _ (card_image_le.trans card_image_le)
      _ = m * (deepHops xs T V).card := mul_comm _ _
  obtain ⟨Q, -, hQ, hcov⟩ := covering lin M hτ
  refine ⟨Q, hQ.trans hMcard, fun Z s hZ => ?_⟩
  refine ⟨fun ℓ => if ℓ ∈ (∅ : Finset (Fin L)) ∨ o ℓ ∈ Γ' ∪ Q ∪ Z then ∅
      else G.coneSet (Γ' ∪ Q ∪ Z) (o ℓ), ?_, ?_, ?_⟩
  · refine G.isIndexCode_of _ (Γ' ∪ Q ∪ Z) ∅ o tpos dec hdec fun w w' hE => ?_
    simp only [Prod.mk.injEq] at hE
    obtain ⟨h1, h2, h3⟩ := hE
    refine ⟨fun v hv => ?_, fun ℓ hℓ => absurd hℓ (Finset.notMem_empty ℓ)⟩
    rcases mem_union.mp hv with hv | hv
    · rcases mem_union.mp hv with hv | hv
      · have ht := (hΓ' v).mp hv
        exact congr_fun (congr_fun h1 ⟨st v, ht⟩) ⟨v, (hnodes v (st v)).mpr rfl⟩
      · exact congr_fun h2 ⟨v, hv⟩
    · exact congr_fun h3 ⟨v, hv⟩
  · intro ℓ j hj
    simp only at hj
    split_ifs at hj with hX
    · simp at hj
    · push Not at hX
      obtain ⟨-, ho⟩ := hX
      have hoZ : o ℓ ∉ Z := fun h => ho (mem_union_right _ h)
      have hoO : o ℓ ∈ (univ.image o).filter (· ∉ Γ' ∪ Q) :=
        mem_filter.mpr ⟨mem_image_of_mem o (mem_univ ℓ), fun h => ho (mem_union_left _ h)⟩
      simp only [FunDag.coneSet, mem_filter, mem_univ, true_and] at hj
      obtain ⟨π, hπ, hfree, hrdj⟩ := hj
      have hlen := length_le_of_cut G.net Rc lin _ Γ' D hcold' hside M hM hτ Q hcov
        hZ hoO hoZ hπ hfree
      obtain ⟨π', rfl⟩ := G.net.mem_paths_head hπ
      simp only [stepBall, mem_filter, mem_univ, true_and]
      refine ⟨π'.map st, ?_, ?_, ?_⟩
      · have := isDepPath_map G st xs T hedge (o ℓ :: π') (o ℓ) hπ
        simpa [hout] using this
      · simp only [List.length_map]
        simp only [List.length_cons] at hlen
        omega
      · rw [← hout ℓ, ← List.map_cons, getLastD_map st (o ℓ :: π') (o ℓ)]
        exact hrd _ _ hrdj
  · calc (univ.image fun w => ((fun t : ΓF => fun v : nodesAt t.1 => G.val w v),
          (fun q : Q => G.val w q.1), (fun z : Z => G.val w z.1))).card
        ≤ ((Fintype.piFinset fun t : ΓF => univ.image fun w => fun v : nodesAt t.1 => G.val w v) ×ˢ
            ((Fintype.piFinset fun q : Q => univ.image fun w => G.val w q.1) ×ˢ
              (Fintype.piFinset fun z : Z => univ.image fun w => G.val w z.1))).card := by
          refine card_le_card fun e he => ?_
          obtain ⟨w, -, rfl⟩ := mem_image.mp he
          refine mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun t => mem_image.mpr ⟨w, mem_univ _, rfl⟩,
            mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun q => mem_image.mpr ⟨w, mem_univ _, rfl⟩,
              Fintype.mem_piFinset.mpr fun z => mem_image.mpr ⟨w, mem_univ _, rfl⟩⟩⟩
      _ = (∏ t : ΓF, (univ.image fun w => fun v : nodesAt t.1 => G.val w v).card) *
            ((∏ q : Q, (univ.image fun w => G.val w q.1).card) *
              ∏ z : Z, (univ.image fun w => G.val w z.1).card) := by
          rw [card_product, card_product, Fintype.card_piFinset, Fintype.card_piFinset,
            Fintype.card_piFinset]
      _ ≤ (∏ _t : ΓF, 2 ^ β) * ((∏ _q : Q, 2 ^ β) * ∏ _z : Z, 2 ^ β) := by
          gcongr with t _ q _ z _
          · exact hstep t.1 t.2
          · exact hfield q.1
          · exact hfield z.1
      _ = 2 ^ (β * ΓF.card + β * Q.card + β * Z.card) := by
          rw [prod_const, prod_const, prod_const, card_univ, card_univ, card_univ,
            Fintype.card_coe, Fintype.card_coe, Fintype.card_coe, ← pow_mul, ← pow_mul, ← pow_mul,
            ← pow_add, ← pow_add, add_assoc]

end MergeDepth
