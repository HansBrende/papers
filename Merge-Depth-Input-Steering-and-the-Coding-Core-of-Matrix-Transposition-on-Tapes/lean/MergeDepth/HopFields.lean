import MergeDepth.FieldDag
import MergeDepth.HopMachine
import MergeDepth.Capacity

/-!
# Theorem HC′(b): hop charging for all codes

A *refinement* of the dependency DAG of the work-head walks `xs` is a function DAG `G` whose vertices
lie at steps (`st`), at most `m` of them at each step (`nodesAt`), whose edges project to
dependency steps and whose reads are reads of their steps (`rdStep`). The field DAG of a pruning of
a machine is one, with `m = k + 2` (the fourth paper's local recursion).

The ball `B^r(t)` of a step (`stepBall`) is the set of positions read at the ends of the dependency
paths with at most `r` edges from `t`.

* `short_paths`: **Lemma 3.10** for a refinement: there is a set `Q` of checkpoints with
  `τ |Q| ≤ m N_R` such that every `(ΓF, Q)`-free path with `s'` deep merges has at most
  `(s' + 1) τ - 1` deep edges and at most `(s' + 1) τ D` vertices.
* `hop_charging_fields`: **Theorem HC′(b)** for a refinement. For a cold genie `ΓF` and a lineage
  assignment on `G` whose other out-edges are dead, if the `ΓF`-free paths from the output vertices
  of every position outside `X` have at most `s` deep merges, then revealing the vertices of the
  steps of `ΓF`, a set `Q` with `τ |Q| ≤ m N_R`, and the bits of the positions in `X` is an index
  code for a system contained in the balls of radius `(s + 1) τ D` around the output steps; when
  every step of `ΓF` and every vertex take at most `2^β` values, it has at most
  `2^{β |ΓF| + β |Q| + |X|}` code words.
* `hop_charging_fields_heads`: the general form from which `hop_charging_fields` follows: the
  checkpoints can be taken among the heads of deep lineage edges, so only those vertices need to
  take few values (at most `2^βQ`); `card_image_triple_le` counts the code words.
-/

namespace MergeDepth

open Finset BoundedNesting

variable {L k : ℕ}

open Classical in
/-- The ball of radius `r` around step `t` of the dependency DAG: the positions read at the ends of
dependency paths of at most `r` edges from `t`. -/
noncomputable def stepBall (xs : Fin k → ℕ → ℤ) (T : ℕ) (rdStep : ℕ → Option (Fin L)) (r t : ℕ) :
    Finset (Fin L) :=
  univ.filter fun j => ∃ π : List ℕ, IsDepPath xs T (t :: π) ∧ π.length ≤ r ∧
    rdStep ((t :: π).getLastD t) = some j

/-- Paths of a refinement project to dependency paths. -/
theorem isDepPath_map (G : FunDag L) (st : ℕ → ℕ) (xs : Fin k → ℕ → ℤ) (T : ℕ)
    (hedge : ∀ u, ∀ v ∈ G.out u, DepStep xs T (st u) (st v)) :
    ∀ (π : List ℕ) (u : ℕ), π ∈ G.net.paths u → IsDepPath xs T (π.map st)
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: π, u, h => by
    have := head_eq_of_mem_paths h
    subst this
    obtain ⟨hb, hπ⟩ := cons_cons_mem_paths.mp h
    exact ⟨hedge a b hb, isDepPath_map G st xs T hedge (b :: π) b hπ⟩

theorem rCount_map (Rr : ℕ → ℕ → Prop) [DecidableRel Rr] (st : ℕ → ℕ) :
    ∀ π : List ℕ, rCount (fun u v => Rr (st u) (st v)) π = rCount Rr (π.map st)
  | [] => rfl
  | [_] => rfl
  | u :: v :: π => by
    simp only [rCount, List.map_cons]
    rw [rCount_map Rr st (v :: π)]
    rfl

theorem gfree_map {Γ : Finset ℕ} {Γ' : Finset ℕ} {st : ℕ → ℕ} (hΓ : ∀ u, u ∈ Γ' ↔ st u ∈ Γ)
    {π : List ℕ} : LinNet.GFree Γ' π ↔ LinNet.GFree Γ (π.map st) := by
  cases π with
  | nil => simp [LinNet.GFree]
  | cons v π =>
    simp only [LinNet.GFree, List.tail_cons, List.map_cons, List.mem_map]
    constructor
    · rintro h _ ⟨x, hx, rfl⟩ hxΓ
      exact h x hx ((hΓ x).mpr hxΓ)
    · intro h x hx hxΓ
      exact h _ ⟨x, hx, rfl⟩ ((hΓ x).mp hxΓ)

open Classical in
/-- **Lemma 3.10** for a refinement of the dependency DAG (a network whose vertices lie at steps, at
most `m` at each step, and whose edges project to dependency steps): there is a set `Q` with
`τ |Q| ≤ m N_R` such that every `(ΓF, Q)`-free path with `s'` deep merges has at most `(s' + 1) τ - 1`
deep edges and at most `(s' + 1) τ D` vertices. -/
theorem short_paths {F : Type*} [Field F] {m' : ℕ} (net : LinNet F L m') (st : ℕ → ℕ)
    (nodesAt : ℕ → Finset ℕ) {m : ℕ} (hnodes : ∀ u t, u ∈ nodesAt t ↔ st u = t)
    (hwidth : ∀ t, (nodesAt t).card ≤ m) (xs : Fin k → ℕ → ℤ) {T V : ℕ}
    (hedge : ∀ u, ∀ v ∈ net.out u, DepStep xs T (st u) (st v)) {D : ℕ} {ΓF : Finset ℕ}
    (hcold : ∀ π, IsDepPath xs T π → LinNet.GFree ΓF π → rCount (DeepStep xs T V) π = 0 →
      π.length ≤ D)
    (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ net.paths u →
      LinNet.GFree (ΓF.biUnion nodesAt) (u :: v' :: π) →
      rCount (fun u v => DeepStep xs T V (st u) (st v)) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) :
    ∃ Q : Finset ℕ, τ * Q.card ≤ m * (deepHops xs T V).card ∧
      ∀ t π, π ∈ net.paths t → LinNet.GFree (ΓF.biUnion nodesAt ∪ Q) π →
        rCount (fun u v => DeepStep xs T V (st u) (st v)) π + 1 ≤
          (dm lin (fun u v => DeepStep xs T V (st u) (st v)) false π + 1) * τ ∧
        π.length ≤ (dm lin (fun u v => DeepStep xs T V (st u) (st v)) false π + 1) * τ * D := by
  set Γ' := ΓF.biUnion nodesAt
  set Rc : ℕ → ℕ → Prop := fun u v => DeepStep xs T V (st u) (st v)
  have hΓ' : ∀ u, u ∈ Γ' ↔ st u ∈ ΓF := fun u => by
    constructor
    · intro h
      obtain ⟨t, ht, hu⟩ := mem_biUnion.mp h
      rw [(hnodes u t).mp hu]
      exact ht
    · intro h
      exact mem_biUnion.mpr ⟨st u, h, (hnodes u (st u)).mpr rfl⟩
  have hdep : ∀ (π : List ℕ) (u : ℕ), π ∈ net.paths u → IsDepPath xs T (π.map st) := by
    intro π
    induction π with
    | nil => intro _ _; trivial
    | cons a π ih =>
      intro u h
      cases π with
      | nil => trivial
      | cons b π =>
        have := head_eq_of_mem_paths h
        subst this
        obtain ⟨hb, hπ⟩ := cons_cons_mem_paths.mp h
        exact ⟨hedge a b hb, ih b hπ⟩
  have hcold' : ∀ t π, π ∈ net.paths t → LinNet.GFree Γ' π → rCount Rc π = 0 → π.length ≤ D := by
    intro t π hπ hfree hR
    have := hcold (π.map st) (hdep π t hπ) ((gfree_map hΓ').mp hfree)
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
  refine ⟨Q, hQ.trans hMcard, fun t π hπ hfree => ?_⟩
  have h1 := rCount_add_le net Rc lin Γ' hside M hM Q hcov π t [t] (by simp) hπ hfree trivial rfl
    (by simp)
  simp only [rCount, add_zero, lt_irrefl, decide_false] at h1
  have h2 : rCount Rc π + 1 ≤ (dm lin Rc false π + 1) * τ := by
    have : (dm lin Rc false π + 1) * τ = τ + τ * dm lin Rc false π := by ring
    omega
  refine ⟨h2, ?_⟩
  calc π.length ≤ (rCount Rc π + 1) * D :=
        length_le_of_cold net Rc Γ' D hcold' hπ (gfree_mono subset_union_left hfree)
    _ ≤ (dm lin Rc false π + 1) * τ * D := Nat.mul_le_mul_right _ h2

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

open Classical in
/-- **Theorem HC′(b) with cheap checkpoints**, for a refinement of the dependency DAG (the setting
of `hop_charging_fields`). The checkpoints `Q` can be taken among the heads of deep lineage edges
(the covering lemma applied to the deep lineage edges only, as in the paper's proof of Lemma 3.10);
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
    if ℓ ∈ X ∨ o ℓ ∈ Γ' ∪ Q then ∅ else coneI G.net (Γ' ∪ Q) (o ℓ)
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
      simp only [coneI, mem_filter, mem_univ, true_and] at hj
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
/-- **Theorem HC′(b)** for a refinement of the dependency DAG. -/
theorem hop_charging_fields (G : FunDag L) (st : ℕ → ℕ) (nodesAt : ℕ → Finset ℕ) {m : ℕ}
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
    {τ : ℕ} (hτ : 1 ≤ τ) (s : ℕ) (o : Fin L → ℕ) (tout : Fin L → ℕ) (hout : ∀ ℓ, st (o ℓ) = tout ℓ)
    (tpos : Fin L → Fin L) (dec : Fin L → ℕ → Bool) (hdec : ∀ w ℓ, dec ℓ (G.val w (o ℓ)) = w (tpos ℓ))
    (X : Finset (Fin L))
    (hround : ∀ ℓ ∉ X, ∀ π, π ∈ G.net.paths (o ℓ) → LinNet.GFree (ΓF.biUnion nodesAt) π →
      dm lin (fun u v => DeepStep xs T V (st u) (st v)) false π ≤ s) :
    ∃ (Q : Finset ℕ) (I : Fin L → Finset (Fin L)), τ * Q.card ≤ m * (deepHops xs T V).card ∧
      IsIndexCode (fun w => ((fun t : ΓF => fun v : nodesAt t.1 => G.val w v),
        (fun q : Q => G.val w q.1), (fun ℓ : X => w (tpos ℓ.1)))) I tpos ∧
      (∀ ℓ, I ℓ ⊆ stepBall xs T rdStep ((s + 1) * τ * D) (tout ℓ)) ∧
      (univ.image fun w => ((fun t : ΓF => fun v : nodesAt t.1 => G.val w v),
        (fun q : Q => G.val w q.1), (fun ℓ : X => w (tpos ℓ.1)))).card ≤
        2 ^ (β * ΓF.card + β * Q.card + X.card) := by
  obtain ⟨Q, I, hQ, -, hcode, hball, himg⟩ := hop_charging_fields_heads G st nodesAt hnodes hwidth
    xs hedge rdStep hrd hcold hstep lin (fun _ v _ _ => hfield v) hside hτ s o tout hout tpos dec
    hdec X hround
  exact ⟨Q, I, hQ, hcode, hball, himg⟩

end MergeDepth
