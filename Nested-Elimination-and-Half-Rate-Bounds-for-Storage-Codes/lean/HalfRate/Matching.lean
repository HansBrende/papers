import HalfRate.Barrier
import Mathlib.Combinatorics.Hall.Basic

/-!
# Fractional matchings and the guessing number

* `fracWeight_le_barrier`: a fractional matching weighs at most `(|V| + |S| − |I(S)|)/2` for every
  vertex set `S` (weak duality).
* `exists_doubleCover_matching`: Hall's theorem on the bipartite double cover, with as many dummy
  vertices as the largest deficiency, gives an injective map `g` on a set `D` sending each vertex
  to a neighbour, and a set `S` (the neighbours of a most deficient set, minus that set) with
  `|D| ≥ |V| + |S| − |I(S)|`.
* `fracMatchingNumber`: the fractional matching number `ν*(G)`, attained, half-integral, and equal
  to `min_S (|V| + |S| − |I(S)|)/2` (`fracMatchingNumber_eq_min_barrier`, the fractional
  Tutte–Berge formula).
* `exists_code_fracMatchingNumber`: on every graph, a storage code over `β × β` with at least
  `|β × β|^{ν*}` words (each vertex shares one half of its symbol with `g v` and receives one from
  its preimage).
* `guessingNumber_eq_fracMatching`: on triangle-free graphs of maximum degree three, every storage
  code satisfies `|C| ≤ |α|^{ν*}`, with equality attained over every alphabet `β × β`: the
  guessing number equals the fractional matching number.
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A fractional matching: symmetric nonnegative weights supported on the edges, of total weight
at most one at every vertex. -/
structure IsFracMatching (G : SimpleGraph V) (y : V → V → ℝ) : Prop where
  nonneg : ∀ u v, 0 ≤ y u v
  symm : ∀ u v, y u v = y v u
  adj : ∀ u v, ¬ G.Adj u v → y u v = 0
  le_one : ∀ v, ∑ u, y v u ≤ 1

/-- The total weight of `y`, each edge counted once. -/
noncomputable def fracWeight (y : V → V → ℝ) : ℝ := (∑ u, ∑ v, y u v) / 2

/-- **Weak duality.** -/
theorem fracWeight_le_barrier {y : V → V → ℝ} (hy : IsFracMatching G y) (S : Finset V) :
    2 * fracWeight y ≤ (Fintype.card V : ℝ) + S.card - (isolatedOut G S).card := by
  unfold fracWeight
  have hsplit : ∑ u, ∑ v, y u v =
      ∑ u ∈ isolatedOut G S, ∑ v, y u v + ∑ u ∈ univ \ isolatedOut G S, ∑ v, y u v := by
    rw [← sum_union disjoint_sdiff, union_sdiff_of_subset (subset_univ _)]
  have hI : ∑ u ∈ isolatedOut G S, ∑ v, y u v ≤ S.card := by
    calc ∑ u ∈ isolatedOut G S, ∑ v, y u v = ∑ u ∈ isolatedOut G S, ∑ v ∈ S, y u v := by
          refine sum_congr rfl fun u hu => ?_
          rw [← sum_subset (subset_univ S)]
          intro v _ hvS
          apply hy.adj
          intro hadj
          exact hvS ((mem_filter.mp hu).2.2 (by simp [nbhd, hadj]))
      _ ≤ ∑ u, ∑ v ∈ S, y u v :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _)
            (fun u _ _ => sum_nonneg fun v _ => hy.nonneg u v)
      _ = ∑ v ∈ S, ∑ u, y u v := sum_comm
      _ = ∑ v ∈ S, ∑ u, y v u :=
          sum_congr rfl fun v _ => sum_congr rfl fun u _ => hy.symm u v
      _ ≤ ∑ _v ∈ S, (1 : ℝ) := sum_le_sum fun v _ => hy.le_one v
      _ = S.card := by simp
  have hR : ∑ u ∈ univ \ isolatedOut G S, ∑ v, y u v ≤ (univ \ isolatedOut G S).card := by
    calc ∑ u ∈ univ \ isolatedOut G S, ∑ v, y u v ≤ ∑ _u ∈ univ \ isolatedOut G S, (1 : ℝ) :=
          sum_le_sum fun u _ => hy.le_one u
      _ = _ := by simp
  have hcard : ((univ \ isolatedOut G S).card : ℝ) = Fintype.card V - (isolatedOut G S).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    push_cast [Nat.cast_sub (card_le_univ (isolatedOut G S))]
    ring
  linarith

/-- **Hall's theorem on the bipartite double cover.** -/
theorem exists_doubleCover_matching (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (D : Finset V) (g : V → V) (S : Finset V), (∀ v ∈ D, G.Adj v (g v)) ∧ Set.InjOn g D ∧
      (Fintype.card V : ℝ) + S.card - (isolatedOut G S).card ≤ D.card := by
  classical
  -- a set of largest deficiency `|X| − |N(X)|`
  obtain ⟨X₀, -, hmax⟩ := exists_max_image (univ : Finset (Finset V))
    (fun X => (X.card : ℤ) - (X.biUnion (nbhd G)).card) ⟨∅, mem_univ _⟩
  have hd0 : (0 : ℤ) ≤ X₀.card - (X₀.biUnion (nbhd G)).card := by
    have := hmax ∅ (mem_univ _); simpa using this
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = X₀.card - (X₀.biUnion (nbhd G)).card :=
    ⟨_, Int.toNat_of_nonneg hd0⟩
  -- Hall's condition with `d` dummy neighbours
  let t : V → Finset (V ⊕ Fin d) := fun v => (nbhd G v).disjSum univ
  have hall : ∀ X : Finset V, X.card ≤ (X.biUnion t).card := by
    intro X
    rcases X.eq_empty_or_nonempty with rfl | hX
    · simp
    · have hb : X.biUnion t = (X.biUnion (nbhd G)).disjSum univ := by
        ext x
        rcases x with w | i
        · simp [t, mem_biUnion]
        · simp only [t, mem_biUnion, inr_mem_disjSum, mem_univ, and_true]
          exact ⟨fun _ => trivial, fun _ => hX⟩
      rw [hb, card_disjSum, card_univ, Fintype.card_fin]
      have := hmax X (mem_univ _)
      omega
  obtain ⟨φ, hφinj, hφt⟩ := (all_card_le_biUnion_card_iff_exists_injective t).mp hall
  -- the matched vertices and their partners
  let D : Finset V := univ.filter (fun v => (φ v).isLeft)
  let g : V → V := fun v => Sum.elim id (fun _ => v) (φ v)
  have hφD : ∀ v ∈ D, φ v = Sum.inl (g v) := by
    intro v hv
    have := (mem_filter.mp hv).2
    rcases h : φ v with w | i
    · simp [g, h]
    · rw [h] at this; simp at this
  refine ⟨D, g, X₀.biUnion (nbhd G) \ X₀, ?_, ?_, ?_⟩
  · intro v hv
    have h1 := hφt v
    rw [hφD v hv] at h1
    simpa [t, nbhd] using h1
  · intro u hu v hv huv
    apply hφinj
    rw [hφD u hu, hφD v hv, huv]
  · -- at most `d` unmatched vertices
    have hunm : (univ \ D).card ≤ d := by
      have := card_le_card_of_injOn φ (s := univ \ D)
        (t := (∅ : Finset V).disjSum (univ : Finset (Fin d)))
        (fun v hv => by
          have hv' : ¬ (φ v).isLeft := by simpa [D] using hv
          rcases h : φ v with w | i
          · rw [h] at hv'; simp at hv'
          · simp)
        (fun a _ b _ hab => hφinj hab)
      simpa [card_disjSum] using this
    have hDc : (D.card : ℝ) ≥ Fintype.card V - d := by
      have h1 : (univ \ D).card = Fintype.card V - D.card := by
        rw [card_sdiff_of_subset (subset_univ D), card_univ]
      have h2 : D.card ≤ Fintype.card V := card_le_univ D
      have : Fintype.card V ≤ D.card + d := by omega
      have : (Fintype.card V : ℝ) ≤ D.card + d := by exact_mod_cast this
      linarith
    -- the isolated vertices of `G − S` contain `X₀ \ N(X₀)`
    have hsub : X₀ \ X₀.biUnion (nbhd G) ⊆ isolatedOut G (X₀.biUnion (nbhd G) \ X₀) := by
      intro v hv
      obtain ⟨hvX, hvN⟩ := mem_sdiff.mp hv
      simp only [isolatedOut, mem_filter, mem_univ, true_and, mem_sdiff, not_and, not_not]
      refine ⟨fun _ => hvX, fun u hu => mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨v, hvX, hu⟩, fun huX => ?_⟩⟩
      apply hvN
      refine mem_biUnion.mpr ⟨u, huX, ?_⟩
      have : G.Adj v u := by simpa [nbhd] using hu
      simpa [nbhd] using this.symm
    have hI := card_le_card hsub
    have e1 := card_sdiff_add_card_inter (X₀.biUnion (nbhd G)) X₀
    have e2 := card_sdiff_add_card_inter X₀ (X₀.biUnion (nbhd G))
    rw [inter_comm] at e2
    have hdR : (d : ℝ) = X₀.card - (X₀.biUnion (nbhd G)).card := by exact_mod_cast hd
    have e1' : ((X₀.biUnion (nbhd G) \ X₀).card : ℝ) + (X₀.biUnion (nbhd G) ∩ X₀).card =
        (X₀.biUnion (nbhd G)).card := by exact_mod_cast e1
    have e2' : ((X₀ \ X₀.biUnion (nbhd G)).card : ℝ) + (X₀.biUnion (nbhd G) ∩ X₀).card =
        X₀.card := by exact_mod_cast e2
    have hI' : ((X₀ \ X₀.biUnion (nbhd G)).card : ℝ) ≤
        (isolatedOut G (X₀.biUnion (nbhd G) \ X₀)).card := by exact_mod_cast hI
    linarith

/-- The fractional matching of a double-cover matching: weight `½` per direction. -/
noncomputable def dcFrac (D : Finset V) (g : V → V) : V → V → ℝ := fun u v =>
  ((if u ∈ D ∧ g u = v then 1 else 0) + (if v ∈ D ∧ g v = u then 1 else 0)) / 2

omit [DecidableRel G.Adj] in
theorem dcFrac_isFracMatching {D : Finset V} {g : V → V} (hadj : ∀ v ∈ D, G.Adj v (g v))
    (hinj : Set.InjOn g D) : IsFracMatching G (dcFrac D g) := by
  refine ⟨fun u v => ?_, fun u v => ?_, fun u v huv => ?_, fun v => ?_⟩
  · unfold dcFrac; positivity
  · unfold dcFrac; ring
  · unfold dcFrac
    have h1 : ¬ (u ∈ D ∧ g u = v) := fun h => huv (h.2 ▸ hadj u h.1)
    have h2 : ¬ (v ∈ D ∧ g v = u) := fun h => huv (h.2 ▸ (hadj v h.1).symm)
    simp [h1, h2]
  · unfold dcFrac
    rw [← sum_div, sum_add_distrib, sum_boole, sum_boole]
    have c1 : (univ.filter (fun u => v ∈ D ∧ g v = u)).card ≤ 1 := by
      rw [card_le_one]; intro a ha b hb
      simp only [mem_filter, mem_univ, true_and] at ha hb
      rw [← ha.2, ← hb.2]
    have c2 : (univ.filter (fun u => u ∈ D ∧ g u = v)).card ≤ 1 := by
      rw [card_le_one]; intro a ha b hb
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact hinj ha.1 hb.1 (ha.2.trans hb.2.symm)
    have c1' : ((univ.filter (fun u => v ∈ D ∧ g v = u)).card : ℝ) ≤ 1 := by exact_mod_cast c1
    have c2' : ((univ.filter (fun u => u ∈ D ∧ g u = v)).card : ℝ) ≤ 1 := by exact_mod_cast c2
    rw [div_le_one (by norm_num)]
    linarith

theorem fracWeight_dcFrac (D : Finset V) (g : V → V) :
    fracWeight (dcFrac D g) = D.card / 2 := by
  have h1 : ∀ u, ∑ v, (if u ∈ D ∧ g u = v then (1 : ℝ) else 0) = if u ∈ D then 1 else 0 := by
    intro u
    by_cases hu : u ∈ D <;> simp [hu]
  have h2 : ∑ u, ∑ v, (if v ∈ D ∧ g v = u then (1 : ℝ) else 0) = D.card := by
    rw [sum_comm]
    simp only [h1, sum_boole]
    simp
  unfold fracWeight dcFrac
  simp only [← sum_div, sum_add_distrib]
  rw [h2]
  simp only [h1, sum_boole]
  simp

/-- The fractional matching number. -/
noncomputable def fracMatchingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup {w | ∃ y, IsFracMatching G y ∧ fracWeight y = w}

/-- **The fractional matching number is attained by a double-cover matching and meets the
barrier bound.** -/
theorem fracMatchingNumber_spec (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (D : Finset V) (g : V → V) (S : Finset V), (∀ v ∈ D, G.Adj v (g v)) ∧ Set.InjOn g D ∧
      fracMatchingNumber G = D.card / 2 ∧
      (Fintype.card V : ℝ) + S.card - (isolatedOut G S).card = D.card ∧
      IsGreatest {w | ∃ y, IsFracMatching G y ∧ fracWeight y = w} (fracMatchingNumber G) := by
  obtain ⟨D, g, S, hadj, hinj, hle⟩ := exists_doubleCover_matching G
  have hfm := dcFrac_isFracMatching hadj hinj
  have hge : (D.card : ℝ) ≤ (Fintype.card V : ℝ) + S.card - (isolatedOut G S).card := by
    have := fracWeight_le_barrier hfm S
    rw [fracWeight_dcFrac] at this
    linarith
  have hgreat : IsGreatest {w | ∃ y, IsFracMatching G y ∧ fracWeight y = w} (D.card / 2) := by
    refine ⟨⟨dcFrac D g, hfm, fracWeight_dcFrac D g⟩, ?_⟩
    rintro w ⟨y, hy, rfl⟩
    have := fracWeight_le_barrier hy S
    linarith
  have heq : fracMatchingNumber G = D.card / 2 := hgreat.csSup_eq
  exact ⟨D, g, S, hadj, hinj, heq, le_antisymm hle hge, heq ▸ hgreat⟩

/-- **The fractional Tutte–Berge formula.** `2 ν*(G) = min_S (|V| + |S| − |I(S)|)`. -/
theorem fracMatchingNumber_eq_min_barrier (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∀ S : Finset V, 2 * fracMatchingNumber G ≤
        (Fintype.card V : ℝ) + S.card - (isolatedOut G S).card) ∧
      ∃ S : Finset V,
        2 * fracMatchingNumber G = (Fintype.card V : ℝ) + S.card - (isolatedOut G S).card := by
  obtain ⟨D, g, S, hadj, hinj, heq, hS, -⟩ := fracMatchingNumber_spec G
  refine ⟨fun S' => ?_, ⟨S, by rw [heq, hS]; ring⟩⟩
  have := fracWeight_le_barrier (dcFrac_isFracMatching hadj hinj) S'
  rw [fracWeight_dcFrac] at this
  rw [heq]; linarith

/-- **Converse.** On a triangle-free graph of maximum degree three every storage code satisfies
`|C| ≤ |α|^{ν*}`. -/
theorem log_card_le_fracMatchingNumber {α : Type*} [Fintype α] [Nonempty α]
    (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) {C : Finset (V → α)}
    (hC : IsStorageCode (nbhd G) C) :
    Real.log C.card ≤ fracMatchingNumber G * Real.log (Fintype.card α) := by
  obtain ⟨D, g, S, -, -, heq, hS, -⟩ := fracMatchingNumber_spec G
  have := log_card_le_barrier hcf hdeg hC S
  rw [hS] at this
  rw [heq]
  linarith

/-- **Codes from double-cover matchings.** On every graph there is a storage code over `β × β`
with at least `|β × β|^{ν*}` words. -/
theorem exists_code_fracMatchingNumber (β : Type*) [Fintype β] [Nonempty β] [DecidableEq β] :
    ∃ C : Finset (V → β × β), IsStorageCode (nbhd G) C ∧
      fracMatchingNumber G * Real.log (Fintype.card (β × β)) ≤ Real.log C.card := by
  classical
  obtain ⟨D, g, S, hadj, hinj, heq, -, -⟩ := fracMatchingNumber_spec G
  obtain ⟨b₀⟩ := (inferInstance : Nonempty β)
  -- the code: `v ∈ D` repeats the first half of `g v` in its second half; free halves are `b₀`
  let C : Finset (V → β × β) := univ.filter (fun x => ∀ v,
    (v ∈ D → (x v).2 = (x (g v)).1) ∧ (v ∉ D → (x v).2 = b₀) ∧ (v ∉ D.image g → (x v).1 = b₀))
  have hadjN : ∀ v ∈ D, g v ∈ nbhd G v := fun v hv => by simpa [nbhd] using hadj v hv
  have hadjN' : ∀ v ∈ D, v ∈ nbhd G (g v) := fun v hv => by simpa [nbhd] using (hadj v hv).symm
  refine ⟨C, ?_, ?_⟩
  · intro x hx y hy v hxy
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    apply Prod.ext
    · by_cases hv : v ∈ D.image g
      · obtain ⟨u, hu, rfl⟩ := mem_image.mp hv
        rw [← (hx' u).1 hu, ← (hy' u).1 hu, hxy u (hadjN' u hu)]
      · rw [(hx' v).2.2 hv, (hy' v).2.2 hv]
    · by_cases hv : v ∈ D
      · rw [(hx' v).1 hv, (hy' v).1 hv, hxy (g v) (hadjN v hv)]
      · rw [(hx' v).2.1 hv, (hy' v).2.1 hv]
  · -- an injection from `D → β` into the code
    have hpre : ∀ v (h : v ∈ D.image g), (Classical.choose (mem_image.mp h)) ∈ D ∧
        g (Classical.choose (mem_image.mp h)) = v := fun v h =>
      Classical.choose_spec (mem_image.mp h)
    let ι : (D → β) → (V → β × β) := fun a v =>
      (if h : v ∈ D.image g then a ⟨Classical.choose (mem_image.mp h), (hpre v h).1⟩ else b₀,
       if h : v ∈ D then a ⟨v, h⟩ else b₀)
    have hιC : ∀ a, ι a ∈ C := by
      intro a
      refine mem_filter.mpr ⟨mem_univ _, fun v => ⟨fun hv => ?_, fun hv => ?_, fun hv => ?_⟩⟩
      · have hg : g v ∈ D.image g := mem_image_of_mem g hv
        have hpv : Classical.choose (mem_image.mp hg) = v :=
          hinj (hpre (g v) hg).1 hv (hpre (g v) hg).2
        simp only [ι, hv, hg, ↓reduceDIte]
        congr 1
        exact Subtype.ext hpv.symm
      · simp [ι, hv]
      · simp [ι, hv]
    have hιinj : Function.Injective ι := by
      intro a a' h
      funext ⟨v, hv⟩
      have := congrArg (fun x => (x v).2) h
      simpa [ι, hv] using this
    have hcard : (Fintype.card β) ^ D.card ≤ C.card := by
      have := card_le_card_of_injOn ι (s := (univ : Finset (D → β))) (t := C)
        (fun a _ => hιC a) (fun a _ b _ hab => hιinj hab)
      simpa [Fintype.card_fun, Fintype.card_coe] using this
    have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
    have hpos : (0 : ℝ) < (Fintype.card β : ℝ) ^ D.card := by positivity
    have hlog : D.card * Real.log (Fintype.card β) ≤ Real.log C.card := by
      rw [← Real.log_pow]
      exact Real.log_le_log hpos (by exact_mod_cast hcard)
    rw [heq, Fintype.card_prod, Nat.cast_mul, Real.log_mul hβ.ne' hβ.ne']
    linarith

/-- **The guessing number equals the fractional matching number** on triangle-free graphs of
maximum degree three: every storage code over every alphabet has `|C| ≤ |α|^{ν*}`, and over every
alphabet `β × β` some storage code has exactly `|β × β|^{ν*}` words. -/
theorem guessingNumber_eq_fracMatching (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    IsGreatest {w | ∃ y, IsFracMatching G y ∧ fracWeight y = w} (fracMatchingNumber G) ∧
      (∀ (α : Type*) [Fintype α] [Nonempty α] (C : Finset (V → α)), IsStorageCode (nbhd G) C →
        Real.log C.card ≤ fracMatchingNumber G * Real.log (Fintype.card α)) ∧
      (∀ (β : Type*) [Fintype β] [Nonempty β] [DecidableEq β], ∃ C : Finset (V → β × β),
        IsStorageCode (nbhd G) C ∧
          Real.log C.card = fracMatchingNumber G * Real.log (Fintype.card (β × β))) := by
  refine ⟨(fracMatchingNumber_spec G).choose_spec.choose_spec.choose_spec.2.2.2.2,
    fun α _ _ C hC => log_card_le_fracMatchingNumber hcf hdeg hC, fun β _ _ _ => ?_⟩
  obtain ⟨C, hC, hge⟩ := exists_code_fracMatchingNumber (G := G) β
  exact ⟨C, hC, le_antisymm (log_card_le_fracMatchingNumber hcf hdeg hC) hge⟩

end HalfRate
