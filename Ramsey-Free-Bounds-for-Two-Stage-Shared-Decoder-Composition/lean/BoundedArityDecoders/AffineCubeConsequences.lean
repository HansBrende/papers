import BoundedArityDecoders.AffineCubeCompositionProofs

/-!
# Consequences & Controls — Part II.A: Single-Subset Cube Extraction, General-Field `d = 13`
# Bridge, and All-Width / Binary `d = 4` Factorization

This module establishes the structural consequences and general-field controls accompanying
Theorem 2A (`BoundedArityDecoders.AffineCubeCompositionProofs`):

1. `singleSubset_CauchySchwarzAffineCubeExtraction`, `denseSubset_AffineCubeCommonMessageBound`,
   and `theorem2A_GrowingClassesNonFactorization`: single-subset Cauchy–Schwarz `k`-cube
   extraction inside any dense subset `J ⊆ ZMod d` (`d ≤ M_eff * J.card`, even when `J.card < d / 2`
   or `ThreeAPFreeMod J`), dense-subset common-message bounds, single-dense-class impossibility,
   and growing-class non-factorization `M₁(d), M₂(d)`.
2. `control_D13_GeneralFieldAndProgressionBridge`: exact cyclic shift kernel dimension `2` over
   every field, Paper 19 `commonMessage_finrank_le` sharpness (`D = 14`) on every 2-point
   progression over every field, and the `D = 9` affine 2-cube witness on `J = {0, 1, 4, 5}` over
   every field `F` with `(13 : F) ≠ 0`.
3. `IsBitLaneCopyClassRule` and `control_D4_AllWidthsAndBinaryFields`: impossibility of uncoded
   bit-lane copy factorizations on `State 4 (Fin b → Sigma)` at all widths `b ≥ 1` and alphabets
   `|Sigma| ≥ 2`, contrasted with exact linear `ClassUniform` factorizations over characteristic-`2`
   fields (`(2 : F) = 0`), fields with `(20 : F) ≠ 0`, and hence every field with `(5 : F) ≠ 0` at
   all widths `b ≥ 0`.
-/

namespace BoundedArityDecoders

open SharedDecoders Module
open scoped BigOperators

/-! ### 1. Single-Subset Cauchy–Schwarz Cube Extraction & Growing-Class Theorem 2A -/

section SingleSubsetAndGrowingClasses

private theorem nat_cs_range : ∀ (Q : ℕ) (a : ℕ → ℕ),
    (∑ r ∈ Finset.range Q, a r) ^ 2 ≤ Q * ∑ r ∈ Finset.range Q, a r ^ 2
  | 0, _ => by simp
  | Q + 1, a => by
      have ih := nat_cs_range Q a
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      by_cases hQ : Q = 0
      · subst hQ; simp
      · have hQpos : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hQ
        zify at ih ⊢
        nlinarith [sq_nonneg ((∑ r ∈ Finset.range Q, (a r : ℤ)) - (Q : ℤ) * (a Q : ℤ))]

private theorem card_lt_pairs (B : Finset ℕ) :
    2 * ((B ×ˢ B).filter (fun p : ℕ × ℕ => p.1 < p.2)).card + B.card = B.card ^ 2 := by
  let ltS := (B ×ˢ B).filter (fun p : ℕ × ℕ => p.1 < p.2)
  let gtS := (B ×ˢ B).filter (fun p : ℕ × ℕ => p.2 < p.1)
  let eqS := (B ×ˢ B).filter (fun p : ℕ × ℕ => p.1 = p.2)
  have hbij : ltS.card = gtS.card := Finset.card_bij (fun p _ => (p.2, p.1))
    (fun p hp => by simp only [ltS, gtS, Finset.mem_filter, Finset.mem_product] at hp ⊢; exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩)
    (fun p₁ _ p₂ _ h => by ext <;> simp_all)
    (fun p hp => ⟨(p.2, p.1), by simp only [ltS, gtS, Finset.mem_filter, Finset.mem_product] at hp ⊢; exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩, by simp⟩)
  have heq : eqS.card = B.card := Finset.card_bij (fun p _ => p.1)
    (fun p hp => by simp only [eqS, Finset.mem_filter, Finset.mem_product] at hp; exact hp.1.1)
    (fun p₁ hp₁ p₂ hp₂ h => by simp only [eqS, Finset.mem_filter, Finset.mem_product] at hp₁ hp₂; ext; exact h; exact hp₁.2.symm.trans (h.trans hp₂.2))
    (fun x hx => ⟨(x, x), by simp [eqS, hx], rfl⟩)
  have hd1 : Disjoint ltS gtS := Finset.disjoint_left.mpr fun p h1 h2 => by
    simp only [ltS, gtS, Finset.mem_filter] at h1 h2; omega
  have hd2 : Disjoint (ltS ∪ gtS) eqS := Finset.disjoint_left.mpr fun p h12 h3 => by
    simp only [ltS, gtS, eqS, Finset.mem_union, Finset.mem_filter] at h12 h3
    rcases h12 with h1 | h2 <;> omega
  have hun : (ltS ∪ gtS) ∪ eqS = B ×ˢ B := by
    ext p; simp only [ltS, gtS, eqS, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    exact ⟨fun h => by rcases h with ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h,
      fun hp => by rcases lt_trichotomy p.1 p.2 with h | h | h; exact Or.inl (Or.inl ⟨hp, h⟩); exact Or.inr ⟨hp, h⟩; exact Or.inl (Or.inr ⟨hp, h⟩)⟩
  have htot := congrArg Finset.card hun
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
    Finset.card_product, ← hbij, heq] at htot
  change 2 * ltS.card + B.card = B.card ^ 2; rw [sq]; omega

private theorem single_cs_step {d Q : ℕ} (hQ : 0 < Q) (hQL : Q ≤ d)
    {S : Finset ℕ} (hS : S ⊆ Finset.range d) :
    ∃ s : ℕ, (1 ≤ s ∧ s ≤ d / Q) ∧
      S.card * (S.card - Q) ≤ 2 * d * (S.filter (fun x => x + s ∈ S)).card := by
  let L₀ := d / Q
  have hL₀ : 1 ≤ L₀ := Nat.div_pos hQL hQ
  by_cases hN : S.card ≤ Q
  · exact ⟨1, ⟨le_rfl, hL₀⟩, by simp [Nat.sub_eq_zero_of_le hN]⟩
  let B : ℕ → Finset ℕ := fun r => S.filter (fun x => x / (L₀ + 1) = r)
  have hpart : (Finset.range Q).biUnion B = S := by
    ext x; simp only [Finset.mem_biUnion, Finset.mem_range, B, Finset.mem_filter]
    refine ⟨fun ⟨_, _, hx, _⟩ => hx, fun hx => ⟨x / (L₀ + 1), ?_, hx, rfl⟩⟩
    have hxd : x < d := Finset.mem_range.mp (hS hx)
    have hmod := Nat.div_add_mod d Q; have hrem := Nat.mod_lt d hQ
    change Q * L₀ + d % Q = d at hmod
    exact Nat.div_lt_of_lt_mul (by nlinarith)
  have hdisjB : Set.PairwiseDisjoint (↑(Finset.range Q) : Set ℕ) B := fun r₁ _ r₂ _ hne =>
    Finset.disjoint_left.mpr fun x hx1 hx2 => by
      simp only [B, Finset.mem_filter] at hx1 hx2; exact hne (hx1.2.symm.trans hx2.2)
  have hsumA : ∑ r ∈ Finset.range Q, (B r).card = S.card := by
    rw [← Finset.card_biUnion hdisjB, hpart]
  let bPairs := (Finset.range Q).biUnion fun r => (B r ×ˢ B r).filter (fun p : ℕ × ℕ => p.1 < p.2)
  have hdisjP : Set.PairwiseDisjoint (↑(Finset.range Q) : Set ℕ)
      (fun r => (B r ×ˢ B r).filter (fun p : ℕ × ℕ => p.1 < p.2)) := fun r₁ _ r₂ _ hne =>
    Finset.disjoint_left.mpr fun p hp1 hp2 => by
      simp only [Finset.mem_filter, Finset.mem_product, B] at hp1 hp2
      exact hne (hp1.1.1.2.symm.trans hp2.1.1.2)
  have hcardP : 2 * bPairs.card + S.card = ∑ r ∈ Finset.range Q, (B r).card ^ 2 := by
    rw [Finset.card_biUnion hdisjP, Finset.mul_sum, ← hsumA, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => card_lt_pairs (B r)
  let sPairs := (Finset.Icc 1 L₀).biUnion fun s =>
    (S.filter (fun x => x + s ∈ S)).map ⟨fun x => (s, x), fun _ _ h => (Prod.mk.inj h).2⟩
  have hdisjS : Set.PairwiseDisjoint (↑(Finset.Icc 1 L₀) : Set ℕ)
      (fun s => (S.filter (fun x => x + s ∈ S)).map ⟨fun x => (s, x), fun _ _ h => (Prod.mk.inj h).2⟩) :=
    fun s₁ _ s₂ _ hne => Finset.disjoint_left.mpr fun p hp1 hp2 => by
      simp only [Finset.mem_map] at hp1 hp2; obtain ⟨_, _, hx₁⟩ := hp1; obtain ⟨_, _, hx₂⟩ := hp2
      exact hne ((congrArg Prod.fst hx₁).trans (congrArg Prod.fst hx₂).symm)
  have hcardS : sPairs.card = ∑ s ∈ Finset.Icc 1 L₀, (S.filter (fun x => x + s ∈ S)).card := by
    rw [Finset.card_biUnion hdisjS]; exact Finset.sum_congr rfl fun _ _ => Finset.card_map _
  have hinj : bPairs.card ≤ sPairs.card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (p.2 - p.1, p.1))
    · intro p hp
      change p ∈ (Finset.range Q).biUnion _ at hp
      obtain ⟨r, _, hp⟩ := Finset.mem_biUnion.mp hp
      rw [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hxB, hyB⟩, hxy⟩ := hp
      simp only [B, Finset.mem_filter] at hxB hyB
      have hxlo : r * (L₀ + 1) ≤ p.1 := by have := Nat.div_mul_le_self p.1 (L₀ + 1); rwa [hxB.2] at this
      have hyhi : p.2 < (r + 1) * (L₀ + 1) := (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)
      have hs2 : p.2 - p.1 ≤ L₀ := by
        have : p.2 < p.1 + (L₀ + 1) := by nlinarith
        omega
      change (p.2 - p.1, p.1) ∈ (Finset.Icc 1 L₀).biUnion _
      refine Finset.mem_biUnion.mpr ⟨p.2 - p.1, Finset.mem_Icc.mpr ⟨by omega, hs2⟩, ?_⟩
      refine Finset.mem_map.mpr ⟨p.1, Finset.mem_filter.mpr ⟨hxB.1, ?_⟩, rfl⟩
      rw [show p.1 + (p.2 - p.1) = p.2 by omega]; exact hyB.1
    · intro p₁ hp₁ p₂ hp₂ heq
      change p₁ ∈ (Finset.range Q).biUnion _ at hp₁
      change p₂ ∈ (Finset.range Q).biUnion _ at hp₂
      obtain ⟨_, _, hp₁⟩ := Finset.mem_biUnion.mp hp₁
      obtain ⟨_, _, hp₂⟩ := Finset.mem_biUnion.mp hp₂
      have h1 := (Finset.mem_filter.mp hp₁).2; have h2 := (Finset.mem_filter.mp hp₂).2
      have hf : p₁.2 - p₁.1 = p₂.2 - p₂.1 := congrArg Prod.fst heq
      have hs : p₁.1 = p₂.1 := congrArg Prod.snd heq
      ext; exact hs; omega
  have hcs := nat_cs_range Q (fun r => (B r).card); rw [hsumA] at hcs
  have hstepB : S.card * (S.card - Q) ≤ 2 * Q * sPairs.card := by
    have hle : Q * (2 * bPairs.card + S.card) ≤ Q * (2 * sPairs.card + S.card) :=
      Nat.mul_le_mul_left Q (by omega)
    rw [hcardP] at hle
    have hsub : S.card * (S.card - Q) + Q * S.card = S.card ^ 2 := by
      have : S.card * (S.card - Q) + S.card * Q = S.card * (S.card - Q + Q) := (Nat.mul_add _ _ _).symm
      have : S.card - Q + Q = S.card := by omega
      nlinarith
    nlinarith
  obtain ⟨s, hsIcc, hsMax⟩ := Finset.exists_max_image (Finset.Icc 1 L₀)
    (fun s => (S.filter (fun x => x + s ∈ S)).card) (Finset.nonempty_Icc.mpr hL₀)
  have hsumLe : sPairs.card ≤ L₀ * (S.filter (fun x => x + s ∈ S)).card := by
    rw [hcardS]
    calc ∑ s' ∈ Finset.Icc 1 L₀, (S.filter (fun x => x + s' ∈ S)).card
      _ ≤ ∑ _ ∈ Finset.Icc 1 L₀, (S.filter (fun x => x + s ∈ S)).card :=
          Finset.sum_le_sum fun s' hs' => hsMax s' hs'
      _ = L₀ * (S.filter (fun x => x + s ∈ S)).card := by simp [Nat.card_Icc, show L₀ + 1 - 1 = L₀ by omega]
  have hQLd : Q * L₀ ≤ d := Nat.mul_div_le d Q
  refine ⟨s, Finset.mem_Icc.mp hsIcc, ?_⟩
  calc S.card * (S.card - Q) ≤ 2 * Q * (L₀ * (S.filter (fun x => x + s ∈ S)).card) :=
        le_trans hstepB (Nat.mul_le_mul_left (2 * Q) hsumLe)
    _ = 2 * (Q * L₀) * (S.filter (fun x => x + s ∈ S)).card := by ring
    _ ≤ 2 * d * (S.filter (fun x => x + s ∈ S)).card :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hQLd)

private def singleCubeDenom (M t : ℕ) : ℚ :=
  (2 : ℚ) ^ (2 ^ t - 1) * (M : ℚ) ^ (2 ^ t)

private theorem singleCubeDenom_succ (M t : ℕ) :
    singleCubeDenom M (t + 1) = 2 * (singleCubeDenom M t) ^ 2 := by
  unfold singleCubeDenom
  have hpos : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hexp1 : 2 ^ (t + 1) - 1 = 1 + (2 ^ t - 1) * 2 := by rw [pow_succ']; omega
  have hexp2 : 2 ^ (t + 1) = (2 ^ t) * 2 := by rw [pow_succ']; ring
  rw [hexp1, hexp2, pow_add, pow_one, pow_mul, pow_mul]; ring

private theorem singleCubeDenom_pos {M : ℕ} (hM : 1 ≤ M) (t : ℕ) : 0 < singleCubeDenom M t := by
  unfold singleCubeDenom; have : (0 : ℚ) < (M : ℚ) := by exact_mod_cast (show 0 < M by omega)
  positivity

private theorem singleCubeDenom_ge_two {M : ℕ} (hM : 1 ≤ M) {t : ℕ} (ht : 1 ≤ t) :
    (2 : ℚ) ≤ singleCubeDenom M t := by
  unfold singleCubeDenom
  have h2t : 2 ≤ 2 ^ t := by calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
  have hp2 : (2 : ℚ) ≤ (2 : ℚ) ^ (2 ^ t - 1) := by
    calc (2 : ℚ) = (2 : ℚ) ^ 1 := by ring
      _ ≤ (2 : ℚ) ^ (2 ^ t - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpM : (1 : ℚ) ≤ (M : ℚ) ^ (2 ^ t) := one_le_pow₀ (by exact_mod_cast hM)
  nlinarith

private theorem singleCubeDenom_mono {M : ℕ} (hM : 1 ≤ M) : Monotone (singleCubeDenom M) := by
  apply monotone_nat_of_le_succ; intro t; rw [singleCubeDenom_succ]
  have h1 : (1 : ℚ) ≤ (2 : ℚ) ^ (2 ^ t - 1) := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℚ) ≤ (M : ℚ) ^ (2 ^ t) := one_le_pow₀ (by exact_mod_cast hM)
  have hge1 : (1 : ℚ) ≤ singleCubeDenom M t := by unfold singleCubeDenom; nlinarith
  nlinarith

private theorem single_div_gt_three_half_Q {d M k : ℕ} (hM : 1 ≤ M) (hk : 2 ≤ k)
    (hd : max (8 * M * k ^ 2) ((2 * M) ^ (2 ^ k)) < d) :
    (3 : ℚ) * (2 * k ^ 2 : ℕ) / 2 < (d : ℚ) / singleCubeDenom M (k - 1) := by
  have hd1 : 8 * M * k ^ 2 < d := lt_of_le_of_lt (le_max_left _ _) hd
  have hd2 : (2 * M) ^ (2 ^ k) < d := lt_of_le_of_lt (le_max_right _ _) hd
  rw [div_lt_div_iff₀ (by norm_num) (singleCubeDenom_pos hM (k - 1))]
  by_cases hk2 : k = 2
  · subst hk2
    by_cases hM1 : M = 1
    · subst hM1; have hdq : (33 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (show 33 ≤ d by omega)
      norm_num [singleCubeDenom]; linarith
    · have hM2 : 2 ≤ M := by omega
      have hsq4 : 4 ≤ M ^ 2 := by nlinarith
      have hnat : 3 * 8 * (2 * M ^ 2) < 2 * d := by
        have hp4 : (2 * M) ^ 4 = 16 * (M ^ 2) * (M ^ 2) := by ring
        have hd2' : (2 * M) ^ 4 < d := by simpa using hd2
        nlinarith
      have hltq : ((3 * 8 * (2 * M ^ 2) : ℕ) : ℚ) < ((2 * d : ℕ) : ℚ) := by exact_mod_cast hnat
      norm_num [singleCubeDenom]; push_cast at hltq ⊢; linarith
  · have hk3 : 3 ≤ k := by omega
    have hlin : ∀ m : ℕ, 3 ≤ m → m + 1 ≤ 2 ^ (m - 1) := by
      intro m hm; induction m with
      | zero => omega
      | succ n ih =>
          by_cases hn : n = 2
          · subst hn; norm_num
          · calc n + 1 + 1 ≤ 2 * (n + 1) := by omega
              _ ≤ 2 * 2 ^ (n - 1) := Nat.mul_le_mul_left 2 (ih (by omega))
              _ = 2 ^ n := by rw [← pow_succ', show n - 1 + 1 = n by omega]
    have hquad : ∀ n : ℕ, 4 ≤ n → 3 * (n - 1) ^ 2 < 2 * 2 ^ n := by
      intro n hn; induction n with
      | zero => omega
      | succ m ih =>
          by_cases hm : m = 3
          · subst hm; norm_num
          · have hm4 : 4 ≤ m := by omega
            have hst : 3 * m ^ 2 ≤ 2 * (3 * (m - 1) ^ 2) := by zify [show 1 ≤ m by omega]; nlinarith
            calc 3 * m ^ 2 ≤ 2 * (3 * (m - 1) ^ 2) := hst
              _ < 2 * (2 * 2 ^ m) := by have := ih hm4; omega
              _ = 2 * 2 ^ (m + 1) := by rw [pow_succ']
    let P := 2 ^ (k - 1)
    have hPpos : 1 ≤ P := Nat.one_le_two_pow
    have hexp : 3 * k ^ 2 < 2 * 2 ^ P :=
      lt_of_lt_of_le (by simpa using hquad (k + 1) (by omega))
        (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) (hlin k hk3)))
    have h2B : 2 * singleCubeDenom M (k - 1) = (2 * (M : ℚ)) ^ P := by
      unfold singleCubeDenom; change 2 * ((2 : ℚ) ^ (P - 1) * (M : ℚ) ^ P) = _
      have h2P : (2 : ℚ) * (2 : ℚ) ^ (P - 1) = (2 : ℚ) ^ P := by
        rw [← pow_succ', show P - 1 + 1 = P by omega]
      calc 2 * ((2 : ℚ) ^ (P - 1) * (M : ℚ) ^ P) = ((2 : ℚ) * (2 : ℚ) ^ (P - 1)) * (M : ℚ) ^ P := by ring
        _ = (2 * (M : ℚ)) ^ P := by rw [h2P, ← mul_pow]
    have h2le : 2 ^ P ≤ (2 * M) ^ P := Nat.pow_le_pow_left (by omega) P
    have hsq : ((2 * M) ^ P) ^ 2 = (2 * M) ^ (2 ^ k) := by
      rw [show 2 ^ k = 2 * P by rw [show k = (k - 1) + 1 by omega, pow_succ'], pow_mul', sq]
    have hstepNat : 3 * k ^ 2 * (2 * M) ^ P < 2 * d := by
      have hposP : 0 < (2 * M) ^ P := Nat.pos_of_ne_zero (by positivity)
      have hlt1 : 3 * k ^ 2 < 2 * (2 * M) ^ P := lt_of_lt_of_le hexp (Nat.mul_le_mul_left 2 h2le)
      nlinarith
    have hfinQ : ((3 * k ^ 2 * (2 * M) ^ P : ℕ) : ℚ) < ((2 * d : ℕ) : ℚ) := by exact_mod_cast hstepNat
    push_cast at hfinQ ⊢; rw [← h2B] at hfinQ; linarith

/-- **Single-Subset Cauchy–Schwarz Affine `k`-Cube Extraction.**
For any dense subset `J ⊆ ZMod d` satisfying `d ≤ M_eff * J.card` and
`max (8 * M_eff * k^2) ((2 * M_eff)^(2^k)) < d` — even when `J.card < d / 2` or `ThreeAPFreeMod J`
holds — `J` itself contains an affine `k`-cube with steps in `[1, d / (2 * k^2)]`. -/
theorem singleSubset_CauchySchwarzAffineCubeExtraction
    (d M_eff k : ℕ) [NeZero d] (J : Finset (ZMod d))
    (hM : 1 ≤ M_eff) (hk : 1 ≤ k) (hdense : d ≤ M_eff * J.card)
    (hd : max (8 * M_eff * k ^ 2) ((2 * M_eff) ^ (2 ^ k)) < d) :
    ∃ (c₀ : ZMod d) (s : Fin k → ℕ),
      c₀ ∈ J ∧
      (∀ t : Fin k, 1 ≤ s t ∧ s t ≤ d / (2 * k ^ 2)) ∧
      ∀ ε : Fin k → Bool,
        c₀ + (∑ t : Fin k, if ε t then (s t : ZMod d) else 0) ∈ J := by
  let Q := 2 * k ^ 2
  let L₀ := d / Q
  have hQpos : 0 < Q := by positivity
  have hd1 : 8 * M_eff * k ^ 2 < d := lt_of_le_of_lt (le_max_left _ _) hd
  have hQL : Q ≤ d := by dsimp only [Q]; nlinarith
  let S₀ : Finset ℕ := J.map ⟨ZMod.val, ZMod.val_injective d⟩
  have hS₀card : S₀.card = J.card := Finset.card_map _
  have hN₀ : d ≤ M_eff * S₀.card := by rwa [hS₀card]
  have hS₀sub : S₀ ⊆ Finset.range d := fun x hx => by
    obtain ⟨c, _, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_range.mpr (ZMod.val_lt c)
  have hS₀mem : ∀ x ∈ S₀, (x : ZMod d) ∈ J := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hx
    simpa [ZMod.natCast_zmod_val] using hc
  by_cases hk1 : k = 1
  · subst hk1
    have hQ2 : Q = 2 := by simp [Q]
    obtain ⟨s₀, hs₀, hcard₁⟩ := single_cs_step hQpos hQL hS₀sub
    let S₁ := S₀.filter (fun x => x + s₀ ∈ S₀)
    have hposS₁ : 0 < S₁.card := by
      have : Q < S₀.card := by rw [hQ2]; nlinarith
      have : 0 < S₀.card * (S₀.card - Q) := Nat.mul_pos (by omega) (by omega)
      change S₀.card * (S₀.card - Q) ≤ 2 * d * S₁.card at hcard₁
      by_contra h0; rw [show S₁.card = 0 by omega, mul_zero] at hcard₁; omega
    obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp hposS₁
    simp only [S₁, Finset.mem_filter] at hx₀
    refine ⟨(x₀ : ZMod d), fun _ => s₀, hS₀mem x₀ hx₀.1, fun _ => by simpa [L₀, Q] using hs₀, fun ε => ?_⟩
    rw [Fin.sum_univ_one]
    cases ε 0
    · simpa using hS₀mem x₀ hx₀.1
    · simpa [Nat.cast_add] using hS₀mem (x₀ + s₀) hx₀.2
  · have hk2 : 2 ≤ k := by omega
    have hEnd := single_div_gt_three_half_Q hM hk2 hd
    have hexists : ∀ t : ℕ, t ≤ k - 1 →
        ∃ (s : Fin t → ℕ) (S : Finset ℕ),
          S ⊆ Finset.range d ∧
          (∀ i : Fin t, 1 ≤ s i ∧ s i ≤ L₀) ∧
          (∀ x ∈ S, ∀ ε : Fin t → Bool, x + (∑ i : Fin t, if ε i then s i else 0) ∈ S₀) ∧
          (if t = 0 then (d : ℚ) / singleCubeDenom M_eff 0 ≤ (S.card : ℚ)
           else (d : ℚ) / singleCubeDenom M_eff t - (Q : ℚ) / 2 ≤ (S.card : ℚ)) := by
      intro t; induction t with
      | zero =>
          intro _; refine ⟨Fin.elim0, S₀, hS₀sub, fun i => Fin.elim0 i, fun x hx _ => by simpa using hx, ?_⟩
          simp only [↓reduceIte, singleCubeDenom, pow_zero, Nat.sub_self, one_mul, pow_one]
          rw [div_le_iff₀ (by exact_mod_cast (show 0 < M_eff by omega))]
          have hq : (d : ℚ) ≤ (M_eff : ℚ) * (S₀.card : ℚ) := by exact_mod_cast hN₀
          linarith
      | succ t ih =>
          intro ht1
          obtain ⟨s, S, hSsub, hsBnd, hCube, hCard⟩ := ih (by omega)
          obtain ⟨s_next, hs_next, hstepNat⟩ := single_cs_step hQpos hQL hSsub
          let S' := S.filter (fun x => x + s_next ∈ S)
          refine ⟨Fin.snoc s s_next, S', le_trans (Finset.filter_subset _ _) hSsub, ?_, ?_, ?_⟩
          · intro i; refine Fin.lastCases (by simpa using hs_next) (fun j => by simpa using hsBnd j) i
          · intro x hx ε; simp only [S', Finset.mem_filter] at hx
            rw [Fin.sum_univ_castSucc]; simp only [Fin.snoc_castSucc, Fin.snoc_last]
            cases ε (Fin.last t)
            · simpa [add_assoc] using hCube x hx.1 (fun j => ε j.castSucc)
            · simp only [↓reduceIte]
              rw [show x + ((∑ i : Fin t, if ε i.castSucc then s i else 0) + s_next) =
                  (x + s_next) + ∑ i : Fin t, if ε i.castSucc then s i else 0 by ring]
              exact hCube (x + s_next) hx.2 (fun j => ε j.castSucc)
          · simp only [Nat.succ_ne_zero, ↓reduceIte]
            have hdpos : (0 : ℚ) < (d : ℚ) := by exact_mod_cast (show 0 < d by omega)
            by_cases ht0 : t = 0
            · subst ht0
              simp only [↓reduceIte, singleCubeDenom, pow_zero, Nat.sub_self, one_mul, pow_one] at hCard
              have hdQ : (4 : ℚ) * (Q : ℚ) < (d : ℚ) / (M_eff : ℚ) := by
                rw [lt_div_iff₀ (by exact_mod_cast (show 0 < M_eff by omega))]
                exact_mod_cast (show 4 * Q * M_eff < d by dsimp [Q]; nlinarith)
              have hSgtQ : Q ≤ S.card := by
                have hQpos' : (0 : ℚ) < (Q : ℚ) := by exact_mod_cast hQpos
                exact_mod_cast le_of_lt (show (Q : ℚ) < (S.card : ℚ) by linarith)
              have hstepQ : ((S.card : ℚ) * ((S.card : ℚ) - (Q : ℚ))) ≤ 2 * (d : ℚ) * (S'.card : ℚ) := by
                have hc : ((S.card * (S.card - Q) : ℕ) : ℚ) ≤ ((2 * d * S'.card : ℕ) : ℚ) := by exact_mod_cast hstepNat
                simpa [Nat.cast_sub hSgtQ] using hc
              have hquad : ((d : ℚ) / (M_eff : ℚ)) * ((d : ℚ) / (M_eff : ℚ) - (Q : ℚ)) ≤
                  (S.card : ℚ) * ((S.card : ℚ) - (Q : ℚ)) := by
                have hQpos' : (0 : ℚ) < (Q : ℚ) := by exact_mod_cast hQpos
                nlinarith
              rw [singleCubeDenom_succ]
              simp only [singleCubeDenom, pow_zero, Nat.sub_self, one_mul, pow_one]
              have hMge1 : (1 : ℚ) ≤ (M_eff : ℚ) := by exact_mod_cast hM
              have hQd : (Q : ℚ) / (2 * (M_eff : ℚ)) ≤ (Q : ℚ) / 2 :=
                div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
              have hid : ((d : ℚ) / (2 * (M_eff : ℚ) ^ 2) - (Q : ℚ) / (2 * (M_eff : ℚ))) * (2 * (d : ℚ)) =
                  ((d : ℚ) / (M_eff : ℚ)) * ((d : ℚ) / (M_eff : ℚ) - (Q : ℚ)) := by field_simp
              nlinarith
            · simp only [ht0, ↓reduceIte] at hCard
              have hXgt : (3 : ℚ) * (Q : ℚ) / 2 < (d : ℚ) / singleCubeDenom M_eff t :=
                lt_of_lt_of_le hEnd (div_le_div_of_nonneg_left (le_of_lt hdpos)
                  (singleCubeDenom_pos hM t) (singleCubeDenom_mono hM (by omega)))
              have hSgtQ : Q ≤ S.card := by
                exact_mod_cast le_of_lt (show (Q : ℚ) < (S.card : ℚ) by linarith)
              have hstepQ : ((S.card : ℚ) * ((S.card : ℚ) - (Q : ℚ))) ≤ 2 * (d : ℚ) * (S'.card : ℚ) := by
                have hc : ((S.card * (S.card - Q) : ℕ) : ℚ) ≤ ((2 * d * S'.card : ℕ) : ℚ) := by exact_mod_cast hstepNat
                simpa [Nat.cast_sub hSgtQ] using hc
              set X := (d : ℚ) / singleCubeDenom M_eff t
              have hquad : (X - (Q : ℚ) / 2) * (X - 3 * (Q : ℚ) / 2) ≤ (S.card : ℚ) * ((S.card : ℚ) - (Q : ℚ)) := by nlinarith
              have hBt2 : (2 : ℚ) ≤ singleCubeDenom M_eff t := singleCubeDenom_ge_two hM (by omega)
              have hBtPos : 0 < singleCubeDenom M_eff t := singleCubeDenom_pos hM t
              rw [singleCubeDenom_succ]
              have hid1 : X ^ 2 = (d : ℚ) / (2 * singleCubeDenom M_eff t ^ 2) * (2 * (d : ℚ)) := by dsimp [X]; field_simp
              have hid2 : 2 * (Q : ℚ) * X = ((Q : ℚ) / singleCubeDenom M_eff t) * (2 * (d : ℚ)) := by dsimp [X]; field_simp
              have hQBt : (Q : ℚ) / singleCubeDenom M_eff t ≤ (Q : ℚ) / 2 :=
                div_le_div_of_nonneg_left (by positivity) (by norm_num) hBt2
              have hQsq : 0 ≤ 3 * (Q : ℚ) ^ 2 / 4 := by positivity
              nlinarith
    obtain ⟨s_init, S_pen, hSpenSub, hsInitBnd, hCubePen, hCardPen⟩ := hexists (k - 1) le_rfl
    simp only [show k - 1 ≠ 0 by omega, ↓reduceIte] at hCardPen
    have hgtQ : Q < S_pen.card := by exact_mod_cast (show (Q : ℚ) < (S_pen.card : ℚ) by linarith)
    obtain ⟨s_last, hs_last, hstepLast⟩ := single_cs_step hQpos hQL hSpenSub
    let S_fin := S_pen.filter (fun x => x + s_last ∈ S_pen)
    have hposFin : 0 < S_fin.card := by
      have : 0 < S_pen.card * (S_pen.card - Q) := Nat.mul_pos (by omega) (by omega)
      change S_pen.card * (S_pen.card - Q) ≤ 2 * d * S_fin.card at hstepLast
      by_contra h0; rw [show S_fin.card = 0 by omega, mul_zero] at hstepLast; omega
    obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp hposFin
    simp only [S_fin, Finset.mem_filter] at hx₀
    have hkeq : (k - 1) + 1 = k := by omega
    let s_all : Fin ((k - 1) + 1) → ℕ := Fin.snoc s_init s_last
    have hx0In : x₀ ∈ S₀ := by simpa using hCubePen x₀ hx₀.1 (fun _ => false)
    refine ⟨(x₀ : ZMod d), s_all ∘ Fin.cast hkeq.symm, hS₀mem x₀ hx0In, ?_, ?_⟩
    · intro t; simp only [Function.comp_apply]
      exact Fin.lastCases (by simpa [s_all, L₀, Q] using hs_last) (fun j => by simpa [s_all, L₀, Q] using hsInitBnd j) (Fin.cast hkeq.symm t)
    · intro ε
      let ε' : Fin ((k - 1) + 1) → Bool := ε ∘ Fin.cast hkeq
      have hsumEq : (∑ t : Fin k, if ε t then ((s_all (Fin.cast hkeq.symm t) : ℕ) : ZMod d) else 0) =
          ((∑ i : Fin ((k - 1) + 1), if ε' i then s_all i else 0 : ℕ) : ZMod d) := by
        rw [Nat.cast_sum]
        refine Fintype.sum_equiv (Fin.castOrderIso hkeq.symm).toEquiv _ _ fun t => ?_
        cases hεt : ε t <;> simp [ε', Fin.castOrderIso, hεt]
      have hxIn : x₀ + (∑ i : Fin ((k - 1) + 1), if ε' i then s_all i else 0) ∈ S₀ := by
        rw [Fin.sum_univ_castSucc]; simp only [s_all, Fin.snoc_castSucc, Fin.snoc_last]
        cases ε' (Fin.last (k - 1))
        · simpa [add_assoc] using hCubePen x₀ hx₀.1 (fun j => ε' j.castSucc)
        · simp only [↓reduceIte]
          rw [show x₀ + ((∑ i : Fin (k - 1), if ε' i.castSucc then s_init i else 0) + s_last) =
              (x₀ + s_last) + ∑ i : Fin (k - 1), if ε' i.castSucc then s_init i else 0 by ring]
          exact hCubePen (x₀ + s_last) hx₀.2 (fun j => ε' j.castSucc)
      dsimp only [Function.comp_apply]; rw [hsumEq]
      simpa [Nat.cast_add] using hS₀mem _ hxIn

private theorem cyclicChannelShift_comp' {F : Type*} [Semiring F] {d q : ℕ} (s₁ s₂ : ZMod d) :
    (cyclicChannelShift F d q s₂).comp (cyclicChannelShift F d q s₁) =
      cyclicChannelShift F d q (s₁ + s₂) := by
  apply LinearMap.ext; intro x; funext u ch
  change x ((u + s₂) + s₁) ch = x (u + (s₁ + s₂)) ch
  rw [show (u + s₂) + s₁ = u + (s₁ + s₂) by ring]

private theorem orderedCubeMap_cyclicShift {F : Type*} [Semiring F] {d q : ℕ} :
    ∀ {k : ℕ} (s : Fin k → ℕ) (ε : Fin k → Bool),
      orderedCubeMap (fun t => cyclicChannelShift F d q (s t : ZMod d)) ε =
        cyclicChannelShift F d q (∑ t : Fin k, if ε t then (s t : ZMod d) else 0)
  | 0, _, _ => by ext x u ch; simp [orderedCubeMap, cyclicChannelShift]
  | k + 1, s, ε => by
      rw [Fin.sum_univ_castSucc]; simp only [orderedCubeMap]
      rw [orderedCubeMap_cyclicShift (fun i : Fin k => s i.castSucc) (fun i : Fin k => ε i.castSucc)]
      cases ε (Fin.last k)
      · simp
      · simp only [↓reduceIte, cyclicChannelShift_comp']

private theorem orderedCubeMap_rowClassRot {F A κ : Type*} [Field F] [AddCommGroup A] [Module F A]
    {d : ℕ} (p : ZMod d → κ) :
    ∀ {k : ℕ} (s : Fin k → ℕ) (ε : Fin k → Bool)
      (X : SharedDecoders.rowClassSpace (F := F) (A := A) p),
      (orderedCubeMap (fun t => SharedDecoders.rowClassRotation (F := F) (A := A) p (s t : ZMod d)) ε X).1 =
        rot (∑ t : Fin k, if ε t then (s t : ZMod d) else 0) X.1
  | 0, _, _, _ => by simp [orderedCubeMap]
  | k + 1, s, ε, X => by
      rw [Fin.sum_univ_castSucc]; simp only [orderedCubeMap]
      have ih := orderedCubeMap_rowClassRot p (fun i : Fin k => s i.castSucc) (fun i : Fin k => ε i.castSucc) X
      cases ε (Fin.last k)
      · simpa using ih
      · simp only [↓reduceIte, LinearMap.comp_apply, SharedDecoders.rowClassRotation_apply, ih, rot_rot, add_comm]

private theorem cyclicChannelShift_ker_le {F : Type*} [Field F] {d q s : ℕ} [NeZero d] (hs : 1 ≤ s) :
    finrank F (LinearMap.ker (cyclicChannelShift F d q (s : ZMod d) - LinearMap.id)) ≤ q * s := by
  let res : LinearMap.ker (cyclicChannelShift F d q (s : ZMod d) - LinearMap.id) →ₗ[F] (Fin s → Fin q → F) :=
    { toFun := fun x i => x.1 (i.val : ZMod d), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective res := by
    rw [injective_iff_map_eq_zero]; intro x hx
    have hper : ∀ u : ZMod d, x.1 (u + (s : ZMod d)) = x.1 u := fun u => by
      have h0 : ((cyclicChannelShift F d q (s : ZMod d) - LinearMap.id) : _ →ₗ[F] _) x.1 = 0 :=
        LinearMap.mem_ker.mp x.2
      rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h0; exact congrFun h0 u
    have hnat : ∀ B n : ℕ, n ≤ B → x.1 (n : ZMod d) = 0 := fun B => by
      induction B with
      | zero =>
          intro n hn; obtain rfl : n = 0 := by omega
          simpa [res] using congrFun hx ⟨0, hs⟩
      | succ B ih =>
          intro n hn; by_cases hlt : n < s
          · exact congrFun hx ⟨n, hlt⟩
          · rw [show (n : ZMod d) = ((n - s : ℕ) : ZMod d) + (s : ZMod d) by
              rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)], hper, ih (n - s) (by omega)]
    apply Subtype.ext; funext u; rw [← ZMod.natCast_zmod_val u]; exact hnat u.val u.val le_rfl
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hdim : finrank F (Fin s → Fin q → F) = q * s := by simp [Module.finrank_pi_fintype, mul_comm]
  omega

/-- **Dense-Subset Affine `k`-Cube Common-Message Bound & Single-Dense-Class Exclusion.**
Over every field `F`: (1) any dense subset `J ⊆ ZMod d` (`d ≤ M_eff * J.card`, even if
`ThreeAPFreeMod J` holds) forces `(k + 1) * finrank F W ≤ q * d + q * k * (d / (2 * k^2))` for
cyclic-shift invariant messages; and (2) on `rowClassSpace p₂`, any single receiver class containing
such a dense subset `J` precludes `K₂ ∘ K₁ = swapLinear F` regardless of how `p₁` behaves on `J^c`. -/
theorem denseSubset_AffineCubeCommonMessageBound :
    (∀ (F Z : Type*) [Field F] [AddCommGroup Z] [Module F Z]
      (d q M_eff k : ℕ) [NeZero d] (J : Finset (ZMod d))
      (W : Submodule F (ZMod d → Fin q → F)) (L : (ZMod d → Fin q → F) →ₗ[F] Z),
      1 ≤ M_eff → 1 ≤ k → d ≤ M_eff * J.card →
      max (8 * M_eff * k ^ 2) ((2 * M_eff) ^ (2 ^ k)) < d →
      (∃ c_ref ∈ J, (∀ x ∈ W, L (cyclicChannelShift F d q c_ref x) = 0 → x = 0) ∧
        (∀ c ∈ J, ∀ x ∈ W, L (cyclicChannelShift F d q c x) = L (cyclicChannelShift F d q c_ref x))) →
      (k + 1) * finrank F W ≤ q * d + q * k * (d / (2 * k ^ 2))) ∧
    (∀ (F : Type*) [Field F] {κ₁ : Type*} (d b M_eff M₂ : ℕ) [NeZero d]
      (p₁ : ZMod d → κ₁) (p₂ : ZMod d → Fin M₂) (m₁ : κ₁) (J : Finset (ZMod d)),
      1 ≤ b → 1 ≤ M_eff → 1 ≤ M₂ → (∀ c ∈ J, p₁ c = m₁) →
      d ≤ M_eff * J.card → max (8 * M_eff * M₂ ^ 2) ((2 * M_eff) ^ (2 ^ M₂)) < d →
      ¬ ∃ K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F),
          ClassUniform p₁ K₁ ∧ ClassUniform p₂ K₂ ∧ K₂.comp K₁ = swapLinear F) := by
  refine ⟨?_, ?_⟩
  · intro F Z _ _ _ d q M_eff k _ J W L hM hk hdense hd ⟨c_ref, hcref, hinj, hconst⟩
    obtain ⟨c₀, s, hc₀, hsBnd, hcube⟩ :=
      singleSubset_CauchySchwarzAffineCubeExtraction d M_eff k J hM hk hdense hd
    let L' := L.comp (cyclicChannelShift F d q c₀)
    let R : Fin k → ((ZMod d → Fin q → F) →ₗ[F] (ZMod d → Fin q → F)) :=
      fun t => cyclicChannelShift F d q (s t : ZMod d)
    have hinj' : ∀ x ∈ W, L' x = 0 → x = 0 := fun x hx h0 =>
      hinj x hx ((hconst c₀ hc₀ x hx).symm.trans h0)
    have hmsg' : ∀ x ∈ W, ∀ ε : Fin k → Bool, L' (orderedCubeMap R ε x) = L' x := fun x hx ε => by
      rw [orderedCubeMap_cyclicShift]
      change L (cyclicChannelShift F d q c₀ (cyclicChannelShift F d q _ x)) =
        L (cyclicChannelShift F d q c₀ x)
      have hcomp : cyclicChannelShift F d q c₀
          (cyclicChannelShift F d q (∑ t : Fin k, if ε t then (s t : ZMod d) else 0) x) =
          cyclicChannelShift F d q (c₀ + ∑ t : Fin k, if ε t then (s t : ZMod d) else 0) x := by
        funext u ch; simp [cyclicChannelShift, add_assoc, add_comm, add_left_comm]
      rw [hcomp, hconst _ (hcube ε) x hx, hconst c₀ hc₀ x hx]
    have hg := lemma_AffineCubeCommonMessageGrowth F (ZMod d → Fin q → F) Z k R W L' hinj' hmsg'
    have hdimA : finrank F (ZMod d → Fin q → F) = q * d := by
      simp [Module.finrank_pi_fintype, ZMod.card, mul_comm]
    have hsum : (∑ t : Fin k, finrank F (LinearMap.ker (R t - LinearMap.id))) ≤ q * k * (d / (2 * k ^ 2)) := by
      calc ∑ t : Fin k, finrank F (LinearMap.ker (R t - LinearMap.id))
        _ ≤ ∑ t : Fin k, q * s t := Finset.sum_le_sum fun t _ => cyclicChannelShift_ker_le (hsBnd t).1
        _ ≤ ∑ _ : Fin k, q * (d / (2 * k ^ 2)) := Finset.sum_le_sum fun t _ => Nat.mul_le_mul_left q (hsBnd t).2
        _ = q * k * (d / (2 * k ^ 2)) := by simp; ring
    omega
  · intro F _ κ₁ d b M_eff M₂ _ p₁ p₂ m₁ J hb hM hM₂ hpJ hdense hd ⟨K₁, K₂, h₁u, h₂u, hcomp⟩
    obtain ⟨c₀, s, hc₀, hsBnd, hcube⟩ :=
      singleSubset_CauchySchwarzAffineCubeExtraction d M_eff M₂ J hM hM₂ hdense hd
    obtain ⟨f₁, hf₁⟩ := SharedDecoders.linearClassUniform_of_classUniform p₁ K₁ h₁u
    obtain ⟨f₂, hf₂⟩ := SharedDecoders.linearClassUniform_of_classUniform p₂ K₂ h₂u
    have hexact : ∀ X, K₂ (K₁ X) = swap X := fun X => LinearMap.congr_fun hcomp X
    let A := Fin b → F
    let E₀ : (ZMod d → A) →ₗ[F] State d A := (swapLinear F).comp (K₂.comp SharedDecoders.repeatColumns)
    have hE₀ : ∀ a, E₀ a ∈ SharedDecoders.rowClassSpace (F := F) (A := A) p₂ := fun a i j hij => by
      funext c
      change K₂ (SharedDecoders.repeatColumns (F := F) a) c i = K₂ (SharedDecoders.repeatColumns (F := F) a) c j
      rw [hf₂, hf₂, hij, SharedDecoders.rot_repeatColumns, SharedDecoders.rot_repeatColumns]
    let E := E₀.codRestrict (SharedDecoders.rowClassSpace (F := F) (A := A) p₂) hE₀
    have hleft (a : ZMod d → A) : K₁ (E a).1 = SharedDecoders.repeatColumns (F := F) a :=
      SharedDecoders.first_swap_second K₁ K₂ hexact _
    have hEinj : Function.Injective E := by
      rw [injective_iff_map_eq_zero]; intro a ha
      have h : SharedDecoders.repeatColumns (F := F) a = 0 := by
        rw [← hleft a, ha, Submodule.coe_zero, map_zero]
      funext i; exact congrFun (congrFun h i) 0
    let W := LinearMap.range E
    let R : Fin M₂ → (SharedDecoders.rowClassSpace (F := F) (A := A) p₂ →ₗ[F]
        SharedDecoders.rowClassSpace (F := F) (A := A) p₂) :=
      fun t => SharedDecoders.rowClassRotation (F := F) (A := A) p₂ (s t : ZMod d)
    let L : SharedDecoders.rowClassSpace (F := F) (A := A) p₂ →ₗ[F] (ZMod d → A) :=
      (f₁ m₁).comp ((rotLinear F c₀).comp (SharedDecoders.rowClassSpace p₂).subtype)
    have hobs : ∀ (ε : Fin M₂ → Bool) (a : ZMod d → A), L (orderedCubeMap R ε (E a)) = a := fun ε a => by
      funext i; change f₁ m₁ (rot c₀ ((orderedCubeMap R ε (E a)).1)) i = a i
      rw [orderedCubeMap_rowClassRot, rot_rot]
      have h := hf₁ (E a).1 (c₀ + ∑ t : Fin M₂, if ε t then (s t : ZMod d) else 0) i
      rw [hpJ _ (hcube ε)] at h; rw [← h, hleft]; rfl
    have hobs0 : ∀ a : ZMod d → A, L (E a) = a := fun a => by
      have h := hobs (fun _ => false) a
      have hf : ∀ {k : ℕ} (R' : Fin k → (SharedDecoders.rowClassSpace (F := F) (A := A) p₂ →ₗ[F]
          SharedDecoders.rowClassSpace (F := F) (A := A) p₂)),
          orderedCubeMap R' (fun _ => false) = LinearMap.id := by
        intro k; induction k with
        | zero => intro _; rfl
        | succ n ih => intro R'; exact ih (fun i : Fin n => R' i.castSucc)
      rwa [hf R, LinearMap.id_apply] at h
    have hdimA : finrank F A = b := by simp [A]
    have hdimW : finrank F W = d * b := by
      rw [LinearMap.finrank_range_of_inj hEinj]; simp [Module.finrank_pi_fintype, ZMod.card, hdimA]
    have hg := lemma_AffineCubeCommonMessageGrowth F
      (SharedDecoders.rowClassSpace (F := F) (A := A) p₂) (ZMod d → A) M₂ R W L
      (by rintro x ⟨a, rfl⟩ hx; simp [(hobs0 a).symm.trans hx])
      (by rintro x ⟨a, rfl⟩ ε; exact (hobs ε a).trans (hobs0 a).symm)
    rw [hdimW] at hg
    have ha := SharedDecoders.rowClassSpace_finrank_le (F := F) (A := A) p₂
    simp only [Fintype.card_fin, hdimA] at ha
    have hsumKer : (∑ t : Fin M₂, finrank F (LinearMap.ker (R t - LinearMap.id))) ≤
        M₂ * (M₂ * (d / (2 * M₂ ^ 2)) * b) := by
      calc ∑ t : Fin M₂, finrank F (LinearMap.ker (R t - LinearMap.id))
        _ ≤ ∑ t : Fin M₂, (M₂ * s t * b) := Finset.sum_le_sum fun t _ => by
            simpa [R, Fintype.card_fin, hdimA] using
              SharedDecoders.rowClassRotation_fixed_finrank_le (F := F) (A := A) p₂ (by have := (hsBnd t).1; omega)
        _ ≤ ∑ _ : Fin M₂, (M₂ * (d / (2 * M₂ ^ 2)) * b) := Finset.sum_le_sum fun t _ =>
            Nat.mul_le_mul_right b (Nat.mul_le_mul_left M₂ (hsBnd t).2)
        _ = M₂ * (M₂ * (d / (2 * M₂ ^ 2)) * b) := by simp
    have hcomb : ((M₂ + 1) * d) * b ≤ (M₂ * d + M₂ ^ 2 * (d / (2 * M₂ ^ 2))) * b := by
      have h1 := le_trans hg (Nat.add_le_add ha hsumKer)
      have : (M₂ + 1) * (d * b) = ((M₂ + 1) * d) * b := by ring
      have : M₂ * d * b + M₂ * (M₂ * (d / (2 * M₂ ^ 2)) * b) = (M₂ * d + M₂ ^ 2 * (d / (2 * M₂ ^ 2))) * b := by ring
      omega
    have hd_ineq : (M₂ + 1) * d ≤ M₂ * d + M₂ ^ 2 * (d / (2 * M₂ ^ 2)) :=
      Nat.le_of_mul_le_mul_right hcomb (by omega)
    have hdiv_le : 2 * M₂ ^ 2 * (d / (2 * M₂ ^ 2)) ≤ d := Nat.mul_div_le d (2 * M₂ ^ 2)
    have hd_pos : 0 < d := NeZero.pos d
    nlinarith

/-- **Growing-Class Theorem 2A.**
Non-factorization for growing class counts `M₁(d), M₂(d)` below the Cauchy–Schwarz cutoff, together
with the polynomial-class `M₂ = 1` specialization (`8 * M₁ < d` and `4 * M₁^2 < d`). -/
theorem theorem2A_GrowingClassesNonFactorization :
    (∀ (F : Type*) [Field F] (M₁ M₂ : ℕ → ℕ) (d b : ℕ) [NeZero d]
      (p₁ : ZMod d → Fin (M₁ d)) (p₂ : ZMod d → Fin (M₂ d)),
      1 ≤ b → 1 ≤ M₁ d → 1 ≤ M₂ d →
      max (8 * M₁ d * (M₂ d) ^ 2) ((2 * M₁ d) ^ (2 ^ M₂ d)) < d →
      ¬ ∃ K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F),
          ClassUniform p₁ K₁ ∧ ClassUniform p₂ K₂ ∧ K₂.comp K₁ = swapLinear F) ∧
    (∀ (F : Type*) [Field F] (d b M₁ : ℕ) [NeZero d]
      (p₁ : ZMod d → Fin M₁) (p₂ : ZMod d → Fin 1),
      1 ≤ b → 1 ≤ M₁ → 8 * M₁ < d → 4 * M₁ ^ 2 < d →
      ¬ ∃ K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F),
          ClassUniform p₁ K₁ ∧ ClassUniform p₂ K₂ ∧ K₂.comp K₁ = swapLinear F) := by
  refine ⟨?_, ?_⟩
  · intro F _ M₁ M₂ d b _ p₁ p₂ hb h1 h2 hd ⟨K₁, K₂, h₁u, h₂u, hcomp⟩
    exact Nat.not_le_of_gt hd
      (theorem2A_TwoStageRamseyFreeCutoff F d b (M₁ d) (M₂ d) p₁ p₂ K₁ K₂ hb h1 h2 h₁u h₂u hcomp)
  · intro F _ d b M₁ _ p₁ p₂ hb hM₁ h8 h4 ⟨K₁, K₂, h₁u, h₂u, hcomp⟩
    have hle := theorem2A_TwoStageRamseyFreeCutoff F d b M₁ 1 p₁ p₂ K₁ K₂ hb hM₁ le_rfl h₁u h₂u hcomp
    have hlt : max (8 * M₁ * 1 ^ 2) ((2 * M₁) ^ (2 ^ 1)) < d := by
      rw [max_lt_iff]; refine ⟨by simpa using h8, ?_⟩
      have : (2 * M₁) ^ (2 ^ 1) = 4 * M₁ ^ 2 := by ring
      rwa [this]
    exact Nat.not_le_of_gt hlt hle

end SingleSubsetAndGrowingClasses

/-! ### 2. Strengthened `d = 13` General-Field Control & `commonMessage_finrank_le` Bridge -/

section D13GeneralFieldBridge

private def d13GenETable : Array (Array Int) :=
  #[#[1, 0, 1, 1, 1, 0, 0, 0, 0], #[1, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 0, 0, 0, 1, 0, 0, 0, 0], #[1, 0, 0, 0, 2, 0, 0, 0, 0],
    #[1, 0, 0, 0, 3, 0, 1, 0, 0], #[1, 0, 0, 1, 4, 0, 1, 0, 0], #[1, 0, 0, 1, 3, 0, 1, 0, 0],
    #[1, 0, 0, 1, 2, 1, 1, 0, 0], #[0, 1, 0, 0, 0, 1, 1, 0, 1], #[0, 1, 0, 0, 1, 0, 0, 0, 1],
    #[0, 1, 0, 0, 2, 0, 0, 0, 1], #[0, 1, 0, 0, 3, 0, 0, 1, 1], #[0, 1, 0, 1, 4, 0, 0, 0, 0],
    #[0, 1, 0, 1, 3, 0, 0, 0, 0], #[0, 1, 0, 1, 2, 0, 0, 0, 0], #[0, 1, 1, 1, 1, 0, 0, 0, 0],
    #[0, 1, 0, 0, 0, 0, 0, 0, -1], #[0, 1, 0, 0, 0, 0, 0, 0, -1], #[0, 1, 0, 0, 0, 0, 1, 0, -1],
    #[0, 1, 0, 0, 0, 0, 1, -1, -1], #[0, 1, 0, 0, 0, 0, 1, 0, 0]]

private def d13GenL13Table : Array (Array Int) :=
  #[#[0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-1, 12, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    #[10, -3, -29, 23, -3, 10, -16, -3, 10, 10, -16, -3, 10, -10, 3, 3, 3, -10, 3, 3, 3, 3, -10, 3, 3, 3],
    #[6, -33, -20, 84, -59, 6, 6, 6, -7, 6, -7, 6, 6, -6, 7, 7, -6, -45, 59, -6, -6, -6, 7, 7, -6, -6],
    #[0, 0, 0, -13, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, -13, 0, 0, 0, 0, 0, 0, 0],
    #[3, 3, -10, -10, 16, 3, -23, 16, 3, 3, -23, 16, 3, 10, -3, -3, -3, 10, -3, -3, -3, -3, 10, -3, -3, -3],
    #[-6, -6, 33, -32, 7, -6, 7, -6, 7, -6, 20, -6, -6, 6, -7, -7, 6, -7, -7, 6, 6, 6, -7, -7, 6, 6],
    #[-19, -19, -6, 59, -19, -32, 33, -19, 7, -6, 33, -32, 20, -20, 6, -7, 6, -20, 19, -20, 19, 19, -7, -20, -7, 32],
    #[16, -10, 29, -49, 16, 16, -10, -10, 3, -10, 3, 16, -10, 10, 10, -3, 10, -3, -16, 10, -16, 10, -3, -3, 10, -16]]

private def d13GenE (ch : Fin 2) (u : ZMod 13) (j : Fin 9) : ℤ :=
  (d13GenETable.getD (ch.val * 13 + u.val) #[]).getD j.val 0

private def d13GenL13 (i : Fin 9) (ch : Fin 2) (u : ZMod 13) : ℤ :=
  (d13GenL13Table.getD i.val #[]).getD (ch.val * 13 + u.val) 0

private theorem d13Gen_int_ident :
    ∀ c ∈ ({0, 1, 4, 5} : Finset (ZMod 13)), ∀ i j : Fin 9,
      (∑ ch : Fin 2, ∑ u : ZMod 13, d13GenL13 i ch u * d13GenE ch (u + c) j) =
        if i = j then 13 else 0 := by decide

private theorem d13ShiftKer_finrank_eq_two {F : Type*} [Field F] {s : ZMod 13} (hs : s ≠ 0) :
    finrank F (LinearMap.ker (cyclicChannelShift F 13 2 s - LinearMap.id)) = 2 := by
  have hinv_ex : ∀ x : ZMod 13, x ≠ 0 → ∃ y : ZMod 13, x * y = 1 := by decide
  obtain ⟨inv, hinv⟩ := hinv_ex s hs
  let e : LinearMap.ker (cyclicChannelShift F 13 2 s - LinearMap.id) ≃ₗ[F] (Fin 2 → F) :=
    { toFun := fun x => x.1 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun v => ⟨fun _ => v, by ext u ch; simp [cyclicChannelShift]⟩
      left_inv := fun x => by
        have hper : ∀ u : ZMod 13, x.1 (u + s) = x.1 u := fun u => by
          have h0 : ((cyclicChannelShift F 13 2 s - LinearMap.id) : _ →ₗ[F] _) x.1 = 0 :=
            LinearMap.mem_ker.mp x.2
          rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h0; exact congrFun h0 u
        have hnat : ∀ n : ℕ, x.1 ((n : ZMod 13) * s) = x.1 0 := fun n => by
          induction n with
          | zero => simp
          | succ n ih =>
              rw [show ((n + 1 : ℕ) : ZMod 13) * s = (n : ZMod 13) * s + s by push_cast; ring, hper, ih]
        apply Subtype.ext; funext u
        change x.1 0 = x.1 u
        have hu : (((u * inv).val : ℕ) : ZMod 13) * s = u := by
          rw [ZMod.natCast_zmod_val, mul_assoc, mul_comm inv s, hinv, mul_one]
        rw [← hu]; exact (hnat (u * inv).val).symm
      right_inv := fun _ => rfl }
  simpa using e.finrank_eq

/-- **Strengthened `d = 13` General-Field Control & Progression Bridge.**
Establishes: (a) exact shift kernel dimension `2` over every field `F`; (b) Paper 19
`commonMessage_finrank_le` bound `D ≤ 14` and an explicit `D = 14` witness on every 2-point
progression over **every** field `F`; and (c) the `D = 9` affine 2-cube witness on `J = {0,1,4,5}`
over **every** field `F` with `(13 : F) ≠ 0`. -/
theorem control_D13_GeneralFieldAndProgressionBridge :
    let J13 : Finset (ZMod 13) := {0, 1, 4, 5}
    (∀ (F : Type*) [Field F],
      finrank F (LinearMap.ker (cyclicChannelShift F 13 2 1 - LinearMap.id)) = 2 ∧
      finrank F (LinearMap.ker (cyclicChannelShift F 13 2 4 - LinearMap.id)) = 2) ∧
    (∀ (F : Type*) [Field F] (s : ZMod 13), s ≠ 0 →
      (∀ (Z : Type*) [AddCommGroup Z] [Module F Z]
        (W : Submodule F (ZMod 13 → Fin 2 → F)) (L : (ZMod 13 → Fin 2 → F) →ₗ[F] Z),
        (∀ y ∈ W, L y = 0 → y = 0) →
        (∀ j < 2, ∀ y ∈ W, L ((cyclicChannelShift F 13 2 s ^ j) y) = L y) →
        2 * finrank F W ≤ 26 + 2 ∧ finrank F W ≤ 14) ∧
      (∃ (W₁₄ : Submodule F (ZMod 13 → Fin 2 → F))
          (L₁₄ : (ZMod 13 → Fin 2 → F) →ₗ[F] (Fin 7 × Fin 2 → F)),
        finrank F W₁₄ = 14 ∧
        (∀ y ∈ W₁₄, L₁₄ y = 0 → y = 0) ∧
        (∀ j < 2, ∀ y ∈ W₁₄, L₁₄ ((cyclicChannelShift F 13 2 s ^ j) y) = L₁₄ y))) ∧
    (∀ (F : Type*) [Field F], (13 : F) ≠ 0 →
      ∃ (W₉ : Submodule F (ZMod 13 → Fin 2 → F))
          (L₉ : (ZMod 13 → Fin 2 → F) →ₗ[F] (Fin 9 → F)),
        finrank F W₉ = 9 ∧
        (∀ x ∈ W₉, L₉ x = 0 → x = 0) ∧
        (∀ x ∈ W₉, ∀ c ∈ J13, L₉ (cyclicChannelShift F 13 2 c x) = L₉ x)) := by
  refine ⟨fun F _ => ⟨d13ShiftKer_finrank_eq_two (by decide), d13ShiftKer_finrank_eq_two (by decide)⟩, ?_, ?_⟩
  · intro F _ s hs
    refine ⟨?_, ?_⟩
    · intro Z _ _ W L hinj hmsg
      have hcm := SharedDecoders.commonMessage_finrank_le (cyclicChannelShift F 13 2 s) W L 2 (by omega) hinj hmsg
      have hdimA : finrank F (ZMod 13 → Fin 2 → F) = 26 := by simp [Module.finrank_pi_fintype, ZMod.card]
      rw [hdimA, d13ShiftKer_finrank_eq_two hs] at hcm
      exact ⟨by omega, by omega⟩
    · have hinv_ex : ∀ x : ZMod 13, x ≠ 0 → ∃ y : ZMod 13, x * y = 1 := by decide
      obtain ⟨inv, hinv⟩ := hinv_ex s hs
      let S : Fin 6 → ZMod 13 := ![0, 2, 4, 6, 8, 10]
      have hS11 : ∀ k : Fin 6, (11 : ZMod 13) ≠ S k := by decide
      have hS12 : ∀ k : Fin 6, (12 : ZMod 13) ≠ S k := by decide
      have hSm1 : ∀ i k : Fin 6, S i - 1 ≠ S k := by decide
      have hSp1 : ∀ i k : Fin 6, S i + 1 ≠ S k := by decide
      have hSinj : ∀ i k : Fin 6, S i = S k ↔ i = k := by decide
      let E₁₄ : (Fin 7 × Fin 2 → F) →ₗ[F] (ZMod 13 → Fin 2 → F) :=
        { toFun := fun v u ch => v (0, ch) + ∑ k : Fin 6, if u * inv = S k then v (k.succ, ch) else 0
          map_add' := fun v w => by
            funext u ch; simp only [Pi.add_apply]
            have hsum : (∑ k : Fin 6, if u * inv = S k then v (k.succ, ch) + w (k.succ, ch) else 0) =
                (∑ k : Fin 6, if u * inv = S k then v (k.succ, ch) else 0) +
                (∑ k : Fin 6, if u * inv = S k then w (k.succ, ch) else 0) := by
              rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
            rw [hsum]; ring
          map_smul' := fun r v => by
            funext u ch; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum]
            congr 1; refine Finset.sum_congr rfl fun k _ => by split_ifs <;> ring }
      let L₁₄ : (ZMod 13 → Fin 2 → F) →ₗ[F] (Fin 7 × Fin 2 → F) :=
        { toFun := fun w p => Fin.cases (w (11 * s) p.2)
            (fun i => w (S i * s) p.2 + w ((S i - 1) * s) p.2 - (w (11 * s) p.2 + w (11 * s) p.2)) p.1
          map_add' := fun w₁ w₂ => by
            funext ⟨i, ch⟩; refine Fin.cases (by simp) (fun i => ?_) i
            simp only [Fin.cases_succ, Pi.add_apply]; ring
          map_smul' := fun r w => by
            funext ⟨i, ch⟩; refine Fin.cases (by simp) (fun i => ?_) i
            simp only [Fin.cases_succ, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
      have hEval : ∀ (v : Fin 7 × Fin 2 → F) (r : ZMod 13) (ch : Fin 2),
          E₁₄ v (r * s) ch = v (0, ch) + ∑ k : Fin 6, if r = S k then v (k.succ, ch) else 0 := fun v r ch => by
        change v (0, ch) + ∑ k : Fin 6, (if (r * s) * inv = S k then v (k.succ, ch) else 0) = _
        rw [mul_assoc, hinv, mul_one]
      have hL0 : ∀ v : Fin 7 × Fin 2 → F, L₁₄ (E₁₄ v) = v := fun v => by
        funext ⟨i, ch⟩; refine Fin.cases ?_ (fun i => ?_) i
        · change E₁₄ v (11 * s) ch = v (0, ch); simp [hEval, hS11]
        · change E₁₄ v (S i * s) ch + E₁₄ v ((S i - 1) * s) ch - (E₁₄ v (11 * s) ch + E₁₄ v (11 * s) ch) = v (i.succ, ch)
          rw [hEval, hEval, hEval]; simp only [hSm1 i, hS11, ↓reduceIte, Finset.sum_const_zero, add_zero]
          simp_rw [hSinj]; simp only [ Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]; ring
      have hL1 : ∀ v : Fin 7 × Fin 2 → F, L₁₄ (cyclicChannelShift F 13 2 s (E₁₄ v)) = v := fun v => by
        have hSh : ∀ (r : ZMod 13) (ch : Fin 2), cyclicChannelShift F 13 2 s (E₁₄ v) (r * s) ch = E₁₄ v ((r + 1) * s) ch :=
          fun r ch => by change E₁₄ v (r * s + s) ch = _; rw [show r * s + s = (r + 1) * s by ring]
        funext ⟨i, ch⟩; refine Fin.cases ?_ (fun i => ?_) i
        · change cyclicChannelShift F 13 2 s (E₁₄ v) (11 * s) ch = v (0, ch)
          rw [hSh, show (11 : ZMod 13) + 1 = 12 by decide, hEval]; simp [hS12]
        · change cyclicChannelShift F 13 2 s (E₁₄ v) (S i * s) ch + cyclicChannelShift F 13 2 s (E₁₄ v) ((S i - 1) * s) ch -
              (cyclicChannelShift F 13 2 s (E₁₄ v) (11 * s) ch + cyclicChannelShift F 13 2 s (E₁₄ v) (11 * s) ch) = v (i.succ, ch)
          rw [hSh, hSh, hSh, sub_add_cancel, show (11 : ZMod 13) + 1 = 12 by decide, hEval, hEval, hEval]
          simp only [hSp1 i, hS12, ↓reduceIte, Finset.sum_const_zero, add_zero]
          simp_rw [hSinj]; simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]; ring
      refine ⟨LinearMap.range E₁₄, L₁₄, ?_, ?_, ?_⟩
      · rw [LinearMap.finrank_range_of_inj (Function.LeftInverse.injective hL0)]; simp
      · rintro y ⟨v, rfl⟩ hy; simp [(hL0 v).symm.trans hy]
      · intro j hj; rintro y ⟨v, rfl⟩
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · simp
        · simpa [pow_one] using (hL1 v).trans (hL0 v).symm
  · intro F _ h13
    let E_F : (Fin 9 → F) →ₗ[F] (ZMod 13 → Fin 2 → F) :=
      { toFun := fun v u ch => ∑ j : Fin 9, (d13GenE ch u j : F) * v j
        map_add' := fun v w => by funext u ch; simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun r v => by funext u ch; simp [Finset.mul_sum, mul_left_comm] }
    let L_F : (ZMod 13 → Fin 2 → F) →ₗ[F] (Fin 9 → F) :=
      { toFun := fun x i => (13 : F)⁻¹ * ∑ ch : Fin 2, ∑ u : ZMod 13, (d13GenL13 i ch u : F) * x u ch
        map_add' := fun x y => by funext i; simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun r x => by
          funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          rw [← mul_assoc, mul_comm r (13 : F)⁻¹, mul_assoc]; congr 1
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ch _ => ?_
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring }
    have hLE : ∀ c ∈ ({0, 1, 4, 5} : Finset (ZMod 13)), ∀ v : Fin 9 → F,
        L_F (cyclicChannelShift F 13 2 c (E_F v)) = v := fun c hc v => by
      funext i
      change (13 : F)⁻¹ * ∑ ch : Fin 2, ∑ u : ZMod 13,
          (d13GenL13 i ch u : F) * (∑ j : Fin 9, (d13GenE ch (u + c) j : F) * v j) = v i
      have hrew : (∑ ch : Fin 2, ∑ u : ZMod 13, (d13GenL13 i ch u : F) * (∑ j : Fin 9, (d13GenE ch (u + c) j : F) * v j)) =
          ∑ j : Fin 9, ((∑ ch : Fin 2, ∑ u : ZMod 13, (d13GenL13 i ch u : F) * (d13GenE ch (u + c) j : F)) * v j) := by
        calc _ = ∑ ch : Fin 2, ∑ u : ZMod 13, ∑ j : Fin 9, ((d13GenL13 i ch u : F) * (d13GenE ch (u + c) j : F)) * v j :=
              Finset.sum_congr rfl fun ch _ => Finset.sum_congr rfl fun u _ => by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
          _ = ∑ ch : Fin 2, ∑ j : Fin 9, ∑ u : ZMod 13, ((d13GenL13 i ch u : F) * (d13GenE ch (u + c) j : F)) * v j :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ j : Fin 9, ∑ ch : Fin 2, ∑ u : ZMod 13, ((d13GenL13 i ch u : F) * (d13GenE ch (u + c) j : F)) * v j := Finset.sum_comm
          _ = _ := Finset.sum_congr rfl fun j _ => by
              rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ch _ => (Finset.sum_mul _ _ _).symm
      rw [hrew]
      have hcoeff : ∀ j : Fin 9, (∑ ch : Fin 2, ∑ u : ZMod 13, (d13GenL13 i ch u : F) * (d13GenE ch (u + c) j : F)) =
          if i = j then (13 : F) else 0 := fun j => by
        have hcast := congrArg (Int.cast : ℤ → F) (d13Gen_int_ident c hc i j)
        simpa [Int.cast_sum, Int.cast_mul] using hcast
      simp_rw [hcoeff]; simp [ite_mul, ← mul_assoc, inv_mul_cancel₀ h13]
    have hL0 : ∀ v : Fin 9 → F, L_F (E_F v) = v := fun v => by
      have h0 := hLE 0 (by decide) v
      have hz : cyclicChannelShift F 13 2 0 (E_F v) = E_F v := by funext u ch; simp [cyclicChannelShift]
      rwa [hz] at h0
    refine ⟨LinearMap.range E_F, L_F, ?_, ?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj (Function.LeftInverse.injective hL0)]; simp
    · rintro x ⟨v, rfl⟩ hx; simp [(hL0 v).symm.trans hx]
    · rintro x ⟨v, rfl⟩ c hc; exact (hLE c hc v).trans (hL0 v).symm

end D13GeneralFieldBridge

/-! ### 3. `d = 4` All-Width Bit-Lane Impossibility & Binary / General-Field Coded Factorization -/

section D4AllWidthsAndBinary

/-- Uncoded bit-lane copying class-uniform rule on `State d (Fin b → Sigma)`: each class `m` and
output wire `(i, ℓ)` copies a fixed rotated entry lane `(srcRow m i ℓ, srcOff m i ℓ, srcLane m i ℓ)`. -/
def IsBitLaneCopyClassRule {d b : ℕ} {κ Sigma : Type*}
    (p : ZMod d → κ) (K : State d (Fin b → Sigma) → State d (Fin b → Sigma)) : Prop :=
  ∃ (srcRow srcOff : κ → ZMod d → Fin b → ZMod d) (srcLane : κ → ZMod d → Fin b → Fin b),
    ∀ (X : State d (Fin b → Sigma)) (c i : ZMod d) (ℓ : Fin b),
      K X i c ℓ = (rot c X) (srcRow (p c) i ℓ) (srcOff (p c) i ℓ) (srcLane (p c) i ℓ)

private def d4BinATable : Array (Array (Array Nat)) :=
  #[#[#[1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0]],
    #[#[1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0]]]

private def d4BinBTable : Array (Array (Array Nat)) :=
  #[#[#[1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      #[1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0],
      #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1]]]

private def d4GenL1Table : Array (Array (Array Int)) :=
  #[#[#[-2, 0, 0, -1, 2, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], #[3, -3, 2, 0, 2, -2, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      #[0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, -1, 2, -1, 1, 1], #[0, 0, 0, 0, 0, 0, 0, 0, 3, -3, 2, 0, 2, -2, 1, -1]],
    #[#[0, 1, 0, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, -1, 1, -1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, -1, 0, -1], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 1, 0, 2]]]

private def d4GenL2Table : Array (Array (Array Int)) :=
  #[#[#[-1, -3, -9, 3, 3, 4, -3, 6, 0, 0, 0, 0, 0, 0, 0, 0], #[1, -7, -1, -3, 2, 1, 8, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      #[-1, -3, 11, 3, 3, -6, 17, -4, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 3, 19, 7, 2, 1, 8, -1, 0, 0, 0, 0, 0, 0, 0, 0]],
    #[#[0, 0, 0, 0, 0, 0, 0, 0, -9, 3, -1, -3, -3, 6, 3, 4], #[0, 0, 0, 0, 0, 0, 0, 0, -1, -3, 1, -7, 8, -1, 2, 1],
      #[0, 0, 0, 0, 0, 0, 0, 0, 11, 3, -1, -3, 17, -4, 3, -6], #[0, 0, 0, 0, 0, 0, 0, 0, 19, 7, 1, 3, 8, -1, 2, 1]]]

private def d4BinA (m : Fin 2) (i r u : ZMod 4) : ℕ :=
  ((d4BinATable.getD m.val #[]).getD i.val #[]).getD (r.val * 4 + u.val) 0

private def d4BinB (m : Fin 2) (i r u : ZMod 4) : ℕ :=
  ((d4BinBTable.getD m.val #[]).getD i.val #[]).getD (r.val * 4 + u.val) 0

private def d4GenL1 (m : Fin 2) (i r u : ZMod 4) : ℤ :=
  ((d4GenL1Table.getD m.val #[]).getD i.val #[]).getD (r.val * 4 + u.val) 0

private def d4GenL2 (m : Fin 2) (i r u : ZMod 4) : ℤ :=
  ((d4GenL2Table.getD m.val #[]).getD i.val #[]).getD (r.val * 4 + u.val) 0

private theorem d4_bin_ident :
    ∀ i c r₀ c₀ : ZMod 4,
      (∑ j : ZMod 4, ∑ v : ZMod 4,
        d4BinB (halfIntervalPartition4 c) i j v *
          d4BinA (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c))) % 2 =
        if r₀ = c ∧ c₀ = i then 1 else 0 := by decide

private theorem d4_gen_ident :
    ∀ i c r₀ c₀ : ZMod 4,
      (∑ j : ZMod 4, ∑ v : ZMod 4,
        d4GenL2 (halfIntervalPartition4 c) i j v *
          d4GenL1 (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c))) =
        if r₀ = c ∧ c₀ = i then 20 else 0 := by decide

private theorem d4_coded_allWidths {F : Type*} [Field F] (b : ℕ)
    (A B : Fin 2 → ZMod 4 → ZMod 4 → ZMod 4 → F)
    (hident : ∀ i c r₀ c₀ : ZMod 4,
      (∑ j : ZMod 4, ∑ v : ZMod 4,
        B (halfIntervalPartition4 c) i j v *
          A (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c))) =
        if r₀ = c ∧ c₀ = i then 1 else 0) :
    ∃ K₁ K₂ : State 4 (Fin b → F) →ₗ[F] State 4 (Fin b → F),
      ClassUniform halfIntervalPartition4 K₁ ∧
      ClassUniform halfIntervalPartition4 K₂ ∧
      K₂.comp K₁ = swapLinear F := by
  let f₁ : Fin 2 → State 4 (Fin b → F) → (ZMod 4 → Fin b → F) :=
    fun m Z i ℓ => ∑ r : ZMod 4, ∑ u : ZMod 4, A m i r u * Z r u ℓ
  let f₂ : Fin 2 → State 4 (Fin b → F) → (ZMod 4 → Fin b → F) :=
    fun m Z i ℓ => ∑ j : ZMod 4, ∑ v : ZMod 4, B m i j v * Z j v ℓ
  let K₁ : State 4 (Fin b → F) →ₗ[F] State 4 (Fin b → F) :=
    { toFun := fun X i c => f₁ (halfIntervalPartition4 c) (rot c X) i
      map_add' := fun X Y => by funext i c ℓ; simp [f₁, rot_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a X => by funext i c ℓ; simp [f₁, rot_apply, Finset.mul_sum, mul_left_comm] }
  let K₂ : State 4 (Fin b → F) →ₗ[F] State 4 (Fin b → F) :=
    { toFun := fun Y i c => f₂ (halfIntervalPartition4 c) (rot c Y) i
      map_add' := fun X Y => by funext i c ℓ; simp [f₂, rot_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a X => by funext i c ℓ; simp [f₂, rot_apply, Finset.mul_sum, mul_left_comm] }
  refine ⟨K₁, K₂, ⟨f₁, fun _ _ _ => rfl⟩, ⟨f₂, fun _ _ _ => rfl⟩, ?_⟩
  apply LinearMap.ext; intro X; funext i c ℓ
  change ∑ j : ZMod 4, ∑ v : ZMod 4, B (halfIntervalPartition4 c) i j v *
      (∑ r₀ : ZMod 4, ∑ u : ZMod 4, A (halfIntervalPartition4 (v + c)) j r₀ u * X r₀ (u + (v + c)) ℓ) = X c i ℓ
  have hsh : ∀ (g h : ZMod 4 → F) (s : ZMod 4), (∑ u : ZMod 4, g u * h (u + s)) = ∑ c₀ : ZMod 4, g (c₀ - s) * h c₀ :=
    fun g h s => Fintype.sum_equiv (Equiv.addRight s) _ _ fun u => by simp
  have h1 : (∑ j : ZMod 4, ∑ v : ZMod 4, B (halfIntervalPartition4 c) i j v *
        (∑ r₀ : ZMod 4, ∑ u : ZMod 4, A (halfIntervalPartition4 (v + c)) j r₀ u * X r₀ (u + (v + c)) ℓ)) =
      ∑ j : ZMod 4, ∑ v : ZMod 4, B (halfIntervalPartition4 c) i j v *
        (∑ r₀ : ZMod 4, ∑ c₀ : ZMod 4, A (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c)) * X r₀ c₀ ℓ) :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => congrArg _ <|
      Finset.sum_congr rfl fun r₀ _ => hsh _ (fun col => X r₀ col ℓ) (v + c)
  rw [h1]
  have h2 : (∑ j : ZMod 4, ∑ v : ZMod 4, B (halfIntervalPartition4 c) i j v *
        (∑ r₀ : ZMod 4, ∑ c₀ : ZMod 4, A (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c)) * X r₀ c₀ ℓ)) =
      ∑ r₀ : ZMod 4, ∑ c₀ : ZMod 4,
        ((∑ j : ZMod 4, ∑ v : ZMod 4, B (halfIntervalPartition4 c) i j v *
          A (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c))) * X r₀ c₀ ℓ) := by
    calc _ = ∑ j : ZMod 4, ∑ v : ZMod 4, ∑ r₀ : ZMod 4, ∑ c₀ : ZMod 4,
            (B (halfIntervalPartition4 c) i j v * A (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c))) * X r₀ c₀ ℓ :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r₀ _ => ?_
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c₀ _ => (mul_assoc _ _ _).symm
      _ = ∑ j : ZMod 4, ∑ r₀ : ZMod 4, ∑ v : ZMod 4, ∑ c₀ : ZMod 4,
            (B (halfIntervalPartition4 c) i j v * A (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c))) * X r₀ c₀ ℓ :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ r₀ : ZMod 4, ∑ j : ZMod 4, ∑ v : ZMod 4, ∑ c₀ : ZMod 4,
            (B (halfIntervalPartition4 c) i j v * A (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c))) * X r₀ c₀ ℓ := Finset.sum_comm
      _ = ∑ r₀ : ZMod 4, ∑ j : ZMod 4, ∑ c₀ : ZMod 4, ∑ v : ZMod 4,
            (B (halfIntervalPartition4 c) i j v * A (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c))) * X r₀ c₀ ℓ :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ r₀ : ZMod 4, ∑ c₀ : ZMod 4, ∑ j : ZMod 4, ∑ v : ZMod 4,
            (B (halfIntervalPartition4 c) i j v * A (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c))) * X r₀ c₀ ℓ :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => (Finset.sum_mul _ _ _).symm
  rw [h2]; simp_rw [hident]
  have h3 : (∑ r₀ : ZMod 4, ∑ c₀ : ZMod 4, (if r₀ = c ∧ c₀ = i then (1 : F) else 0) * X r₀ c₀ ℓ) =
      ∑ r₀ : ZMod 4, if r₀ = c then X r₀ i ℓ else 0 := by
    refine Finset.sum_congr rfl fun r₀ _ => ?_
    by_cases hr : r₀ = c
    · subst hr; simp [ite_mul]
    · simp [hr]
  rw [h3]; simp

private theorem d4_coded_char2 {F : Type*} [Field F] (b : ℕ) (h2 : (2 : F) = 0) :
    ∃ K₁ K₂ : State 4 (Fin b → F) →ₗ[F] State 4 (Fin b → F),
      ClassUniform halfIntervalPartition4 K₁ ∧
      ClassUniform halfIntervalPartition4 K₂ ∧
      K₂.comp K₁ = swapLinear F := by
  have hmod2 : ∀ n : ℕ, (n : F) = ((n % 2 : ℕ) : F) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n 2]
    push_cast; simp [h2]
  refine d4_coded_allWidths b (fun m i r u => (d4BinA m i r u : F)) (fun m i j v => (d4BinB m i j v : F)) ?_
  intro i c r₀ c₀
  have hcast : ((∑ j : ZMod 4, ∑ v : ZMod 4, d4BinB (halfIntervalPartition4 c) i j v *
      d4BinA (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c)) : ℕ) : F) =
      ∑ j : ZMod 4, ∑ v : ZMod 4, (d4BinB (halfIntervalPartition4 c) i j v : F) *
        (d4BinA (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c)) : F) := by
    rw [Nat.cast_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun v _ => Nat.cast_mul _ _
  rw [← hcast, hmod2, d4_bin_ident]
  by_cases h : r₀ = c ∧ c₀ = i <;> simp [h]

private theorem d4_coded_ne20 {F : Type*} [Field F] (b : ℕ) (h20 : (20 : F) ≠ 0) :
    ∃ K₁ K₂ : State 4 (Fin b → F) →ₗ[F] State 4 (Fin b → F),
      ClassUniform halfIntervalPartition4 K₁ ∧
      ClassUniform halfIntervalPartition4 K₂ ∧
      K₂.comp K₁ = swapLinear F := by
  refine d4_coded_allWidths b (fun m i r u => (d4GenL1 m i r u : F))
    (fun m i j v => (20 : F)⁻¹ * (d4GenL2 m i j v : F)) ?_
  intro i c r₀ c₀
  have hpull : (∑ j : ZMod 4, ∑ v : ZMod 4, ((20 : F)⁻¹ * (d4GenL2 (halfIntervalPartition4 c) i j v : F)) *
        (d4GenL1 (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c)) : F)) =
      (20 : F)⁻¹ * ∑ j : ZMod 4, ∑ v : ZMod 4, (d4GenL2 (halfIntervalPartition4 c) i j v : F) *
        (d4GenL1 (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c)) : F) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
  rw [hpull]
  have hcast : ((∑ j : ZMod 4, ∑ v : ZMod 4, d4GenL2 (halfIntervalPartition4 c) i j v *
      d4GenL1 (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c)) : ℤ) : F) =
      ∑ j : ZMod 4, ∑ v : ZMod 4, (d4GenL2 (halfIntervalPartition4 c) i j v : F) *
        (d4GenL1 (halfIntervalPartition4 (v + c)) j r₀ (c₀ - (v + c)) : F) := by
    rw [Int.cast_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_sum]; exact Finset.sum_congr rfl fun v _ => Int.cast_mul _ _
  rw [← hcast, d4_gen_ident]
  by_cases h : r₀ = c ∧ c₀ = i
  · rcases h with ⟨rfl, rfl⟩
    simp only [and_self, ↓reduceIte]
    have h20cast : ((20 : ℤ) : F) = (20 : F) := by norm_num
    rw [h20cast, inv_mul_cancel₀ h20]
  · simp only [h, ↓reduceIte, Int.cast_zero, mul_zero]

/-- **`d = 4` All-Width Bit-Lane Impossibility & Binary / General-Field Coded Factorization.**
At `d = 4` with `p₁ = p₂ = halfIntervalPartition4`: (a) uncoded `IsBitLaneCopyClassRule`
factorizations are impossible for all widths `b ≥ 1` and alphabets `|Sigma| ≥ 2`; (b) linear
`ClassUniform` factorizations exist at all widths `b` whenever `(2 : F) = 0` or `(20 : F) ≠ 0`,
and hence over every field `F` with `(5 : F) ≠ 0`. -/
theorem control_D4_AllWidthsAndBinaryFields :
    (∀ (b : ℕ) (Sigma : Type*) [Fintype Sigma], 1 ≤ b → 2 ≤ Fintype.card Sigma →
      ¬ ∃ K₁ K₂ : State 4 (Fin b → Sigma) → State 4 (Fin b → Sigma),
          IsBitLaneCopyClassRule halfIntervalPartition4 K₁ ∧
          IsBitLaneCopyClassRule halfIntervalPartition4 K₂ ∧
          K₂ ∘ K₁ = swap) ∧
    ((∀ (F : Type*) [Field F] (b : ℕ), (2 : F) = 0 →
        ∃ K₁ K₂ : State 4 (Fin b → F) →ₗ[F] State 4 (Fin b → F),
          ClassUniform halfIntervalPartition4 K₁ ∧
          ClassUniform halfIntervalPartition4 K₂ ∧
          K₂.comp K₁ = swapLinear F) ∧
      (∀ (F : Type*) [Field F] (b : ℕ), (20 : F) ≠ 0 →
        ∃ K₁ K₂ : State 4 (Fin b → F) →ₗ[F] State 4 (Fin b → F),
          ClassUniform halfIntervalPartition4 K₁ ∧
          ClassUniform halfIntervalPartition4 K₂ ∧
          K₂.comp K₁ = swapLinear F) ∧
      (∀ (F : Type*) [Field F] (b : ℕ), (5 : F) ≠ 0 →
        ∃ K₁ K₂ : State 4 (Fin b → F) →ₗ[F] State 4 (Fin b → F),
          ClassUniform halfIntervalPartition4 K₁ ∧
          ClassUniform halfIntervalPartition4 K₂ ∧
          K₂.comp K₁ = swapLinear F)) := by
  refine ⟨?_, fun F _ b h2 => d4_coded_char2 b h2, fun F _ b h20 => d4_coded_ne20 b h20, ?_⟩
  · intro b Sigma _ hb hcard ⟨K₁, K₂, ⟨r₁, u₁, ℓ₁, hK₁⟩, ⟨r₂, u₂, ℓ₂, hK₂⟩, hcomp⟩
    obtain ⟨s₀, s₁, hne⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Sigma)
    let p := halfIntervalPartition4
    have hwire : ∀ (i c : ZMod 4) (ℓ : Fin b),
        r₁ (p (u₂ (p c) i ℓ + c)) (r₂ (p c) i ℓ) (ℓ₂ (p c) i ℓ) = c ∧
        u₁ (p (u₂ (p c) i ℓ + c)) (r₂ (p c) i ℓ) (ℓ₂ (p c) i ℓ) + (u₂ (p c) i ℓ + c) = i ∧
        ℓ₁ (p (u₂ (p c) i ℓ + c)) (r₂ (p c) i ℓ) (ℓ₂ (p c) i ℓ) = ℓ := fun i c ℓ => by
      let X : State 4 (Fin b → Sigma) := fun r col ln => if r = c ∧ col = i ∧ ln = ℓ then s₁ else s₀
      have heq : K₂ (K₁ X) i c ℓ = swap X i c ℓ := congrFun (congrFun (congrFun (congrFun hcomp X) i) c) ℓ
      rw [hK₂, rot_apply, hK₁, rot_apply, swap_apply] at heq
      simp only [X, and_self, ↓reduceIte] at heq
      split_ifs at heq with h
      · exact h
      · exact False.elim (hne heq)
    have hz4 : ∀ (u a₀ a₁ : ZMod 4),
        ![a₀, a₁] (halfIntervalPartition4 u) = 0 →
        ![a₀, a₁] (halfIntervalPartition4 (u + 1)) = 1 →
        (u = 1 ∧ a₀ = 0 ∧ a₁ = 1) ∨ (u = 3 ∧ a₀ = 1 ∧ a₁ = 0) := by decide
    have hfin2 : ∀ (g : Fin 2 → ZMod 4) (m : Fin 2), ![g 0, g 1] m = g m := fun g m => by fin_cases m <;> rfl
    have hp0 : p 0 = 0 := by decide
    have hp1 : p 1 = 0 := by decide
    have hp2 : p 2 = 1 := by decide
    let φ₀ : ZMod 4 × Fin b → ZMod 4 × Fin b := fun q => (r₂ 0 q.1 q.2, ℓ₂ 0 q.1 q.2)
    have hφ₀_cases : ∀ q : ZMod 4 × Fin b,
        (u₂ 0 q.1 q.2 = 1 ∧ r₁ 0 (φ₀ q).1 (φ₀ q).2 = 0 ∧ r₁ 1 (φ₀ q).1 (φ₀ q).2 = 1) ∨
        (u₂ 0 q.1 q.2 = 3 ∧ r₁ 0 (φ₀ q).1 (φ₀ q).2 = 1 ∧ r₁ 1 (φ₀ q).1 (φ₀ q).2 = 0) := fun q => by
      have h0 := (hwire q.1 0 q.2).1; have h1 := (hwire q.1 1 q.2).1
      rw [hp0, add_zero] at h0; rw [hp1] at h1
      exact hz4 (u₂ 0 q.1 q.2) (r₁ 0 (φ₀ q).1 (φ₀ q).2) (r₁ 1 (φ₀ q).1 (φ₀ q).2)
        (by rwa [hfin2 (fun m => r₁ m (φ₀ q).1 (φ₀ q).2)]) (by rwa [hfin2 (fun m => r₁ m (φ₀ q).1 (φ₀ q).2)])
    have hinj : Function.Injective φ₀ := fun q₁ q₂ heq => by
      have hc1 := hφ₀_cases q₁; have hc2 := hφ₀_cases q₂; rw [← heq] at hc2
      have hu : u₂ 0 q₁.1 q₁.2 = u₂ 0 q₂.1 q₂.2 := by
        rcases hc1 with ⟨hu1, hr0, _⟩ | ⟨hu1, hr0, _⟩ <;> rcases hc2 with ⟨hu2, hr0', _⟩ | ⟨hu2, hr0', _⟩
        · exact hu1.trans hu2.symm
        · exact False.elim ((by decide : (0 : ZMod 4) ≠ 1) (hr0.symm.trans hr0'))
        · exact False.elim ((by decide : (1 : ZMod 4) ≠ 0) (hr0.symm.trans hr0'))
        · exact hu1.trans hu2.symm
      have hj : r₂ 0 q₁.1 q₁.2 = r₂ 0 q₂.1 q₂.2 := congrArg Prod.fst heq
      have hl : ℓ₂ 0 q₁.1 q₁.2 = ℓ₂ 0 q₂.1 q₂.2 := congrArg Prod.snd heq
      have hcol1 := (hwire q₁.1 0 q₁.2).2.1; have hcol2 := (hwire q₂.1 0 q₂.2).2.1
      have hln1 := (hwire q₁.1 0 q₁.2).2.2; have hln2 := (hwire q₂.1 0 q₂.2).2.2
      simp only [hp0, add_zero] at hcol1 hcol2 hln1 hln2
      ext
      · rw [← hcol1, ← hcol2, hu, hj, hl]
      · rw [← hln1, ← hln2, hu, hj, hl]
    let ℓ₀ : Fin b := ⟨0, hb⟩
    obtain ⟨q, hq⟩ := Finite.surjective_of_injective hinj (r₂ 1 0 ℓ₀, ℓ₂ 1 0 ℓ₀)
    have hr2 := (hwire 0 2 ℓ₀).1; rw [hp2] at hr2
    have hq_c := hφ₀_cases q; rw [hq] at hq_c
    have hne2 : ∀ m : Fin 2, r₁ m (r₂ 1 0 ℓ₀) (ℓ₂ 1 0 ℓ₀) ≠ 2 := fun m => by
      fin_cases m <;> rcases hq_c with ⟨_, h0, h1⟩ | ⟨_, h0, h1⟩ <;> simp [h0, h1] <;> decide
    exact hne2 _ hr2
  · intro F _ b h5
    by_cases h2 : (2 : F) = 0
    · exact d4_coded_char2 b h2
    · apply d4_coded_ne20 b
      rw [show (20 : F) = (2 : F) * ((2 : F) * (5 : F)) by norm_num]
      exact mul_ne_zero h2 (mul_ne_zero h2 h5)

end D4AllWidthsAndBinary

end BoundedArityDecoders
