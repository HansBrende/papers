import Mathlib

/-! # Random block rankings and LYM-type separation sums

For disjoint subsets `A, E ⊆ Fin B`, exactly `B! / C(|A| + |E|, |A|)` permutations of `Fin B`
rank every element of `A` strictly below every element of `E`. Averaging over all permutations
yields a ranking that separates at least `∑_{q ∈ Q_*} 1 / C(|A(q)| + |E(q)|, |A(q)|)` elements of
any finite family `(A(q), E(q))`.
-/

namespace LeanMachine.BlockRanking

open Finset
set_option autoImplicit false

/-- Elements of `V₀` whose `A_cut`-set is ranked strictly below their `E_cut`-set by `f`. -/
def cutSet {V Γ α : Type*} [LinearOrder α] (V₀ : Finset V) (A_cut E_cut : V → Finset Γ)
    (f : Γ → α) : Finset V :=
  V₀.filter fun q => ∀ x ∈ A_cut q, ∀ y ∈ E_cut q, f x < f y

theorem cutSet_subset {V Γ α : Type*} [LinearOrder α] {V₀ : Finset V}
    {A_cut E_cut : V → Finset Γ} {f : Γ → α} :
    cutSet V₀ A_cut E_cut f ⊆ V₀ :=
  filter_subset _ _

/-- Permutations of `Fin B` that rank every element of `A` strictly below every element of `E`. -/
def goodPerms {B : ℕ} (A E : Finset (Fin B)) : Finset (Equiv.Perm (Fin B)) :=
  univ.filter fun σ => ∀ x ∈ A, ∀ y ∈ E, σ x < σ y

private lemma exists_initial_subset_of_perm {B : ℕ} (σ : Equiv.Perm (Fin B)) :
    ∀ (a : ℕ) (S : Finset (Fin B)), a ≤ S.card →
      ∃ A' ∈ S.powersetCard a, σ ∈ goodPerms A' (S \ A')
  | 0, S, _ => by
    refine ⟨∅, mem_powersetCard.mpr ⟨empty_subset S, card_empty⟩, ?_⟩
    simp [goodPerms]
  | a + 1, S, ha => by
    have hSne : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨x₀, hx₀S, hx₀_min⟩ := mem_image.mp ((S.image σ).min'_mem (hSne.image σ))
    have ha' : a ≤ (S.erase x₀).card := by
      have hc := card_erase_add_one hx₀S
      omega
    obtain ⟨A'', hA''_mem, hA''_good⟩ := exists_initial_subset_of_perm σ a (S.erase x₀) ha'
    obtain ⟨hA''_sub, hA''_card⟩ := mem_powersetCard.mp hA''_mem
    have hx₀_not : x₀ ∉ A'' := fun h => (mem_erase.mp (hA''_sub h)).1 rfl
    refine ⟨insert x₀ A'',
      mem_powersetCard.mpr ⟨insert_subset hx₀S (hA''_sub.trans (erase_subset _ _)),
        by rw [card_insert_of_notMem hx₀_not, hA''_card]⟩, ?_⟩
    simp only [goodPerms, mem_filter, mem_univ, true_and] at hA''_good ⊢
    intro x hx y hy
    obtain ⟨hyS, hy_not_ins⟩ := mem_sdiff.mp hy
    have hy_ne_x₀ : y ≠ x₀ := fun heq => hy_not_ins (heq ▸ mem_insert_self x₀ A'')
    have hy_not_A'' : y ∉ A'' := fun h => hy_not_ins (mem_insert_of_mem h)
    rcases mem_insert.mp hx with rfl | hxA''
    · have hle : (S.image σ).min' (hSne.image σ) ≤ σ y :=
        (S.image σ).min'_le (σ y) (mem_image_of_mem σ hyS)
      rw [← hx₀_min] at hle
      exact lt_of_le_of_ne hle fun heq => hy_ne_x₀ (σ.injective heq.symm)
    · exact hA''_good x hxA'' y (mem_sdiff.mpr ⟨mem_erase.mpr ⟨hy_ne_x₀, hyS⟩, hy_not_A''⟩)

private lemma disjoint_goodPerms_of_ne {B : ℕ} {S A₁ A₂ : Finset (Fin B)}
    (h1 : A₁ ∈ S.powersetCard A₁.card) (h2 : A₂ ∈ S.powersetCard A₁.card) (hne : A₁ ≠ A₂) :
    Disjoint (goodPerms A₁ (S \ A₁)) (goodPerms A₂ (S \ A₂)) := by
  rw [disjoint_left]
  intro σ hσ1 hσ2
  obtain ⟨hA1S, _⟩ := mem_powersetCard.mp h1
  obtain ⟨hA2S, hcard_eq⟩ := mem_powersetCard.mp h2
  have hnot_sub1 : ¬ A₁ ⊆ A₂ := fun hsub => hne (eq_of_subset_of_card_le hsub (by omega))
  have hnot_sub2 : ¬ A₂ ⊆ A₁ := fun hsub => hne (eq_of_subset_of_card_le hsub (by omega)).symm
  obtain ⟨x, hx1, hx2⟩ := not_subset.mp hnot_sub1
  obtain ⟨y, hy2, hy1⟩ := not_subset.mp hnot_sub2
  simp only [goodPerms, mem_filter, mem_univ, true_and] at hσ1 hσ2
  have hlt1 : σ x < σ y := hσ1 x hx1 y (mem_sdiff.mpr ⟨hA2S hy2, hy1⟩)
  have hlt2 : σ y < σ x := hσ2 y hy2 x (mem_sdiff.mpr ⟨hA1S hx1, hx2⟩)
  exact lt_asymm hlt1 hlt2

private lemma card_goodPerms_eq_of_card_eq {B : ℕ} {A E A' E' : Finset (Fin B)}
    (hd : Disjoint A E) (hd' : Disjoint A' E')
    (hA : A.card = A'.card) (hE : E.card = E'.card) :
    (goodPerms A' E').card = (goodPerms A E).card := by
  have hAE_card : (A ∪ E).card = (A' ∪ E').card := by
    rw [card_union_of_disjoint hd, card_union_of_disjoint hd', hA, hE]
  have hcompl_card : (univ \ (A ∪ E)).card = (univ \ (A' ∪ E')).card := by
    have h1 := card_sdiff_add_card_inter (univ : Finset (Fin B)) (A ∪ E)
    have h2 := card_sdiff_add_card_inter (univ : Finset (Fin B)) (A' ∪ E')
    rw [univ_inter] at h1 h2
    omega
  let eA : A ≃ A' := Finset.equivOfCardEq hA
  let eE : E ≃ E' := Finset.equivOfCardEq hE
  let eC : ↑(univ \ (A ∪ E)) ≃ ↑(univ \ (A' ∪ E')) := Finset.equivOfCardEq hcompl_card
  let toFun : Fin B → Fin B := fun x =>
    if hxA : x ∈ A then (eA ⟨x, hxA⟩).1
    else if hxE : x ∈ E then (eE ⟨x, hxE⟩).1
    else (eC ⟨x, mem_sdiff.mpr ⟨mem_univ x, fun h => by
      rcases mem_union.mp h with h1 | h2
      · exact hxA h1
      · exact hxE h2⟩⟩).1
  let invFun : Fin B → Fin B := fun y =>
    if hyA : y ∈ A' then (eA.symm ⟨y, hyA⟩).1
    else if hyE : y ∈ E' then (eE.symm ⟨y, hyE⟩).1
    else (eC.symm ⟨y, mem_sdiff.mpr ⟨mem_univ y, fun h => by
      rcases mem_union.mp h with h1 | h2
      · exact hyA h1
      · exact hyE h2⟩⟩).1
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    dsimp only [toFun]
    split_ifs with hxA hxE
    · have h1 : (eA ⟨x, hxA⟩).1 ∈ A' := (eA ⟨x, hxA⟩).2
      dsimp only [invFun]
      split_ifs
      exact congrArg Subtype.val (eA.symm_apply_apply ⟨x, hxA⟩)
    · have h2 : (eE ⟨x, hxE⟩).1 ∈ E' := (eE ⟨x, hxE⟩).2
      have hnotA' : (eE ⟨x, hxE⟩).1 ∉ A' := disjoint_right.mp hd' h2
      dsimp only [invFun]
      split_ifs
      exact congrArg Subtype.val (eE.symm_apply_apply ⟨x, hxE⟩)
    · set xc : ↑(univ \ (A ∪ E)) := ⟨x, mem_sdiff.mpr ⟨mem_univ x, fun h => by
        rcases mem_union.mp h with h1 | h2
        · exact hxA h1
        · exact hxE h2⟩⟩
      have h3 : (eC xc).1 ∈ univ \ (A' ∪ E') := (eC xc).2
      have hnotAE' : (eC xc).1 ∉ A' ∪ E' := (mem_sdiff.mp h3).2
      have hnotA' : (eC xc).1 ∉ A' := fun ha => hnotAE' (mem_union_left _ ha)
      have hnotE' : (eC xc).1 ∉ E' := fun he => hnotAE' (mem_union_right _ he)
      dsimp only [invFun]
      split_ifs
      exact congrArg Subtype.val (eC.symm_apply_apply xc)
  have hright : Function.RightInverse invFun toFun := by
    intro y
    dsimp only [invFun]
    split_ifs with hyA hyE
    · have h1 : (eA.symm ⟨y, hyA⟩).1 ∈ A := (eA.symm ⟨y, hyA⟩).2
      dsimp only [toFun]
      split_ifs
      exact congrArg Subtype.val (eA.apply_symm_apply ⟨y, hyA⟩)
    · have h2 : (eE.symm ⟨y, hyE⟩).1 ∈ E := (eE.symm ⟨y, hyE⟩).2
      have hnotA : (eE.symm ⟨y, hyE⟩).1 ∉ A := disjoint_right.mp hd h2
      dsimp only [toFun]
      split_ifs
      exact congrArg Subtype.val (eE.apply_symm_apply ⟨y, hyE⟩)
    · set yc : ↑(univ \ (A' ∪ E')) := ⟨y, mem_sdiff.mpr ⟨mem_univ y, fun h => by
        rcases mem_union.mp h with h1 | h2
        · exact hyA h1
        · exact hyE h2⟩⟩
      have h3 : (eC.symm yc).1 ∈ univ \ (A ∪ E) := (eC.symm yc).2
      have hnotAE : (eC.symm yc).1 ∉ A ∪ E := (mem_sdiff.mp h3).2
      have hnotA : (eC.symm yc).1 ∉ A := fun ha => hnotAE (mem_union_left _ ha)
      have hnotE : (eC.symm yc).1 ∉ E := fun he => hnotAE (mem_union_right _ he)
      dsimp only [toFun]
      split_ifs
      exact congrArg Subtype.val (eC.apply_symm_apply yc)
  let τ : Equiv.Perm (Fin B) := ⟨toFun, invFun, hleft, hright⟩
  refine Finset.card_bij (fun σ _ => τ.trans σ) ?_ ?_ ?_
  · intro σ hσ
    simp only [goodPerms, mem_filter, mem_univ, true_and] at hσ ⊢
    intro x hxA y hyE
    have hτx : τ x ∈ A' := by
      change toFun x ∈ A'
      dsimp only [toFun]
      split_ifs
      exact (eA ⟨x, hxA⟩).2
    have hτy : τ y ∈ E' := by
      have hxnot : y ∉ A := disjoint_right.mp hd hyE
      change toFun y ∈ E'
      dsimp only [toFun]
      split_ifs
      exact (eE ⟨y, hyE⟩).2
    exact hσ (τ x) hτx (τ y) hτy
  · intro σ₁ _ σ₂ _ heq
    exact Equiv.Perm.ext fun z => by
      have h1 := Equiv.Perm.ext_iff.mp heq (τ.symm z)
      simpa [Equiv.trans_apply] using h1
  · intro σ hσ
    refine ⟨τ.symm.trans σ, ?_, ?_⟩
    · simp only [goodPerms, mem_filter, mem_univ, true_and] at hσ ⊢
      intro x' hx' y' hy'
      have hτx : τ.symm x' ∈ A := by
        change invFun x' ∈ A
        dsimp only [invFun]
        split_ifs
        exact (eA.symm ⟨x', hx'⟩).2
      have hτy : τ.symm y' ∈ E := by
        have hynot : y' ∉ A' := disjoint_right.mp hd' hy'
        change invFun y' ∈ E
        dsimp only [invFun]
        split_ifs
        exact (eE.symm ⟨y', hy'⟩).2
      exact hσ (τ.symm x') hτx (τ.symm y') hτy
    · exact Equiv.Perm.ext fun z => by simp [Equiv.trans_apply]

/-- Exact permutation-counting identity for disjoint subsets `A, E ⊆ Fin B`. -/
theorem choose_mul_card_goodPerms_eq_factorial {B : ℕ} {A E : Finset (Fin B)}
    (hd : Disjoint A E) :
    Nat.choose (A.card + E.card) A.card * (goodPerms A E).card = Nat.factorial B := by
  let S := A ∪ E
  have hS_card : S.card = A.card + E.card := card_union_of_disjoint hd
  have hcov : (univ : Finset (Equiv.Perm (Fin B))) =
      (S.powersetCard A.card).biUnion (fun A' => goodPerms A' (S \ A')) := by
    symm
    apply eq_univ_of_forall
    intro σ
    obtain ⟨A', hA', hgood⟩ := exists_initial_subset_of_perm σ A.card S (by omega)
    exact mem_biUnion.mpr ⟨A', hA', hgood⟩
  have hpw : ∀ A₁ ∈ S.powersetCard A.card, ∀ A₂ ∈ S.powersetCard A.card, A₁ ≠ A₂ →
      Disjoint (goodPerms A₁ (S \ A₁)) (goodPerms A₂ (S \ A₂)) := by
    intro A₁ h1 A₂ h2 hne
    have hc1 : A₁.card = A.card := (mem_powersetCard.mp h1).2
    rw [← hc1] at h1 h2
    exact disjoint_goodPerms_of_ne h1 h2 hne
  have huniv_card : (univ : Finset (Equiv.Perm (Fin B))).card = Nat.factorial B := by
    rw [card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← huniv_card, hcov, card_biUnion hpw]
  have hterm_eq : ∀ A' ∈ S.powersetCard A.card,
      (goodPerms A' (S \ A')).card = (goodPerms A E).card := by
    intro A' hA'
    obtain ⟨hA'S, hA'c⟩ := mem_powersetCard.mp hA'
    have hEc : (S \ A').card = E.card := by
      have hs := card_sdiff_add_card_inter S A'
      rw [inter_eq_right.mpr hA'S] at hs
      omega
    exact card_goodPerms_eq_of_card_eq hd disjoint_sdiff_self_right hA'c.symm hEc.symm
  rw [sum_congr rfl hterm_eq, sum_const, card_powersetCard, hS_card, smul_eq_mul]

/-- Averaging over all permutations of `Fin B` produces a ranking `σ` that separates at least
`∑_{q ∈ Q_*} 1 / C(|A(q)| + |E(q)|, |A(q)|)` elements of `V₀`. -/
theorem exists_ranking_card_ge {V : Type*} [DecidableEq V] {B : ℕ}
    (V₀ : Finset V) (A_blk E_blk : V → Finset (Fin B)) :
    let Q_star := V₀.filter fun q => Disjoint (A_blk q) (E_blk q)
    ∃ σ : Equiv.Perm (Fin B),
      (∑ q ∈ Q_star,
        (1 : ℝ) / (Nat.choose ((A_blk q).card + (E_blk q).card) (A_blk q).card : ℝ)) ≤
          ((cutSet V₀ A_blk E_blk σ).card : ℝ) := by
  intro Q_star
  have hsum_ge : (Nat.factorial B : ℝ) *
      (∑ q ∈ Q_star,
        (1 : ℝ) / (Nat.choose ((A_blk q).card + (E_blk q).card) (A_blk q).card : ℝ)) ≤
      ∑ σ : Equiv.Perm (Fin B), ((cutSet V₀ A_blk E_blk σ).card : ℝ) := by
    have h_each : ∀ q ∈ Q_star,
        (Nat.factorial B : ℝ) *
          ((1 : ℝ) / (Nat.choose ((A_blk q).card + (E_blk q).card) (A_blk q).card : ℝ)) =
          ((goodPerms (A_blk q) (E_blk q)).card : ℝ) := by
      intro q hq
      have hd : Disjoint (A_blk q) (E_blk q) := (mem_filter.mp hq).2
      have hid := choose_mul_card_goodPerms_eq_factorial hd
      have hch_pos : (0 : ℝ) <
          (Nat.choose ((A_blk q).card + (E_blk q).card) (A_blk q).card : ℝ) := by
        exact_mod_cast Nat.choose_pos (Nat.le_add_right _ _)
      have hid_r : (Nat.choose ((A_blk q).card + (E_blk q).card) (A_blk q).card : ℝ) *
          ((goodPerms (A_blk q) (E_blk q)).card : ℝ) = (Nat.factorial B : ℝ) := by
        exact_mod_cast hid
      rw [← hid_r]
      field_simp
    rw [mul_sum, sum_congr rfl h_each]
    have hnat : ∑ q ∈ Q_star, (goodPerms (A_blk q) (E_blk q)).card ≤
        ∑ σ : Equiv.Perm (Fin B), (cutSet V₀ A_blk E_blk σ).card := by
      calc ∑ q ∈ Q_star, (goodPerms (A_blk q) (E_blk q)).card
          ≤ ∑ q ∈ V₀, (goodPerms (A_blk q) (E_blk q)).card :=
            sum_le_sum_of_subset (filter_subset _ _)
        _ = ∑ q ∈ V₀, ∑ σ : Equiv.Perm (Fin B),
              (if ∀ x ∈ A_blk q, ∀ y ∈ E_blk q, σ x < σ y then 1 else 0) := by
            refine sum_congr rfl fun q _ => ?_
            rw [goodPerms, card_filter]
        _ = ∑ σ : Equiv.Perm (Fin B), ∑ q ∈ V₀,
              (if ∀ x ∈ A_blk q, ∀ y ∈ E_blk q, σ x < σ y then 1 else 0) := sum_comm
        _ = ∑ σ : Equiv.Perm (Fin B), (cutSet V₀ A_blk E_blk σ).card := by
            refine sum_congr rfl fun σ _ => ?_
            rw [cutSet, card_filter]
            refine sum_congr rfl fun q _ => ?_
            by_cases h : ∀ x ∈ A_blk q, ∀ y ∈ E_blk q, σ x < σ y <;> simp [h]
    exact_mod_cast hnat
  by_contra hcon
  have hne : (univ : Finset (Equiv.Perm (Fin B))).Nonempty := ⟨Equiv.refl _, mem_univ _⟩
  have hlt : ∑ σ ∈ (univ : Finset (Equiv.Perm (Fin B))), ((cutSet V₀ A_blk E_blk σ).card : ℝ) <
      ∑ _σ ∈ (univ : Finset (Equiv.Perm (Fin B))),
        (∑ q ∈ Q_star,
          (1 : ℝ) / (Nat.choose ((A_blk q).card + (E_blk q).card) (A_blk q).card : ℝ)) := by
    refine sum_lt_sum_of_nonempty hne fun σ _ => ?_
    by_contra hge
    exact hcon ⟨σ, not_lt.mp hge⟩
  rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] at hlt
  linarith

/-- Monotonicity of `Nat.choose (a + e) a` in both `a` and `e`. -/
theorem choose_add_mono {a₁ a₂ e₁ e₂ : ℕ} (ha : a₁ ≤ a₂) (he : e₁ ≤ e₂) :
    Nat.choose (a₁ + e₁) a₁ ≤ Nat.choose (a₂ + e₂) a₂ := by
  have h1 : ∀ d a e : ℕ, Nat.choose (a + e) a ≤ Nat.choose (a + d + e) (a + d) := by
    intro d
    induction d with
    | zero => intro a e; simp
    | succ d ih =>
      intro a e
      calc Nat.choose (a + e) a ≤ Nat.choose (a + d + e) (a + d) := ih a e
        _ ≤ Nat.choose (a + d + e) (a + d) + Nat.choose (a + d + e) (a + d + 1) :=
          Nat.le_add_right _ _
        _ = Nat.choose (a + (d + 1) + e) (a + (d + 1)) := by
          have heq1 : a + (d + 1) + e = (a + d + e) + 1 := by omega
          have heq2 : a + (d + 1) = (a + d) + 1 := by omega
          rw [heq1, heq2, Nat.choose_succ_succ]
  have h2 : ∀ d a e : ℕ, Nat.choose (a + e) a ≤ Nat.choose (a + (e + d)) a := by
    intro d
    induction d with
    | zero => intro a e; simp
    | succ d ih =>
      intro a e
      rcases a with _ | a'
      · simp
      · calc Nat.choose (a' + 1 + e) (a' + 1)
            ≤ Nat.choose (a' + 1 + (e + d)) (a' + 1) := ih (a' + 1) e
          _ ≤ Nat.choose (a' + 1 + (e + d)) a' + Nat.choose (a' + 1 + (e + d)) (a' + 1) :=
            Nat.le_add_left _ _
          _ = Nat.choose (a' + 1 + (e + (d + 1))) (a' + 1) := by
            have heq : a' + 1 + (e + (d + 1)) = (a' + 1 + (e + d)) + 1 := by omega
            rw [heq, Nat.choose_succ_succ]
  calc Nat.choose (a₁ + e₁) a₁
      ≤ Nat.choose (a₁ + (a₂ - a₁) + e₁) (a₁ + (a₂ - a₁)) := h1 (a₂ - a₁) a₁ e₁
    _ = Nat.choose (a₂ + e₁) a₂ := by rw [Nat.add_sub_of_le ha]
    _ ≤ Nat.choose (a₂ + (e₁ + (e₂ - e₁))) a₂ := h2 (e₂ - e₁) a₂ e₁
    _ = Nat.choose (a₂ + e₂) a₂ := by rw [Nat.add_sub_of_le he]

end LeanMachine.BlockRanking
