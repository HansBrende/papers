import Transpose.Tape.Forest
import Transpose.Tape.Blocks

/-!
# The Disjointness Lemma, input part (the time-ordered chain), and the coverage count

* `read_chain_abstract` / `read_chain`: ordered in time, the read sets of time-separated nodes in
  one pass each meet the union of the earlier ones in at most one position.
* `readSet_convex`: a node reads an interval of input positions (unit steps).
* `residue_count`: an interval of length `λ` meets a set `Res` of residues mod `m` in at most
  `|Res| (λ + m) / m` positions.
* `combSet_subset_residue`: the comb of a group of columns is a residue set mod `n b`.
* Groups of columns: `numGroups_mul_ge` (`n ≤ ⌈n/γ⌉ γ`), `mul_numGroups_lt` (`γ ⌈n/γ⌉ < n + γ`).
* `coverage_per_address`, `coverage_grouped` (any `γ`; for `γ = 0` there are no groups).
-/

namespace Transpose.Tape.Impl

open Transpose

/-! ### The time-ordered input chain -/

/-- **The input chain, abstract form.** Let the input head be monotone on `[a, e]` and let the
step sets `N s` (`s ∈ S`) inside `[a, e)` be pairwise time-separated. Then their read sets in
`[0, L)` satisfy `Σ_s |I_s| + 1 ≤ L + |S|`. -/
theorem read_chain_abstract {ip : ℕ → ℤ} {a e L : ℕ} (hm : MonoOn ip a e) {ι : Type*}
    (S : Finset ι) (hS : S.Nonempty) (N : ι → Finset ℕ)
    (hN : ∀ s ∈ S, ∀ τ ∈ N s, a ≤ τ ∧ τ < e)
    (hsep : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → TimeSep (N s) (N s')) :
    ∑ s ∈ S, (readSet ip L (N s)).card + 1 ≤ L + S.card := by
  classical
  set R : ι → Finset ℕ := fun s => readSet ip L (N s) with hR
  have key : ∀ S' : Finset ι, S' ⊆ S →
      ∑ s ∈ S', (R s).card ≤ (S'.biUnion R).card + S'.card - 1 := by
    intro S'
    refine Finset.induction_on_max_value
      (motive := fun S' => S' ⊆ S → ∑ s ∈ S', (R s).card ≤ (S'.biUnion R).card + S'.card - 1)
      (fun s => firstStep (N s)) S' (fun _ => by simp) ?_
    intro x S' hx hmax ih hsub
    have hxS : x ∈ S := hsub (Finset.mem_insert_self _ _)
    have ih' := ih (fun y hy => hsub (Finset.mem_insert_of_mem hy))
    rw [Finset.sum_insert hx, Finset.biUnion_insert, Finset.card_insert_of_notMem hx]
    -- the read set of the time-last node meets the earlier ones in at most one position
    have hinter : (R x ∩ S'.biUnion R).card ≤ 1 := by
      have hval : ∀ d ∈ R x ∩ S'.biUnion R, (d : ℤ) = ip (firstStep (N x)) := by
        intro d hd
        rw [Finset.mem_inter, Finset.mem_biUnion] at hd
        obtain ⟨hdx, y, hy, hdy⟩ := hd
        simp only [hR, readSet, Finset.mem_filter, Finset.mem_range] at hdx hdy
        obtain ⟨-, τ, hτ, hτd⟩ := hdx
        obtain ⟨-, τ', hτ', hτ'd⟩ := hdy
        have hyS : y ∈ S := hsub (Finset.mem_insert_of_mem hy)
        have hyx : y ≠ x := fun h => hx (h ▸ hy)
        have ha : firstStep (N x) ∈ N x := firstStep_mem ⟨τ, hτ⟩
        have haτ : firstStep (N x) ≤ τ := firstStep_le hτ
        have hτ'a : τ' < firstStep (N x) := by
          rcases hsep y hyS x hxS hyx with h | h
          · exact h τ' hτ' _ ha
          · exfalso
            have h1 := h (firstStep (N y)) (firstStep_mem ⟨τ', hτ'⟩) _ ha
            have h2 : firstStep (N y) ≤ firstStep (N x) := hmax y hy
            omega
        have m1 := hN x hxS τ hτ
        have m2 := hN x hxS _ ha
        have m3 := hN y hyS τ' hτ'
        rcases monoOn_cases hm with up | dn
        · have e1 := up τ' _ m3.1 (le_of_lt hτ'a) (le_of_lt m2.2)
          have e2 := up _ τ m2.1 haτ (le_of_lt m1.2)
          omega
        · have e1 := dn τ' _ m3.1 (le_of_lt hτ'a) (le_of_lt m2.2)
          have e2 := dn _ τ m2.1 haτ (le_of_lt m1.2)
          omega
      apply Finset.card_le_one.2
      intro d hd d' hd'
      have := hval d hd
      have := hval d' hd'
      omega
    have hu := Finset.card_union_add_card_inter (R x) (S'.biUnion R)
    rcases S'.eq_empty_or_nonempty with he | hne
    · subst he; simp
    · have := hne.card_pos
      omega
  have h1 := key S (subset_refl _)
  have h2 : (S.biUnion R).card ≤ L := by
    calc (S.biUnion R).card ≤ (Finset.range L).card := Finset.card_le_card (by
          intro d hd
          rw [Finset.mem_biUnion] at hd
          obtain ⟨s, -, hds⟩ := hd
          simp only [hR, readSet, Finset.mem_filter] at hds
          exact hds.1)
      _ = L := Finset.card_range L
  have h3 := hS.card_pos
  show ∑ s ∈ S, (R s).card + 1 ≤ L + S.card
  omega

section Chain

variable {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}

/-- **The Disjointness Lemma, input part (the time-ordered chain).** -/
theorem read_chain (hp : PassPartition M w T r p) {α : ℕ × List (ℕ × Fin M.k)}
    (hα : α ∈ addresses M.k r) {L : ℕ} {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (o₁ o₂ : ι → ℕ) (hdisj : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → o₂ s ≤ o₁ s' ∨ o₂ s' ≤ o₁ s) :
    ∑ s ∈ S, (readSet (inTraj M w) L (forestNode M w p (o₁ s) (o₂ s) α.1 α.2)).card + 1 ≤
      L + S.card := by
  have hPr : lastPass α.2 α.1 < r := lastPass_lt hα
  refine read_chain_abstract (hp.2.2.2 _ hPr).1 S hS _ (fun s _ τ hτ => ?_) (fun s _ s' _ hss' => ?_)
  · exact mem_passSteps.1 ((forestNode_inv hp hα _ _).1 hτ)
  · rcases hdisj s ‹_› s' ‹_› hss' with h | h
    · exact forestNode_timeSep hp hα h
    · exact timeSep_symm (forestNode_timeSep hp hα h)

end Chain

/-! ### Read sets are intervals -/

theorem readSet_convex {ip : ℕ → ℤ} (hip : UnitSteps ip) {L : ℕ} {N : Finset ℕ}
    (hN : IsConvex N) : IsConvex (readSet ip L N) := by
  classical
  intro d₁ h₁ d₂ h₂ d hd₁ hd₂
  simp only [readSet, Finset.mem_filter, Finset.mem_range] at h₁ h₂ ⊢
  obtain ⟨-, τ₁, hτ₁, e₁⟩ := h₁
  obtain ⟨hL₂, τ₂, hτ₂, e₂⟩ := h₂
  refine ⟨by omega, ?_⟩
  rcases le_total τ₁ τ₂ with h | h
  · obtain ⟨τ, h1, h2, hτ⟩ := discrete_ivt hip h (β := (d : ℤ))
      (by rw [e₁, e₂]; constructor <;> omega)
    exact ⟨τ, hN τ₁ hτ₁ τ₂ hτ₂ τ h1 h2, hτ⟩
  · obtain ⟨τ, h1, h2, hτ⟩ := discrete_ivt hip h (β := (d : ℤ))
      (by rw [e₁, e₂]; constructor <;> omega)
    exact ⟨τ, hN τ₂ hτ₂ τ₁ hτ₁ τ h1 h2, hτ⟩

/-! ### Residues in an interval -/

/-- In a convex set `R` of naturals, at most `|Res| (|R| + m) / m` elements have their residue
mod `m` in `Res`. -/
theorem residue_count {R Res : Finset ℕ} {m : ℕ} (hR : IsConvex R) :
    m * (R.filter (fun d => d % m ∈ Res)).card ≤ Res.card * (R.card + m) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases R.eq_empty_or_nonempty with he | hne
  · subst he; simp
  set u := R.min' hne with hu
  set v := R.max' hne with hv
  have hRI : R = Finset.Icc u v := convex_eq_Icc hR hne
  have hcard : R.card = v + 1 - u := by rw [hRI, Nat.card_Icc]
  have inj : ∀ d d', u ≤ d → d ≤ d' → d % m = d' % m → (d - u) / m = (d' - u) / m → d = d' := by
    intro d d' hud hle hmod hdiv
    have e1 := Nat.div_add_mod (d - u) m
    have e2 := Nat.div_add_mod (d' - u) m
    have e3 := Nat.mod_lt (d - u) hm
    have e4 := Nat.mod_lt (d' - u) hm
    rw [hdiv] at e1
    have hlt : d' - d < m := by omega
    have hdvd : m ∣ d' - d := (Nat.modEq_iff_dvd' (n := m) hle).1 hmod
    have := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  have hF : (R.filter (fun d => d % m ∈ Res)).card ≤
      (Res ×ˢ Finset.range ((v - u) / m + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun d => (d % m, (d - u) / m))
    · intro d hd
      rw [Finset.mem_coe, Finset.mem_filter] at hd
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
      have hdR : d ∈ Finset.Icc u v := hRI ▸ hd.1
      rw [Finset.mem_Icc] at hdR
      exact ⟨hd.2, Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))⟩
    · intro d hd d' hd' heq
      rw [Finset.mem_coe, Finset.mem_filter] at hd hd'
      have h1 : d ∈ Finset.Icc u v := hRI ▸ hd.1
      have h2 : d' ∈ Finset.Icc u v := hRI ▸ hd'.1
      rw [Finset.mem_Icc] at h1 h2
      simp only [Prod.mk.injEq] at heq
      rcases le_total d d' with hle | hle
      · exact inj d d' h1.1 hle heq.1 heq.2
      · exact (inj d' d h2.1 hle heq.1.symm heq.2.symm).symm
  rw [Finset.card_product, Finset.card_range] at hF
  have h1 : m * ((v - u) / m) ≤ v - u := Nat.mul_div_le (v - u) m
  calc m * (R.filter (fun d => d % m ∈ Res)).card ≤ m * (Res.card * ((v - u) / m + 1)) :=
        Nat.mul_le_mul_left _ hF
    _ = Res.card * (m * ((v - u) / m) + m) := by ring
    _ ≤ Res.card * (R.card + m) := Nat.mul_le_mul_left _ (by omega)

/-! ### Combs of groups of columns -/

/-- The comb of the columns `[j₁, j₂)` consists of input bits whose position mod `n b` lies in
`[j₁ b, j₂ b)`. -/
theorem combSet_subset_residue (n b j₁ j₂ : ℕ) :
    combSet n b (j₁ * (n * b)) (j₂ * (n * b)) ⊆
      (Finset.range (n * n * b)).filter (fun d => d % (n * b) ∈ Finset.Ico (j₁ * b) (j₂ * b)) := by
  intro d hd
  simp only [combSet, Finset.mem_filter, Finset.mem_range] at hd ⊢
  obtain ⟨hdL, h1, h2⟩ := hd
  refine ⟨hdL, ?_⟩
  obtain ⟨hi, hj, ht, hdec⟩ := pos_decomp hdL
  have htp : tpos n b d = (d / b % n * n + d / b / n) * b + d % b := rfl
  rw [htp] at h1 h2
  generalize d / b / n = i at hi hdec h1 h2
  generalize d / b % n = j at hj hdec h1 h2
  generalize d % b = t at ht hdec h1 h2
  -- the column `j` of `d` lies in `[j₁, j₂)`
  have hrow : (j * n + i) * b + t < (j + 1) * (n * b) :=
    calc (j * n + i) * b + t < (j * n + i) * b + b := by omega
      _ = (j * n + i + 1) * b := by ring
      _ ≤ (j * n + n) * b := Nat.mul_le_mul_right _ (by omega)
      _ = (j + 1) * (n * b) := by ring
  have hcol1 : j₁ ≤ j := by
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul_right (n * b) (show j + 1 ≤ j₁ by omega)
    omega
  have hcol2 : j < j₂ := by
    by_contra hc
    push Not at hc
    have e1 : j₂ * (n * b) ≤ j * (n * b) := Nat.mul_le_mul_right _ hc
    have e2 : j * (n * b) ≤ (j * n + i) * b + t :=
      calc j * (n * b) = (j * n) * b := by ring
        _ ≤ (j * n + i) * b := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        _ ≤ (j * n + i) * b + t := Nat.le_add_right _ _
    omega
  -- the residue of `d`
  have hjb : j * b + t < n * b :=
    calc j * b + t < j * b + b := by omega
      _ = (j + 1) * b := by ring
      _ ≤ n * b := Nat.mul_le_mul_right _ hj
  have hmod : d % (n * b) = j * b + t := by
    have : d = n * b * i + (j * b + t) := by rw [hdec]; ring
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hjb]
  rw [hmod, Finset.mem_Ico]
  constructor
  · calc j₁ * b ≤ j * b := Nat.mul_le_mul_right _ hcol1
      _ ≤ j * b + t := Nat.le_add_right _ _
  · calc j * b + t < j * b + b := by omega
      _ = (j + 1) * b := by ring
      _ ≤ j₂ * b := Nat.mul_le_mul_right _ hcol2

/-! ### Groups -/

theorem segLo_mono (n b γ : ℕ) {s s' : ℕ} (h : s ≤ s') : segLo n b γ s ≤ segLo n b γ s' := by
  unfold segLo
  apply Nat.mul_le_mul_right
  have : s * γ ≤ s' * γ := Nat.mul_le_mul_right _ h
  omega

theorem numGroups_mul_ge {n γ : ℕ} (hγ : 1 ≤ γ) : n ≤ numGroups n γ * γ := by
  unfold numGroups
  have h1 := Nat.div_add_mod (n + γ - 1) γ
  have h2 := Nat.mod_lt (n + γ - 1) (show 0 < γ by omega)
  rw [Nat.mul_comm]
  omega

theorem segLo_numGroups (n b : ℕ) {γ : ℕ} (hγ : 1 ≤ γ) :
    segLo n b γ (numGroups n γ) = n * (n * b) := by
  unfold segLo
  rw [min_eq_right (numGroups_mul_ge hγ)]

theorem numGroups_pos {n γ : ℕ} (hγ : 1 ≤ γ) (hn : 1 ≤ n) : 0 < numGroups n γ := by
  unfold numGroups
  exact Nat.div_pos (by omega) (by omega)

/-- `γ ⌈n/γ⌉ < n + γ`. -/
theorem mul_numGroups_lt (n : ℕ) {γ : ℕ} (hγ : 1 ≤ γ) : γ * numGroups n γ < n + γ := by
  simp only [numGroups]
  have := Nat.div_mul_le_self (n + γ - 1) γ
  have h' : (n + γ - 1) / γ * γ = γ * ((n + γ - 1) / γ) := by ring
  omega

theorem numGroups_sub_one_mul {n γ : ℕ} (hγ : 1 ≤ γ) (hn : 1 ≤ n) :
    (numGroups n γ - 1) * γ < n := by
  have := mul_numGroups_lt n hγ
  have h2 : (numGroups n γ - 1) * γ = γ * numGroups n γ - γ := by
    rw [Nat.sub_mul, one_mul, Nat.mul_comm]
  omega

theorem sum_width (n γ K : ℕ) :
    ∑ s ∈ Finset.range K, (min ((s + 1) * γ) n - min (s * γ) n) = min (K * γ) n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have : K * γ ≤ (K + 1) * γ := Nat.mul_le_mul_right _ (Nat.le_succ K)
    omega

theorem width_le (n γ s : ℕ) : min ((s + 1) * γ) n - min (s * γ) n ≤ γ := by
  have : (s + 1) * γ = s * γ + γ := by ring
  omega

/-! ### Coverage -/

section Coverage

variable {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}

/-- **Coverage per address (groups of `γ` columns).** -/
theorem coverage_per_address {n b γ : ℕ} (hp : PassPartition M w T r p)
    {α : ℕ × List (ℕ × Fin M.k)} (hα : α ∈ addresses M.k r) :
    ∑ s ∈ Finset.range (numGroups n γ),
      (combSet n b (segLo n b γ s) (segHi n b γ s) ∩
        readSet (inTraj M w) (n * n * b)
          (forestNode M w p (segLo n b γ s) (segHi n b γ s) α.1 α.2)).card ≤
      (γ + 1) * n * b := by
  classical
  rcases Nat.eq_zero_or_pos γ with rfl | hγ
  · simp [numGroups]
  replace hγ : 1 ≤ γ := hγ
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp [combSet]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : numGroups 0 γ = 0 := by unfold numGroups; exact Nat.div_eq_of_lt (by omega)
    simp [this]
  set G := numGroups n γ with hG
  set R : ℕ → Finset ℕ := fun s => readSet (inTraj M w) (n * n * b)
    (forestNode M w p (segLo n b γ s) (segHi n b γ s) α.1 α.2) with hR
  set C : ℕ → Finset ℕ := fun s => combSet n b (segLo n b γ s) (segHi n b γ s) ∩ R s with hC
  set g : ℕ → ℕ := fun s => min ((s + 1) * γ) n - min (s * γ) n with hg
  show ∑ s ∈ Finset.range G, (C s).card ≤ (γ + 1) * n * b
  -- one group: the residue count
  have hper : ∀ s, (n * b) * (C s).card ≤ g s * b * ((R s).card + n * b) := by
    intro s
    have hsub : C s ⊆ (R s).filter (fun d => d % (n * b) ∈
        Finset.Ico (min (s * γ) n * b) (min ((s + 1) * γ) n * b)) := by
      intro d hd
      rw [hC, Finset.mem_inter] at hd
      have := combSet_subset_residue n b (min (s * γ) n) (min ((s + 1) * γ) n) hd.1
      rw [Finset.mem_filter] at this ⊢
      exact ⟨hd.2, this.2⟩
    have hconv : IsConvex (R s) :=
      readSet_convex (unitSteps_inTraj M w) (forestNode_inv hp hα _ _).2
    have := residue_count (Res := Finset.Ico (min (s * γ) n * b) (min ((s + 1) * γ) n * b))
      (m := n * b) hconv
    rw [Nat.card_Ico] at this
    calc (n * b) * (C s).card ≤ (n * b) * ((R s).filter (fun d => d % (n * b) ∈
          Finset.Ico (min (s * γ) n * b) (min ((s + 1) * γ) n * b))).card :=
          Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
      _ ≤ (min ((s + 1) * γ) n * b - min (s * γ) n * b) * ((R s).card + n * b) := this
      _ = g s * b * ((R s).card + n * b) := by rw [hg, ← Nat.sub_mul]
  -- the chain over groups
  have hchain : ∑ s ∈ Finset.range G, (R s).card + 1 ≤ n * n * b + G := by
    have := read_chain (L := n * n * b) hp hα (Finset.range G)
      (Finset.nonempty_range_iff.2 (Nat.pos_iff_ne_zero.1 (numGroups_pos hγ hn)))
      (segLo n b γ) (segHi n b γ) (fun s _ s' _ hss' => by
        rcases Nat.lt_or_gt_of_ne hss' with h | h
        · exact Or.inl (segLo_mono n b γ (show s + 1 ≤ s' by omega))
        · exact Or.inr (segLo_mono n b γ (show s' + 1 ≤ s by omega)))
    simpa [Finset.card_range] using this
  have hsumg : ∑ s ∈ Finset.range G, g s = n := by
    rw [hg, sum_width]; exact min_eq_right (numGroups_mul_ge hγ)
  have h1 : (n * b) * ∑ s ∈ Finset.range G, (C s).card ≤
      ∑ s ∈ Finset.range G, g s * b * ((R s).card + n * b) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun s _ => hper s)
  have h2 : ∑ s ∈ Finset.range G, g s * b * ((R s).card + n * b) ≤
      b * (γ * ∑ s ∈ Finset.range G, (R s).card) + b * (n * b) * n := by
    calc ∑ s ∈ Finset.range G, g s * b * ((R s).card + n * b)
        = b * ∑ s ∈ Finset.range G, g s * (R s).card +
            b * (n * b) * ∑ s ∈ Finset.range G, g s := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro s _; ring
      _ ≤ b * (γ * ∑ s ∈ Finset.range G, (R s).card) + b * (n * b) * n := by
          rw [hsumg]
          apply Nat.add_le_add_right
          apply Nat.mul_le_mul_left
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun s _ => Nat.mul_le_mul_right _ (width_le n γ s))
  have h3 : n * ∑ s ∈ Finset.range G, (C s).card ≤
      γ * ∑ s ∈ Finset.range G, (R s).card + n * b * n := by
    have : b * (n * ∑ s ∈ Finset.range G, (C s).card) ≤
        b * (γ * ∑ s ∈ Finset.range G, (R s).card + n * b * n) := by
      calc b * (n * ∑ s ∈ Finset.range G, (C s).card)
          = (n * b) * ∑ s ∈ Finset.range G, (C s).card := by ring
        _ ≤ _ := le_trans h1 h2
        _ = b * (γ * ∑ s ∈ Finset.range G, (R s).card + n * b * n) := by ring
    exact Nat.le_of_mul_le_mul_left this hb
  have h4 : (G - 1) * γ < n := numGroups_sub_one_mul hγ hn
  have h5 : γ * ∑ s ∈ Finset.range G, (R s).card ≤ γ * (n * n * b) + (G - 1) * γ := by
    have : ∑ s ∈ Finset.range G, (R s).card ≤ n * n * b + (G - 1) := by omega
    calc γ * ∑ s ∈ Finset.range G, (R s).card ≤ γ * (n * n * b + (G - 1)) :=
          Nat.mul_le_mul_left _ this
      _ = γ * (n * n * b) + (G - 1) * γ := by ring
  have h6 : n * ∑ s ∈ Finset.range G, (C s).card < n * ((γ + 1) * n * b + 1) := by
    calc n * ∑ s ∈ Finset.range G, (C s).card ≤ γ * ∑ s ∈ Finset.range G, (R s).card + n * b * n :=
          h3
      _ ≤ γ * (n * n * b) + (G - 1) * γ + n * b * n := Nat.add_le_add_right h5 _
      _ < γ * (n * n * b) + n + n * b * n := by omega
      _ = n * ((γ + 1) * n * b + 1) := by ring
  have := Nat.lt_of_mul_lt_mul_left h6
  omega

/-- **Coverage count (groups of `γ` columns).** -/
theorem coverage_grouped {n b γ : ℕ} (hp : PassPartition M w T r p) :
    ∑ s ∈ Finset.range (numGroups n γ),
      (combSet n b (segLo n b γ s) (segHi n b γ s) ∩
        readSet (inTraj M w) (n * n * b) (forest M w p r (segLo n b γ s) (segHi n b γ s))).card ≤
      (addresses M.k r).card * ((γ + 1) * n * b) := by
  classical
  calc _ ≤ ∑ s ∈ Finset.range (numGroups n γ), ∑ α ∈ addresses M.k r,
        (combSet n b (segLo n b γ s) (segHi n b γ s) ∩ readSet (inTraj M w) (n * n * b)
          (forestNode M w p (segLo n b γ s) (segHi n b γ s) α.1 α.2)).card := by
        apply Finset.sum_le_sum
        intro s _
        refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
        intro d hd
        rw [Finset.mem_inter] at hd
        obtain ⟨hdc, hdr⟩ := hd
        simp only [readSet, Finset.mem_filter, Finset.mem_range, forest,
          Finset.mem_biUnion] at hdr
        obtain ⟨hdL, τ, ⟨α, hα, hτ⟩, hτd⟩ := hdr
        rw [Finset.mem_biUnion]
        refine ⟨α, hα, Finset.mem_inter.2 ⟨hdc, ?_⟩⟩
        simp only [readSet, Finset.mem_filter, Finset.mem_range]
        exact ⟨hdL, τ, hτ, hτd⟩
    _ = ∑ α ∈ addresses M.k r, ∑ s ∈ Finset.range (numGroups n γ),
        (combSet n b (segLo n b γ s) (segHi n b γ s) ∩ readSet (inTraj M w) (n * n * b)
          (forestNode M w p (segLo n b γ s) (segHi n b γ s) α.1 α.2)).card := Finset.sum_comm
    _ ≤ ∑ _α ∈ addresses M.k r, (γ + 1) * n * b :=
        Finset.sum_le_sum (fun α hα => coverage_per_address hp hα)
    _ = (addresses M.k r).card * ((γ + 1) * n * b) := by rw [Finset.sum_const, smul_eq_mul]

end Coverage

end Transpose.Tape.Impl
