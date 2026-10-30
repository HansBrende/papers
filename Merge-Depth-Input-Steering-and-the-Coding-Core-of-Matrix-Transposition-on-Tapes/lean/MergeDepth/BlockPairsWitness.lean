import MergeDepth.BlockPairsModel

/-!
# Block pairs: half-blindness, witnesses and Theorem BP (Lemmas 7.8, 7.9, Theorem 7.10)

The probabilities are over the odd residues `ξ` modulo `P` (`oddRange (dnpPeriod s0 m)`, uniform).

* `BlindnessBound s0 m`: the odd-shift blindness bound of the eighth paper's Proposition 5.17 (in
  the form without its level-`0` term, which is all that is used): a window `(p, u]` of either head
  is blind with probability at least `N⁻¹ ∑_{i=1}^{m} (1 - (u - p)/R_i)^+ - 2/(N R_m)`. It is a
  hypothesis of Lemma 7.8 and Theorem BP.
* `card_not_blind_le`: from it and the hop lengths of the families, every hop of a family of a
  level-`k` class is non-blind with probability at most `ε_g = (g + 4 + ⌈log₂(g + 2)⌉)/N`, `g = m - k`
  (`epsG`); `card_not_halfBlind_le`: the family fails to be half-blind with probability at most
  `2 ε_g`.
* **Lemma 7.8**: `sum_nonHalfBlind_le`, the expected number of non-half-blind triples `(h, k, f)` with
  `k ∈ ℱ_ε` (`nonHalfBlind`) is at most `64 ε² m`; `prob_many_nonHalfBlind_le`, more than
  `δ |ℱ_ε|` of them, `δ = 1/(48 (a₀ + 1))`, occur with probability at most `6144 (a₀ + 1) ε`.
* **Lemma 7.9**: `witnesses_unserved`, with its three cases `case1_unserved` (the run bound in windows
  of `11` fine levels), `case2_unserved` (the overflow bound on a residue class of fine levels) and
  `case3_unserved` (Theorem V*, the residue bound and the V decomposition of the other head's
  potential at the `a`-good coarse levels, `witnessErr_ge_straddle`).
* **Theorem BP**: `theoremBP`, assuming `ConjectureS a` for `a = 1, …, a₀` and `BlindnessBound`.

Service is measured on the witness hops (`ServedOnWitness`); by the eighth paper's Lemma 5.1(b),(c)
(not formalized) a level that is doubly `θ`-served is doubly `θ`-served on its witness hops, so the
counts of `doublyServedLevels` bound the counts of doubly served levels from above.
-/

namespace MergeDepth

open Finset DirectedReciprocity

/-- The odd-shift blindness bound of the eighth paper's Proposition 5.17 (without its level-`0`
term): a window `(p, u]` of either head is blind at a uniformly random odd shift with probability at
least `N⁻¹ ∑_{i=1}^{m} (1 - (u - p)/R_i)^+ - 2/(N R_m)`. -/
def BlindnessBound (s0 m : ℕ) : Prop :=
  ∀ (h : Bool) (p u : ℤ), p < u →
    ((m : ℝ) + 1)⁻¹ * ∑ i ∈ Icc 1 m, max 0 (1 - ((u - p : ℤ) : ℝ) / scaleR s0 i) -
        2 / (((m : ℝ) + 1) * scaleR s0 m) ≤
      (((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ => BlindHop s0 m (ξ : ℤ) h p u).card : ℝ) /
        (oddRange (dnpPeriod s0 m)).card

/-- `ε_g = (g + 4 + ⌈log₂(g + 2)⌉)/N`. -/
noncomputable def epsG (m g : ℕ) : ℝ := ((g : ℝ) + 4 + Nat.clog 2 (g + 2)) / ((m : ℝ) + 1)

theorem scaleR_div_scaleR {s0 i L : ℕ} (hiL : i ≤ L) (hL : L ≤ s0) :
    (scaleR s0 L : ℝ) / scaleR s0 i = (1 / 2) ^ (L - i) := by
  rw [scaleR_real hL, scaleR_real (by omega)]
  have : (2 : ℝ)⁻¹ ^ L = (2 : ℝ)⁻¹ ^ i * (2 : ℝ)⁻¹ ^ (L - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hiL]
  rw [this]; field_simp

theorem sum_half_pow_le (L : ℕ) : ∑ i ∈ Icc 1 L, ((1 : ℝ) / 2) ^ (L - i) ≤ 2 := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hset : Icc 1 (L + 1) = insert (L + 1) (Icc 1 L) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hset, Finset.sum_insert (by simp), Nat.sub_self, pow_zero]
    have : ∑ i ∈ Icc 1 L, ((1 : ℝ) / 2) ^ (L + 1 - i) = (1 / 2) * ∑ i ∈ Icc 1 L, ((1 : ℝ) / 2) ^ (L - i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [mem_Icc] at hi
      rw [show L + 1 - i = (L - i) + 1 by omega, pow_succ]; ring
    rw [this]; linarith

/-- If `ℓ ≤ R_L`, the levels `1, …, L` contribute at least `L - 2` to the blindness sum. -/
theorem sum_max_ge {s0 m L : ℕ} (hLm : L ≤ m) (hms : m ≤ s0) {ℓ : ℝ} (hℓ : ℓ ≤ scaleR s0 L) :
    (L : ℝ) - 2 ≤ ∑ i ∈ Icc 1 m, max 0 (1 - ℓ / scaleR s0 i) := by
  have hsub : Icc 1 L ⊆ Icc 1 m := Finset.Icc_subset_Icc le_rfl hLm
  calc (L : ℝ) - 2 ≤ ∑ i ∈ Icc 1 L, (1 - ((1 : ℝ) / 2) ^ (L - i)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
        have := sum_half_pow_le L
        push_cast [Nat.add_sub_cancel]; linarith
    _ ≤ ∑ i ∈ Icc 1 L, max 0 (1 - ℓ / scaleR s0 i) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [mem_Icc] at hi
        have hR : (0 : ℝ) < scaleR s0 i := by exact_mod_cast scaleR_pos s0 i
        have : ℓ / scaleR s0 i ≤ (1 / 2) ^ (L - i) := by
          rw [← scaleR_div_scaleR (s0 := s0) hi.2 (by omega)]
          exact div_le_div_of_nonneg_right hℓ hR.le
        exact le_trans (by linarith) (le_max_right _ _)
    _ ≤ ∑ i ∈ Icc 1 m, max 0 (1 - ℓ / scaleR s0 i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => le_max_left _ _

theorem card_oddRange_pos (s0 m : ℕ) : (0 : ℝ) < (oddRange (dnpPeriod s0 m)).card := by
  obtain ⟨M', hM'⟩ : ∃ M', dnpPeriod s0 m = 2 * M' := ⟨dnpPeriod s0 m / 2, by
    have := dnpPeriod_even s0 m; omega⟩
  have hpos := dnpPeriod_pos s0 m
  rw [hM', card_oddRange_two_mul]; exact_mod_cast (by omega : 0 < M')

theorem one_le_clog (g : ℕ) : 1 ≤ Nat.clog 2 (g + 2) :=
  Nat.lt_clog_iff_pow_lt (by norm_num) |>.mpr (by simp; omega)


/-- Every hop of a family of a level-`k` class (`g = m - k`) fails to be blind with probability at most
`ε_g` (from the blindness bound and the hop lengths). -/
theorem card_not_blind_le {s0 m k f : ℕ} (hB : BlindnessBound s0 m) (hms : m < s0) (hk1 : 1 ≤ k)
    (hkm : k + 2 ≤ m) (hf : f < 4) (h : Bool) {η : ℤ × ℤ} (hη : η ∈ family s0 m k f) :
    (((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ => ¬ BlindHop s0 m (ξ : ℤ) h η.1 η.2).card : ℝ) ≤
      epsG m (m - k) * (oddRange (dnpPeriod s0 m)).card := by
  set Ω := oddRange (dnpPeriod s0 m) with hΩ
  have hΩpos : (0 : ℝ) < Ω.card := card_oddRange_pos s0 m
  have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hsplit := Finset.card_filter_add_card_filter_not (s := Ω)
    (fun ξ : ℕ => BlindHop s0 m (ξ : ℤ) h η.1 η.2)
  have hsplitR : ((Ω.filter fun ξ : ℕ => BlindHop s0 m (ξ : ℤ) h η.1 η.2).card : ℝ) +
      ((Ω.filter fun ξ : ℕ => ¬ BlindHop s0 m (ξ : ℤ) h η.1 η.2).card : ℝ) = Ω.card := by
    exact_mod_cast hsplit
  have hRm : (2 : ℝ) ≤ scaleR s0 m := by
    have : 2 ≤ scaleR s0 m := by
      unfold scaleR; exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num)
        (show 1 ≤ s0 - m by omega))
    exact_mod_cast this
  have h2R : 2 / (((m : ℝ) + 1) * scaleR s0 m) ≤ ((m : ℝ) + 1)⁻¹ := by
    rw [← one_div, div_le_div_iff₀ (by positivity) hN]; nlinarith
  have hc1 : ((m : ℝ) + 1)⁻¹ * ((m : ℝ) + 1) = 1 := inv_mul_cancel₀ hN.ne'
  have hinv : 0 < ((m : ℝ) + 1)⁻¹ := inv_pos.mpr hN
  -- it suffices that the blindness bound is at least `1 - ε_g`
  suffices hkey : 1 - epsG m (m - k) ≤ ((m : ℝ) + 1)⁻¹ *
      ∑ i ∈ Icc 1 m, max 0 (1 - ((η.2 - η.1 : ℤ) : ℝ) / scaleR s0 i) -
        2 / (((m : ℝ) + 1) * scaleR s0 m) by
    have hlt : η.1 < η.2 := by
      unfold family apexFamily bandFamily at hη
      split_ifs at hη
      · obtain ⟨x, hx, rfl⟩ := mem_image.mp hη
        rw [mem_product, mem_Icc] at hx; simp only; omega
      · obtain ⟨x, hx, rfl⟩ := mem_image.mp hη
        rw [mem_product, mem_Ioo] at hx
        simp only
        have h1 := Nat.cast_nonneg (α := ℤ) ((m - (k + (f - 1))) * scaleR s0 (k + (f - 1)))
        have h2 : ((x.1 + strokeLen s0 m k + x.2 : ℕ) : ℤ) =
            ((x.1 + strokeLen s0 m k : ℕ) : ℤ) + x.2 := by push_cast; ring
        rw [h2]; omega
    have hb := hB h η.1 η.2 hlt
    rw [le_div_iff₀ hΩpos] at hb
    nlinarith
  have hclog1 := one_le_clog (m - k)
  have hsum0 : 0 ≤ ∑ i ∈ Icc 1 m, max 0 (1 - ((η.2 - η.1 : ℤ) : ℝ) / scaleR s0 i) :=
    Finset.sum_nonneg fun i _ => le_max_left _ _
  unfold family at hη
  split_ifs at hη with hf0
  · -- apex hops: length `2d < R_{k-1}`
    obtain ⟨⟨α, d⟩, hx, rfl⟩ := mem_image.mp hη
    rw [mem_product, mem_Icc] at hx
    have hRk1 : scaleR s0 (k - 1) = 2 * scaleR s0 k := by
      simpa [Nat.sub_add_cancel hk1] using scaleR_succ (s0 := s0) (i := k - 1) (by omega)
    have hlen : (((α : ℤ) + d - ((α : ℤ) - d) : ℤ) : ℝ) ≤ scaleR s0 (k - 1) := by
      push_cast; rw [hRk1]; push_cast
      have : (d : ℝ) ≤ scaleR s0 k - 1 := by
        have := hx.2.2; have hRk := scaleR_pos s0 k
        exact_mod_cast (show (d : ℤ) ≤ scaleR s0 k - 1 by omega)
      linarith
    have hs := sum_max_ge (L := k - 1) (by omega) hms.le hlen
    simp only at hs ⊢
    unfold epsG
    have hk' : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by push_cast [Nat.cast_sub hk1]; ring
    have hg : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by push_cast [Nat.cast_sub (by omega : k ≤ m)]; ring
    rw [hk'] at hs
    rw [hg, div_eq_inv_mul]
    have hc : (1 : ℝ) ≤ Nat.clog 2 (m - k + 2) := by exact_mod_cast hclog1
    have p1 := mul_le_mul_of_nonneg_left hs hinv.le
    have p3 := mul_le_mul_of_nonneg_left hc hinv.le
    nlinarith
  · -- band hops: length `(m - l) R_l + 2x < (m - l + 2) R_l`
    obtain ⟨⟨α, x⟩, hx, rfl⟩ := mem_image.mp hη
    rw [mem_product, mem_Ioo] at hx
    set l := k + (f - 1) with hl
    set lam := Nat.clog 2 (m - l + 2) with hlam
    have hpow : m - l + 2 ≤ 2 ^ lam := Nat.le_pow_clog (by norm_num) _
    have hlamg : lam ≤ Nat.clog 2 (m - k + 2) := Nat.clog_mono_right 2 (by omega)
    unfold epsG
    have hg : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by push_cast [Nat.cast_sub (by omega : k ≤ m)]; ring
    rw [hg, div_eq_inv_mul]
    have hlamR : (lam : ℝ) ≤ Nat.clog 2 (m - k + 2) := by exact_mod_cast hlamg
    have p3 := mul_le_mul_of_nonneg_left hlamR hinv.le
    rcases le_or_gt lam l with hll | hll
    · have hlen : (((((α + strokeLen s0 m k + x : ℕ) : ℤ)) -
          (((α + strokeLen s0 m k : ℕ) : ℤ) - ((m - l) * scaleR s0 l : ℕ) - x) : ℤ) : ℝ) ≤
          scaleR s0 (l - lam) := by
        have hRl : scaleR s0 (l - lam) = 2 ^ lam * scaleR s0 l := by
          unfold scaleR; rw [← pow_add]; congr 1; omega
        have hxl : x + 1 ≤ scaleR s0 l := hx.2.2
        have hnat : (m - l) * scaleR s0 l + 2 * x ≤ 2 ^ lam * scaleR s0 l := by
          calc (m - l) * scaleR s0 l + 2 * x ≤ (m - l) * scaleR s0 l + 2 * scaleR s0 l := by omega
            _ = (m - l + 2) * scaleR s0 l := by ring
            _ ≤ 2 ^ lam * scaleR s0 l := Nat.mul_le_mul_right _ hpow
        rw [hRl]
        have : ((((α + strokeLen s0 m k + x : ℕ) : ℤ)) -
            (((α + strokeLen s0 m k : ℕ) : ℤ) - ((m - l) * scaleR s0 l : ℕ) - x) : ℤ) =
            (((m - l) * scaleR s0 l + 2 * x : ℕ) : ℤ) := by push_cast; ring
        rw [this]
        exact_mod_cast hnat
      have hs := sum_max_ge (L := l - lam) (by omega) hms.le hlen
      have hL : ((l - lam : ℕ) : ℝ) = (l : ℝ) - lam := by push_cast [Nat.cast_sub hll]; ring
      rw [hL] at hs
      have hlk : (k : ℝ) ≤ l := by exact_mod_cast (show k ≤ l by omega)
      simp only at hs ⊢
      have p1 := mul_le_mul_of_nonneg_left hs hinv.le
      have p2 := mul_le_mul_of_nonneg_left hlk hinv.le
      nlinarith
    · have hlk : (k : ℝ) ≤ l := by exact_mod_cast (show k ≤ l by omega)
      have hll' : (l : ℝ) + 1 ≤ lam := by exact_mod_cast hll
      simp only at hsum0 ⊢
      have p1 := mul_nonneg hinv.le hsum0
      have p2 := mul_le_mul_of_nonneg_left hlk hinv.le
      have p4 := mul_le_mul_of_nonneg_left hll' hinv.le
      nlinarith


/-- A family fails to be half-blind with probability at most `2 ε_g` (Markov). -/
theorem card_not_halfBlind_le {s0 m k f : ℕ} (hB : BlindnessBound s0 m) (hms : m < s0) (hk1 : 1 ≤ k)
    (hkm : k + 2 ≤ m) (hf : f < 4) (h : Bool) :
    (((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ => ¬ HalfBlind s0 m (ξ : ℤ) h k f).card : ℝ) ≤
      2 * epsG m (m - k) * (oddRange (dnpPeriod s0 m)).card := by
  set Ω := oddRange (dnpPeriod s0 m)
  have hFpos : (0 : ℝ) < (family s0 m k f).card := by
    have := family_card_ge (f := f) hk1 hkm hms hf
    have h2 : 0 < 4 * 2 ^ s0 := by positivity
    exact_mod_cast (show 0 < (family s0 m k f).card by omega)
  set nb : ℕ → ℕ := fun ξ => ((family s0 m k f).filter fun η => ¬ BlindHop s0 m (ξ : ℤ) h η.1 η.2).card
  have hbad : ∀ ξ ∈ Ω.filter (fun ξ : ℕ => ¬ HalfBlind s0 m (ξ : ℤ) h k f),
      ((family s0 m k f).card : ℝ) ≤ 2 * nb ξ := by
    intro ξ hξ
    have hn := (Finset.mem_filter.mp hξ).2
    unfold HalfBlind at hn
    push Not at hn
    have hsplit := Finset.card_filter_add_card_filter_not (s := family s0 m k f)
      (fun η => BlindHop s0 m (ξ : ℤ) h η.1 η.2)
    have : (family s0 m k f).card ≤ 2 * nb ξ := by simp only [nb]; omega
    exact_mod_cast this
  have hswap : ∑ ξ ∈ Ω, (nb ξ : ℝ) = ∑ η ∈ family s0 m k f,
      ((Ω.filter fun ξ : ℕ => ¬ BlindHop s0 m (ξ : ℤ) h η.1 η.2).card : ℝ) := by
    simp only [nb, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  have hsum_le : ∑ ξ ∈ Ω, (nb ξ : ℝ) ≤ (family s0 m k f).card * (epsG m (m - k) * Ω.card) := by
    rw [hswap]
    calc ∑ η ∈ family s0 m k f, ((Ω.filter fun ξ : ℕ => ¬ BlindHop s0 m (ξ : ℤ) h η.1 η.2).card : ℝ)
        ≤ ∑ _η ∈ family s0 m k f, epsG m (m - k) * Ω.card :=
          Finset.sum_le_sum fun η hη => card_not_blind_le hB hms hk1 hkm hf h hη
      _ = (family s0 m k f).card * (epsG m (m - k) * Ω.card) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hmarkov : ((family s0 m k f).card : ℝ) * ((Ω.filter fun ξ : ℕ => ¬ HalfBlind s0 m (ξ : ℤ) h k f).card : ℝ) ≤
      2 * ∑ ξ ∈ Ω, (nb ξ : ℝ) := by
    calc ((family s0 m k f).card : ℝ) * ((Ω.filter fun ξ : ℕ => ¬ HalfBlind s0 m (ξ : ℤ) h k f).card : ℝ)
        = ∑ _ξ ∈ Ω.filter (fun ξ : ℕ => ¬ HalfBlind s0 m (ξ : ℤ) h k f), ((family s0 m k f).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ ξ ∈ Ω.filter (fun ξ : ℕ => ¬ HalfBlind s0 m (ξ : ℤ) h k f), 2 * (nb ξ : ℝ) :=
          Finset.sum_le_sum hbad
      _ ≤ ∑ ξ ∈ Ω, 2 * (nb ξ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => by positivity
      _ = 2 * ∑ ξ ∈ Ω, (nb ξ : ℝ) := by rw [Finset.mul_sum]
  have : ((family s0 m k f).card : ℝ) * ((Ω.filter fun ξ : ℕ => ¬ HalfBlind s0 m (ξ : ℤ) h k f).card : ℝ) ≤
      (family s0 m k f).card * (2 * epsG m (m - k) * Ω.card) := by nlinarith
  exact le_of_mul_le_mul_left this hFpos

/-- The non-half-blind triples `(h, k, f)`, `k ∈ ℱ_ε`, at the shift `ξ`. -/
noncomputable def nonHalfBlind (s0 m : ℕ) (ε : ℝ) (ξ : ℕ) : Finset (Bool × ℕ × ℕ) :=
  ((Finset.univ : Finset Bool) ×ˢ (fineZone m ε ×ˢ range 4)).filter
    fun x => ¬ HalfBlind s0 m (ξ : ℤ) x.1 x.2.1 x.2.2

theorem clog_le_self {g : ℕ} (hg : 2 ≤ g) : Nat.clog 2 (g + 2) ≤ g := by
  apply Nat.clog_le_of_le_pow
  induction g, hg using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- Basic facts on the fine zone. -/
theorem fineZone_props {m : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) (hεm : 4 ≤ ε * m) :
    4 ≤ ⌊ε * m⌋₊ ∧ (⌊ε * m⌋₊ : ℝ) ≤ ε * m ∧ ⌊ε * m⌋₊ + 2 ≤ m ∧
      (fineZone m ε).card = ⌊ε * m⌋₊ - 1 ∧ ε * m / 2 ≤ (fineZone m ε).card ∧
      ∀ k ∈ fineZone m ε, 1 ≤ k ∧ k + 2 ≤ m ∧ 2 ≤ m - k ∧ m - k ≤ ⌊ε * m⌋₊ := by
  have hG4 : 4 ≤ ⌊ε * m⌋₊ := Nat.le_floor (by exact_mod_cast hεm)
  have hGle : (⌊ε * m⌋₊ : ℝ) ≤ ε * m := Nat.floor_le (by positivity)
  have hGm : ⌊ε * m⌋₊ + 2 ≤ m := by
    have : (⌊ε * m⌋₊ : ℝ) + 2 ≤ m := by nlinarith
    exact_mod_cast this
  have hcard : (fineZone m ε).card = ⌊ε * m⌋₊ - 1 := by
    unfold fineZone; rw [Nat.card_Icc]; omega
  refine ⟨hG4, hGle, hGm, hcard, ?_, fun k hk => ?_⟩
  · rw [hcard]
    have hlt : ε * m < (⌊ε * m⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have : ((⌊ε * m⌋₊ - 1 : ℕ) : ℝ) = (⌊ε * m⌋₊ : ℝ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ ⌊ε * m⌋₊)]; ring
    rw [this]; linarith
  · unfold fineZone at hk; rw [mem_Icc] at hk; omega

/-- **Lemma 7.8** (expectation): the expected number of non-half-blind triples `(h, k, f)` with
`k ∈ ℱ_ε` is at most `64 ε² m`. -/
theorem sum_nonHalfBlind_le {s0 m : ℕ} {ε : ℝ} (hB : BlindnessBound s0 m) (hms : m < s0)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) (hεm : 4 ≤ ε * m) :
    ∑ ξ ∈ oddRange (dnpPeriod s0 m), ((nonHalfBlind s0 m ε ξ).card : ℝ) ≤
      64 * ε ^ 2 * m * (oddRange (dnpPeriod s0 m)).card := by
  obtain ⟨hG4, hGle, hGm, hcard, -, hk⟩ := fineZone_props hε0 hε1 hεm
  set Ω := oddRange (dnpPeriod s0 m)
  set G := ⌊ε * m⌋₊
  set T := (Finset.univ : Finset Bool) ×ˢ (fineZone m ε ×ˢ range 4)
  have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hΩ : (0 : ℝ) ≤ Ω.card := by positivity
  have hswap : ∑ ξ ∈ Ω, ((nonHalfBlind s0 m ε ξ).card : ℝ) =
      ∑ x ∈ T, ((Ω.filter fun ξ : ℕ => ¬ HalfBlind s0 m (ξ : ℤ) x.1 x.2.1 x.2.2).card : ℝ) := by
    unfold nonHalfBlind
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  have heps : ∀ k ∈ fineZone m ε, epsG m (m - k) ≤ 4 * G / ((m : ℝ) + 1) := by
    intro k hkF
    obtain ⟨-, -, hg2, hgG⟩ := hk k hkF
    unfold epsG
    rw [div_le_div_iff_of_pos_right hN]
    have hc := clog_le_self hg2
    have : (m - k : ℕ) + 4 + Nat.clog 2 (m - k + 2) ≤ 4 * G := by omega
    exact_mod_cast this
  rw [hswap]
  calc ∑ x ∈ T, ((Ω.filter fun ξ : ℕ => ¬ HalfBlind s0 m (ξ : ℤ) x.1 x.2.1 x.2.2).card : ℝ)
      ≤ ∑ x ∈ T, 2 * (4 * G / ((m : ℝ) + 1)) * Ω.card := by
        refine Finset.sum_le_sum fun x hx => ?_
        simp only [T, Finset.mem_product, Finset.mem_univ, true_and, mem_range] at hx
        obtain ⟨hk1, hkm, -, -⟩ := hk x.2.1 hx.1
        calc ((Ω.filter fun ξ : ℕ => ¬ HalfBlind s0 m (ξ : ℤ) x.1 x.2.1 x.2.2).card : ℝ)
            ≤ 2 * epsG m (m - x.2.1) * Ω.card := card_not_halfBlind_le hB hms hk1 hkm hx.2 x.1
          _ ≤ 2 * (4 * G / ((m : ℝ) + 1)) * Ω.card := by
              gcongr; exact heps x.2.1 hx.1
    _ = 2 * 4 * (G - 1) * (2 * (4 * G / ((m : ℝ) + 1)) * Ω.card) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [T, Finset.card_product, Finset.card_univ, Fintype.card_bool, card_range, hcard]
        push_cast [Nat.cast_sub (by omega : 1 ≤ G)]; ring
    _ ≤ 64 * ε ^ 2 * m * Ω.card := by
        have hG1 : (1 : ℝ) ≤ G := by exact_mod_cast (show 1 ≤ G by omega)
        have hmN : (m : ℝ) ^ 2 ≤ m * ((m : ℝ) + 1) := by nlinarith
        have hGsq : (G : ℝ) ^ 2 ≤ (ε * m) ^ 2 := by
          have : (0 : ℝ) ≤ G := by positivity
          nlinarith
        have key : 2 * 4 * ((G : ℝ) - 1) * (2 * (4 * G / ((m : ℝ) + 1))) ≤ 64 * ε ^ 2 * m := by
          rw [show 2 * 4 * ((G : ℝ) - 1) * (2 * (4 * G / ((m : ℝ) + 1))) =
            64 * ((G - 1) * G) / ((m : ℝ) + 1) by ring, div_le_iff₀ hN]
          have : ((G : ℝ) - 1) * G ≤ (G : ℝ) ^ 2 := by nlinarith
          have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
          nlinarith
        nlinarith

/-- **Lemma 7.8** (probability): for `δ = 1/(48 (a₀ + 1))`, more than `δ |ℱ_ε|` non-half-blind
triples occur with probability at most `6144 (a₀ + 1) ε`. -/
theorem prob_many_nonHalfBlind_le {s0 m : ℕ} {ε : ℝ} (hB : BlindnessBound s0 m) (hms : m < s0)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) (hεm : 4 ≤ ε * m) (a0 : ℕ) :
    (((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ =>
        1 / (48 * ((a0 : ℝ) + 1)) * (fineZone m ε).card < (nonHalfBlind s0 m ε ξ).card).card : ℝ) /
      (oddRange (dnpPeriod s0 m)).card ≤ 6144 * ((a0 : ℝ) + 1) * ε := by
  obtain ⟨-, -, -, -, hFge, -⟩ := fineZone_props hε0 hε1 hεm
  set Ω := oddRange (dnpPeriod s0 m)
  set δ : ℝ := 1 / (48 * ((a0 : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hΩpos := card_oddRange_pos s0 m
  have hF : (0 : ℝ) < (fineZone m ε).card := by nlinarith
  have hsum := sum_nonHalfBlind_le hB hms hε0 hε1 hεm
  set Bad := Ω.filter fun ξ : ℕ => δ * (fineZone m ε).card < (nonHalfBlind s0 m ε ξ).card
  have hmarkov : δ * (fineZone m ε).card * Bad.card ≤
      ∑ ξ ∈ Ω, ((nonHalfBlind s0 m ε ξ).card : ℝ) := by
    calc δ * (fineZone m ε).card * Bad.card = ∑ _ξ ∈ Bad, δ * (fineZone m ε).card := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ ξ ∈ Bad, ((nonHalfBlind s0 m ε ξ).card : ℝ) :=
          Finset.sum_le_sum fun ξ hξ => (Finset.mem_filter.mp hξ).2.le
      _ ≤ ∑ ξ ∈ Ω, ((nonHalfBlind s0 m ε ξ).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => by positivity
  rw [div_le_iff₀ hΩpos]
  have hden : 0 < δ * (fineZone m ε).card := by positivity
  have h1 : δ * (fineZone m ε).card * Bad.card ≤ 64 * ε ^ 2 * m * Ω.card := le_trans hmarkov hsum
  have h2 : δ * (ε * m / 2) ≤ δ * (fineZone m ε).card := mul_le_mul_of_nonneg_left hFge hδpos.le
  have hm : (0 : ℝ) < m := by
    have : (0 : ℝ) < ε * m := by linarith
    by_contra hc; push Not at hc; nlinarith
  have hBad0 : (0 : ℝ) ≤ Bad.card := by positivity
  have h3 : δ * (ε * m / 2) * Bad.card ≤ 64 * ε ^ 2 * m * Ω.card := by nlinarith
  have h4 : δ * (ε * m / 2) * (6144 * ((a0 : ℝ) + 1) * ε * Ω.card) = 64 * ε ^ 2 * m * Ω.card := by
    rw [hδ]; field_simp; ring
  have hpos : 0 < δ * (ε * m / 2) := by positivity
  nlinarith


/-- Theorem V* summed over the level-`κ` V's of a period: the apex hops around a centre `c₀` that
straddle a V of the other head carry, in total, at least `q/4` times their number. -/
theorem straddle_err_ge {s0 m k κ : ℕ} (hκ1 : 1 ≤ κ) (hκm : κ ≤ m) (hms : m < s0)
    (hpi : strokeLen s0 m κ ≤ scaleR s0 k) (cb cf : ℕ → ℤ) (jTip A' q : ℤ) (hq : 0 < q)
    (hres : q ≤ 2 * ((2 * A' + 2 * (cf κ - cb κ)) % q)) (c0 : ℕ) :
    q * (totalStraddleAtCenter s0 m κ (scaleR s0 k) c0 : ℤ) ≤
      4 * ∑ d ∈ Icc 1 (scaleR s0 k - 1),
        (A' + otherHeadInc (turnPotential s0 m cb cf jTip) (c0 : ℤ) d) % q := by
  classical
  set Φ := turnPotential s0 m cb cf jTip
  set e : ℕ → ℤ := fun d => (A' + otherHeadInc Φ (c0 : ℤ) d) % q
  set S : ℕ → Finset ℕ := fun α => straddleSet (c0 : ℤ) (α : ℤ) (strokeLen s0 m κ) (scaleR s0 k)
  have he0 : ∀ d, 0 ≤ e d := fun d => Int.emod_nonneg _ hq.ne'
  -- per V
  have hV : ∀ α ∈ periodVApices s0 m κ, q * ((S α).card : ℤ) ≤ 4 * ∑ d ∈ S α, e d := by
    intro α hα
    obtain ⟨C, hC⟩ := turnPotential_vDecomp hκ1 hκm hms.le cb cf jTip hα
    have hv := theoremVStar_sum (c0 := (c0 : ℤ)) (A' := A') (R_k := scaleR s0 k) hq hpi hC
    have hcard0 : (0 : ℤ) ≤ (S α).card := by positivity
    calc q * ((S α).card : ℤ) ≤ 2 * ((2 * A' + 2 * (cf κ - cb κ)) % q) * (S α).card :=
          mul_le_mul_of_nonneg_right hres hcard0
      _ = 2 * ((S α).card * ((2 * A' + 2 * (cf κ - cb κ)) % q)) := by ring
      _ ≤ 2 * (2 * ∑ d ∈ S α, e d) := by gcongr
      _ = 4 * ∑ d ∈ S α, e d := by ring
  -- the straddle sets of distinct V's are disjoint and lie in `[1, R_k - 1]`
  have hdisj : (periodVApices s0 m κ : Set ℕ).PairwiseDisjoint S := by
    intro α₁ h₁ α₂ h₂ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    have c1 := center_mem_span_of_straddleSet_nonempty ⟨d, hd1⟩
    have c2 := center_mem_span_of_straddleSet_nonempty ⟨d, hd2⟩
    rcases periodVApices_spans_disjoint hκ1 hκm hms.le h₁ h₂ hne with h | h <;> omega
  have hsub : (periodVApices s0 m κ).biUnion S ⊆ Icc 1 (scaleR s0 k - 1) := by
    intro d hd
    obtain ⟨α, -, hd⟩ := Finset.mem_biUnion.mp hd
    simp only [S, straddleSet, Finset.mem_filter] at hd
    exact hd.1
  unfold totalStraddleAtCenter
  push_cast
  rw [Finset.mul_sum]
  calc ∑ α ∈ periodVApices s0 m κ, q * ((S α).card : ℤ)
      ≤ ∑ α ∈ periodVApices s0 m κ, 4 * ∑ d ∈ S α, e d := Finset.sum_le_sum hV
    _ = 4 * ∑ d ∈ (periodVApices s0 m κ).biUnion S, e d := by
        rw [Finset.sum_biUnion hdisj, Finset.mul_sum]
    _ ≤ 4 * ∑ d ∈ Icc 1 (scaleR s0 k - 1), e d := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => he0 d) (by norm_num)

/-- The error of an apex hop `(α₁ - d, α₁ + d)` of a coarse class under the block-pair label: the
own head contributes `A_k`, the other head its increment around the centre `c₀ ≡ α₁ ± ξ (mod P)`. -/
theorem pairHopErr_apex {s0 m k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) (hms : m < s0) (a1 a2 : ℕ)
    (K1 K2 q ξ : ℤ) (h : Bool) {α1 : ℕ} (hα1 : α1 ∈ periodVApices s0 m k) {d : ℕ} (hd1 : 1 ≤ d)
    (hd2 : d < scaleR s0 k) (c0 : ℕ) (n : ℤ)
    (hc0 : (α1 : ℤ) + (if h then ξ else -ξ) = c0 + n * dnpPeriod s0 m) :
    pairHopErr s0 m a1 a2 K1 K2 q ξ h ((α1 : ℤ) - d) ((α1 : ℤ) + d) =
      ((if h then blockA m a1 K1 k else blockA m a2 K2 k) +
        otherHeadInc (if h then blockPotential s0 m a2 K2 else blockPotential s0 m a1 K1)
          (c0 : ℤ) d) % q := by
  unfold pairHopErr otherHeadInc
  cases h
  · simp only [Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
    have hown := turnPotential_apex hk1 hkm hms.le (blockA m a2 K2) (blockE m a2 K2) 1 hα1 hd1 hd2
    have e1 : (α1 : ℤ) + d + -ξ = (c0 + d) + n * dnpPeriod s0 m := by linarith
    have e2 : (α1 : ℤ) - d + -ξ = (c0 - d) + n * dnpPeriod s0 m := by linarith
    unfold blockPotential at hown ⊢
    rw [e1, e2, turnPotential_add_mul_period, turnPotential_add_mul_period]
    congr 1; linarith
  · simp only [↓reduceIte] at hc0 ⊢
    have hown := turnPotential_apex hk1 hkm hms.le (blockA m a1 K1) (blockE m a1 K1) 1 hα1 hd1 hd2
    have e1 : (α1 : ℤ) + d + ξ = (c0 + d) + n * dnpPeriod s0 m := by linarith
    have e2 : (α1 : ℤ) - d + ξ = (c0 - d) + n * dnpPeriod s0 m := by linarith
    unfold blockPotential at hown ⊢
    rw [e1, e2, turnPotential_add_mul_period, turnPotential_add_mul_period]
    congr 1; linarith


theorem apexFamily_subset_witness {s0 m k : ℕ} (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m) :
    apexFamily s0 m k ⊆ witnessHops s0 m k := by
  have := family_subset_witness (s0 := s0) (f := 0) hk1 hkm (by norm_num)
  simpa [family] using this

/-- **Case 3 of Lemma 7.9**: at a coarse level `k`, against a canceller `κ` of the other head's block
label with straddle residue at least `q/2`, the witness hops of head `h` carry total error at least
`q X/4`, where `X` is the class straddle count in the direction of `h`. -/
theorem witnessErr_ge_straddle {s0 m a1 a2 : ℕ} (hms : m < s0) {K1 K2 q : ℤ} (hq : 0 < q) {ξ : ℕ}
    (hξP : ξ ≤ dnpPeriod s0 m) (h : Bool) {k κ : ℕ} (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m) (hkκ : k < κ)
    (hκm : κ ≤ m) (hpi : strokeLen s0 m κ ≤ scaleR s0 k)
    (hres : q ≤ 2 * ((2 * (if h then blockA m a1 K1 k else blockA m a2 K2 k) +
      2 * ((if h then pathSumFwd (blockA m a2 K2) (blockE m a2 K2) else
          pathSumFwd (blockA m a1 K1) (blockE m a1 K1)) κ -
        (if h then pathSumBack (blockA m a2 K2) else pathSumBack (blockA m a1 K1)) κ)) % q)) :
    q * (classStraddleCount s0 m k κ h ξ : ℤ) ≤ 4 * witnessErr s0 m a1 a2 K1 K2 q ξ h k := by
  set P := dnpPeriod s0 m with hP
  have hPpos := dnpPeriod_pos s0 m
  set A' := if h then blockA m a1 K1 k else blockA m a2 K2 k
  set cbO := if h then pathSumBack (blockA m a2 K2) else pathSumBack (blockA m a1 K1)
  set cfO := if h then pathSumFwd (blockA m a2 K2) (blockE m a2 K2) else
    pathSumFwd (blockA m a1 K1) (blockE m a1 K1)
  have hΨ : (if h then blockPotential s0 m a2 K2 else blockPotential s0 m a1 K1) =
      turnPotential s0 m cbO cfO 1 := by
    cases h <;> rfl
  set center : ℕ → ℕ := fun c => if h then (c + ξ) % P else (c + P - ξ) % P
  have hcenter : ∀ c : ℕ, ∃ n : ℤ, (c : ℤ) + (if h then (ξ : ℤ) else -(ξ : ℤ)) =
      (center c : ℤ) + n * P := by
    intro c
    cases h
    · refine ⟨((c + P - ξ) / P : ℕ) - 1, ?_⟩
      simp only [center, Bool.false_eq_true, ↓reduceIte]
      have h1 : ((c + P - ξ : ℕ) : ℤ) = (c : ℤ) + P - ξ := by
        push_cast [Nat.cast_sub (by omega : ξ ≤ c + P)]; ring
      have h2 : (((c + P - ξ) % P : ℕ) : ℤ) + P * (((c + P - ξ) / P : ℕ) : ℤ) =
          ((c + P - ξ : ℕ) : ℤ) := by
        exact_mod_cast Nat.mod_add_div (c + P - ξ) P
      linear_combination -h1 - h2
    · refine ⟨((c + ξ) / P : ℕ), ?_⟩
      simp only [center, ↓reduceIte]
      have := Nat.mod_add_div (c + ξ) P
      have h' : (((c + ξ) % P : ℕ) : ℤ) + P * (((c + ξ) / P : ℕ) : ℤ) = c + ξ := by
        exact_mod_cast this
      linarith
  -- the apex family carries the error
  have hstep : ∀ α1 ∈ periodVApices s0 m k,
      q * (totalStraddleAtCenter s0 m κ (scaleR s0 k) (center α1) : ℤ) ≤
        4 * ∑ d ∈ Icc 1 (scaleR s0 k - 1),
          pairHopErr s0 m a1 a2 K1 K2 q ξ h ((α1 : ℤ) - d) ((α1 : ℤ) + d) := by
    intro α1 hα1
    obtain ⟨n, hn⟩ := hcenter α1
    have hsum : ∑ d ∈ Icc 1 (scaleR s0 k - 1),
        pairHopErr s0 m a1 a2 K1 K2 q ξ h ((α1 : ℤ) - d) ((α1 : ℤ) + d) =
        ∑ d ∈ Icc 1 (scaleR s0 k - 1),
          (A' + otherHeadInc (turnPotential s0 m cbO cfO 1) (center α1 : ℤ) d) % q := by
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [mem_Icc] at hd
      have hRk := scaleR_pos s0 k
      rw [pairHopErr_apex hk1 (by omega) hms a1 a2 K1 K2 q ξ h hα1 hd.1 (by omega) (center α1) n
        (by exact hn), hΨ]
    rw [hsum]
    exact straddle_err_ge (by omega) hκm hms hpi cbO cfO 1 A' q hq hres (center α1)
  have happex : ∑ η ∈ apexFamily s0 m k, pairHopErr s0 m a1 a2 K1 K2 q ξ h η.1 η.2 =
      ∑ α1 ∈ periodVApices s0 m k, ∑ d ∈ Icc 1 (scaleR s0 k - 1),
        pairHopErr s0 m a1 a2 K1 K2 q ξ h ((α1 : ℤ) - d) ((α1 : ℤ) + d) := by
    unfold apexFamily
    rw [Finset.sum_image (fun x _ y _ hxy => by
      simp only [Prod.mk.injEq] at hxy; exact Prod.ext (by omega) (by omega)), Finset.sum_product]
  have hX : (classStraddleCount s0 m k κ h ξ : ℤ) =
      ∑ α1 ∈ periodVApices s0 m k, (totalStraddleAtCenter s0 m κ (scaleR s0 k) (center α1) : ℤ) := by
    unfold classStraddleCount; push_cast; rfl
  have hwit : ∑ η ∈ apexFamily s0 m k, pairHopErr s0 m a1 a2 K1 K2 q ξ h η.1 η.2 ≤
      witnessErr s0 m a1 a2 K1 K2 q ξ h k :=
    Finset.sum_le_sum_of_subset_of_nonneg (apexFamily_subset_witness hk1 hkm)
      fun η _ _ => pairHopErr_nonneg s0 m a1 a2 K1 K2 hq ξ h _ _
  rw [hX, Finset.mul_sum]
  calc ∑ α1 ∈ periodVApices s0 m k, q * (totalStraddleAtCenter s0 m κ (scaleR s0 k) (center α1) : ℤ)
      ≤ ∑ α1 ∈ periodVApices s0 m k, 4 * ∑ d ∈ Icc 1 (scaleR s0 k - 1),
          pairHopErr s0 m a1 a2 K1 K2 q ξ h ((α1 : ℤ) - d) ((α1 : ℤ) + d) :=
        Finset.sum_le_sum hstep
    _ = 4 * ∑ η ∈ apexFamily s0 m k, pairHopErr s0 m a1 a2 K1 K2 q ξ h η.1 η.2 := by
        rw [happex, Finset.mul_sum]
    _ ≤ 4 * witnessErr s0 m a1 a2 K1 K2 q ξ h k := by linarith


noncomputable instance (s0 m a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (θ : ℝ) (h : Bool) (k : ℕ) :
    Decidable (ServedOnWitness s0 m a1 a2 K1 K2 q ξ θ h k) := by
  unfold ServedOnWitness; infer_instance

/-- The levels `k ∈ {0, …, m}` that are not doubly `θ`-served (on their witness hops). -/
noncomputable def unservedLevels (s0 m a1 a2 : ℕ) (K1 K2 q : ℤ) (ξ : ℕ) (θ : ℝ) : Finset ℕ :=
  (range (m + 1)).filter fun k => ¬ (ServedOnWitness s0 m a1 a2 K1 K2 q ξ θ true k ∧
    ServedOnWitness s0 m a1 a2 K1 K2 q ξ θ false k)

/-- Levels of the fine zone with a family whose blind error exceeds `64 θ q`: all but the
non-half-blind ones are unserved. -/
theorem card_unserved_ge_of_witness {s0 m a1 a2 : ℕ} {K1 K2 q : ℤ} (hq : 0 < q) {ξ : ℕ} {θ ε : ℝ}
    (hms : m < s0) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) (hεm : 4 ≤ ε * m) (h : Bool) (S : Finset ℕ)
    (hS : S ⊆ fineZone m ε)
    (hwit : ∀ k ∈ S, ∃ f < 4, 64 * θ * q <
      (familyBlindErr m (if h then a1 else a2) (if h then K1 else K2) q k f : ℝ)) :
    (S.card : ℝ) - (nonHalfBlind s0 m ε ξ).card ≤ (unservedLevels s0 m a1 a2 K1 K2 q ξ θ).card := by
  classical
  obtain ⟨-, -, -, -, -, hk⟩ := fineZone_props hε0 hε1 hεm
  set fsel : ℕ → ℕ := fun k => if hk : k ∈ S then Classical.choose (hwit k hk) else 0
  have hfsel : ∀ k ∈ S, fsel k < 4 ∧ 64 * θ * q <
      (familyBlindErr m (if h then a1 else a2) (if h then K1 else K2) q k (fsel k) : ℝ) := by
    intro k hkS
    simp only [fsel, dite_eq_left hkS]
    exact Classical.choose_spec (hwit k hkS)
  set Sg := S.filter fun k : ℕ => HalfBlind s0 m (ξ : ℤ) h k (fsel k)
  set Sb := S.filter fun k : ℕ => ¬ HalfBlind s0 m (ξ : ℤ) h k (fsel k)
  have hgood : Sg ⊆ unservedLevels s0 m a1 a2 K1 K2 q ξ θ := by
    intro k hkg
    obtain ⟨hkS, hhb⟩ := Finset.mem_filter.mp hkg
    obtain ⟨hk1, hkm, -, -⟩ := hk k (hS hkS)
    obtain ⟨hf4, hlt⟩ := hfsel k hkS
    unfold unservedLevels
    rw [Finset.mem_filter, mem_range]
    refine ⟨by omega, fun hserv => ?_⟩
    have hs : ServedOnWitness s0 m a1 a2 K1 K2 q ξ θ h k := by cases h <;> simp_all
    have := familyBlindErr_le_of_served hms hq hk1 hkm hf4 hs hhb
    linarith
  have hbad : Sb.card ≤ (nonHalfBlind s0 m ε ξ).card := by
    refine Finset.card_le_card_of_injOn (fun k => (h, k, fsel k)) ?_ ?_
    · intro k hkb
      obtain ⟨hkS, hnhb⟩ := Finset.mem_filter.mp hkb
      unfold nonHalfBlind
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_univ,
        true_and, mem_range]
      exact ⟨⟨hS hkS, (hfsel k hkS).1⟩, hnhb⟩
    · intro k₁ _ k₂ _ heq
      simp only [Prod.mk.injEq] at heq
      exact heq.2.1
  have hsplit := Finset.card_filter_add_card_filter_not (s := S)
    (fun k : ℕ => HalfBlind s0 m (ξ : ℤ) h k (fsel k))
  have h1 : (Sg.card : ℝ) ≤ (unservedLevels s0 m a1 a2 K1 K2 q ξ θ).card := by
    exact_mod_cast Finset.card_le_card hgood
  have h2 : (Sb.card : ℝ) ≤ (nonHalfBlind s0 m ε ξ).card := by exact_mod_cast hbad
  have h3 : (Sg.card : ℝ) + Sb.card = S.card := by exact_mod_cast hsplit
  linarith

/-- A set meeting each of `n` disjoint consecutive blocks of length `w` has at least `n` elements. -/
theorem card_ge_of_blocks (S : Finset ℕ) (lo w n : ℕ)
    (hmeet : ∀ i < n, ∃ k ∈ S, lo + i * w ≤ k ∧ k < lo + (i + 1) * w) : n ≤ S.card := by
  classical
  set sel : ℕ → ℕ := fun i => if hi : i < n then Classical.choose (hmeet i hi) else 0
  have hsel : ∀ i < n, sel i ∈ S ∧ lo + i * w ≤ sel i ∧ sel i < lo + (i + 1) * w := by
    intro i hi
    simp only [sel, dite_eq_left hi]
    exact Classical.choose_spec (hmeet i hi)
  have := Finset.card_le_card_of_injOn sel (s := range n) (t := S)
    (fun i hi => (hsel i (mem_range.mp hi)).1) (by
      intro i hi j hj hij
      have hi' := hsel i (mem_range.mp hi)
      have hj' := hsel j (mem_range.mp hj)
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have : (i + 1) * w ≤ j * w := Nat.mul_le_mul_right _ hlt
        omega
      · have : (j + 1) * w ≤ i * w := Nat.mul_le_mul_right _ hlt
        omega)
  simpa using this


/-- `θ₀ = 2^{-(a₀+11)}`. -/
noncomputable def theta0 (a0 : ℕ) : ℝ := (1 / 2) ^ (a0 + 11)

theorem theta0_pos (a0 : ℕ) : 0 < theta0 a0 := by unfold theta0; positivity

theorem sixtyfour_theta0_le {a0 : ℕ} (ha0 : 1 ≤ a0) : 64 * theta0 a0 ≤ 1 / 64 := by
  unfold theta0
  have : ((1 : ℝ) / 2) ^ (a0 + 11) ≤ (1 / 2) ^ 12 := pow_le_pow_of_le_one (by norm_num) (by norm_num)
    (by omega)
  norm_num at this ⊢; linarith

/-- **Case 1 of Lemma 7.9** (`q < 32`): the run bound in every window of `11` fine levels. -/
theorem case1_unserved {s0 m a0 a1 a2 : ℕ} {K1 K2 q : ℤ} {ξ : ℕ} {ε : ℝ} (ha0 : 1 ≤ a0)
    (hms : m < s0) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) (hεm : 4 ≤ ε * m) (hq3 : 3 ≤ q) (hq32 : q < 32)
    (hii : ((nonHalfBlind s0 m ε ξ).card : ℝ) ≤ 1 / (48 * ((a0 : ℝ) + 1)) * (fineZone m ε).card) :
    (fineZone m ε).card / 13 - 1 ≤
      ((unservedLevels s0 m a1 a2 K1 K2 q ξ (theta0 a0)).card : ℝ) := by
  obtain ⟨hG4, -, hGm, hcard, -, hk⟩ := fineZone_props hε0 hε1 hεm
  set G := ⌊ε * m⌋₊
  set lo := m - G
  set W := (G - 1) / 11
  set S := (fineZone m ε).filter fun k : ℕ => ∃ f < (4 : ℕ), q < 8 * familyBlindErr m a1 K1 q k f
  have hlog : Nat.log 2 q.toNat ≤ 4 := by
    by_contra hc; push Not at hc
    have : 2 ^ 5 ≤ q.toNat := le_trans (Nat.pow_le_pow_right (by norm_num) hc)
      (Nat.pow_log_le_self 2 (by omega))
    omega
  have hmeet : ∀ i < W, ∃ k ∈ S, lo + i * 11 ≤ k ∧ k < lo + (i + 1) * 11 := by
    intro i hi
    have hiW : (i + 1) * 11 ≤ G - 1 := by
      have := Nat.div_mul_le_self (G - 1) 11
      have : (i + 1) * 11 ≤ W * 11 := Nat.mul_le_mul_right _ hi
      omega
    by_contra hno
    push Not at hno
    have hall : ∀ i' < 11, ∀ f < 4, 8 * familyBlindErr m a1 K1 q (lo + i * 11 + i') f ≤ q := by
      intro i' hi' f hf
      have hkF : lo + i * 11 + i' ∈ fineZone m ε := by
        unfold fineZone; rw [mem_Icc]; omega
      by_contra hc; push Not at hc
      exact absurd (hno (lo + i * 11 + i') (Finset.mem_filter.mpr ⟨hkF, f, hf, hc⟩) (by omega))
        (by omega)
    have hLU := theoremLU_consecutive (blockA m a1 K1) (blockE m a1 K1) hq3 (k0 := lo + i * 11)
      (s := 11) (by norm_num)
      (fun i' hi' => by simpa [familyBlindErr] using hall i' hi' 0 (by norm_num))
      (fun i' hi' => by simpa [familyBlindErr] using hall i' hi' 1 (by norm_num))
      (fun i' hi' => by simpa [familyBlindErr, Nat.add_assoc] using hall i' (by omega) 2 (by norm_num))
      (fun i' hi' => by simpa [familyBlindErr, Nat.add_assoc] using hall i' (by omega) 3 (by norm_num))
    omega
  have hWS := card_ge_of_blocks S lo 11 W hmeet
  have hwit : ∀ k ∈ S, ∃ f < 4, 64 * theta0 a0 * q <
      (familyBlindErr m (if true then a1 else a2) (if true then K1 else K2) q k f : ℝ) := by
    intro k hkS
    obtain ⟨-, f, hf, hlt⟩ := Finset.mem_filter.mp hkS
    refine ⟨f, hf, ?_⟩
    simp only [ite_true]
    have h1 : (1 : ℤ) ≤ familyBlindErr m a1 K1 q k f := by omega
    have h1R : (1 : ℝ) ≤ familyBlindErr m a1 K1 q k f := by exact_mod_cast h1
    have hqR : (q : ℝ) < 32 := by exact_mod_cast hq32
    have hqR0 : (0 : ℝ) < q := by exact_mod_cast (show (0 : ℤ) < q by omega)
    have := sixtyfour_theta0_le ha0
    nlinarith
  have hU := card_unserved_ge_of_witness (s0 := s0) (a1 := a1) (a2 := a2) (K1 := K1) (K2 := K2)
    (by omega : (0 : ℤ) < q) (ξ := ξ) (θ := theta0 a0) hms hε0 hε1 hεm true S
    (Finset.filter_subset _ _) hwit
  have hWR : ((fineZone m ε).card : ℝ) - 10 ≤ 11 * W := by
    have : (G - 1) - 10 ≤ 11 * W := by have := Nat.div_add_mod (G - 1) 11; omega
    rw [hcard]
    have h' : ((G - 1 - 10 : ℕ) : ℝ) ≤ 11 * W := by exact_mod_cast this
    have h'' : ((G - 1 : ℕ) : ℝ) - 10 ≤ ((G - 1 - 10 : ℕ) : ℝ) := by
      rcases le_or_gt 10 (G - 1) with hh | hh
      · push_cast [Nat.cast_sub hh]; linarith
      · have : ((G - 1 : ℕ) : ℝ) < 10 := by exact_mod_cast hh
        have : (0 : ℝ) ≤ ((G - 1 - 10 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
    linarith
  have hδ : 1 / (48 * ((a0 : ℝ) + 1)) ≤ 1 / 96 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ a0 := by exact_mod_cast ha0
    linarith
  have hF0 : (0 : ℝ) ≤ (fineZone m ε).card := by positivity
  have hWS' : (W : ℝ) ≤ S.card := by exact_mod_cast hWS
  have hii' : ((nonHalfBlind s0 m ε ξ).card : ℝ) ≤ (fineZone m ε).card / 96 := by
    calc ((nonHalfBlind s0 m ε ξ).card : ℝ) ≤ 1 / (48 * ((a0 : ℝ) + 1)) * (fineZone m ε).card := hii
      _ ≤ 1 / 96 * (fineZone m ε).card := by gcongr
      _ = (fineZone m ε).card / 96 := by ring
  linarith


/-- Every run of `b` consecutive levels below `m` contains one with `(m - k) mod b = r`. -/
theorem exists_residue_in_block {m x b r : ℕ} (hb : 0 < b) (hr : r < b) (hxm : x + b ≤ m + 1) :
    ∃ k, x ≤ k ∧ k < x + b ∧ (m - k) % b = r := by
  set y0 := m + 1 - (x + b)
  set t := (r + b - y0 % b) % b
  have ht : t < b := Nat.mod_lt _ hb
  have hy0b : y0 % b < b := Nat.mod_lt _ hb
  refine ⟨m - (y0 + t), by omega, by omega, ?_⟩
  rw [show m - (m - (y0 + t)) = y0 + t by omega]
  calc (y0 + t) % b = (y0 % b + (r + b - y0 % b) % b) % b := by rw [Nat.add_mod]; simp [t]
    _ = (y0 % b + (r + b - y0 % b)) % b := by rw [Nat.add_mod_mod]
    _ = (r + b) % b := by congr 1; omega
    _ = r := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hr]

theorem div_bound_aux (a0 : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    c / (2 * ((a0 : ℝ) + 1)) ≤ c / ((a0 : ℝ) + 1) - 1 / (48 * ((a0 : ℝ) + 1)) * c := by
  have hA : (0 : ℝ) < (a0 : ℝ) + 1 := by positivity
  have e : c / ((a0 : ℝ) + 1) - 1 / (48 * ((a0 : ℝ) + 1)) * c - c / (2 * ((a0 : ℝ) + 1)) =
      23 * c / (48 * ((a0 : ℝ) + 1)) := by field_simp; ring
  have : 0 ≤ 23 * c / (48 * ((a0 : ℝ) + 1)) := by positivity
  linarith

/-- **Case 2 of Lemma 7.9** (`q ≥ 32` and `4 Q̃_h + 4 > q`): the overflow bound on one residue class
of fine levels. -/
theorem case2_unserved {s0 m a0 a1 a2 : ℕ} {K1 K2 q : ℤ} {ξ : ℕ} {ε : ℝ} (ha0 : 1 ≤ a0) (h : Bool)
    (ha : 1 ≤ (if h then a1 else a2)) (haa0 : (if h then a1 else a2) ≤ a0) (hms : m < s0)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) (hεm : 4 ≤ ε * m) (hq32 : 32 ≤ q)
    (hover : q < 4 * blockQ (if h then a1 else a2) ((if h then K1 else K2) % q) + 4)
    (hii : ((nonHalfBlind s0 m ε ξ).card : ℝ) ≤ 1 / (48 * ((a0 : ℝ) + 1)) * (fineZone m ε).card) :
    (fineZone m ε).card / (2 * ((a0 : ℝ) + 1)) - 1 ≤
      ((unservedLevels s0 m a1 a2 K1 K2 q ξ (theta0 a0)).card : ℝ) := by
  obtain ⟨hG4, -, hGm, hcard, -, hk⟩ := fineZone_props hε0 hε1 hεm
  set a := if h then a1 else a2 with hadef
  set K := if h then K1 else K2 with hKdef
  obtain ⟨rem, hrem, hw⟩ := block_overflow_band_witness m a K ha hq32 hover
  set G := ⌊ε * m⌋₊
  set lo := m - G
  set n := (G - 1) / (a + 1)
  set S := (fineZone m ε).filter fun k : ℕ => (m - k) % (a + 1) = rem
  have hmeet : ∀ i < n, ∃ k ∈ S, lo + i * (a + 1) ≤ k ∧ k < lo + (i + 1) * (a + 1) := by
    intro i hi
    have hin : (i + 1) * (a + 1) ≤ G - 1 :=
      calc (i + 1) * (a + 1) ≤ n * (a + 1) := Nat.mul_le_mul_right _ hi
        _ ≤ G - 1 := Nat.div_mul_le_self (G - 1) (a + 1)
    obtain ⟨k, hk1, hk2, hk3⟩ := exists_residue_in_block (m := m) (x := lo + i * (a + 1))
      (b := a + 1) (r := rem) (by omega) (by omega) (by rw [add_mul] at hin; omega)
    refine ⟨k, Finset.mem_filter.mpr ⟨?_, hk3⟩, hk1, by rw [add_mul]; omega⟩
    unfold fineZone; rw [mem_Icc]; rw [add_mul] at hin; omega
  have hnS := card_ge_of_blocks S lo (a + 1) n hmeet
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show (0 : ℤ) < q by omega)
  have h64 := sixtyfour_theta0_le ha0
  have hwit : ∀ k ∈ S, ∃ f < 4, 64 * theta0 a0 * q <
      (familyBlindErr m (if h then a1 else a2) (if h then K1 else K2) q k f : ℝ) := by
    intro k hkS
    obtain ⟨hkF, hkr⟩ := Finset.mem_filter.mp hkS
    obtain ⟨-, hkm, -, -⟩ := hk k hkF
    have hlt : 64 * theta0 a0 * q < (q : ℝ) / 16 := by nlinarith
    rcases hw k (by omega) hkr with h0 | h0 | h0
    · refine ⟨0, by norm_num, ?_⟩
      have : (q : ℝ) ≤ 16 * blindApexErr (blockA m a K) q k := by exact_mod_cast h0
      simp only [familyBlindErr, ite_true]; linarith
    · refine ⟨1, by norm_num, ?_⟩
      have : (q : ℝ) ≤ 8 * blindBandErr (blockA m a K) (blockE m a K) q k k := by exact_mod_cast h0
      have hnn : (0 : ℝ) ≤ blindBandErr (blockA m a K) (blockE m a K) q k k := by
        exact_mod_cast blindBandErr_nonneg _ _ (by omega) _ _
      simp only [familyBlindErr, one_ne_zero, ite_false, Nat.sub_self, add_zero]; linarith
    · refine ⟨2, by norm_num, ?_⟩
      have : (q : ℝ) ≤ 8 * blindBandErr (blockA m a K) (blockE m a K) q k (k + 1) := by
        exact_mod_cast h0
      have hnn : (0 : ℝ) ≤ blindBandErr (blockA m a K) (blockE m a K) q k (k + 1) := by
        exact_mod_cast blindBandErr_nonneg _ _ (by omega) _ _
      simp only [familyBlindErr, show (2 : ℕ) ≠ 0 by norm_num, ite_false,
        show (2 : ℕ) - 1 = 1 by norm_num]; linarith
  have hU := card_unserved_ge_of_witness (s0 := s0) (a1 := a1) (a2 := a2) (K1 := K1) (K2 := K2)
    (by omega : (0 : ℤ) < q) (ξ := ξ) (θ := theta0 a0) hms hε0 hε1 hεm h S
    (Finset.filter_subset _ _) hwit
  have ha1R : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have haa0R : (a : ℝ) ≤ a0 := by exact_mod_cast haa0
  have hnR : ((fineZone m ε).card : ℝ) + 1 ≤ (a + 1) * (n + 1) := by
    rw [hcard]
    have : G - 1 + 1 ≤ (a + 1) * (n + 1) := by
      have h1 : (a + 1) * n + (G - 1) % (a + 1) = G - 1 := Nat.div_add_mod (G - 1) (a + 1)
      have h2 : (G - 1) % (a + 1) < a + 1 := Nat.mod_lt (G - 1) (by omega)
      rw [mul_add, mul_one]
      linarith
    have h' : ((G - 1 + 1 : ℕ) : ℝ) ≤ ((a + 1) * (n + 1) : ℕ) := by exact_mod_cast this
    push_cast at h'
    have : ((G - 1 : ℕ) : ℝ) + 1 = ((G - 1 + 1 : ℕ) : ℝ) := by push_cast; ring
    linarith
  have hn' : ((fineZone m ε).card : ℝ) / ((a0 : ℝ) + 1) - 1 ≤ n := by
    rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
    have : ((fineZone m ε).card : ℝ) + 1 ≤ ((a0 : ℝ) + 1) * (n + 1) := by
      have : ((a : ℝ) + 1) * (n + 1) ≤ ((a0 : ℝ) + 1) * (n + 1) := by
        have : (0 : ℝ) ≤ n + 1 := by positivity
        nlinarith
      linarith
    linarith
  have hnS' : (n : ℝ) ≤ S.card := by exact_mod_cast hnS
  have hF0 : (0 : ℝ) ≤ (fineZone m ε).card := Nat.cast_nonneg _
  have := div_bound_aux a0 _ hF0
  linarith

/-- **Case 3 of Lemma 7.9** (`q ≥ 32`, `4 Q̃_h + 4 ≤ q` for both heads): every `a`-good coarse level
in the direction of head `h`, against the cancellers of the other head's block length `a`, is not
`θ₀`-served for head `h`. -/
theorem case3_unserved {s0 m a0 a1 a2 : ℕ} {K1 K2 q : ℤ} {ξ : ℕ} (h : Bool)
    (haO : 1 ≤ (if h then a2 else a1)) (haOa0 : (if h then a2 else a1) ≤ a0) (hms : m < s0)
    (hsize : 4 * (jZero m + a0) ≤ m + 1) (hξ : ξ ∈ oddRange (dnpPeriod s0 m)) (hq : 0 < q)
    (hres : ∀ k ∈ coarseZone m, q ≤ 2 * ((2 * (if h then blockA m a1 K1 k else blockA m a2 K2 k) +
      2 * ((if h then pathSumFwd (blockA m a2 K2) (blockE m a2 K2) else
          pathSumFwd (blockA m a1 K1) (blockE m a1 K1)) (cancellerBelow m (if h then a2 else a1) k) -
        (if h then pathSumBack (blockA m a2 K2) else pathSumBack (blockA m a1 K1))
          (cancellerBelow m (if h then a2 else a1) k))) % q)) :
    (goodCount s0 m (if h then a2 else a1) h ξ : ℝ) ≤
      ((unservedLevels s0 m a1 a2 K1 K2 q ξ (theta0 a0)).card : ℝ) := by
  set aO := if h then a2 else a1 with haOdef
  have hξP : ξ ≤ dnpPeriod s0 m := by
    simp only [oddRange, mem_filter, mem_range] at hξ; omega
  have hsub : goodLevels s0 m aO h ξ ⊆ unservedLevels s0 m a1 a2 K1 K2 q ξ (theta0 a0) := by
    intro k hkg
    obtain ⟨hkK, hgood⟩ := Finset.mem_filter.mp hkg
    obtain ⟨hk1, hkκ, hκm, -, hpi, -, -, -⟩ := coarse_canceller_props haO haOa0 hms hsize hkK
    have hkm : k + 2 ≤ m := by
      unfold coarseZone at hkK; unfold jZero at hsize; rw [mem_Icc] at hkK; omega
    have hW := witnessErr_ge_straddle (a1 := a1) (a2 := a2) (K1 := K1) (K2 := K2) hms hq hξP h hk1
      hkm hkκ hκm hpi (hres k hkK)
    unfold unservedLevels
    rw [Finset.mem_filter, mem_range]
    refine ⟨by omega, fun hserv => ?_⟩
    have hs : ServedOnWitness s0 m a1 a2 K1 K2 q ξ (theta0 a0) h k := by cases h <;> simp_all
    unfold ServedOnWitness at hs
    have hΛ : (2 : ℝ) ^ (k + 2) * scaleR s0 k = 4 * 2 ^ s0 := by
      rw [scaleR_real (by omega), pow_add, inv_pow]; field_simp; ring
    have hgoodR : (2 : ℝ) ^ (k + 2) * scaleR s0 k ≤
        2 ^ (aO + 7) * classStraddleCount s0 m k (cancellerBelow m aO k) h ξ := by
      exact_mod_cast hgood
    rw [hΛ] at hgoodR
    have hWR : (q : ℝ) * classStraddleCount s0 m k (cancellerBelow m aO k) h ξ ≤
        4 * witnessErr s0 m a1 a2 K1 K2 q ξ h k := by exact_mod_cast hW
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hθ : theta0 a0 * 2 ^ (aO + 9) < 1 := by
      unfold theta0
      rw [show a0 + 11 = (aO + 9) + (a0 - aO + 2) by omega, pow_add, mul_comm, ← mul_assoc,
        ← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow, one_mul]
      exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    have key : (q : ℝ) * (4 * 2 ^ s0) ≤ 2 ^ (aO + 9) * witnessErr s0 m a1 a2 K1 K2 q ξ h k := by
      have h1 := mul_le_mul_of_nonneg_left hgoodR hqR.le
      have h2 := mul_le_mul_of_nonneg_left hWR (show (0 : ℝ) ≤ 2 ^ (aO + 7) by positivity)
      rw [show (2 : ℝ) ^ (aO + 9) = 4 * 2 ^ (aO + 7) by rw [pow_add]; ring]
      nlinarith
    have hΛpos : (0 : ℝ) < q * (4 * 2 ^ s0) := by positivity
    have e1 := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 2 ^ (aO + 9) by positivity)
    have e2 := mul_lt_mul_of_pos_right hθ hΛpos
    nlinarith
  have := Finset.card_le_card hsub
  unfold goodCount
  exact_mod_cast this


theorem card_coarseZone_ge (m : ℕ) : ((m : ℝ) + 1) / 4 - 1 ≤ (coarseZone m).card := by
  unfold coarseZone
  rw [Nat.card_Icc, Nat.add_sub_cancel]
  have h := Nat.div_add_mod (m + 1) 4
  have h2 := Nat.mod_lt (m + 1) (show 0 < 4 by norm_num)
  have : ((m + 1 : ℕ) : ℝ) ≤ 4 * ((m + 1) / 4 : ℕ) + 3 := by
    have : m + 1 ≤ 4 * ((m + 1) / 4) + 3 := by omega
    exact_mod_cast this
  push_cast at this
  linarith

/-- **Lemma 7.9**: at an odd shift `ξ` such that (i) `Γ_{a,±}(ξ) ≥ γ|𝒦|` for all `1 ≤ a ≤ a₀` and
both signs and (ii) at most `δ |ℱ_ε|` triples are not half-blind, every block pair with
`1 ≤ a₁, a₂ ≤ a₀`, every `K₁, K₂` and every `q ≥ 3` leave at least `c(m + 1) - 2` levels that are not
doubly `θ₀`-served (on their witness hops), `c = min(γ/8, ε/(26 (a₀ + 1)))`. -/
theorem witnesses_unserved {s0 m a0 : ℕ} {γ ε : ℝ} (ha0 : 1 ≤ a0) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) (hms : m < s0) (hεm : 4 ≤ ε * m)
    (hsize : 4 * (jZero m + a0) ≤ m + 1) {ξ : ℕ} (hξ : ξ ∈ oddRange (dnpPeriod s0 m))
    (hi : ∀ a ∈ Icc (1 : ℕ) a0, ∀ dir : Bool,
      γ * ((coarseZone m).card : ℝ) ≤ goodCount s0 m a dir ξ)
    (hii : ((nonHalfBlind s0 m ε ξ).card : ℝ) ≤ 1 / (48 * ((a0 : ℝ) + 1)) * (fineZone m ε).card)
    {a1 a2 : ℕ} (ha1 : 1 ≤ a1) (ha1' : a1 ≤ a0) (ha2 : 1 ≤ a2) (ha2' : a2 ≤ a0) (K1 K2 q : ℤ)
    (hq : 3 ≤ q) :
    min (γ / 8) (ε / (26 * ((a0 : ℝ) + 1))) * ((m : ℝ) + 1) - 2 ≤
      ((unservedLevels s0 m a1 a2 K1 K2 q ξ (theta0 a0)).card : ℝ) := by
  obtain ⟨-, -, -, -, hFge, -⟩ := fineZone_props hε0 hε1 hεm
  set U := ((unservedLevels s0 m a1 a2 K1 K2 q ξ (theta0 a0)).card : ℝ)
  set c := min (γ / 8) (ε / (26 * ((a0 : ℝ) + 1)))
  have hA : (0 : ℝ) < (a0 : ℝ) + 1 := by positivity
  have ha0R : (1 : ℝ) ≤ a0 := by exact_mod_cast ha0
  have hcε : c ≤ ε / (26 * ((a0 : ℝ) + 1)) := min_le_right _ _
  have hcγ : c ≤ γ / 8 := min_le_left _ _
  -- the fine-zone bound `ε m / (26 (a₀ + 1)) - 1`
  have hfine : ∀ t : ℝ, ε * m / (26 * ((a0 : ℝ) + 1)) - 1 ≤ t → c * ((m : ℝ) + 1) - 2 ≤ t := by
    intro t ht
    have h1 : c * ((m : ℝ) + 1) ≤ ε / (26 * ((a0 : ℝ) + 1)) * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hcε (by positivity)
    have h2 : ε / (26 * ((a0 : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have h3 : ε / (26 * ((a0 : ℝ) + 1)) * ((m : ℝ) + 1) =
        ε * m / (26 * ((a0 : ℝ) + 1)) + ε / (26 * ((a0 : ℝ) + 1)) := by ring
    linarith
  have hcoarse : ∀ t : ℝ, γ * ((m : ℝ) + 1) / 4 - 1 ≤ t → c * ((m : ℝ) + 1) - 2 ≤ t := by
    intro t ht
    have h1 : c * ((m : ℝ) + 1) ≤ γ / 8 * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hcγ (by positivity)
    have h2 : 0 ≤ γ * ((m : ℝ) + 1) := by positivity
    linarith
  have hq0 : (0 : ℤ) < q := by omega
  by_cases hq32 : q < 32
  · -- Case 1
    have h1 := case1_unserved (a1 := a1) (a2 := a2) (K1 := K1) (K2 := K2) ha0 hms hε0 hε1 hεm hq hq32 hii
    apply hfine
    have : ε * m / (26 * ((a0 : ℝ) + 1)) ≤ (fineZone m ε).card / 13 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  push Not at hq32
  have hfine2 : ∀ t : ℝ, (fineZone m ε).card / (2 * ((a0 : ℝ) + 1)) - 1 ≤ t →
      c * ((m : ℝ) + 1) - 2 ≤ t := by
    intro t ht
    apply hfine
    have : ε * m / (26 * ((a0 : ℝ) + 1)) ≤ (fineZone m ε).card / (2 * ((a0 : ℝ) + 1)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  by_cases hov1 : q < 4 * blockQ a1 (K1 % q) + 4
  · exact hfine2 _ (case2_unserved (s0 := s0) (a2 := a2) (K2 := K2) (ξ := ξ) ha0 true
      (by simpa using ha1) (by simpa using ha1') hms hε0 hε1 hεm hq32 (by simpa using hov1) hii)
  by_cases hov2 : q < 4 * blockQ a2 (K2 % q) + 4
  · exact hfine2 _ (case2_unserved (s0 := s0) (a1 := a1) (K1 := K1) (ξ := ξ) ha0 false
      (by simpa using ha2) (by simpa using ha2') hms hε0 hε1 hεm hq32 (by simpa using hov2) hii)
  push Not at hov1 hov2
  apply hcoarse
  have hK := card_coarseZone_ge m
  have hγK : γ * ((m : ℝ) + 1) / 4 - 1 ≤ γ * (coarseZone m).card := by
    have := mul_le_mul_of_nonneg_left hK hγ0
    nlinarith
  by_cases hQ : blockQ a1 (K1 % q) ≤ blockQ a2 (K2 % q)
  · have h3 := case3_unserved (s0 := s0) (a0 := a0) (K1 := K1) (K2 := K2) (ξ := ξ) true
      (by simpa using ha2) (by simpa using ha2') hms hsize hξ hq0 (fun k hk => by
        obtain ⟨-, -, -, hcanc, -, -, -, -⟩ := coarse_canceller_props ha2 ha2' hms hsize hk
        have := block_straddle_residue_ge_half_q m a1 a2 K1 K2 hq0 ha1 k _ hcanc hQ hov2
        simpa using this)
    have hgood := hi a2 (mem_Icc.mpr ⟨ha2, ha2'⟩) true
    simp only [ite_true] at h3
    linarith
  · push Not at hQ
    have h3 := case3_unserved (s0 := s0) (a0 := a0) (K1 := K1) (K2 := K2) (ξ := ξ) false
      (by simpa using ha1) (by simpa using ha1') hms hsize hξ hq0 (fun k hk => by
        obtain ⟨-, -, -, hcanc, -, -, -, -⟩ := coarse_canceller_props ha1 ha1' hms hsize hk
        have := block_straddle_residue_ge_half_q m a2 a1 K2 K1 hq0 ha2 k _ hcanc hQ.le hov1
        simpa using this)
    have hgood := hi a1 (mem_Icc.mpr ⟨ha1, ha1'⟩) false
    simp only [Bool.false_eq_true, ite_false] at h3
    linarith


/-- The levels `k ∈ {0, …, m}` doubly `θ`-served (on their witness hops). -/
noncomputable def doublyServedLevels (s0 m a1 a2 : ℕ) (K1 K2 q : ℤ) (ξ : ℕ) (θ : ℝ) : Finset ℕ :=
  (range (m + 1)).filter fun k => ServedOnWitness s0 m a1 a2 K1 K2 q ξ θ true k ∧
    ServedOnWitness s0 m a1 a2 K1 K2 q ξ θ false k

/-- `c = 2^{-16}/(26 (a₀ + 1)²)`. -/
noncomputable def constBP (a0 : ℕ) : ℝ := (1 / 2) ^ 16 / (26 * ((a0 : ℝ) + 1) ^ 2)

theorem card_doubly_add_unserved (s0 m a1 a2 : ℕ) (K1 K2 q : ℤ) (ξ : ℕ) (θ : ℝ) :
    ((doublyServedLevels s0 m a1 a2 K1 K2 q ξ θ).card : ℝ) +
      (unservedLevels s0 m a1 a2 K1 K2 q ξ θ).card = (m : ℝ) + 1 := by
  have := Finset.card_filter_add_card_filter_not (s := range (m + 1))
    (fun k => ServedOnWitness s0 m a1 a2 K1 K2 q ξ θ true k ∧
      ServedOnWitness s0 m a1 a2 K1 K2 q ξ θ false k)
  rw [card_range] at this
  unfold doublyServedLevels unservedLevels
  exact_mod_cast this

/-- **Theorem BP**: assume Conjecture S for `a = 1, …, a₀` and the odd-shift blindness bound of the
eighth paper's Proposition 5.17 (`BlindnessBound`). Put `θ₀ = 2^{-(a₀+11)}` and
`c = 2^{-16}/(26 (a₀ + 1)²)`. There is a constant `C'` such that for all `m` and `s₀ > m` some odd
shift `ξ` has the property: for all `1 ≤ a₁, a₂ ≤ a₀`, all `K₁, K₂` and every `q ≥ 3`, the block-pair
label of `(B(a₁, K₁), B(a₂, K₂))` modulo `q` doubly `θ₀`-serves (on the witness hops) at most
`(1 - c)(m + 1) + C'` levels. -/
theorem theoremBP {a0 : ℕ} (ha0 : 1 ≤ a0) (hS : ∀ a ∈ Icc 1 a0, ConjectureS a)
    (hB : ∀ s0 m : ℕ, m < s0 → BlindnessBound s0 m) :
    ∃ C' : ℝ, ∀ m s0 : ℕ, m < s0 → ∃ ξ ∈ oddRange (dnpPeriod s0 m),
      ∀ a1 a2 : ℕ, 1 ≤ a1 → a1 ≤ a0 → 1 ≤ a2 → a2 ≤ a0 → ∀ K1 K2 q : ℤ, 3 ≤ q →
        ((doublyServedLevels s0 m a1 a2 K1 K2 q ξ (theta0 a0)).card : ℝ) ≤
          (1 - constBP a0) * ((m : ℝ) + 1) + C' := by
  obtain ⟨m0, hm0⟩ := good_shift_prob a0 (γ := 1 / 2) (by norm_num) hS
  set c := constBP a0 with hcdef
  set ε : ℝ := (1 / 2) ^ 16 / ((a0 : ℝ) + 1) with hεdef
  have hA : (0 : ℝ) < (a0 : ℝ) + 1 := by positivity
  have hc0 : 0 ≤ c := by rw [hcdef]; unfold constBP; positivity
  set m1 := max m0 (2 ^ 18 * (a0 + 1))
  refine ⟨max 2 (c * ((m1 : ℝ) + 1)), fun m s0 hms => ?_⟩
  have hΩpos := card_oddRange_pos s0 m
  by_cases hm : m < m1
  · -- small `m`: every odd shift will do
    obtain ⟨ξ, hξ⟩ : (oddRange (dnpPeriod s0 m)).Nonempty := Finset.card_pos.mp (by exact_mod_cast hΩpos)
    refine ⟨ξ, hξ, fun a1 a2 _ _ _ _ K1 K2 q _ => ?_⟩
    have hle := card_doubly_add_unserved s0 m a1 a2 K1 K2 q ξ (theta0 a0)
    have hU0 : (0 : ℝ) ≤ (unservedLevels s0 m a1 a2 K1 K2 q ξ (theta0 a0)).card := Nat.cast_nonneg _
    have hmm : ((m : ℝ) + 1) ≤ (m1 : ℝ) + 1 := by
      have : (m : ℝ) ≤ m1 := by exact_mod_cast hm.le
      linarith
    have h1 : c * ((m : ℝ) + 1) ≤ c * ((m1 : ℝ) + 1) := mul_le_mul_of_nonneg_left hmm hc0
    have h2 : c * ((m1 : ℝ) + 1) ≤ max 2 (c * ((m1 : ℝ) + 1)) := le_max_right _ _
    nlinarith
  push Not at hm
  obtain ⟨hsize, hgood⟩ := hm0 m (le_trans (le_max_left _ _) hm)
  have hmR : (2 : ℝ) ^ 18 * ((a0 : ℝ) + 1) ≤ m := by
    have : 2 ^ 18 * (a0 + 1) ≤ m := le_trans (le_max_right _ _) hm
    exact_mod_cast this
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 8 := by
    rw [hεdef, div_le_iff₀ hA]
    have : (1 : ℝ) ≤ (a0 : ℝ) + 1 := by
      have : (0 : ℝ) ≤ a0 := Nat.cast_nonneg _
      linarith
    norm_num; nlinarith
  have hεm : 4 ≤ ε * m := by
    rw [hεdef, div_mul_eq_mul_div, le_div_iff₀ hA]
    nlinarith
  have hbad := prob_many_nonHalfBlind_le (hB s0 m hms) hms hε0 hε1 hεm a0
  have hgood' := hgood s0 hms
  set Ω := oddRange (dnpPeriod s0 m)
  set Agood := Ω.filter fun ξ : ℕ => ∀ a ∈ Icc (1 : ℕ) a0, ∀ dir : Bool,
    1 / 2 * ((coarseZone m).card : ℝ) ≤ goodCount s0 m a dir ξ
  set Bbad := Ω.filter fun ξ : ℕ =>
    1 / (48 * ((a0 : ℝ) + 1)) * (fineZone m ε).card < (nonHalfBlind s0 m ε ξ).card
  have hAg : (Ω.card : ℝ) / 2 ≤ Agood.card := by
    rw [le_div_iff₀ hΩpos] at hgood'; linarith
  have hBb : (Bbad.card : ℝ) ≤ 3 / 32 * Ω.card := by
    rw [div_le_iff₀ hΩpos] at hbad
    have : 6144 * ((a0 : ℝ) + 1) * ε = 3 / 32 := by rw [hεdef]; field_simp; norm_num
    rw [this] at hbad; linarith
  have hne : (Agood \ Bbad).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.le_card_sdiff Bbad Agood
    have h1R : (Agood.card : ℝ) - Bbad.card ≤ (Agood \ Bbad).card := by
      have := Nat.sub_le_iff_le_add.mp h1
      have hR : (Agood.card : ℝ) ≤ (Agood \ Bbad).card + Bbad.card := by exact_mod_cast this
      linarith
    have : (0 : ℝ) < (Agood \ Bbad).card := by linarith
    exact_mod_cast this
  obtain ⟨ξ, hξ⟩ := hne
  rw [Finset.mem_sdiff] at hξ
  obtain ⟨hξA, hξB⟩ := hξ
  obtain ⟨hξΩ, hi⟩ := Finset.mem_filter.mp hξA
  have hii : ((nonHalfBlind s0 m ε ξ).card : ℝ) ≤ 1 / (48 * ((a0 : ℝ) + 1)) * (fineZone m ε).card := by
    by_contra hc; push Not at hc
    exact hξB (Finset.mem_filter.mpr ⟨hξΩ, hc⟩)
  refine ⟨ξ, hξΩ, fun a1 a2 ha1 ha1' ha2 ha2' K1 K2 q hq => ?_⟩
  have hw := witnesses_unserved (s0 := s0) (γ := 1 / 2) ha0 (by norm_num) (by norm_num) hε0 hε1 hms
    hεm hsize hξΩ hi hii ha1 ha1' ha2 ha2' K1 K2 q hq
  have hmin : min ((1 : ℝ) / 2 / 8) (ε / (26 * ((a0 : ℝ) + 1))) = c := by
    rw [hcdef, hεdef]; unfold constBP
    rw [min_eq_right]
    · field_simp
    · rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (1 : ℝ) ≤ (a0 : ℝ) + 1 := by
        have : (0 : ℝ) ≤ a0 := Nat.cast_nonneg _
        linarith
      nlinarith
  rw [hmin] at hw
  have hsum := card_doubly_add_unserved s0 m a1 a2 K1 K2 q ξ (theta0 a0)
  have : (2 : ℝ) ≤ max 2 (c * ((m1 : ℝ) + 1)) := le_max_left _ _
  linarith

end MergeDepth
