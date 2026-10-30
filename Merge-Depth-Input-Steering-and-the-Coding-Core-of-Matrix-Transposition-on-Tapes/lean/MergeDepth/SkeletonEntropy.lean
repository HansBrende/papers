import MergeDepth.CoarseCount
import MergeDepth.Entropy

/-!
# Coarse entropy of bounded-entry heads (Lemma 4.15)

The run of a machine on an input `X ∈ {0,1}^L` is described by its halting time `T X`, the input-head
walk `x0 X`, the work-head walks `xs X j` and the output count `nout X` (the number of bits appended
before each step). The skeleton at scale `w` (`skelData`) records `T X` and, for `t < T X`, the
blocks of all heads and of the output count; the input skeleton (`inSkel`) records `T X` and the
blocks of the input head.

`coarse_entropy_le` is Lemma 4.15: if on every input `L ≤ T ≤ c (L + 1)`, the work heads start at
`0` and enter every cell at most `V` times, and the output count starts at `0`, grows by `0` or `1`
and stays at most `L`, then for `w ≥ 4V` and `L ≥ max(2w, 16V)`,
`H(σ_w) ≤ H(σ^in_w) + θ L + 4kV log₂(ew/V)` with `θ = (4kVc log₂(ew/V) + log₂(2ecw))/w`.
-/

namespace MergeDepth

open Finset BoundedNesting Real

variable {L k : ℕ}

/-- The skeleton at scale `w`: the halting time and, before it, the blocks of all heads and of the
output count. -/
noncomputable def skelData (w : ℕ) (T : (Fin L → Bool) → ℕ) (x0 : (Fin L → Bool) → ℕ → ℤ)
    (xs : (Fin L → Bool) → Fin k → ℕ → ℤ) (nout : (Fin L → Bool) → ℕ → ℤ) (X : Fin L → Bool) :
    ℕ × (ℕ → ℤ × (Fin k → ℤ) × ℤ) :=
  (T X, fun t => if t < T X then (x0 X t / w, fun j => xs X j t / w, nout X t / w)
    else (0, fun _ => 0, 0))

/-- The input skeleton at scale `w`. -/
noncomputable def inSkel (w : ℕ) (T : (Fin L → Bool) → ℕ) (x0 : (Fin L → Bool) → ℕ → ℤ)
    (X : Fin L → Bool) : ℕ × (ℕ → ℤ) :=
  (T X, fun t => if t < T X then x0 X t / w else 0)

/-- The input skeleton is the first component of the skeleton. -/
theorem inSkel_eq (w : ℕ) (T : (Fin L → Bool) → ℕ) (x0 : (Fin L → Bool) → ℕ → ℤ)
    (xs : (Fin L → Bool) → Fin k → ℕ → ℤ) (nout : (Fin L → Bool) → ℕ → ℤ) :
    inSkel w T x0 = (fun p => (p.1, fun t => (p.2 t).1)) ∘ skelData w T x0 xs nout := by
  funext X
  simp only [inSkel, skelData, Function.comp_apply, Prod.mk.injEq, true_and]
  funext t
  split_ifs <;> rfl

open Classical in
/-- **Lemma 4.15.** -/
theorem coarse_entropy_le {V w : ℕ} {c : ℝ} (hV : 1 ≤ V) (hw : 4 * V ≤ w) (hL2w : 2 * w ≤ L)
    (hL16 : 16 * V ≤ L) (T : (Fin L → Bool) → ℕ) (x0 : (Fin L → Bool) → ℕ → ℤ)
    (xs : (Fin L → Bool) → Fin k → ℕ → ℤ) (nout : (Fin L → Bool) → ℕ → ℤ)
    (hT : ∀ X, L ≤ T X ∧ (T X : ℝ) ≤ c * (L + 1))
    (hxs : ∀ X j, IsWalk (xs X j) ∧ xs X j 0 = 0 ∧ ∀ c', (entries (xs X j) c' (T X - 1)).card ≤ V)
    (hn : ∀ X, nout X 0 = 0 ∧ (∀ t, t + 1 < T X → nout X (t + 1) = nout X t ∨
      nout X (t + 1) = nout X t + 1) ∧ ∀ t < T X, nout X t ≤ L) :
    entropy (skelData w T x0 xs nout) ≤ entropy (inSkel w T x0) +
      (4 * k * V * c * logb 2 (exp 1 * w / V) + logb 2 (2 * exp 1 * c * w)) / w * L +
      4 * k * V * logb 2 (exp 1 * w / V) := by
  have hw0 : 0 < w := by omega
  have hwz : (0 : ℤ) < w := by exact_mod_cast hw0
  have hwr : (0 : ℝ) < w := by exact_mod_cast hw0
  have hVr : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hLr : (2 * w : ℝ) ≤ L := by exact_mod_cast hL2w
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw0
  have hL1 : (1 : ℝ) ≤ L := by linarith
  -- `c ≥ 1/2`, so all the bases below exceed one
  have hc : (1 / 2 : ℝ) ≤ c := by
    obtain ⟨X⟩ : Nonempty (Fin L → Bool) := inferInstance
    obtain ⟨h1, h2⟩ := hT X
    have : (L : ℝ) ≤ c * (L + 1) := le_trans (by exact_mod_cast h1) h2
    by_contra hcon
    push Not at hcon
    nlinarith
  set A : ℝ := exp 1 * w / V
  set B : ℝ := 2 * exp 1 * c * w
  have hA : 1 < A := by
    have : (4 : ℝ) * V ≤ w := by exact_mod_cast hw
    have he : (2 : ℝ) < exp 1 := by have := add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
    simp only [A]
    rw [lt_div_iff₀ (by linarith)]
    nlinarith
  have hB : 1 < B := by
    have : (4 : ℝ) ≤ w := by
      have h4 : (4 : ℝ) * V ≤ w := by exact_mod_cast hw
      linarith
    have he : (2 : ℝ) < exp 1 := by have := add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
    have hcw : (2 : ℝ) ≤ c * w := by nlinarith
    simp only [B]
    rw [show (2 : ℝ) * exp 1 * c * w = 2 * exp 1 * (c * w) by ring]
    nlinarith
  set N : ℝ := A ^ ((k * (4 * V * c * L / w + 4 * V)) : ℝ) * B ^ ((L / w : ℝ))
  have hNlog : logb 2 N = (4 * k * V * c * logb 2 A + logb 2 B) / w * L + 4 * k * V * logb 2 A := by
    simp only [N]
    rw [logb_mul (by positivity) (by positivity), logb_rpow_eq_mul_logb_of_pos (by linarith),
      logb_rpow_eq_mul_logb_of_pos (by linarith)]
    field_simp
    ring
  -- the fibre bound
  have hfib : ∀ b, (((univ.image (skelData w T x0 xs nout)).filter
      ((fun p : ℕ × (ℕ → ℤ × (Fin k → ℤ) × ℤ) => (p.1, fun t => (p.2 t).1)) · = b)).card : ℝ) ≤
        N := by
    intro b
    set F := (univ.image (skelData w T x0 xs nout)).filter
      ((fun p : ℕ × (ℕ → ℤ × (Fin k → ℤ) × ℤ) => (p.1, fun t => (p.2 t).1)) · = b)
    set T₀ := b.1
    -- the inputs of the fibre all halt at `T₀`
    set W := (univ : Finset (Fin L → Bool)).filter fun X => T X = T₀
    have hF : ∀ p ∈ F, ∃ X ∈ W, skelData w T x0 xs nout X = p := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
      obtain ⟨X, -, rfl⟩ := mem_image.mp hp1
      refine ⟨X, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      have := congr_arg Prod.fst hp2
      simpa [skelData, T₀] using this
    -- the coarse work walks and the coarse output counts of the fibre
    set Swork : Finset (Fin T₀ → ℤ) :=
      W.biUnion fun X => univ.image fun j : Fin k => fun t : Fin T₀ => xs X j t / w
    set Sout : Finset (Fin T₀ → ℤ) := W.image fun X => fun t : Fin T₀ => nout X t / w
    -- an injection of the fibre into the product
    let e : ℕ × (ℕ → ℤ × (Fin k → ℤ) × ℤ) → (Fin k → Fin T₀ → ℤ) × (Fin T₀ → ℤ) :=
      fun p => (fun j t => (p.2 t).2.1 j, fun t => (p.2 t).2.2)
    have hinj : Set.InjOn e F := by
      intro p hp p' hp' he
      obtain ⟨X, hX, rfl⟩ := hF p hp
      obtain ⟨X', hX', rfl⟩ := hF p' hp'
      have hT1 : T X = T₀ := (mem_filter.mp hX).2
      have hT2 : T X' = T₀ := (mem_filter.mp hX').2
      have hb1 := (mem_filter.mp hp).2
      have hb2 := (mem_filter.mp hp').2
      simp only [e, Prod.mk.injEq] at he
      obtain ⟨he1, he2⟩ := he
      simp only [skelData, Prod.mk.injEq]
      refine ⟨hT1.trans hT2.symm, ?_⟩
      funext t
      by_cases ht : t < T₀
      · have h1 : x0 X t / w = x0 X' t / w := by
          have := congr_fun (congr_arg Prod.snd (hb1.trans hb2.symm)) t
          simpa [skelData, hT1, hT2, ht] using this
        have h2 := fun j => congr_fun (congr_fun he1 j) ⟨t, ht⟩
        have h3 := congr_fun he2 ⟨t, ht⟩
        simp only [skelData, hT1, hT2, ht, ↓reduceIte] at h2 h3 ⊢
        rw [h1, h3]
        congr 1
        exact Prod.ext (funext fun j => h2 j) rfl
      · simp only [hT1, hT2, ht, ↓reduceIte]
    have hsub : F.image e ⊆ (Fintype.piFinset fun _ : Fin k => Swork) ×ˢ Sout := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      obtain ⟨X, hX, rfl⟩ := hF p hp
      have hT1 : T X = T₀ := (mem_filter.mp hX).2
      refine mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun j => ?_, ?_⟩
      · refine mem_biUnion.mpr ⟨X, hX, mem_image.mpr ⟨j, mem_univ _, ?_⟩⟩
        funext t
        simp [e, skelData, hT1, t.2]
      · refine mem_image.mpr ⟨X, hX, ?_⟩
        funext t
        simp [e, skelData, hT1, t.2]
    have hcardF : (F.card : ℝ) ≤ (Swork.card : ℝ) ^ k * Sout.card := by
      have := card_le_card hsub
      rw [card_image_of_injOn hinj, card_product, Fintype.card_piFinset, prod_const, card_univ,
        Fintype.card_fin] at this
      exact_mod_cast this
    -- the fibre is empty, or `L ≤ T₀ ≤ c (L + 1)`
    rcases F.eq_empty_or_nonempty with hFe | ⟨p, hp⟩
    · rw [hFe, card_empty, Nat.cast_zero]
      positivity
    obtain ⟨X₀, hX₀, -⟩ := hF p hp
    have hT0 : T X₀ = T₀ := (mem_filter.mp hX₀).2
    obtain ⟨hLT, hTc⟩ := hT X₀
    rw [hT0] at hLT hTc
    -- the work walks: Lemma 4.14(a)
    have hwork : (Swork.card : ℝ) ≤ A ^ ((2 * V * (T₀ / w + 2) : ℝ)) := by
      refine card_coarse_le hV hw (by omega) Swork fun σ hσ => ?_
      obtain ⟨X, hX, hσ⟩ := mem_biUnion.mp hσ
      obtain ⟨j, -, rfl⟩ := mem_image.mp hσ
      have hT1 : T X = T₀ := (mem_filter.mp hX).2
      obtain ⟨h1, h2, h3⟩ := hxs X j
      exact ⟨xs X j, h1, h2, by rw [← hT1]; exact h3, fun t => rfl⟩
    -- the output counts: Lemma 4.14(b)
    have hout : (Sout.card : ℝ) ≤ (exp 1 * T₀ / (L / w : ℝ)) ^ ((L / w : ℝ)) := by
      have hm1 : 1 ≤ L / w := (Nat.le_div_iff_mul_le hw0).mpr (by omega)
      have hmT : L / w ≤ T₀ - 1 := by
        have : L / w ≤ L / 2 := Nat.div_le_div_left (by omega) (by norm_num)
        omega
      have hmy : ((L / w : ℕ) : ℝ) ≤ (L / w : ℝ) := Nat.cast_div_le
      have hyT : (L / w : ℝ) ≤ T₀ := by
        rw [div_le_iff₀ hwr]
        have : (L : ℝ) ≤ T₀ := by exact_mod_cast hLT
        nlinarith
      refine card_monotone_le hm1 hmT hmy hyT Sout fun σ hσ => ?_
      obtain ⟨X, hX, rfl⟩ := mem_image.mp hσ
      have hT1 : T X = T₀ := (mem_filter.mp hX).2
      obtain ⟨h0, hstep, hle⟩ := hn X
      have hT0pos : 0 < T₀ := by omega
      refine ⟨?_, fun t ht => ?_, ?_⟩
      · simp [ext0, hT0pos, h0]
      · simp only [ext0, ht, show t < T₀ by omega, ↓reduceDIte]
        rcases hstep t (by omega) with h | h
        · left; rw [h]
        · rw [h]
          have h1 := Int.ediv_le_ediv hwz (show nout X t ≤ nout X t + 1 by omega)
          have h2 := skel_step hwz (show |nout X t + 1 - nout X t| ≤ 1 by simp)
          have := abs_le.mp h2
          omega
      · simp only [ext0, show T₀ - 1 < T₀ by omega, ↓reduceDIte]
        have := hle (T₀ - 1) (by omega)
        have h2 : nout X (T₀ - 1) / (w : ℤ) ≤ (L : ℤ) / (w : ℤ) := Int.ediv_le_ediv hwz this
        have h3 : ((L : ℤ) / (w : ℤ)) = ((L / w : ℕ) : ℤ) := by push_cast; rfl
        rw [h3] at h2
        exact h2
    -- the numbers
    have hT₀r : (T₀ : ℝ) ≤ c * (L + 1) := hTc
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hm1bound : (2 * V * (T₀ / w + 2) : ℝ) ≤ 4 * V * c * L / w + 4 * V := by
      have : (T₀ : ℝ) / w ≤ 2 * c * L / w := by
        apply div_le_div_of_nonneg_right _ hwr.le
        nlinarith
      have e1 : (2 * V * (2 * c * L / w + 2) : ℝ) = 4 * V * c * L / w + 4 * V := by ring
      nlinarith
    have hwork' : (Swork.card : ℝ) ^ k ≤ A ^ ((k * (4 * V * c * L / w + 4 * V)) : ℝ) := by
      calc (Swork.card : ℝ) ^ k ≤ (A ^ ((2 * V * (T₀ / w + 2) : ℝ))) ^ k :=
            pow_le_pow_left₀ (by positivity) hwork k
        _ = A ^ ((k * (2 * V * (T₀ / w + 2)) : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
            ring_nf
        _ ≤ A ^ ((k * (4 * V * c * L / w + 4 * V)) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hA.le (mul_le_mul_of_nonneg_left hm1bound hk0)
    have hout' : (Sout.card : ℝ) ≤ B ^ ((L / w : ℝ)) := by
      refine hout.trans (Real.rpow_le_rpow (by positivity) ?_ (by positivity))
      rw [div_div_eq_mul_div, div_le_iff₀ (by linarith)]
      simp only [B]
      have : (T₀ : ℝ) * w ≤ 2 * c * w * L := by nlinarith
      nlinarith [exp_pos 1]
    calc (F.card : ℝ) ≤ (Swork.card : ℝ) ^ k * Sout.card := hcardF
      _ ≤ A ^ ((k * (4 * V * c * L / w + 4 * V)) : ℝ) * B ^ ((L / w : ℝ)) :=
          mul_le_mul hwork' hout' (by positivity) (by positivity)
  have h := entropy_le_of_fibres (skelData w T x0 xs nout)
    (fun p : ℕ × (ℕ → ℤ × (Fin k → ℤ) × ℤ) => (p.1, fun t => (p.2 t).1)) hfib
  rw [← inSkel_eq] at h
  rw [hNlog] at h
  linarith

open Filter Topology in
/-- **Lemma 4.15, the limit.** `θ_{k,V,c}(w) → 0` as `w → ∞`. -/
theorem theta_tendsto (k V c : ℝ) (hV : 0 < V) (hc : 0 < c) :
    Tendsto (fun w : ℝ => (4 * k * V * c * logb 2 (exp 1 * w / V) + logb 2 (2 * exp 1 * c * w)) / w)
      atTop (𝓝 0) := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  set α := (4 * k * V * c + 1) / log 2
  set β := (4 * k * V * c * (1 - log V) + log (2 * exp 1 * c)) / log 2
  have hlim : Tendsto (fun w : ℝ => α * (log w / w) + β * (1 / w)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun w : ℝ => log w / w) atTop (𝓝 0) := by
      simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun w : ℝ => 1 / w) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero
    simpa using (h1.const_mul α).add (h2.const_mul β)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
  have e1 : logb 2 (exp 1 * w / V) = (1 + log w - log V) / log 2 := by
    rw [logb, log_div (by positivity) hV.ne', log_mul (exp_pos 1).ne' hw.ne', log_exp]
  have e2 : logb 2 (2 * exp 1 * c * w) = (log (2 * exp 1 * c) + log w) / log 2 := by
    rw [logb, log_mul (by positivity) hw.ne']
  rw [e1, e2]
  simp only [α, β]
  field_simp
  ring

end MergeDepth
