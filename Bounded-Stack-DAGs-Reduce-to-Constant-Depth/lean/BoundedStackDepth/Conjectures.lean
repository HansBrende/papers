import BoundedStackDepth.DeepNesting
import MergeDepth.DeepNestingLabels

/-!
# Corollary N, second statement: Conjectures A′ and A″ are false

Conjecture A′ of the fourth paper (its Conjecture 5.25, restated as the eighth paper's
Conjecture 2.8) and its weakening, Conjecture A″ of the eighth paper (its Conjecture 5.24), bound
the number of levels that a cheap label on a cyclic cover of a deep-nesting pair can doubly serve.
The eighth paper's Corollary 5.26 shows that either conjecture makes the pairs depth-robust; Theorem T
cuts them to bounded depth. This module refutes both conjectures directly: the label that Theorem T
builds for the pair on `N` periods, read on the `N`-fold cover, is cheap and doubly serves almost
every level, with a number of values that does not depend on the nesting depth `m`.

The cover, its hops (`MergeDepth.coverHops`), their classes (`MergeDepth.coverClass`) and the error
of a hop (`MergeDepth.hopError`) are those of the eleventh paper's library.

* `IsCoverLabel`, `coverViolated`, `coverDescents`, `coverCost`, `classError`, `ThetaServesLevel`,
  `doublyServedCount`: labels on the `r`-fold cover, their cost (violated hops of both heads, counted
  per head, plus descents), the total error of a class, `θ`-serving, and the number of doubly
  `θ`-served levels, as in the eighth paper's Section 2.5.
* `ConjAprime`, `ConjAsecond`: the two conjectures; `conjAsecond_of_conjAprime`.
* `sum_hopError_le`: the per-head form of Lemma Zq on the cover, `Σ e ≤ q · #violated` for each
  head, from `sum_headPrev_eq` (the earlier endpoints of the hops of a head run over every time of
  the cover once).
* `unserved_mul_le`: a label of cost `κ` leaves at most `2 (m + 1) κ / (θ n_h)` levels not doubly
  `θ`-served, since the classes split the error of each head (`sum_classError_le`).
* `periodize`, `coverCost_periodize_le`: a label of the walk DAG on `[0, NP)` read on the `N`-fold
  cover costs at most `2 · cost + 2P + 1` there.
* `exists_label`: the label of Theorem T, with `K^P` values and cost at most `εT`.
* `not_conjAsecond`, `not_conjAprime`: **Corollary N, second statement.**
-/

set_option autoImplicit false

namespace BoundedStackDepth

open Finset BoundedNesting MergeDepth DirectedReciprocity

/-! ### Labels on the cover and the two conjectures -/

/-- A **label on the `r`-fold cover** with values in `[0, q)`: an `rP`-periodic map `G : ℤ → ℤ`. -/
def IsCoverLabel (s0 m r q : ℕ) (G : ℤ → ℤ) : Prop :=
  (∀ t, G (t + r * dnpPeriod s0 m) = G t) ∧ ∀ t, 0 ≤ G t ∧ G t < q

open Classical in
/-- The **violated hops** of head `h` on the `r`-fold cover: the hops `(p, u)` with `G u ≤ G p`. -/
noncomputable def coverViolated (s0 m : ℕ) (ξ : ℤ) (r : ℕ) (G : ℤ → ℤ) (h : Bool) :
    Finset (ℤ × ℤ) :=
  (coverHops s0 m ξ r h).filter fun η => G η.2 ≤ G η.1

open Classical in
/-- The **descents** of `G` on the `r`-fold cover: the times `t ∈ ℤ_{rP}` with `G t < G (t - 1)`. -/
noncomputable def coverDescents (s0 m r : ℕ) (G : ℤ → ℤ) : Finset ℤ :=
  (Ico 0 ((r : ℤ) * dnpPeriod s0 m)).filter fun t => G t < G (t - 1)

/-- The **cost** of a label on the cover: the violated hops of both heads, counted per head, plus
the descents. -/
noncomputable def coverCost (s0 m : ℕ) (ξ : ℤ) (r : ℕ) (G : ℤ → ℤ) : ℕ :=
  (coverViolated s0 m ξ r G true).card + (coverViolated s0 m ξ r G false).card +
    (coverDescents s0 m r G).card

/-- The **total error** of the class `(h, k)` of the `r`-fold cover under `G`. -/
noncomputable def classError (s0 m : ℕ) (ξ : ℤ) (r q : ℕ) (G : ℤ → ℤ) (h : Bool) (k : ℕ) : ℤ :=
  ∑ η ∈ coverClass s0 m ξ r h k, hopError G q η.1 η.2

/-- `G` **`θ`-serves** level `k` for head `h`: the class `(h, k)` has total error at most
`θ q n_h / (2 (m + 1))`. The fourth paper defines it for `0 < θ < 1`; since the number of doubly
served levels grows with `θ`, the conjectures below read the same with `θ₀ > 0`. -/
def ThetaServesLevel (s0 m : ℕ) (ξ : ℤ) (r q : ℕ) (θ : ℝ) (G : ℤ → ℤ) (h : Bool) (k : ℕ) :
    Prop :=
  (classError s0 m ξ r q G h k : ℝ) ≤ θ * q * coverHopCount s0 m ξ r / (2 * ((m : ℝ) + 1))

open Classical in
/-- The number of levels `k ≤ m` that `G` **doubly `θ`-serves**: it `θ`-serves them for both heads. -/
noncomputable def doublyServedCount (s0 m : ℕ) (ξ : ℤ) (r q : ℕ) (θ : ℝ) (G : ℤ → ℤ) : ℕ :=
  ((range (m + 1)).filter fun k =>
    ThetaServesLevel s0 m ξ r q θ G true k ∧ ThetaServesLevel s0 m ξ r q θ G false k).card

/-- **Conjecture A″ of the eighth paper** (its Conjecture 5.24). There are `θ₀ > 0`, `η < 1` and
constants `C, C'` such that for all `s₀ > m` some odd shift `ξ` has the following property: for all
`r ≥ 1` and `q`, every label of cost at most `n_h / 8` on the `r`-fold cover of the pair
`x₁ = U(s₀, m, 1)`, `x₂ = x₁(· + ξ)`, has at most `C log₂ q + C' + η (m + 1)` doubly `θ₀`-served
levels. -/
def ConjAsecond : Prop :=
  ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∃ η : ℝ, η < 1 ∧ ∃ C C' : ℝ, ∀ s0 m : ℕ, m < s0 → ∃ ξ : ℤ, Odd ξ ∧
    ∀ r q : ℕ, 1 ≤ r → ∀ G : ℤ → ℤ, IsCoverLabel s0 m r q G →
      (coverCost s0 m ξ r G : ℝ) ≤ coverHopCount s0 m ξ r / 8 →
      (doublyServedCount s0 m ξ r q θ₀ G : ℝ) ≤ C * Real.logb 2 q + C' + η * ((m : ℝ) + 1)

/-- **Conjecture A′ of the fourth paper** (its Conjecture 5.25, as restated in the eighth paper's
Conjecture 2.8): Conjecture A″ with `η = 0`. -/
def ConjAprime : Prop :=
  ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∃ C C' : ℝ, ∀ s0 m : ℕ, m < s0 → ∃ ξ : ℤ, Odd ξ ∧
    ∀ r q : ℕ, 1 ≤ r → ∀ G : ℤ → ℤ, IsCoverLabel s0 m r q G →
      (coverCost s0 m ξ r G : ℝ) ≤ coverHopCount s0 m ξ r / 8 →
      (doublyServedCount s0 m ξ r q θ₀ G : ℝ) ≤ C * Real.logb 2 q + C'

/-- Conjecture A′ implies Conjecture A″. -/
theorem conjAsecond_of_conjAprime : ConjAprime → ConjAsecond := by
  rintro ⟨θ₀, hθ, C, C', h⟩
  refine ⟨θ₀, hθ, 0, by norm_num, C, C', fun s0 m hms => ?_⟩
  obtain ⟨ξ, hξ, hG⟩ := h s0 m hms
  exact ⟨ξ, hξ, fun r q hr G hGl hc => by simpa using hG r q hr G hGl hc⟩

/-! ### The per-class split of Lemma Zq on the cover -/

/-- The error of a hop under a label with values in `[0, q)`: `G u - G p - 1`, plus `q` if the hop
is violated. -/
theorem hopError_eq {G : ℤ → ℤ} {q : ℕ} (hG : ∀ t, 0 ≤ G t ∧ G t < q) (p u : ℤ) :
    hopError G q p u = G u - G p - 1 + if G u ≤ G p then (q : ℤ) else 0 := by
  unfold hopError
  have hp := hG p
  have hu := hG u
  split_ifs with hle
  · have e := Int.emod_eq_of_lt (a := G u - G p - 1 + q) (b := q) (by omega) (by omega)
    rwa [Int.add_emod_right] at e
  · rw [add_zero]
    exact Int.emod_eq_of_lt (by omega) (by omega)

/-- **The earlier endpoints of the hops of a head run over every time of the cover once**: for an
`rP`-periodic `G`, `Σ_u G (prev u) = Σ_u G u` over `u ∈ [0, rP)`. -/
theorem sum_headPrev_eq {s0 m : ℕ} (ξ : ℤ) {r : ℕ} (hr : 1 ≤ r) (h : Bool) {G : ℤ → ℤ}
    (hper : ∀ t, G (t + r * dnpPeriod s0 m) = G t) :
    ∑ u ∈ Ico (0 : ℤ) (r * dnpPeriod s0 m), G (headPrev s0 m ξ h u) =
      ∑ u ∈ Ico (0 : ℤ) (r * dnpPeriod s0 m), G u := by
  have hP : (0 : ℤ) < dnpPeriod s0 m := by exact_mod_cast dnpPeriod_pos s0 m
  set T : ℤ := r * dnpPeriod s0 m with hTdef
  have hT : 0 < T := mul_pos (by exact_mod_cast hr) hP
  set f : ℤ → ℤ := fun u => headPrev s0 m ξ h u % T
  have hmaps : ∀ u ∈ Ico (0 : ℤ) T, f u ∈ Ico (0 : ℤ) T := fun u _ =>
    mem_Ico.mpr ⟨Int.emod_nonneg _ hT.ne', Int.emod_lt_of_pos _ hT⟩
  have hinj : Set.InjOn f (Ico (0 : ℤ) T) := by
    intro u hu u' hu' hf
    have hdvd : T ∣ headPrev s0 m ξ h u' - headPrev s0 m ξ h u := Int.ModEq.dvd hf
    obtain ⟨n, hn⟩ := hdvd
    have hp : headPrev s0 m ξ h (u + (n * r) * dnpPeriod s0 m) = headPrev s0 m ξ h u' := by
      rw [headPrev_add_mul_period]
      linear_combination (-1 : ℤ) * hn
    have h1 := isHopZ_headPrev s0 m ξ h u'
    have h2 := isHopZ_headPrev s0 m ξ h (u + (n * r) * dnpPeriod s0 m)
    rw [hp] at h2
    have he : u' = u + n * T := by rw [h1.eq_of_fst h2, hTdef]; ring
    rw [coe_Ico, Set.mem_Ico] at hu hu'
    have hn0 : n = 0 := by
      rcases lt_trichotomy n 0 with hlt | heq | hgt
      · have : n * T ≤ -T := by nlinarith
        omega
      · exact heq
      · have : T ≤ n * T := by nlinarith
        omega
    rw [he, hn0]; ring
  have himg : (Ico (0 : ℤ) T).image f = Ico (0 : ℤ) T :=
    Finset.eq_of_subset_of_card_le (image_subset_iff.mpr hmaps)
      (by rw [card_image_of_injOn hinj])
  calc ∑ u ∈ Ico (0 : ℤ) T, G (headPrev s0 m ξ h u) = ∑ u ∈ Ico (0 : ℤ) T, G (f u) := by
        refine sum_congr rfl fun u _ => ?_
        have e := periodic_add_int_mul hper (headPrev s0 m ξ h u % T) (headPrev s0 m ξ h u / T)
        have e2 : headPrev s0 m ξ h u % T + headPrev s0 m ξ h u / T * (r * dnpPeriod s0 m) =
            headPrev s0 m ξ h u := by
          rw [← hTdef, mul_comm (headPrev s0 m ξ h u / T)]
          exact Int.emod_add_mul_ediv _ _
        rw [e2] at e
        exact e
    _ = ∑ t ∈ (Ico (0 : ℤ) T).image f, G t := (sum_image hinj).symm
    _ = ∑ t ∈ Ico (0 : ℤ) T, G t := by rw [himg]

/-- **The per-head form of Lemma Zq on the cover**: for each head, the total error of its hops is at
most `q` times the number of its violated hops. -/
theorem sum_hopError_le {s0 m : ℕ} (ξ : ℤ) {r q : ℕ} (hr : 1 ≤ r) {G : ℤ → ℤ}
    (hG : IsCoverLabel s0 m r q G) (h : Bool) :
    ∑ η ∈ coverHops s0 m ξ r h, hopError G q η.1 η.2 ≤ q * (coverViolated s0 m ξ r G h).card := by
  classical
  have hsplit : ∑ η ∈ coverHops s0 m ξ r h, hopError G q η.1 η.2 =
      (∑ η ∈ coverHops s0 m ξ r h, G η.2 - ∑ η ∈ coverHops s0 m ξ r h, G η.1 -
        (coverHops s0 m ξ r h).card) + q * (coverViolated s0 m ξ r G h).card := by
    rw [sum_congr rfl fun η _ => hopError_eq hG.2 η.1 η.2]
    simp only [sum_add_distrib, sum_sub_distrib, sum_ite, sum_const_zero, add_zero, sum_const,
      nsmul_eq_mul, mul_one, coverViolated]
    ring
  have htel : ∑ η ∈ coverHops s0 m ξ r h, G η.1 = ∑ η ∈ coverHops s0 m ξ r h, G η.2 := by
    have hinj : ∀ a ∈ Ico (0 : ℤ) (r * dnpPeriod s0 m), ∀ b ∈ Ico (0 : ℤ) (r * dnpPeriod s0 m),
        (headPrev s0 m ξ h a, a) = (headPrev s0 m ξ h b, b) → a = b :=
      fun a _ b _ hab => (Prod.mk.injEq _ _ _ _ ▸ hab).2
    rw [coverHops_eq_image, sum_image hinj, sum_image hinj]
    exact sum_headPrev_eq ξ hr h hG.1
  rw [hsplit, htel, sub_self, zero_sub]
  have : (0 : ℤ) ≤ (coverHops s0 m ξ r h).card := Nat.cast_nonneg _
  linarith

/-- A hop has at most one level. -/
theorem headHopLevelIs_unique {s0 m : ℕ} {ξ : ℤ} {h : Bool} {p u : ℤ} {k k' : ℕ}
    (hk : HeadHopLevelIs s0 m ξ h p u k) (hk' : HeadHopLevelIs s0 m ξ h p u k') : k = k' :=
  ((headHopLevelIs_iff _ _ _ _ _ _ _).mp hk).unique ((headHopLevelIs_iff _ _ _ _ _ _ _).mp hk')

/-- **The classes of the levels `k ≤ m` share the error of the hops of a head.** -/
theorem sum_classError_le (s0 m : ℕ) (ξ : ℤ) (r : ℕ) {q : ℕ} (hq : 1 ≤ q) (G : ℤ → ℤ) (h : Bool) :
    ∑ k ∈ range (m + 1), classError s0 m ξ r q G h k ≤
      ∑ η ∈ coverHops s0 m ξ r h, hopError G q η.1 η.2 := by
  classical
  unfold classError
  simp_rw [sum_coverClass]
  rw [sum_comm, coverHops_eq_image, sum_image fun a _ b _ hab => (Prod.mk.injEq _ _ _ _ ▸ hab).2]
  refine sum_le_sum fun u _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hcard : ((range (m + 1)).filter fun k =>
      HeadHopLevelIs s0 m ξ h (headPrev s0 m ξ h u) u k).card ≤ 1 :=
    card_le_one.mpr fun a ha b hb =>
      headHopLevelIs_unique (mem_filter.mp ha).2 (mem_filter.mp hb).2
  have he : 0 ≤ hopError G q (headPrev s0 m ξ h u) u := hopError_nonneg G (by omega) _ _
  have hc : (((range (m + 1)).filter fun k =>
      HeadHopLevelIs s0 m ξ h (headPrev s0 m ξ h u) u k).card : ℤ) ≤ 1 := by exact_mod_cast hcard
  nlinarith

/-- **Few levels are not doubly served**: a label of cost `κ` on the `r`-fold cover leaves at most
`2 (m + 1) κ / (θ n_h)` levels `k ≤ m` not doubly `θ`-served. -/
theorem unserved_mul_le {s0 m : ℕ} (ξ : ℤ) {r q : ℕ} (hr : 1 ≤ r) (hq : 1 ≤ q) {θ : ℝ}
    (hθ : 0 < θ) {G : ℤ → ℤ} (hG : IsCoverLabel s0 m r q G) :
    (((m : ℝ) + 1) - doublyServedCount s0 m ξ r q θ G) * (θ * coverHopCount s0 m ξ r) ≤
      2 * ((m : ℝ) + 1) * coverCost s0 m ξ r G := by
  classical
  set B : ℝ := θ * q * coverHopCount s0 m ξ r / (2 * ((m : ℝ) + 1)) with hBdef
  set S := (range (m + 1)).filter fun k =>
    ThetaServesLevel s0 m ξ r q θ G true k ∧ ThetaServesLevel s0 m ξ r q θ G false k
  set NS := (range (m + 1)).filter fun k =>
    ¬ (ThetaServesLevel s0 m ξ r q θ G true k ∧ ThetaServesLevel s0 m ξ r q θ G false k)
  have hcount : ((m : ℝ) + 1) - doublyServedCount s0 m ξ r q θ G = NS.card := by
    have := card_filter_add_card_filter_not (s := range (m + 1)) fun k =>
      ThetaServesLevel s0 m ξ r q θ G true k ∧ ThetaServesLevel s0 m ξ r q θ G false k
    rw [card_range] at this
    have e : (doublyServedCount s0 m ξ r q θ G : ℝ) + NS.card = (m : ℝ) + 1 := by
      unfold doublyServedCount; exact_mod_cast this
    linarith
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq
  have hcE : ∀ h k, (0 : ℝ) ≤ classError s0 m ξ r q G h k := fun h k => by
    unfold classError
    exact_mod_cast sum_nonneg fun η _ => hopError_nonneg G hq0 _ _
  -- every level that is not doubly served has a class of error above `B`
  have hNS : ∀ k ∈ NS, B ≤ (classError s0 m ξ r q G true k : ℝ) + classError s0 m ξ r q G false k := by
    intro k hk
    have hk' := (mem_filter.mp hk).2
    unfold ThetaServesLevel at hk'
    rw [not_and_or, not_le, not_le] at hk'
    rcases hk' with h1 | h1
    · linarith [hcE false k]
    · linarith [hcE true k]
  have h1 : (NS.card : ℝ) * B ≤ ∑ k ∈ NS, ((classError s0 m ξ r q G true k : ℝ) +
      classError s0 m ξ r q G false k) := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hNS
  have h2 : ∑ k ∈ NS, ((classError s0 m ξ r q G true k : ℝ) + classError s0 m ξ r q G false k) ≤
      ∑ k ∈ range (m + 1), ((classError s0 m ξ r q G true k : ℝ) +
        classError s0 m ξ r q G false k) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ => add_nonneg (hcE _ _) (hcE _ _)
  have h3 : ∑ k ∈ range (m + 1), ((classError s0 m ξ r q G true k : ℝ) +
      classError s0 m ξ r q G false k) ≤ q * coverCost s0 m ξ r G := by
    rw [sum_add_distrib]
    have ht := (sum_classError_le s0 m ξ r hq G true).trans (sum_hopError_le ξ hr hG true)
    have hf := (sum_classError_le s0 m ξ r hq G false).trans (sum_hopError_le ξ hr hG false)
    have ht' : ∑ k ∈ range (m + 1), (classError s0 m ξ r q G true k : ℝ) ≤
        q * (coverViolated s0 m ξ r G true).card := by exact_mod_cast ht
    have hf' : ∑ k ∈ range (m + 1), (classError s0 m ξ r q G false k : ℝ) ≤
        q * (coverViolated s0 m ξ r G false).card := by exact_mod_cast hf
    unfold coverCost
    push_cast
    have : (0 : ℝ) ≤ q * (coverDescents s0 m r G).card := by positivity
    nlinarith
  have hm : (0 : ℝ) < 2 * ((m : ℝ) + 1) := by positivity
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have key : (NS.card : ℝ) * B ≤ q * coverCost s0 m ξ r G := h1.trans (h2.trans h3)
  rw [hcount]
  rw [hBdef] at key
  have e : (NS.card : ℝ) * (θ * q * coverHopCount s0 m ξ r / (2 * ((m : ℝ) + 1))) * (2 * ((m : ℝ) + 1)) =
      q * ((NS.card : ℝ) * (θ * coverHopCount s0 m ξ r)) := by
    field_simp
  have key2 := mul_le_mul_of_nonneg_right key hm.le
  rw [e] at key2
  have key3 : q * ((NS.card : ℝ) * (θ * coverHopCount s0 m ξ r)) ≤
      q * (2 * ((m : ℝ) + 1) * coverCost s0 m ξ r G) := by linarith
  exact le_of_mul_le_mul_left key3 hqr

/-! ### From the walk DAG to the cover -/

/-- The label `Ψ` of the walk DAG on `[0, T)`, read on the cyclic time axis `ℤ_T`. -/
def periodize (Ψ : ℕ → ℕ) (T : ℕ) (t : ℤ) : ℤ := Ψ (t % T).toNat

theorem periodize_of_lt {Ψ : ℕ → ℕ} {T : ℕ} {t : ℤ} (h0 : 0 ≤ t) (hT : t < T) :
    periodize Ψ T t = Ψ t.toNat := by
  unfold periodize; rw [Int.emod_eq_of_lt h0 hT]

theorem isCoverLabel_periodize {s0 m N q : ℕ} {Ψ : ℕ → ℕ} (hΨ : ∀ t, Ψ t < q) :
    IsCoverLabel s0 m N q (periodize Ψ (N * dnpPeriod s0 m)) := by
  refine ⟨fun t => ?_, fun t => ⟨by unfold periodize; positivity, ?_⟩⟩
  · unfold periodize
    rw [show ((N * dnpPeriod s0 m : ℕ) : ℤ) = (N : ℤ) * dnpPeriod s0 m by push_cast; ring,
      Int.add_emod_right]
  · unfold periodize; exact_mod_cast hΨ _

/-- The hops of the cover with a nonnegative earlier endpoint are hops of the walk DAG. -/
theorem mem_hopPairs_of_coverHops {s0 m : ℕ} (hms : m ≤ s0) {ξ : ℤ} {N : ℕ} {h : Bool}
    {η : ℤ × ℤ} (hη : η ∈ coverHops s0 m ξ N h) (h0 : 0 ≤ η.1) :
    (η.1.toNat, η.2.toNat) ∈ hopPairs (allHops (dnpPair s0 m ξ) (N * dnpPeriod s0 m)) := by
  classical
  rw [mem_coverHops] at hη
  obtain ⟨hu, hp⟩ := hη
  rw [mem_Ico] at hu
  have hhop : IsHopZ (MergeDepth.headWalk s0 m ξ h) η.1 η.2 := by
    rw [hp]; exact isHopZ_headPrev s0 m ξ h η.2
  have hlong : η.1 + 2 ≤ η.2 := by
    have := ((isHopZ_headWalk_iff s0 m ξ h η.1 η.2).mp hhop).long hms
    linarith
  unfold hopPairs
  refine mem_image.mpr ⟨(if h then 0 else 1, η.1.toNat, η.2.toNat), ?_, rfl⟩
  rw [mem_allHops]
  dsimp only
  have hx : dnpPair s0 m ξ (if h then 0 else 1) = fun t : ℕ => MergeDepth.headWalk s0 m ξ h t := by
    funext t
    unfold dnpPair
    cases h <;> rfl
  rw [hx, isHop_iff_isHopZ]
  have hT : ((η.2.toNat : ℕ) : ℤ) < ((N * dnpPeriod s0 m : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg hu.1]; push_cast; exact hu.2
  refine ⟨by omega, by exact_mod_cast hT, ?_⟩
  rwa [Int.toNat_of_nonneg h0, Int.toNat_of_nonneg hu.1]

/-- The violated hops of a head on the cover: those with a negative earlier endpoint end in the first
period, and the others are violated hops of the walk DAG. -/
theorem card_coverViolated_le {s0 m : ℕ} (hms : m ≤ s0) (ξ : ℤ) {N : ℕ} (Ψ : ℕ → ℕ) (h : Bool) :
    (coverViolated s0 m ξ N (periodize Ψ (N * dnpPeriod s0 m)) h).card ≤
      (violatedOf Ψ (hopPairs (allHops (dnpPair s0 m ξ) (N * dnpPeriod s0 m)))).card +
        dnpPeriod s0 m := by
  classical
  set G := periodize Ψ (N * dnpPeriod s0 m)
  set V := coverViolated s0 m ξ N G h
  rw [← card_filter_add_card_filter_not (s := V) fun η => 0 ≤ η.1]
  have hP : (0 : ℤ) < dnpPeriod s0 m := by exact_mod_cast dnpPeriod_pos s0 m
  -- the hops with a nonnegative earlier endpoint
  have hA : (V.filter fun η => 0 ≤ η.1).card ≤
      (violatedOf Ψ (hopPairs (allHops (dnpPair s0 m ξ) (N * dnpPeriod s0 m)))).card := by
    refine card_le_card_of_injOn (fun η => (η.1.toNat, η.2.toNat)) (fun η hη => ?_) ?_
    · obtain ⟨hηV, h0⟩ := mem_filter.mp hη
      obtain ⟨hηH, hviol⟩ := mem_filter.mp hηV
      have hmem := mem_hopPairs_of_coverHops hms hηH h0
      have hη' := hηH
      rw [mem_coverHops, mem_Ico] at hη'
      have hlt : η.1 < η.2 := by
        have := isHopZ_headPrev s0 m ξ h η.2
        rw [← hη'.2] at this
        exact this.1
      refine mem_filter.mpr ⟨hmem, ?_⟩
      have e1 : G η.1 = Ψ η.1.toNat := periodize_of_lt h0 (by push_cast at hη' ⊢; linarith [hη'.1.2])
      have e2 : G η.2 = Ψ η.2.toNat := periodize_of_lt hη'.1.1 (by push_cast at hη' ⊢; linarith [hη'.1.2])
      have hv : G η.2 ≤ G η.1 := hviol
      rw [e1, e2] at hv
      exact_mod_cast hv
    · intro a ha b hb hab
      obtain ⟨haV, ha0⟩ := mem_filter.mp ha
      obtain ⟨hbV, hb0⟩ := mem_filter.mp hb
      have ha2 := (mem_Ico.mp ((mem_coverHops.mp (mem_filter.mp haV).1).1)).1
      have hb2 := (mem_Ico.mp ((mem_coverHops.mp (mem_filter.mp hbV).1).1)).1
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (by omega) (by omega)
  -- the hops with a negative earlier endpoint end in `[0, P)`
  have hB : (V.filter fun η => ¬ 0 ≤ η.1).card ≤ dnpPeriod s0 m := by
    have hsub : (V.filter fun η => ¬ 0 ≤ η.1) ⊆
        (Ico (0 : ℤ) (dnpPeriod s0 m)).image fun u => (headPrev s0 m ξ h u, u) := by
      intro η hη
      obtain ⟨hηV, hneg⟩ := mem_filter.mp hη
      have hη' := mem_coverHops.mp (mem_filter.mp hηV).1
      have hge := headPrev_ge s0 m ξ h η.2
      rw [← hη'.2] at hge
      rw [mem_Ico] at hη'
      refine mem_image.mpr ⟨η.2, mem_Ico.mpr ⟨hη'.1.1, by linarith⟩, ?_⟩
      exact Prod.ext hη'.2.symm rfl
    refine (card_le_card hsub).trans (card_image_le.trans ?_)
    rw [Int.card_Ico, sub_zero, Int.toNat_natCast]
  omega

/-- The descents of the read label on the cover: those of `Ψ` and possibly the time `0`. -/
theorem card_coverDescents_le {s0 m N : ℕ} (Ψ : ℕ → ℕ) :
    (coverDescents s0 m N (periodize Ψ (N * dnpPeriod s0 m))).card ≤
      (descentsOf Ψ (N * dnpPeriod s0 m)).card + 1 := by
  classical
  set T := N * dnpPeriod s0 m
  have hsub : coverDescents s0 m N (periodize Ψ T) ⊆
      insert 0 ((descentsOf Ψ T).image fun t : ℕ => (t : ℤ)) := by
    intro t ht
    obtain ⟨htI, hdesc⟩ := mem_filter.mp ht
    rw [mem_Ico] at htI
    have hT' : ((N : ℤ) * dnpPeriod s0 m) = (T : ℤ) := by simp [T]
    rw [hT'] at htI
    rcases eq_or_lt_of_le htI.1 with h0 | hpos
    · exact mem_insert.mpr (Or.inl h0.symm)
    · refine mem_insert.mpr (Or.inr (mem_image.mpr ⟨t.toNat, ?_, Int.toNat_of_nonneg htI.1⟩))
      refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      rw [periodize_of_lt htI.1 htI.2, periodize_of_lt (by omega) (by omega)] at hdesc
      have e : (t - 1).toNat = t.toNat - 1 := by omega
      rw [e] at hdesc
      exact_mod_cast hdesc
  refine (card_le_card hsub).trans ((card_insert_le _ _).trans ?_)
  have := card_image_le (s := descentsOf Ψ T) (f := fun t : ℕ => (t : ℤ))
  omega

/-- **From the walk DAG to the cover** (a crude form of the eighth paper's Lemma 5.25): a label of the
walk DAG of the pair on `[0, NP)`, read on the `N`-fold cover, costs at most `2 · cost + 2P + 1`
there. -/
theorem coverCost_periodize_le {s0 m : ℕ} (hms : m ≤ s0) (ξ : ℤ) {N : ℕ} (Ψ : ℕ → ℕ) :
    coverCost s0 m ξ N (periodize Ψ (N * dnpPeriod s0 m)) ≤
      2 * labelCutSize (dnpPair s0 m ξ) (N * dnpPeriod s0 m) Ψ + 2 * dnpPeriod s0 m + 1 := by
  have ht := card_coverViolated_le hms ξ (N := N) Ψ true
  have hf := card_coverViolated_le hms ξ (N := N) Ψ false
  have hd := card_coverDescents_le (s0 := s0) (m := m) (N := N) Ψ
  unfold coverCost labelCutSize
  omega

/-! ### The label of Theorem T -/

/-- **The label of Theorem T**: for `k` walks and `ε > 0` there is a label with values in `[0, K^P)`
whose cut has at most `εT` edges. -/
theorem exists_label (k : ℕ) {ε : ℝ} (hε : 0 < ε) (T : ℕ) (xs : Fin k → ℕ → ℤ)
    (hx : ∀ h, IsWalk (xs h)) :
    ∃ Ψ : ℕ → ℕ, (∀ t, Ψ t < parK k ε ^ parP k ε) ∧ (labelCutSize xs T Ψ : ℝ) ≤ ε * T := by
  obtain ⟨α, Ω, Ψ, hΩ, hΨ, havg⟩ := exists_avgLabel k hε T xs hx
  obtain ⟨ω, -, hω⟩ := exists_le_of_sum_le hΩ
    (f := fun ω => (labelCutSize xs T (Ψ ω) : ℝ)) (g := fun _ => ε * T)
    (by rw [sum_const, nsmul_eq_mul]; exact havg)
  exact ⟨Ψ ω, hΨ ω, hω⟩

/-! ### Corollary N, second statement -/

/-- **Corollary N, second statement: Conjecture A″ of the eighth paper is false.** For given
`θ₀, η, C, C'`, take `ε` small, the nesting depth `m` large and `s₀ = m + 2`; at every shift, the label
of Theorem T for the pair on `N` periods, read on the `N`-fold cover, has `K^P` values, independent
of `m`, and cost at most `2ε n_h ≤ n_h / 8`, and it doubly `θ₀`-serves at least `(m + 1)(1 - δ/4)`
levels, `δ = 1 - η`, which exceeds `C log₂ q + C' + η (m + 1)`. -/
theorem not_conjAsecond : ¬ ConjAsecond := by
  rintro ⟨θ₀, hθ₀, η, hη, C, C', hconj⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 - η := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (1 / 32) (δ * θ₀ / 16) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 32 := by rw [hεdef]; exact min_le_left _ _
  have hε2 : ε ≤ δ * θ₀ / 16 := by rw [hεdef]; exact min_le_right _ _
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = parK 2 ε ^ parP 2 ε := ⟨_, rfl⟩
  have hq : 1 ≤ q := by rw [hqdef]; exact Nat.one_le_pow _ _ (by unfold parK; omega)
  -- the nesting depth: `C log₂ q + C' < (m + 1) δ / 2`
  obtain ⟨m, hm⟩ := exists_nat_gt ((C * Real.logb 2 q + C') * (2 / δ))
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hmδ : C * Real.logb 2 q + C' < ((m : ℝ) + 1) * (δ / 2) := by
    have h1 : (C * Real.logb 2 q + C') * (2 / δ) < (m : ℝ) + 1 := by linarith
    have e : (C * Real.logb 2 q + C') = (C * Real.logb 2 q + C') * (2 / δ) * (δ / 2) := by
      field_simp
    rw [e]
    exact mul_lt_mul_of_pos_right h1 (by positivity)
  obtain ⟨ξ, -, hξ⟩ := hconj (m + 2) m (by omega)
  -- the period and the number of periods
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = dnpPeriod (m + 2) m := ⟨_, rfl⟩
  have hP : 1 ≤ P := by rw [hPdef]; exact dnpPeriod_pos (m + 2) m
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈2 / ε⌉₊ + 1 := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by omega
  have hN : 2 / ε ≤ (N : ℝ) := by
    have := Nat.le_ceil (2 / ε)
    rw [hNdef]; push_cast; linarith
  have hεN : 2 ≤ ε * N := by
    have := mul_le_mul_of_nonneg_left hN hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  -- the label of Theorem T on `[0, NP)`, read on the `N`-fold cover
  obtain ⟨Ψ, hΨq, hΨc⟩ := exists_label 2 hε (N * P) (dnpPair (m + 2) m ξ)
    (dnpPair_isWalk (by omega) ξ)
  rw [← hqdef] at hΨq
  have hGl : IsCoverLabel (m + 2) m N q (periodize Ψ (N * dnpPeriod (m + 2) m)) :=
    isCoverLabel_periodize hΨq
  have hcost := coverCost_periodize_le (s0 := m + 2) (m := m) (by omega) ξ (N := N) Ψ
  rw [← hPdef] at hGl hcost
  obtain ⟨G, hGdef⟩ : ∃ G, G = periodize Ψ (N * P) := ⟨_, rfl⟩
  rw [← hGdef] at hGl hcost
  -- the quantities, as opaque reals
  obtain ⟨n, hndef⟩ : ∃ n : ℝ, n = coverHopCount (m + 2) m ξ N := ⟨_, rfl⟩
  have hn : n = 2 * N * P := by rw [hndef, coverHopCount_eq, ← hPdef]; push_cast; ring
  have hnpos : 0 < n := by rw [hn]; positivity
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = coverCost (m + 2) m ξ N G := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = labelCutSize (dnpPair (m + 2) m ξ) (N * P) Ψ := ⟨_, rfl⟩
  have h1 : κ ≤ 2 * c + 2 * P + 1 := by
    have := Nat.cast_le (α := ℝ) |>.mpr hcost
    push_cast at this
    rw [hκdef, hcdef]; exact this
  have h3 : c ≤ ε * (N * P) := by
    rw [hcdef]; have := hΨc; push_cast at this; exact this
  -- the cost: at most `2 ε n_h ≤ n_h / 8`
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ε * N * P := ⟨_, rfl⟩
  have hP2 : 2 * (P : ℝ) ≤ A := by
    have := mul_le_mul_of_nonneg_right hεN (by positivity : (0 : ℝ) ≤ P)
    rw [hAdef]; linarith
  have h3' : c ≤ A := by rw [hAdef, mul_assoc]; exact h3
  have hc2' : κ ≤ 4 * A := by linarith
  have hc2 : κ ≤ 2 * ε * n := by
    have e : 2 * ε * n = 4 * A := by rw [hn, hAdef]; ring
    rw [e]; exact hc2'
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ε * n := ⟨_, rfl⟩
  have hεn : B ≤ 1 / 32 * n := by rw [hBdef]; exact mul_le_mul_of_nonneg_right hε1 hnpos.le
  have hc8 : κ ≤ n / 8 := by
    have e : 2 * ε * n = 2 * B := by rw [hBdef]; ring
    rw [e] at hc2; linarith
  -- the conjecture bounds the doubly served levels
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = doublyServedCount (m + 2) m ξ N q θ₀ G := ⟨_, rfl⟩
  have hupper : D ≤ C * Real.logb 2 q + C' + η * ((m : ℝ) + 1) := by
    rw [hDdef]; exact hξ N q hN1 G hGl (by rw [← hκdef, ← hndef]; exact hc8)
  -- Theorem T's label doubly serves almost every level
  have hlower : ((m : ℝ) + 1 - D) * (θ₀ * n) ≤ 2 * ((m : ℝ) + 1) * κ := by
    rw [hDdef, hndef, hκdef]; exact unserved_mul_le ξ hN1 hq hθ₀ hGl
  have hk1 : ((m : ℝ) + 1 - D) * θ₀ * n ≤ (4 * ε * ((m : ℝ) + 1)) * n := by
    have h := mul_le_mul_of_nonneg_left hc2 (by positivity : (0 : ℝ) ≤ 2 * ((m : ℝ) + 1))
    have e1 : ((m : ℝ) + 1 - D) * θ₀ * n = ((m : ℝ) + 1 - D) * (θ₀ * n) := by ring
    have e2 : (4 * ε * ((m : ℝ) + 1)) * n = 2 * ((m : ℝ) + 1) * (2 * ε * n) := by ring
    rw [e1, e2]; exact hlower.trans h
  have hk2 : ((m : ℝ) + 1 - D) * θ₀ ≤ 4 * ε * ((m : ℝ) + 1) := le_of_mul_le_mul_right hk1 hnpos
  have hk3 : 4 * ε * ((m : ℝ) + 1) ≤ θ₀ * (δ / 4 * ((m : ℝ) + 1)) := by
    have h := mul_le_mul_of_nonneg_left hε2 (by positivity : (0 : ℝ) ≤ 4 * ((m : ℝ) + 1))
    have e1 : 4 * ε * ((m : ℝ) + 1) = 4 * ((m : ℝ) + 1) * ε := by ring
    have e2 : θ₀ * (δ / 4 * ((m : ℝ) + 1)) = 4 * ((m : ℝ) + 1) * (δ * θ₀ / 16) := by ring
    rw [e1, e2]; exact h
  have hk4 : θ₀ * ((m : ℝ) + 1 - D) ≤ θ₀ * (δ / 4 * ((m : ℝ) + 1)) := by
    have e : θ₀ * ((m : ℝ) + 1 - D) = ((m : ℝ) + 1 - D) * θ₀ := by ring
    rw [e]; exact hk2.trans hk3
  have hD0 : (m : ℝ) + 1 - D ≤ δ / 4 * ((m : ℝ) + 1) := le_of_mul_le_mul_left hk4 hθ₀
  -- the contradiction, with `W = δ (m + 1)` and `L = C log₂ q + C'`
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = δ * ((m : ℝ) + 1) := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = C * Real.logb 2 q + C' := ⟨_, rfl⟩
  have hW : 0 < W := by rw [hWdef]; exact mul_pos hδ hm1
  have hD : (m : ℝ) + 1 - W / 4 ≤ D := by
    have e : δ / 4 * ((m : ℝ) + 1) = W / 4 := by rw [hWdef]; ring
    rw [e] at hD0; linarith
  have hup : D ≤ L + ((m : ℝ) + 1) - W := by
    have e : C * Real.logb 2 q + C' + η * ((m : ℝ) + 1) = L + ((m : ℝ) + 1) - W := by
      rw [hLdef, hWdef, hδdef]; ring
    rw [e] at hupper; exact hupper
  have hmW : L < W / 2 := by
    have e : ((m : ℝ) + 1) * (δ / 2) = W / 2 := by rw [hWdef]; ring
    rw [← hLdef, e] at hmδ; exact hmδ
  linarith

/-- **Corollary N, second statement: Conjecture A′ of the fourth paper is false.** -/
theorem not_conjAprime : ¬ ConjAprime := fun h => not_conjAsecond (conjAsecond_of_conjAprime h)

end BoundedStackDepth
