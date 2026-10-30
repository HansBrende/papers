import Mathlib

/-!
# Counting entropies of labels in classes

For a finite set `U` of labels and a map `f` on it, `fcard U f x` is the size of the fibre of `f`
through `x` inside `U`, and `fs U f = ∑_{x ∈ U} log (fcard U f x)` (natural logarithms). For a
uniformly random label of `U`, `|U| log |U| - fs U f` is `|U|` times the Shannon entropy of `f`, and
`condEnt U A c = fs U c - fs U (c, A)` is `|U|` times the conditional entropy `H(A | c)`. All the
inequalities below come from `log y ≤ y - 1`.

* `nlogn_sub_fs_le`: `|U| log |U| - fs U f ≤ |U| log r` if `f` takes `r` values on `U`.
* `condEnt_le_comp`: conditioning on less cannot lower the conditional entropy,
  `H(A | c) ≤ H(A | g ∘ c)`.
* `condEnt_local`: if `c` is a function of `c'` outside one class `act` of `c'`, and takes at most two
  values on it, then `H(A | c') ≤ H(A | c) + Pr[c' = act] log 2` (unnormalised).
* `condEnt_le_of_card_image`, `condEnt_ge`: the bounds used at the start and at the end of a
  transport.
-/

namespace MergeDepth

open Finset Real

variable {ι γ δ α : Type*} [DecidableEq γ] [DecidableEq δ] [DecidableEq α]

/-- The size of the fibre of `f` through `x` inside `U`. -/
def fcard (U : Finset ι) (f : ι → γ) (x : ι) : ℕ := (U.filter fun y => f y = f x).card

/-- `fs U f = ∑_{x ∈ U} log |U ∩ f⁻¹(f x)|`. -/
noncomputable def fs (U : Finset ι) (f : ι → γ) : ℝ := ∑ x ∈ U, Real.log (fcard U f x)

/-- `|U|` times the conditional entropy of `A` given `c`, for a uniform label of `U`, in nats. -/
noncomputable def condEnt (U : Finset ι) (A : ι → α) (c : ι → γ) : ℝ :=
  fs U c - fs U (fun x => (c x, A x))

theorem fcard_pos {U : Finset ι} (f : ι → γ) {x : ι} (hx : x ∈ U) : 0 < fcard U f x :=
  card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩

theorem fcard_le_of_imp {U : Finset ι} {f : ι → γ} {g : ι → δ} {x : ι}
    (h : ∀ y ∈ U, f y = f x → g y = g x) : fcard U f x ≤ fcard U g x := by
  refine card_le_card fun y hy => ?_
  obtain ⟨hyU, hyx⟩ := mem_filter.mp hy
  exact mem_filter.mpr ⟨hyU, h y hyU hyx⟩

theorem fcard_congr {U : Finset ι} {f : ι → γ} {g : ι → δ} {x : ι}
    (h : ∀ y ∈ U, f y = f x ↔ g y = g x) : fcard U f x = fcard U g x :=
  le_antisymm (fcard_le_of_imp fun y hy => (h y hy).mp) (fcard_le_of_imp fun y hy => (h y hy).mpr)

/-- Inside a fibre of `c`, the fibres of `(c, A)` are those of `A`. -/
theorem fcard_pair_fibre {U : Finset ι} (c : ι → γ) (A : ι → α) {z : γ} {x : ι}
    (hx : x ∈ U.filter fun y => c y = z) :
    fcard U (fun x => (c x, A x)) x = fcard (U.filter fun y => c y = z) A x := by
  unfold fcard
  rw [filter_filter]
  congr 1
  ext y
  simp only [mem_filter, Prod.mk.injEq, (mem_filter.mp hx).2]

/-- Inside a fibre of `c`, the fibre of `c` is the whole fibre. -/
theorem fcard_fibre {U : Finset ι} (c : ι → γ) {z : γ} {x : ι}
    (hx : x ∈ U.filter fun y => c y = z) :
    fcard U c x = (U.filter fun y => c y = z).card := by
  unfold fcard
  rw [(mem_filter.mp hx).2]

/-- Coarser maps have larger fibres. -/
theorem fs_le_of_imp {U : Finset ι} {f : ι → γ} {g : ι → δ}
    (h : ∀ x ∈ U, ∀ y ∈ U, f y = f x → g y = g x) : fs U f ≤ fs U g := by
  refine sum_le_sum fun x hx => ?_
  apply Real.log_le_log (by exact_mod_cast fcard_pos f hx)
  exact_mod_cast fcard_le_of_imp (h x hx)

/-- Every fibre contributes one in total: `∑_{x ∈ U} G (f x) / |fibre of x| = ∑_{t ∈ f(U)} G t`. -/
theorem sum_div_fcard (U : Finset ι) (f : ι → γ) (G : γ → ℝ) :
    ∑ x ∈ U, G (f x) / fcard U f x = ∑ t ∈ U.image f, G t := by
  rw [← sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem f hx)]
  refine sum_congr rfl fun t ht => ?_
  have hpos : 0 < (U.filter fun y => f y = t).card := by
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
    exact card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩
  have : ∀ x ∈ U.filter (fun y => f y = t), G (f x) / fcard U f x =
      G t / (U.filter fun y => f y = t).card := by
    intro x hx
    obtain ⟨-, hxt⟩ := mem_filter.mp hx
    simp only [fcard, hxt]
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul]
  field_simp

/-- **Maximal entropy.** If `f` takes `r` values on `U`, then `|U| log |U| - fs U f ≤ |U| log r`. -/
theorem nlogn_sub_fs_le (U : Finset ι) (f : ι → γ) :
    (U.card : ℝ) * Real.log U.card - fs U f ≤ U.card * Real.log (U.image f).card := by
  rcases U.eq_empty_or_nonempty with rfl | hU
  · simp [fs]
  have hn : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hr : (0 : ℝ) < (U.image f).card := by exact_mod_cast (hU.image f).card_pos
  -- `∑ log (n / (r c_x)) ≤ ∑ (n / (r c_x) - 1) = 0`
  have hkey : ∀ x ∈ U, Real.log U.card - Real.log (fcard U f x) - Real.log (U.image f).card ≤
      U.card / ((U.image f).card * fcard U f x) - 1 := by
    intro x hx
    have hc : (0 : ℝ) < fcard U f x := by exact_mod_cast fcard_pos f hx
    have hy : 0 < (U.card : ℝ) / ((U.image f).card * fcard U f x) := by positivity
    have := Real.log_le_sub_one_of_pos hy
    rw [Real.log_div hn.ne' (by positivity), Real.log_mul hr.ne' hc.ne'] at this
    linarith
  have hsum : ∑ x ∈ U, ((U.card : ℝ) / ((U.image f).card * fcard U f x) - 1) = 0 := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
    have : ∑ x ∈ U, (U.card : ℝ) / ((U.image f).card * fcard U f x) =
        (U.card / (U.image f).card) * ∑ x ∈ U, (fun _ => (1 : ℝ)) (f x) / fcard U f x := by
      rw [mul_sum]
      refine sum_congr rfl fun x _ => ?_
      field_simp
    rw [this, sum_div_fcard U f (fun _ => (1 : ℝ)), sum_const, nsmul_eq_mul, mul_one]
    field_simp
    ring
  have := sum_le_sum hkey
  rw [hsum, sum_sub_distrib, sum_sub_distrib, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul] at this
  unfold fs
  linarith

/-- The fibres of `c` cover `U`: `∑_{y ∈ c(U)} |U ∩ c⁻¹ y| = |U|`. -/
theorem sum_card_fibres (U : Finset ι) (c : ι → γ) :
    ∑ y ∈ U.image c, ((U.filter fun x => c x = y).card : ℝ) = U.card := by
  exact_mod_cast (card_eq_sum_card_image c U).symm

/-- **The log-sum step.** `fs c + fs (g ∘ c, A) ≤ fs (g ∘ c) + fs (c, A)`. -/
theorem fs_cond_le (U : Finset ι) (c : ι → γ) (g : γ → δ) (A : ι → α) :
    fs U c + fs U (fun x => (g (c x), A x)) ≤ fs U (fun x => g (c x)) + fs U (fun x => (c x, A x)) := by
  classical
  -- counts as functions of the value
  set cc : γ → ℝ := fun y => ((U.filter fun x => c x = y).card : ℝ)
  set cg : δ → ℝ := fun z => ((U.filter fun x => g (c x) = z).card : ℝ)
  set cgA : δ × α → ℝ := fun p => ((U.filter fun x => (g (c x), A x) = p).card : ℝ)
  set G : γ × α → ℝ := fun p => cc p.1 * cgA (g p.1, p.2) / cg (g p.1)
  -- the ratio summed over `U` is at most `|U|`
  have hratio : ∑ x ∈ U, G (c x, A x) / fcard U (fun x => (c x, A x)) x ≤ U.card := by
    rw [sum_div_fcard U (fun x => (c x, A x)) G]
    have hsub : U.image (fun x => (c x, A x)) ⊆ (U.image c) ×ˢ (U.image A) := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hp
      exact mem_product.mpr ⟨mem_image_of_mem c hx, mem_image_of_mem A hx⟩
    have hG0 : ∀ p, 0 ≤ G p := fun p => by simp only [G, cc, cgA, cg]; positivity
    refine (sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hG0 p).trans ?_
    rw [sum_product]
    -- `∑_a cgA (z, a) = cg z`
    have hfib : ∀ z, ∑ a ∈ U.image A, cgA (z, a) = cg z := by
      intro z
      simp only [cgA, cg]
      rw [card_eq_sum_card_fiberwise (f := A) (t := U.image A)
        (fun x hx => mem_image_of_mem A (mem_filter.mp hx).1)]
      push_cast
      refine sum_congr rfl fun a _ => ?_
      rw [filter_filter]
      congr 2
      ext x
      simp only [mem_filter, Prod.mk.injEq]
    have : ∀ y ∈ U.image c, ∑ a ∈ U.image A, G (y, a) = cc y := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      have hpos : 0 < cg (g (c x)) := by
        have hmem : x ∈ U.filter (fun y => g (c y) = g (c x)) := mem_filter.mpr ⟨hx, rfl⟩
        have := card_pos.mpr ⟨x, hmem⟩
        simp only [cg]
        exact_mod_cast this
      simp only [G]
      rw [← sum_div, ← mul_sum, hfib]
      field_simp
    rw [sum_congr rfl this]
    exact (sum_card_fibres U c).le
  -- pointwise `log` bound
  have hpt : ∀ x ∈ U, Real.log (fcard U c x) + Real.log (fcard U (fun x => (g (c x), A x)) x) -
      Real.log (fcard U (fun x => g (c x)) x) - Real.log (fcard U (fun x => (c x, A x)) x) ≤
      G (c x, A x) / fcard U (fun x => (c x, A x)) x - 1 := by
    intro x hx
    have h1 : (0 : ℝ) < fcard U c x := by exact_mod_cast fcard_pos c hx
    have h2 : (0 : ℝ) < fcard U (fun x => (g (c x), A x)) x := by exact_mod_cast fcard_pos _ hx
    have h3 : (0 : ℝ) < fcard U (fun x => g (c x)) x := by exact_mod_cast fcard_pos _ hx
    have h4 : (0 : ℝ) < fcard U (fun x => (c x, A x)) x := by exact_mod_cast fcard_pos _ hx
    have hG : G (c x, A x) / fcard U (fun x => (c x, A x)) x =
        fcard U c x * fcard U (fun x => (g (c x), A x)) x /
          (fcard U (fun x => g (c x)) x * fcard U (fun x => (c x, A x)) x) := by
      simp only [G, cc, cgA, cg, fcard]
      ring
    rw [hG]
    have hy : 0 < (fcard U c x : ℝ) * fcard U (fun x => (g (c x), A x)) x /
        (fcard U (fun x => g (c x)) x * fcard U (fun x => (c x, A x)) x) := by positivity
    have := Real.log_le_sub_one_of_pos hy
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul h1.ne' h2.ne',
      Real.log_mul h3.ne' h4.ne'] at this
    linarith
  have := sum_le_sum hpt
  simp only [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one] at this
  unfold fs
  linarith

/-- **Conditioning on less cannot lower the conditional entropy.** -/
theorem condEnt_le_comp (U : Finset ι) (A : ι → α) (c : ι → γ) (g : γ → δ) :
    condEnt U A c ≤ condEnt U A (fun x => g (c x)) := by
  have := fs_cond_le U c g A
  unfold condEnt
  linarith

/-- **A local change of classes.** Suppose that outside the class `act` of `c'` the class of `c` is a
function of that of `c'`, and that on the class `act` the map `c` takes at most the two values `z₁`,
`z₂`. Then `H(A | c') ≤ H(A | c) + |c'⁻¹(act)| log 2` (unnormalised). -/
theorem condEnt_local (U : Finset ι) (A : ι → α) (c c' : ι → γ) (act z₁ z₂ : γ) (g : γ → γ)
    (hout : ∀ x ∈ U, c' x ≠ act → c x = g (c' x))
    (hin : ∀ x ∈ U, c' x = act → c x = z₁ ∨ c x = z₂) :
    condEnt U A c' ≤ condEnt U A c + (U.filter fun x => c' x = act).card * Real.log 2 := by
  set V := U.filter fun x => c' x = act
  -- (1) `H(A | c') ≤ H((c, A) | c')`
  have h1 : fs U (fun x => ((c' x, c x), A x)) ≤ fs U (fun x => (c' x, A x)) :=
    fs_le_of_imp fun x _ y _ h => by
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1.1, h.2⟩
  -- (2) `H(c | c') ≤ |V| log 2`
  have h2 : fs U c' - fs U (fun x => (c' x, c x)) ≤ V.card * Real.log 2 := by
    unfold fs
    rw [← sum_sub_distrib, ← sum_filter_add_sum_filter_not U fun x => c' x = act]
    have hout0 : ∑ x ∈ U.filter (fun x => ¬ c' x = act),
        (Real.log (fcard U c' x) - Real.log (fcard U (fun x => (c' x, c x)) x)) = 0 := by
      refine sum_eq_zero fun x hx => ?_
      obtain ⟨hxU, hxa⟩ := mem_filter.mp hx
      rw [fcard_congr (g := fun x => (c' x, c x)) (fun y hy => ?_), sub_self]
      constructor
      · intro hyx
        refine Prod.ext hyx ?_
        rw [hout y hy (by rw [hyx]; exact hxa), hout x hxU hxa, hyx]
      · intro h
        exact (Prod.mk.inj h).1
    have hin' : ∑ x ∈ V, (Real.log (fcard U c' x) - Real.log (fcard U (fun x => (c' x, c x)) x)) =
        V.card * Real.log V.card - fs V c := by
      unfold fs
      rw [sum_sub_distrib]
      congr 1
      · rw [← nsmul_eq_mul, ← sum_const]
        refine sum_congr rfl fun x hx => ?_
        rw [fcard_fibre c' hx]
      · refine sum_congr rfl fun x hx => ?_
        rw [fcard_pair_fibre c' c hx]
    rw [hout0, add_zero, hin']
    refine (nlogn_sub_fs_le V c).trans ?_
    rcases V.eq_empty_or_nonempty with hV | hV
    · simp [hV]
    have hsub : V.image c ⊆ {z₁, z₂} := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
      obtain ⟨hxU, hxa⟩ := mem_filter.mp hx
      rcases hin x hxU hxa with h | h <;> simp [h]
    have hc : ((V.image c).card : ℝ) ≤ 2 := by
      have := (card_le_card hsub).trans (card_insert_le _ _)
      simp only [card_singleton] at this
      exact_mod_cast this
    have hpos : (0 : ℝ) < (V.image c).card := by exact_mod_cast (hV.image c).card_pos
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hc) (by positivity)
  -- (3) `H(A | (c', c)) ≤ H(A | c)`
  have h3 := condEnt_le_comp U A (fun x => (c' x, c x)) Prod.snd
  have h4 : fs U (fun x => ((c' x, c x), A x)) = fs U (fun x => (c' x, c x)) -
      condEnt U A (fun x => (c' x, c x)) := by
    unfold condEnt; ring
  unfold condEnt at h3 ⊢
  simp only at h3
  linarith

/-- **Few rows per class.** If on every class of `c` the map `A` takes at most `R` values, then
`H(A | c) ≤ |U| log R` (unnormalised). -/
theorem condEnt_le_of_card_image (U : Finset ι) (A : ι → α) (c : ι → γ) {R : ℕ}
    (h : ∀ z, ((U.filter fun x => c x = z).image A).card ≤ R) :
    condEnt U A c ≤ U.card * Real.log R := by
  unfold condEnt fs
  rw [← sum_sub_distrib, ← sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem c hx)]
  have hfib : ∀ z ∈ U.image c,
      ∑ x ∈ U.filter (fun x => c x = z),
        (Real.log (fcard U c x) - Real.log (fcard U (fun x => (c x, A x)) x)) =
      (U.filter fun x => c x = z).card * Real.log (U.filter fun x => c x = z).card -
        fs (U.filter fun x => c x = z) A := by
    intro z _
    unfold fs
    rw [sum_sub_distrib]
    congr 1
    · rw [← nsmul_eq_mul, ← sum_const]
      refine sum_congr rfl fun x hx => ?_
      rw [fcard_fibre c hx]
    · refine sum_congr rfl fun x hx => ?_
      rw [fcard_pair_fibre c A hx]
  rw [sum_congr rfl hfib]
  calc ∑ z ∈ U.image c, ((U.filter fun x => c x = z).card * Real.log (U.filter fun x => c x = z).card -
        fs (U.filter fun x => c x = z) A)
      ≤ ∑ z ∈ U.image c, ((U.filter fun x => c x = z).card : ℝ) * Real.log R := by
        refine sum_le_sum fun z hz => (nlogn_sub_fs_le _ A).trans ?_
        rcases (U.filter fun x => c x = z).eq_empty_or_nonempty with he | hne
        · simp [he]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Real.log_le_log (by exact_mod_cast (hne.image A).card_pos) (by exact_mod_cast h z)
    _ = U.card * Real.log R := by rw [← sum_mul, sum_card_fibres]

/-- **The end bound.** If `f` takes at most `r` values on `U` and every fibre of `(f, A)` has at most
`b` elements, then `H(A | f) ≥ |U| log |U| - |U| log r - |U| log b` (unnormalised). -/
theorem condEnt_ge (U : Finset ι) (A : ι → α) (f : ι → γ) {r b : ℕ} (hr : (U.image f).card ≤ r)
    (hfib : ∀ x ∈ U, fcard U (fun x => (f x, A x)) x ≤ b) :
    (U.card : ℝ) * Real.log U.card - U.card * Real.log r - U.card * Real.log b ≤ condEnt U A f := by
  rcases U.eq_empty_or_nonempty with rfl | hU
  · simp [condEnt, fs]
  have h1 := nlogn_sub_fs_le U f
  have hr' : Real.log (U.image f).card ≤ Real.log r :=
    Real.log_le_log (by exact_mod_cast (hU.image f).card_pos) (by exact_mod_cast hr)
  have h2 : fs U (fun x => (f x, A x)) ≤ U.card * Real.log b := by
    unfold fs
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun x hx => Real.log_le_log (by exact_mod_cast fcard_pos _ hx) ?_
    exact_mod_cast hfib x hx
  unfold condEnt
  have : (U.card : ℝ) * Real.log (U.image f).card ≤ U.card * Real.log r :=
    mul_le_mul_of_nonneg_left hr' (by positivity)
  linarith

end MergeDepth
