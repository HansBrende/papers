import NativeRelations.MacroBankCrux

/-!
# Suffix Macro-Phase Bank Schedules (Theorem B)

Proves Theorem B in its suffix form, for oblivious runs that satisfy the bounded macro-phase
condition on a final interval containing all appends while leaving a positive fraction of input rows
unread before it (`suffixMacroBank_has_crux`, `suffixMacroBank_excludes`), and deduces the
whole-run form (`boundedMacroBank_has_crux`, `boundedMacroBank_excludes`) as the `δ₀ = 1`
specialization (`boundedSuffixMacroBank_of_boundedMacroBank`).
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape BoundedNesting MergeDepth BoundedStackDepth
  TapeStorageRates
open scoped BigOperators Topology

/-! ## §1. Suffix Macro-Bank Class (`BoundedSuffixMacroBank`, Theorem B, suffix form) -/

/-- Raw-row index `u = p / b / d : Fin d` of a flat matrix bit coordinate `p : Fin (d * d * b)`. -/
def rawRowOf {d b : ℕ} (p : Fin (d * d * b)) : Fin d :=
  ⟨p.1 / b / d, (Transpose.Tape.Impl.pos_decomp p.2).1⟩

/-- **Suffix Macro-Bank with Raw-Row Input Mass (`BoundedSuffixMacroBank`)**, matching the suffix
form of Theorem B: for all `d ≥ d_suf` and every halting horizon `T ≤ C (L + 1)` at which `M` is
oblivious on `inputsOfLength L` (`L = d² entryBits(d)`), there exist a suffix start time
`t_suf ≤ T` and a raw-row set `R_suf ⊆ Fin d` such that:
1. every output append before `T` occurs during `[t_suf, T)`, `[t_suf, T)` partitions into `M_ph`
   contiguous macro-phases on each of which `τ₀.input` and every `j ∈ B_bank` are weakly monotone,
   and every `w ∉ B_bank` visits at most `S d` cells during `[t_suf, T)`;
2. `|R_suf| ≥ δ₀ d` and no coordinate `p` with `rawRowOf p ∈ R_suf` is visited by `τ₀.input` during
   `[0, t_suf)`. -/
def BoundedSuffixMacroBank (M : TM) (C : ℝ) (M_ph : ℕ) (δ₀ : ℝ)
    (B_bank : Finset (Fin M.k)) (S : ℕ → ℕ) : Prop :=
  ∃ d_suf : ℕ, ∀ d ≥ d_suf, ∀ T : ℕ,
    let b := entryBits d
    let L := d * d * b
    let τ₀ := traceAt M L
    ObliviousOn M (inputsOfLength L) T →
    (T : ℝ) ≤ C * ((L : ℝ) + 1) →
    ∃ (t_suf : ℕ) (R_suf : Finset (Fin d)),
      t_suf ≤ T ∧
      (∀ ℓ < (appendList τ₀ T).length, t_suf ≤ appendTime τ₀ T ℓ) ∧
      (∃ a : ℕ → ℕ, a 0 = t_suf ∧ a M_ph = T ∧ (∀ α < M_ph, a α ≤ a (α + 1)) ∧
        (∀ α < M_ph, WeakMonoOnInterval τ₀.input (a α) (a (α + 1))) ∧
        (∀ α < M_ph, ∀ j ∈ B_bank, WeakMonoOnInterval (τ₀.work j) (a α) (a (α + 1)))) ∧
      (∀ w : Fin M.k, w ∉ B_bank →
        ((Finset.Ico t_suf T).image (τ₀.work w)).card ≤ S d) ∧
      δ₀ * (d : ℝ) ≤ (R_suf.card : ℝ) ∧
      (∀ t < t_suf, ∀ p : Fin L, τ₀.input t = (p.1 : ℤ) → rawRowOf p ∉ R_suf)

/-- `BoundedMacroBank` is the `δ₀ = 1` specialization of `BoundedSuffixMacroBank`: take
`t_suf = 0` and `R_suf = univ`. -/
theorem boundedSuffixMacroBank_of_boundedMacroBank {M : TM} {C : ℝ} {M_ph : ℕ}
    {B_bank : Finset (Fin M.k)} {S : ℕ → ℕ} (hBM : BoundedMacroBank M C M_ph B_bank S) :
    BoundedSuffixMacroBank M C M_ph 1 B_bank S := by
  obtain ⟨d_BM, hd_BM⟩ := hBM
  refine ⟨d_BM, fun d hd T hobl hT => ?_⟩
  obtain ⟨hph, hwork⟩ := hd_BM d hd T hobl hT
  refine ⟨0, Finset.univ, Nat.zero_le T, fun _ _ => Nat.zero_le _, hph, fun w hw => ?_, by simp,
    fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  simpa [Nat.Ico_zero_eq_range] using hwork w hw

/-! ## §2. Backward time-monotonicity and suffix phase helpers -/

/-- Step 1 of the suffix form of Theorem B: every `DepDag` edge strictly decreases time
(`depStep_lt`), so the final vertex `(t₀ :: ρ).getLastD t₀` of any dependency path is `≤ x` for
every vertex `x ∈ t₀ :: ρ`. -/
theorem getLastD_le_of_mem_depPath {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ} :
    ∀ (ρ : List ℕ) (t₀ : ℕ), IsDepPath xs T (t₀ :: ρ) →
      ∀ {x : ℕ}, x ∈ t₀ :: ρ → (t₀ :: ρ).getLastD t₀ ≤ x
  | [], t₀, _, x, hx => by
    simp only [List.mem_singleton] at hx
    subst hx
    exact le_rfl
  | t₁ :: ρ₁, t₀, ⟨hstep, htail⟩, x, hx => by
    have hlt : t₁ < t₀ := (depStep_lt hstep).1
    rw [LinNet.getLastD_cons_cons t₀ t₁ ρ₁]
    rcases List.mem_cons.mp hx with rfl | hx_tail
    · exact (getLastD_le_of_mem_depPath ρ₁ t₁ htail List.mem_cons_self).trans hlt.le
    · exact getLastD_le_of_mem_depPath ρ₁ t₁ htail hx_tail

/-- Every step `t ∈ [a 0, a m)` lies in some phase `[a α, a (α + 1))` with `α < m`. -/
theorem exists_phase_of_le_lt {m : ℕ} {a : ℕ → ℕ} {t : ℕ} (hlo : a 0 ≤ t) (ht : t < a m) :
    ∃ α < m, a α ≤ t ∧ t < a (α + 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm : a m ≤ t
    · exact ⟨m, by omega, hm, ht⟩
    · obtain ⟨α, hα, h1, h2⟩ := ih (by omega)
      exact ⟨α, by omega, h1, h2⟩

/-- Suffix specification of `MacroBankCrux.phaseOf` for steps `t ∈ [a 0, T)`. -/
theorem phaseOf_spec_of_ge {M_ph T : ℕ} {a : ℕ → ℕ} (haM : a M_ph = T)
    {t : ℕ} (hlo : a 0 ≤ t) (ht : t < T) :
    phaseOf M_ph a t < M_ph ∧ a (phaseOf M_ph a t) ≤ t ∧ t < a (phaseOf M_ph a t + 1) := by
  have hex : ∃ α < M_ph, a α ≤ t ∧ t < a (α + 1) :=
    exists_phase_of_le_lt hlo (by omega)
  unfold phaseOf
  rw [dite_eq_left hex]
  exact Nat.find_spec hex

/-- Suffix characterization of `phaseOf M_ph a t = α` for `t ∈ [a 0, T)`. -/
theorem phaseOf_eq_iff_of_ge {M_ph T : ℕ} {a : ℕ → ℕ} (haM : a M_ph = T)
    (ha : ∀ α < M_ph, a α ≤ a (α + 1)) {t α : ℕ} (hlo : a 0 ≤ t) (ht : t < T) (hα : α < M_ph) :
    phaseOf M_ph a t = α ↔ a α ≤ t ∧ t < a (α + 1) := by
  obtain ⟨h1, h2, h3⟩ := phaseOf_spec_of_ge haM hlo ht
  constructor
  · rintro rfl; exact ⟨h2, h3⟩
  · rintro ⟨hlo', hhi'⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := phase_le_of_step ha (α := phaseOf M_ph a t + 1) (β := α) (by omega) (by omega)
      omega
    · have := phase_le_of_step ha (α := α + 1) (β := phaseOf M_ph a t) (by omega) (by omega)
      omega

/-- Upper endpoints `u ∈ [t_suf, T)` of workspace hops (`w ∉ B_bank`) exceeding duration `τ_cut`. -/
noncomputable def longWorkHopsSuffix {k : ℕ} (xs : Fin k → ℕ → ℤ) (B_bank : Finset (Fin k))
    (t_suf T τ_cut : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico t_suf T).filter fun u =>
    ∃ w : Fin k, w ∉ B_bank ∧ ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v

/-- Suffix workspace hop bound: reuses `card_longHopsAtCell_le` over the `≤ S_val` cells visited by
each workspace head `w ∉ B_bank` during `[t_suf, T)`. -/
theorem card_longWorkHopsSuffix_le {k : ℕ} (xs : Fin k → ℕ → ℤ) (B_bank : Finset (Fin k))
    (t_suf T τ_cut S_val : ℕ) (hτ : 1 ≤ τ_cut)
    (hS : ∀ w : Fin k, w ∉ B_bank → ((Finset.Ico t_suf T).image (xs w)).card ≤ S_val) :
    (longWorkHopsSuffix xs B_bank t_suf T τ_cut).card ≤ k * (S_val * (T / τ_cut)) := by
  classical
  let Wset := (Finset.univ : Finset (Fin k)).filter fun w => w ∉ B_bank
  have hW : ∀ w ∈ Wset,
      ((Finset.Ico t_suf T).filter fun u => ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v).card ≤
        S_val * (T / τ_cut) := by
    intro w hw
    have hwB : w ∉ B_bank := (Finset.mem_filter.mp hw).2
    let cells := (Finset.Ico t_suf T).image (xs w)
    have hsub : ((Finset.Ico t_suf T).filter fun u => ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v) ⊆
        cells.biUnion fun z =>
          (Finset.range T).filter fun u => xs w u = z ∧ ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v := by
      intro u hu
      obtain ⟨huIco, hex⟩ := Finset.mem_filter.mp hu
      have huT : u ∈ Finset.range T := Finset.mem_range.mpr (Finset.mem_Ico.mp huIco).2
      exact Finset.mem_biUnion.mpr ⟨xs w u, Finset.mem_image_of_mem _ huIco,
        Finset.mem_filter.mpr ⟨huT, rfl, hex⟩⟩
    calc
      _ ≤ (cells.biUnion _).card := Finset.card_le_card hsub
      _ ≤ ∑ z ∈ cells, ((Finset.range T).filter fun u =>
            xs w u = z ∧ ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ cells, (T / τ_cut) :=
          Finset.sum_le_sum fun z _ => card_longHopsAtCell_le (xs w) T τ_cut hτ z
      _ = cells.card * (T / τ_cut) := by simp
      _ ≤ S_val * (T / τ_cut) := Nat.mul_le_mul_right _ (hS w hwB)
  have htotal : longWorkHopsSuffix xs B_bank t_suf T τ_cut ⊆
      Wset.biUnion fun w =>
        (Finset.Ico t_suf T).filter fun u => ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v := by
    intro u hu
    obtain ⟨huIco, w, hw, hex⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩,
      Finset.mem_filter.mpr ⟨huIco, hex⟩⟩
  calc
    (longWorkHopsSuffix xs B_bank t_suf T τ_cut).card
      ≤ (Wset.biUnion _).card := Finset.card_le_card htotal
    _ ≤ ∑ w ∈ Wset, ((Finset.Ico t_suf T).filter fun u =>
          ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ Wset, (S_val * (T / τ_cut)) := Finset.sum_le_sum hW
    _ = Wset.card * (S_val * (T / τ_cut)) := by simp
    _ ≤ k * (S_val * (T / τ_cut)) := by
        refine Nat.mul_le_mul_right _ ?_
        calc Wset.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
          _ = k := by simp

/-! ## §3. Suffix phase-splitting and signature existence -/

/-- Step 2 (phase splitting): any dependency path in `[a 0, T)` avoiding
`longWorkHopsSuffix ∪ phaseStartGuard` either remains inside `phaseOf M_ph a t₀` with drop at most
`ρ.length * τ_cut` or first exits below `a α` via an inter-phase bank hop `j ∈ B_bank`. -/
theorem depPath_phase_split_suffix {k : ℕ} {τ₀ : Trace k} {T M_ph τ_cut : ℕ} (hτ : 1 ≤ τ_cut)
    {B_bank : Finset (Fin k)} {a : ℕ → ℕ}
    (haM : a M_ph = T) (ha : ∀ α < M_ph, a α ≤ a (α + 1))
    (hbank : ∀ α < M_ph, ∀ j ∈ B_bank, WeakMonoOnInterval (τ₀.work j) (a α) (a (α + 1))) :
    ∀ (ρ : List ℕ) (t₀ : ℕ), a 0 ≤ (t₀ :: ρ).getLastD t₀ → t₀ < T →
      IsDepPath τ₀.work T (t₀ :: ρ) →
      (∀ x ∈ t₀ :: ρ, x ∉ longWorkHopsSuffix τ₀.work B_bank (a 0) T τ_cut ∧
        x ∉ phaseStartGuard M_ph a τ_cut) →
      let α := phaseOf M_ph a t₀
      let t_last := (t₀ :: ρ).getLastD t₀
      (a α ≤ t_last ∧ t_last ≤ t₀ ∧ t₀ ≤ t_last + ρ.length * τ_cut) ∨
      (∃ (u₁ v₁ : ℕ) (ρ' : List ℕ) (j : B_bank),
        a α ≤ u₁ ∧ u₁ ≤ t₀ ∧ t₀ ≤ u₁ + ρ.length * τ_cut ∧
        v₁ < a α ∧ IsHop (τ₀.work j.1) T v₁ u₁ ∧
        IsDepPath τ₀.work T (v₁ :: ρ') ∧
        (v₁ :: ρ').getLastD v₁ = t_last ∧
        ρ'.length ≤ ρ.length ∧
        ∀ x ∈ v₁ :: ρ', x ∈ t₀ :: ρ)
  | [], t₀, hge, ht₀, _, _ => by
    have ht₀_ge : a 0 ≤ t₀ := by simpa using hge
    obtain ⟨_, hlo, _⟩ := phaseOf_spec_of_ge haM ht₀_ge ht₀
    exact Or.inl ⟨hlo, le_rfl, by simp⟩
  | t₁ :: ρ₁, t₀, hge, ht₀, hdep, havoid => by
    classical
    have ht₀_ge : a 0 ≤ t₀ := hge.trans (getLastD_le_of_mem_depPath (t₁ :: ρ₁) t₀ hdep List.mem_cons_self)
    have hlast_eq : (t₀ :: t₁ :: ρ₁).getLastD t₀ = (t₁ :: ρ₁).getLastD t₁ :=
      LinNet.getLastD_cons_cons t₀ t₁ ρ₁
    have hge₁ : a 0 ≤ (t₁ :: ρ₁).getLastD t₁ := by rwa [← hlast_eq]
    obtain ⟨hstep, htail⟩ := hdep
    have ht₁_ge : a 0 ≤ t₁ := hge₁.trans (getLastD_le_of_mem_depPath ρ₁ t₁ htail List.mem_cons_self)
    obtain ⟨hlt10, _⟩ := depStep_lt hstep
    have ht₁ : t₁ < T := hlt10.trans ht₀
    obtain ⟨hαM, hlo0, hhi0⟩ := phaseOf_spec_of_ge haM ht₀_ge ht₀
    obtain ⟨hno_long, hno_guard⟩ := havoid t₀ List.mem_cons_self
    by_cases ht1_ge : a (phaseOf M_ph a t₀) ≤ t₁
    · have hdrop : t₀ ≤ t₁ + τ_cut := by
        rcases hstep with ⟨hb, -⟩ | hhop_mem
        · omega
        · obtain ⟨⟨w, v, u⟩, hη, heq⟩ := Finset.mem_image.mp hhop_mem
          simp only [Prod.mk.injEq] at heq
          have hhop : IsHop (τ₀.work w) T t₁ t₀ := heq.2 ▸ heq.1 ▸ mem_allHops.mp hη
          by_cases hw : w ∈ B_bank
          · exfalso
            exact not_isHop_of_weakMonoOnInterval (hbank _ hαM w hw) ht1_ge hhi0 hhop
          · by_contra hgt
            apply hno_long
            unfold longWorkHopsSuffix
            exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ht₀_ge, ht₀⟩, w, hw, t₁, hhop, by omega⟩
      have hph_eq : phaseOf M_ph a t₁ = phaseOf M_ph a t₀ :=
        (phaseOf_eq_iff_of_ge haM ha ht₁_ge ht₁ hαM).mpr ⟨ht1_ge, hlt10.trans hhi0⟩
      have havoid1 : ∀ x ∈ t₁ :: ρ₁, x ∉ longWorkHopsSuffix τ₀.work B_bank (a 0) T τ_cut ∧
          x ∉ phaseStartGuard M_ph a τ_cut :=
        fun x hx => havoid x (List.mem_cons_of_mem t₀ hx)
      rcases depPath_phase_split_suffix hτ haM ha hbank ρ₁ t₁ hge₁ ht₁ htail havoid1 with
        ⟨h1, h2, h3⟩ | ⟨u₁, v₁, ρ', j, hu_lo, hu_hi, hu_drop, hv_lt, hhop, hdep', hlast', hlen', hsub'⟩
      · left
        rw [hph_eq] at h1
        refine ⟨by rw [hlast_eq]; exact h1, ?_, ?_⟩
        · rw [hlast_eq]; omega
        · rw [hlast_eq]
          calc t₀ ≤ t₁ + τ_cut := hdrop
            _ ≤ (t₁ :: ρ₁).getLastD t₁ + ρ₁.length * τ_cut + τ_cut := Nat.add_le_add_right h3 _
            _ = (t₁ :: ρ₁).getLastD t₁ + (t₁ :: ρ₁).length * τ_cut := by rw [List.length_cons]; ring
      · right
        rw [hph_eq] at hu_lo hv_lt
        refine ⟨u₁, v₁, ρ', j, hu_lo, hu_hi.trans hlt10.le, ?_, hv_lt, hhop, hdep',
          hlast'.trans hlast_eq.symm, hlen'.trans (Nat.le_succ _),
          fun x hx => List.mem_cons_of_mem t₀ (hsub' x hx)⟩
        calc t₀ ≤ t₁ + τ_cut := hdrop
          _ ≤ u₁ + ρ₁.length * τ_cut + τ_cut := Nat.add_le_add_right hu_drop _
          _ = u₁ + (t₁ :: ρ₁).length * τ_cut := by rw [List.length_cons]; ring
    · have ht0_guard : a (phaseOf M_ph a t₀) + τ_cut ≤ t₀ := by
        by_contra hlt_g
        apply hno_guard
        unfold phaseStartGuard
        exact Finset.mem_biUnion.mpr ⟨phaseOf M_ph a t₀, Finset.mem_range.mpr hαM,
          Finset.mem_Ico.mpr ⟨hlo0, by omega⟩⟩
      have hgap : τ_cut < t₀ - t₁ := by omega
      rcases hstep with ⟨hb, -⟩ | hhop_mem
      · omega
      · obtain ⟨⟨w, v, u⟩, hη, heq⟩ := Finset.mem_image.mp hhop_mem
        simp only [Prod.mk.injEq] at heq
        have hhop : IsHop (τ₀.work w) T t₁ t₀ := heq.2 ▸ heq.1 ▸ mem_allHops.mp hη
        by_cases hw : w ∈ B_bank
        · right
          refine ⟨t₀, t₁, ρ₁, ⟨w, hw⟩, hlo0, le_rfl, by omega, by omega, hhop, htail,
            hlast_eq.symm, Nat.le_succ _, fun x hx => List.mem_cons_of_mem t₀ hx⟩
        · exfalso
          apply hno_long
          unfold longWorkHopsSuffix
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ht₀_ge, ht₀⟩, w, hw, t₁, hhop, hgap⟩

/-- Step 3 (signatures): every short dependency path avoiding `longWorkHopsSuffix ∪ phaseStartGuard`
and ending at a read has a single signature pulling back every raw threshold whose windows it
avoids; uses `cutOf`, `windowsOf`, `cutOf_none` and `cutOf_consSig` from `MacroBankCrux` on the
suffix phase partition `a 0 ≤ … ≤ a M_ph = T`. -/
theorem depPath_signature_exists_suffix {k : ℕ} {τ₀ : Trace k} {L T M_ph τ_cut Δ : ℕ}
    (hτ : 1 ≤ τ_cut) {B_bank : Finset (Fin k)} {a : ℕ → ℕ}
    (haM : a M_ph = T) (ha : ∀ α < M_ph, a α ≤ a (α + 1))
    (hin : ∀ α < M_ph, WeakMonoOnInterval τ₀.input (a α) (a (α + 1)))
    (hbank : ∀ α < M_ph, ∀ j ∈ B_bank, WeakMonoOnInterval (τ₀.work j) (a α) (a (α + 1))) :
    ∀ (α : ℕ), α < M_ph →
      ∀ {t₀ : ℕ} (_ht₀ : t₀ < T) (_hα : phaseOf M_ph a t₀ = α)
        {ρ : List ℕ} (_hge : a 0 ≤ (t₀ :: ρ).getLastD t₀)
        (_hdep : IsDepPath τ₀.work T (t₀ :: ρ)) (_hΔ : ρ.length * τ_cut ≤ Δ)
        (_havoid : ∀ x ∈ t₀ :: ρ, x ∉ longWorkHopsSuffix τ₀.work B_bank (a 0) T τ_cut ∧
          x ∉ phaseStartGuard M_ph a τ_cut)
        {p : Fin L} (_hrd : readPos τ₀ L ((t₀ :: ρ).getLastD t₀) = some p),
        ∃ s : SigAt B_bank α, ∀ pStar : ℕ,
          (∀ x ∈ t₀ :: ρ, x ∉ windowsOf τ₀ L T Δ B_bank a α (liftSig s) pStar) →
          (tcut (cutOf τ₀ L T B_bank a α (liftSig s) pStar).1
            (cutOf τ₀ L T B_bank a α (liftSig s) pStar).2 t₀ ↔ p.1 < pStar) := by
  intro α
  induction α using Nat.strong_induction_on with
  | h α ih =>
    intro hαM t₀ ht₀ hα ρ hge hdep hΔ havoid p hrd
    have ht₀_ge : a 0 ≤ t₀ := hge.trans (getLastD_le_of_mem_depPath ρ t₀ hdep List.mem_cons_self)
    obtain ⟨_, hlo0, hhi0⟩ := phaseOf_spec_of_ge haM ht₀_ge ht₀
    subst hα
    let α := phaseOf M_ph a t₀
    rcases depPath_phase_split_suffix hτ haM ha hbank ρ t₀ hge ht₀ hdep havoid with
      ⟨htm_lo, htm_le, htm_drop⟩ |
      ⟨u₁, v₁, ρ', j, hu_lo, hu_hi, hu_drop, hv_lt, hhop, hdep', hlast', hlen', hsub'⟩
    · let s₀ : SigAt B_bank α := fun _ => none
      refine ⟨s₀, fun pStar hnowin => ?_⟩
      let t_m := (t₀ :: ρ).getLastD t₀
      have htm_hi : t_m < a (α + 1) := htm_le.trans_lt hhi0
      have hR : ReadPhaseRel τ₀ L (a α) (a (α + 1)) t_m p.1 :=
        ⟨htm_lo, htm_hi, p, hrd, rfl⟩
      have hdom : ∀ u v, ReadPhaseRel τ₀ L (a α) (a (α + 1)) u v → u < T := by
        intro u _ hRu
        have hleT : a (α + 1) ≤ T := haM ▸ phase_le_of_step ha (by omega) le_rfl
        exact hRu.2.1.trans_le hleT
      have hmono := relSign_spec (readPhaseRel_signed_mono (L := L) (hin α hαM))
      have hpull := pullCut_spec hdom hmono (false, pStar) hR
      rw [← cutOf_none τ₀ L T B_bank a α pStar] at hpull
      have ht0_not_win : t₀ ∉ Finset.Icc
          (cutOf τ₀ L T B_bank a α (liftSig s₀) pStar).2
          ((cutOf τ₀ L T B_bank a α (liftSig s₀) pStar).2 + Δ) :=
        fun hmem => hnowin t₀ List.mem_cons_self
          (mem_windowsOf_self τ₀ L T Δ B_bank a α (liftSig s₀) pStar hmem)
      have hwin := tcut_eq_of_notMem_window
        (pos := (cutOf τ₀ L T B_bank a α (liftSig s₀) pStar).1)
        htm_le (htm_drop.trans (Nat.add_le_add_left hΔ t_m)) ht0_not_win
      exact hwin.trans (hpull.trans (by simp [tcut]))
    · have hvT : v₁ < T := hv_lt.trans_le (haM ▸ phase_le_of_step ha (by omega) (by omega))
      have hge' : a 0 ≤ (v₁ :: ρ').getLastD v₁ := by rwa [hlast']
      have hv_ge : a 0 ≤ v₁ := hge'.trans (getLastD_le_of_mem_depPath ρ' v₁ hdep' List.mem_cons_self)
      let α' := phaseOf M_ph a v₁
      obtain ⟨hα'M, hlo', hhi'⟩ := phaseOf_spec_of_ge haM hv_ge hvT
      have hlt_ph : α' < α := by
        by_contra hge_ph
        have hstep_le := phase_le_of_step ha (α := α) (β := α') (by omega) (by omega)
        dsimp only [α', α] at hstep_le hv_lt hlo'
        omega
      have hΔ' : ρ'.length * τ_cut ≤ Δ := (Nat.mul_le_mul_right τ_cut hlen').trans hΔ
      have havoid' : ∀ x ∈ v₁ :: ρ', x ∉ longWorkHopsSuffix τ₀.work B_bank (a 0) T τ_cut ∧
          x ∉ phaseStartGuard M_ph a τ_cut := fun x hx => havoid x (hsub' x hx)
      have hrd' : readPos τ₀ L ((v₁ :: ρ').getLastD v₁) = some p := by rw [hlast']; exact hrd
      obtain ⟨s', hs'⟩ := ih α' hlt_ph hα'M hvT rfl hge' hdep' hΔ' havoid' hrd'
      refine ⟨consSig hlt_ph j s', fun pStar hnowin => ?_⟩
      obtain ⟨hcut_cons, hwin_sub⟩ := cutOf_consSig τ₀ L T Δ B_bank a hlt_ph j s' pStar
      have hnowin' : ∀ x ∈ v₁ :: ρ', x ∉ windowsOf τ₀ L T Δ B_bank a α' (liftSig s') pStar :=
        fun x hx hmem => hnowin x (hsub' x hx) (hwin_sub hmem)
      have ih_eq := hs' pStar hnowin'
      have hsep : a (α' + 1) ≤ a α := phase_le_of_step ha (by omega) (by omega)
      have hR : BankInterRel (τ₀.work j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1)) u₁ v₁ :=
        ⟨hu_lo, hu_hi.trans_lt hhi0, hlo', hhi', hhop⟩
      have hdom : ∀ u v,
          BankInterRel (τ₀.work j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1)) u v → u < T := by
        intro u _ hRu
        have hleT : a (α + 1) ≤ T := haM ▸ phase_le_of_step ha (by omega) le_rfl
        exact hRu.2.1.trans_le hleT
      have hmono := relSign_spec
        (bankInterRel_signed_mono (T := T) hsep (hbank α' hα'M j.1 j.2) (hbank α hαM j.1 j.2))
      have hpull := pullCut_spec hdom hmono (cutOf τ₀ L T B_bank a α' (liftSig s') pStar) hR
      rw [← hcut_cons] at hpull
      have ht0_not_win : t₀ ∉ Finset.Icc
          (cutOf τ₀ L T B_bank a α (liftSig (consSig hlt_ph j s')) pStar).2
          ((cutOf τ₀ L T B_bank a α (liftSig (consSig hlt_ph j s')) pStar).2 + Δ) :=
        fun hmem => hnowin t₀ List.mem_cons_self
          (mem_windowsOf_self τ₀ L T Δ B_bank a α _ pStar hmem)
      have hwin := tcut_eq_of_notMem_window
        (pos := (cutOf τ₀ L T B_bank a α (liftSig (consSig hlt_ph j s')) pStar).1)
        hu_hi (hu_drop.trans (Nat.add_le_add_left hΔ u₁)) ht0_not_win
      exact hwin.trans (hpull.trans ih_eq)

/-! ## §4. Order-quantile raw-row bucketing on `R_suf` and main theorems -/

/-- Finite quantitative core of Theorem B (suffix form): slices `R_suf` into `B = 2 K₀`
order-separated sub-buckets via `Finset.orderIsoOfFin` and extracts an independent rectangle `S_ind`
in the full demand-labelled cone relation `q ↦ coneSystem τ₀ T Γ d b (tposOf d b q)`. At
`t_suf = 0` and `R_suf = univ` this is the whole-run core of Theorem B. -/
theorem suffixMacroBank_independent_exists {M : TM} {M_ph D d b T t_suf S_val : ℕ}
    (hMph : 1 ≤ M_ph) (hd : 1 ≤ d) (hb : 1 ≤ b)
    {B_bank : Finset (Fin M.k)} {Γ : Finset ℕ} {R_suf : Finset (Fin d)}
    (_ht_suf : t_suf ≤ T)
    (happ : ∀ ℓ < (appendList (traceAt M (d * d * b)) T).length,
      t_suf ≤ appendTime (traceAt M (d * d * b)) T ℓ)
    (hlen : (appendList (traceAt M (d * d * b)) T).length = d * d * b)
    (hpath : ∀ π, IsDepPath (traceAt M (d * d * b)).work T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    {a : ℕ → ℕ} (ha0 : a 0 = t_suf) (haM : a M_ph = T) (ha : ∀ α < M_ph, a α ≤ a (α + 1))
    (hin : ∀ α < M_ph, WeakMonoOnInterval (traceAt M (d * d * b)).input (a α) (a (α + 1)))
    (hbank : ∀ α < M_ph, ∀ j ∈ B_bank,
      WeakMonoOnInterval ((traceAt M (d * d * b)).work j) (a α) (a (α + 1)))
    (hwork : ∀ w : Fin M.k, w ∉ B_bank →
      ((Finset.Ico t_suf T).image ((traceAt M (d * d * b)).work w)).card ≤ S_val)
    (hno_pre : ∀ t < t_suf, ∀ p : Fin (d * d * b),
      (traceAt M (d * d * b)).input t = (p.1 : ℤ) → rawRowOf p ∉ R_suf) :
    let K₀ := (B_bank.card + 1) ^ (M_ph - 1)
    let B := 2 * K₀
    let τ_cut := Nat.sqrt (max 1 S_val * (T + 1)) + 1
    let C_split := (M_ph + 1) + M_ph * (K₀ * B)
    let C_cone := (M.k + 2) ^ D * (M.k + M_ph + M_ph * (K₀ * (B * (M_ph * (D + 1)))))
    ∃ S_ind : Finset (Fin (d * d * b)),
      DirectedRecovery.IsIndependent
        (fun q => coneSystem (traceAt M (d * d * b)) T Γ d b (tposOf d b q)) S_ind ∧
      (R_suf.card / B) * ((d - C_split) / 2) * b ≤ S_ind.card + C_cone * τ_cut := by
  classical
  set L := d * d * b
  set W := d * b
  have hW : 1 ≤ W := Nat.mul_pos hd hb
  set τ₀ := traceAt M L
  have hlenL : (appendList τ₀ T).length = L := hlen
  set K₀ := (B_bank.card + 1) ^ (M_ph - 1)
  have hK₀ : 1 ≤ K₀ := Nat.one_le_pow _ _ (by omega)
  set B := 2 * K₀
  have hB : 2 ≤ B := by omega
  have hB0 : 0 < B := by omega
  set τ_cut := Nat.sqrt (max 1 S_val * (T + 1)) + 1
  have hτ : 1 ≤ τ_cut := by omega
  -- Degenerate small-`R_suf` guard: when `R_suf.card < B`, `R_suf.card / B = 0`.
  by_cases hNB : R_suf.card < B
  · refine ⟨∅, ?_, ?_⟩
    · intro q hq
      exact False.elim (Finset.notMem_empty q hq)
    · rw [Nat.div_eq_of_lt hNB, Nat.zero_mul, Nat.zero_mul]
      exact Nat.zero_le _
  have hBN : B ≤ R_suf.card := Nat.le_of_not_lt hNB
  set N := R_suf.card
  have hN_pos : 0 < N := by omega
  let e : Fin N ≃o R_suf := R_suf.orderIsoOfFin rfl
  let idxBucket : Fin B → Finset (Fin N) := fun c =>
    Finset.univ.filter fun k : Fin N => c.1 * N / B ≤ k.1 ∧ k.1 < (c.1 + 1) * N / B
  let bucketR : Fin B → Finset (Fin d) := fun c =>
    (idxBucket c).image fun k => (e k).1
  have hbucket_sub : ∀ c : Fin B, bucketR c ⊆ R_suf := by
    intro c u hu
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hu
    exact (e k).2
  have hbucket_card : ∀ c : Fin B, N / B ≤ (bucketR c).card := by
    intro c
    have hinj : Function.Injective (fun k : Fin N => (e k).1) :=
      Subtype.val_injective.comp e.injective
    calc N / B ≤ (idxBucket c).card := bucketR_card_ge (d := N) hB0 c
      _ = (bucketR c).card := (Finset.card_image_of_injective _ hinj).symm
  have hthresh_lt : ∀ m : Fin (B - 1), (m.1 + 1) * N / B < N := by
    intro m
    rw [Nat.div_lt_iff_lt_mul hB0, Nat.mul_comm N B]
    exact Nat.mul_lt_mul_of_pos_right (by omega) hN_pos
  let kThresh : Fin (B - 1) → Fin N := fun m => ⟨(m.1 + 1) * N / B, hthresh_lt m⟩
  let rThresh : Fin (B - 1) → ℕ := fun m => (e (kThresh m)).1.1
  let pThresh : Fin (B - 1) → ℕ := fun m => rThresh m * W
  let P_set : Finset ℕ := (Finset.univ : Finset (Fin (B - 1))).image pThresh
  have hP_card : P_set.card ≤ B := by
    calc P_set.card ≤ (Finset.univ : Finset (Fin (B - 1))).card := Finset.card_image_le
      _ = B - 1 := by simp
      _ ≤ B := Nat.sub_le B 1
  set Δ := D * τ_cut
  have hSdiv : S_val * (T / τ_cut) ≤ τ_cut := by
    have hlt_sq : max 1 S_val * (T + 1) < τ_cut * τ_cut := Nat.lt_succ_sqrt _
    have hmul : (max 1 S_val * (T / τ_cut)) * τ_cut ≤ τ_cut * τ_cut := by
      calc (max 1 S_val * (T / τ_cut)) * τ_cut
          = max 1 S_val * ((T / τ_cut) * τ_cut) := by ring
        _ ≤ max 1 S_val * T := Nat.mul_le_mul_left _ (Nat.div_mul_le_self T τ_cut)
        _ ≤ max 1 S_val * (T + 1) := Nat.mul_le_mul_left _ (Nat.le_succ T)
        _ ≤ τ_cut * τ_cut := hlt_sq.le
    calc S_val * (T / τ_cut)
        ≤ max 1 S_val * (T / τ_cut) := Nat.mul_le_mul_right _ (Nat.le_max_right 1 S_val)
      _ ≤ τ_cut := Nat.le_of_mul_le_mul_right hmul hτ
  have hSig_card : ∀ α < M_ph, (Finset.univ : Finset (SigAt B_bank α)).card ≤ K₀ := by
    intro α hα
    rw [Finset.card_univ, card_sigAt]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  -- Suffix bad DAG vertices `X_bad` and cone-bad coordinates `Z_cone`.
  let W_bad : Finset ℕ :=
    (Finset.range M_ph).biUnion fun α =>
      (Finset.univ : Finset (SigAt B_bank α)).biUnion fun s =>
        P_set.biUnion fun pStar =>
          windowsOf τ₀ L T Δ B_bank a α (liftSig s) pStar
  have hW_bad : W_bad.card ≤ M_ph * (K₀ * (B * (M_ph * (D + 1)))) * τ_cut := by
    have h1 : W_bad.card ≤ M_ph * (K₀ * (B * (M_ph * (Δ + 1)))) := by
      calc W_bad.card
          ≤ ∑ α ∈ Finset.range M_ph,
              ((Finset.univ : Finset (SigAt B_bank α)).biUnion fun s =>
                P_set.biUnion fun pStar => windowsOf τ₀ L T Δ B_bank a α (liftSig s) pStar).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _α ∈ Finset.range M_ph, (K₀ * (B * (M_ph * (Δ + 1)))) := by
            refine Finset.sum_le_sum fun α hα => ?_
            have hαM : α < M_ph := Finset.mem_range.mp hα
            calc _ ≤ ∑ s ∈ (Finset.univ : Finset (SigAt B_bank α)),
                    (P_set.biUnion fun pStar =>
                      windowsOf τ₀ L T Δ B_bank a α (liftSig s) pStar).card :=
                    Finset.card_biUnion_le
              _ ≤ ∑ _s ∈ (Finset.univ : Finset (SigAt B_bank α)), (B * (M_ph * (Δ + 1))) := by
                    refine Finset.sum_le_sum fun s _ => ?_
                    calc _ ≤ ∑ pStar ∈ P_set,
                            (windowsOf τ₀ L T Δ B_bank a α (liftSig s) pStar).card :=
                            Finset.card_biUnion_le
                      _ ≤ ∑ _pStar ∈ P_set, (M_ph * (Δ + 1)) := by
                            refine Finset.sum_le_sum fun pStar _ => ?_
                            exact (card_windowsOf_le τ₀ L T Δ B_bank a α (liftSig s) pStar).trans
                              (Nat.mul_le_mul_right (Δ + 1) (by omega))
                      _ = P_set.card * (M_ph * (Δ + 1)) := by simp
                      _ ≤ B * (M_ph * (Δ + 1)) := Nat.mul_le_mul_right _ hP_card
              _ = (Finset.univ : Finset (SigAt B_bank α)).card * (B * (M_ph * (Δ + 1))) := by simp
              _ ≤ K₀ * (B * (M_ph * (Δ + 1))) := Nat.mul_le_mul_right _ (hSig_card α hαM)
        _ = M_ph * (K₀ * (B * (M_ph * (Δ + 1)))) := by simp
    have hΔ1 : Δ + 1 ≤ (D + 1) * τ_cut := by
      show D * τ_cut + 1 ≤ (D + 1) * τ_cut
      rw [Nat.add_mul, Nat.one_mul]
      omega
    calc W_bad.card
        ≤ M_ph * (K₀ * (B * (M_ph * ((D + 1) * τ_cut)))) :=
          h1.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hΔ1))))
      _ = M_ph * (K₀ * (B * (M_ph * (D + 1)))) * τ_cut := by ring
  let X_bad : Finset ℕ :=
    longWorkHopsSuffix τ₀.work B_bank (a 0) T τ_cut ∪ phaseStartGuard M_ph a τ_cut ∪ W_bad
  have hwork_a0 : ∀ w : Fin M.k, w ∉ B_bank →
      ((Finset.Ico (a 0) T).image (τ₀.work w)).card ≤ S_val := by
    rwa [ha0]
  have hX_bad : X_bad.card ≤ (M.k + M_ph + M_ph * (K₀ * (B * (M_ph * (D + 1))))) * τ_cut := by
    have hlong : (longWorkHopsSuffix τ₀.work B_bank (a 0) T τ_cut).card ≤ M.k * τ_cut :=
      (card_longWorkHopsSuffix_le τ₀.work B_bank (a 0) T τ_cut S_val hτ hwork_a0).trans
        (Nat.mul_le_mul_left M.k hSdiv)
    have hguard : (phaseStartGuard M_ph a τ_cut).card ≤ M_ph * τ_cut :=
      card_phaseStartGuard_le M_ph a τ_cut
    calc X_bad.card
        ≤ (longWorkHopsSuffix τ₀.work B_bank (a 0) T τ_cut ∪ phaseStartGuard M_ph a τ_cut).card +
            W_bad.card := Finset.card_union_le _ _
      _ ≤ (longWorkHopsSuffix τ₀.work B_bank (a 0) T τ_cut).card +
            (phaseStartGuard M_ph a τ_cut).card + W_bad.card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ M.k * τ_cut + M_ph * τ_cut + M_ph * (K₀ * (B * (M_ph * (D + 1)))) * τ_cut :=
          Nat.add_le_add (Nat.add_le_add hlong hguard) hW_bad
      _ = (M.k + M_ph + M_ph * (K₀ * (B * (M_ph * (D + 1))))) * τ_cut := by ring
  let Anc := ancestors τ₀.work T X_bad D
  let Z_cone : Finset (Fin L) :=
    Finset.univ.filter fun q : Fin L => appendTime τ₀ T (tposOf d b q) ∈ Anc
  have hZ_card : Z_cone.card ≤
      (M.k + 2) ^ D * (M.k + M_ph + M_ph * (K₀ * (B * (M_ph * (D + 1))))) * τ_cut := by
    let f : Fin L → ℕ := fun q => appendTime τ₀ T (tposOf d b q)
    have hinj : Set.InjOn f Z_cone := by
      intro q₁ _ q₂ _ heq
      have h1 : (tposOf d b q₁).1 < (appendList τ₀ T).length := by rw [hlen]; exact (tposOf d b q₁).2
      have h2 : (tposOf d b q₂).1 < (appendList τ₀ T).length := by rw [hlen]; exact (tposOf d b q₂).2
      have htp_eq : tposOf d b q₁ = tposOf d b q₂ :=
        Fin.ext ((appendTime_strictMonoOn τ₀ T).injOn h1 h2 heq)
      calc q₁ = tposOf d b (tposOf d b q₁) := (tposOf_tposOf d b q₁).symm
        _ = tposOf d b (tposOf d b q₂) := by rw [htp_eq]
        _ = q₂ := tposOf_tposOf d b q₂
    have hsub : Z_cone.image f ⊆ Anc := by
      intro t ht
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
      exact (Finset.mem_filter.mp hq).2
    calc Z_cone.card
        = (Z_cone.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Anc.card := Finset.card_le_card hsub
      _ ≤ (M.k + 2) ^ D * X_bad.card := card_ancestors_le τ₀.work T X_bad D
      _ ≤ (M.k + 2) ^ D * ((M.k + M_ph + M_ph * (K₀ * (B * (M_ph * (D + 1))))) * τ_cut) :=
          Nat.mul_le_mul_left _ hX_bad
      _ = (M.k + 2) ^ D * (M.k + M_ph + M_ph * (K₀ * (B * (M_ph * (D + 1))))) * τ_cut := by ring
  -- Unsplit output rows (`Step 4` on `[t_suf, T)`).
  let loOut : Fin d → ℕ := fun j => j.1 * W
  let hiOut : Fin d → ℕ := fun j => (j.1 + 1) * W - 1
  have hlo_hi_lt : ∀ j : Fin d, loOut j ≤ hiOut j ∧ hiOut j < L := by
    intro j
    have h1 : j.1 * W + 1 ≤ (j.1 + 1) * W := by rw [Nat.add_mul, Nat.one_mul]; omega
    have h2 : (j.1 + 1) * W ≤ L := by
      show (j.1 + 1) * (d * b) ≤ d * d * b
      calc (j.1 + 1) * (d * b) ≤ d * (d * b) := Nat.mul_le_mul_right _ (by omega)
        _ = d * d * b := by ring
    exact ⟨by dsimp [loOut, hiOut]; omega, by dsimp [hiOut]; omega⟩
  have happ_a0 : ∀ ℓ < L, a 0 ≤ appendTime τ₀ T ℓ := by
    intro ℓ hℓ
    rw [ha0]
    exact happ ℓ (by rwa [hlenL])
  have happ_mono : ∀ {x y : ℕ}, x ≤ y → y < L → appendTime τ₀ T x ≤ appendTime τ₀ T y := by
    intro x y hxy hyL
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    · exact ((appendTime_strictMonoOn τ₀ T)
        (Set.mem_Iio.mpr (by rw [hlenL]; omega))
        (Set.mem_Iio.mpr (by rw [hlenL]; exact hyL)) hlt).le
  let SplitsRow : ℕ → Fin d → Prop := fun θ j =>
    appendTime τ₀ T (loOut j) < θ ∧ θ ≤ appendTime τ₀ T (hiOut j)
  have hSplits_le_one : ∀ θ : ℕ, ((Finset.univ : Finset (Fin d)).filter (SplitsRow θ)).card ≤ 1 := by
    intro θ
    refine Finset.card_le_one.mpr fun j₁ hj₁ j₂ hj₂ => ?_
    have hs1 := (Finset.mem_filter.mp hj₁).2
    have hs2 := (Finset.mem_filter.mp hj₂).2
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · have hlt_idx : hiOut j₁ < loOut j₂ := by
        dsimp [loOut, hiOut]
        have h1 : (j₁.1 + 1) * W ≤ j₂.1 * W := Nat.mul_le_mul_right W (by omega)
        have h2 : 1 ≤ (j₁.1 + 1) * W := Nat.mul_pos (by omega) hW
        omega
      have hlt_app : appendTime τ₀ T (hiOut j₁) < appendTime τ₀ T (loOut j₂) :=
        (appendTime_strictMonoOn τ₀ T) (by rw [hlen]; exact (hlo_hi_lt j₁).2)
          (by rw [hlen]; exact (hlo_hi_lt j₂).1.trans_lt (hlo_hi_lt j₂).2) hlt_idx
      omega
    · have hlt_idx : hiOut j₂ < loOut j₁ := by
        dsimp [loOut, hiOut]
        have h1 : (j₂.1 + 1) * W ≤ j₁.1 * W := Nat.mul_le_mul_right W (by omega)
        have h2 : 1 ≤ (j₂.1 + 1) * W := Nat.mul_pos (by omega) hW
        omega
      have hlt_app : appendTime τ₀ T (hiOut j₂) < appendTime τ₀ T (loOut j₁) :=
        (appendTime_strictMonoOn τ₀ T) (by rw [hlen]; exact (hlo_hi_lt j₂).2)
          (by rw [hlen]; exact (hlo_hi_lt j₁).1.trans_lt (hlo_hi_lt j₁).2) hlt_idx
      omega
  let Θ_cuts : Finset ℕ :=
    (Finset.range M_ph).biUnion fun α =>
      (Finset.univ : Finset (SigAt B_bank α)).biUnion fun s =>
        P_set.image fun pStar => (cutOf τ₀ L T B_bank a α (liftSig s) pStar).2
  have hΘ_cuts_card : Θ_cuts.card ≤ M_ph * (K₀ * B) := by
    calc Θ_cuts.card
        ≤ ∑ α ∈ Finset.range M_ph,
            ((Finset.univ : Finset (SigAt B_bank α)).biUnion fun s =>
              P_set.image fun pStar => (cutOf τ₀ L T B_bank a α (liftSig s) pStar).2).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _α ∈ Finset.range M_ph, (K₀ * B) := by
          refine Finset.sum_le_sum fun α hα => ?_
          have hαM : α < M_ph := Finset.mem_range.mp hα
          calc _ ≤ ∑ s ∈ (Finset.univ : Finset (SigAt B_bank α)),
                  (P_set.image fun pStar => (cutOf τ₀ L T B_bank a α (liftSig s) pStar).2).card :=
                  Finset.card_biUnion_le
            _ ≤ ∑ _s ∈ (Finset.univ : Finset (SigAt B_bank α)), B :=
                  Finset.sum_le_sum fun _ _ => Finset.card_image_le.trans hP_card
            _ = (Finset.univ : Finset (SigAt B_bank α)).card * B := by simp
            _ ≤ K₀ * B := Nat.mul_le_mul_right B (hSig_card α hαM)
      _ = M_ph * (K₀ * B) := by simp
  let Θ_all : Finset ℕ := (Finset.range (M_ph + 1)).image a ∪ Θ_cuts
  let J_split : Finset (Fin d) :=
    Θ_all.biUnion fun θ => (Finset.univ : Finset (Fin d)).filter (SplitsRow θ)
  have hJ_split_card : J_split.card ≤ (M_ph + 1) + M_ph * (K₀ * B) := by
    calc J_split.card
        ≤ ∑ θ ∈ Θ_all, ((Finset.univ : Finset (Fin d)).filter (SplitsRow θ)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _θ ∈ Θ_all, 1 := Finset.sum_le_sum fun θ _ => hSplits_le_one θ
      _ = Θ_all.card := by simp
      _ ≤ ((Finset.range (M_ph + 1)).image a).card + Θ_cuts.card := Finset.card_union_le _ _
      _ ≤ (M_ph + 1) + M_ph * (K₀ * B) := by
          refine Nat.add_le_add ?_ hΘ_cuts_card
          exact Finset.card_image_le.trans (by simp)
  let J_good : Finset (Fin d) := Finset.univ \ J_split
  let α₀ : Fin d → ℕ := fun j => phaseOf M_ph a (appendTime τ₀ T (loOut j))
  have hα₀_lt : ∀ j : Fin d, α₀ j < M_ph := by
    intro j
    have hlo_lt_L : loOut j < L := (hlo_hi_lt j).1.trans_lt (hlo_hi_lt j).2
    have hltT : appendTime τ₀ T (loOut j) < T := appendTime_lt τ₀ T (by rwa [hlenL])
    exact (phaseOf_spec_of_ge haM (happ_a0 (loOut j) hlo_lt_L) hltT).1
  -- Forbidden quantile-bucket set `F(j)` of size `≤ K₀` for each `j ∈ J_good`.
  let matchBuckets : (j : Fin d) → SigAt B_bank (α₀ j) → Finset (Fin B) := fun j s =>
    Finset.univ.filter fun c : Fin B =>
      ∃ u ∈ bucketR c, ∀ m : Fin (B - 1),
        (u.1 < rThresh m ↔
          tcut (cutOf τ₀ L T B_bank a (α₀ j) (liftSig s) (pThresh m)).1
            (cutOf τ₀ L T B_bank a (α₀ j) (liftSig s) (pThresh m)).2
            (appendTime τ₀ T (loOut j)))
  have hsep_buckets : ∀ {c₁ c₂ : Fin B}, c₁.1 < c₂.1 →
      ∀ u₁ ∈ bucketR c₁, ∀ u₂ ∈ bucketR c₂,
        ∃ m : Fin (B - 1), u₁.1 < rThresh m ∧ ¬ (u₂.1 < rThresh m) := by
    intro c₁ c₂ hlt u₁ hu₁ u₂ hu₂
    let m : Fin (B - 1) := ⟨c₁.1, by omega⟩
    obtain ⟨k₁, hk₁, rfl⟩ := Finset.mem_image.mp hu₁
    obtain ⟨k₂, hk₂, rfl⟩ := Finset.mem_image.mp hu₂
    have hb₁ := (Finset.mem_filter.mp hk₁).2
    have hb₂ := (Finset.mem_filter.mp hk₂).2
    refine ⟨m, ?_, ?_⟩
    · have hk_lt : k₁ < kThresh m := Fin.lt_def.mpr hb₁.2
      exact Fin.lt_def.mp (show (e k₁).1 < (e (kThresh m)).1 from e.strictMono hk_lt)
    · have hle_div : (c₁.1 + 1) * N / B ≤ c₂.1 * N / B :=
        Nat.div_le_div_right (Nat.mul_le_mul_right N (by omega))
      have hk_le : kThresh m ≤ k₂ := Fin.le_def.mpr (hle_div.trans hb₂.1)
      have he_le : rThresh m ≤ (e k₂).1.1 :=
        Fin.le_def.mp (show (e (kThresh m)).1 ≤ (e k₂).1 from e.monotone hk_le)
      omega
  have hmatch_le_one : ∀ (j : Fin d) (s : SigAt B_bank (α₀ j)), (matchBuckets j s).card ≤ 1 := by
    intro j s
    refine Finset.card_le_one.mpr fun c₁ hc₁ c₂ hc₂ => ?_
    obtain ⟨_, u₁, hu₁, hm₁⟩ := Finset.mem_filter.mp hc₁
    obtain ⟨_, u₂, hu₂, hm₂⟩ := Finset.mem_filter.mp hc₂
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · obtain ⟨m, h1, h2⟩ := hsep_buckets hlt u₁ hu₁ u₂ hu₂
      exact h2 (((hm₁ m).trans (hm₂ m).symm).mp h1)
    · obtain ⟨m, h2, h1⟩ := hsep_buckets hgt u₂ hu₂ u₁ hu₁
      exact h1 (((hm₂ m).trans (hm₁ m).symm).mp h2)
  let F : Fin d → Finset (Fin B) := fun j =>
    (Finset.univ : Finset (SigAt B_bank (α₀ j))).biUnion (matchBuckets j)
  have hF_card : ∀ j : Fin d, (F j).card ≤ K₀ := by
    intro j
    calc (F j).card
        ≤ ∑ s ∈ (Finset.univ : Finset (SigAt B_bank (α₀ j))), (matchBuckets j s).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ (Finset.univ : Finset (SigAt B_bank (α₀ j))), 1 :=
          Finset.sum_le_sum fun s _ => hmatch_le_one j s
      _ = (Finset.univ : Finset (SigAt B_bank (α₀ j))).card := by simp
      _ ≤ K₀ := hSig_card (α₀ j) (hα₀_lt j)
  -- Pigeonhole a bucket `cStar : Fin B` avoided by at least half of `J_good`.
  let J_of : Fin B → Finset (Fin d) := fun c => J_good.filter fun j => c ∉ F j
  have hpigeon : ∃ cStar : Fin B, J_good.card ≤ 2 * (J_of cStar).card := by
    have hsum : J_good.card * K₀ ≤ ∑ c : Fin B, (J_of c).card := by
      have hswap : ∑ c : Fin B, (J_of c).card =
          ∑ j ∈ J_good, ((Finset.univ : Finset (Fin B)).filter fun c => c ∉ F j).card := by
        simp only [J_of, Finset.card_filter]
        exact Finset.sum_comm
      rw [hswap]
      calc J_good.card * K₀
          = ∑ _j ∈ J_good, K₀ := by simp
        _ ≤ ∑ j ∈ J_good, ((Finset.univ : Finset (Fin B)).filter fun c => c ∉ F j).card := by
            refine Finset.sum_le_sum fun j _ => ?_
            have hsdiff : ((Finset.univ : Finset (Fin B)).filter fun c => c ∉ F j) =
                Finset.univ \ F j := by
              ext c; simp
            rw [hsdiff]
            have hleF := hF_card j
            have hcardU : (Finset.univ : Finset (Fin B)).card = 2 * K₀ := by simp [B]
            have hadd := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin B)) (F j)
            have hinter : (Finset.univ ∩ F j).card = (F j).card := by simp
            omega
    by_contra hall
    push Not at hall
    have hlt_sum : ∑ c : Fin B, (2 * (J_of c).card) < ∑ _c : Fin B, J_good.card :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB0⟩⟩) fun c _ => hall c
    have h1 : ∑ c : Fin B, (2 * (J_of c).card) = 2 * ∑ c : Fin B, (J_of c).card := by
      rw [Finset.mul_sum]
    have h2 : (∑ _c : Fin B, J_good.card) = 2 * K₀ * J_good.card := by simp [B]
    have hmul_comm : 2 * (J_good.card * K₀) = 2 * K₀ * J_good.card := by ring
    omega
  obtain ⟨cStar, hcStar⟩ := hpigeon
  -- Construct `Rect ⊆ R_suf × J_of cStar × Fin b` and `S_ind := Rect \ Z_cone`.
  let outRow : Fin L → Fin d := fun q => ⟨q.1 / b % d, (Transpose.Tape.Impl.pos_decomp q.2).2.1⟩
  let Rect : Finset (Fin L) :=
    Finset.univ.filter fun q : Fin L => rawRowOf q ∈ bucketR cStar ∧ outRow q ∈ J_of cStar
  let S_ind : Finset (Fin L) := Rect \ Z_cone
  refine ⟨S_ind, ?_, ?_⟩
  · -- Prove `IsIndependent` on the full cone relation `q ↦ coneSystem τ₀ T Γ d b (tposOf d b q)`.
    intro q hqS p hpN hpS
    obtain ⟨hqRect, hqNotZ⟩ := Finset.mem_sdiff.mp hqS
    obtain ⟨hpRect, -⟩ := Finset.mem_sdiff.mp hpS
    obtain ⟨-, _, hqJ⟩ := Finset.mem_filter.mp hqRect
    obtain ⟨-, hpR, -⟩ := Finset.mem_filter.mp hpRect
    obtain ⟨hjGood, hcNotF⟩ := Finset.mem_filter.mp hqJ
    have hjNotSplit : outRow q ∉ J_split := (Finset.mem_sdiff.mp hjGood).2
    have hnot_splits : ∀ θ ∈ Θ_all, ¬ SplitsRow θ (outRow q) := by
      intro θ hθ hs
      exact hjNotSplit (Finset.mem_biUnion.mpr ⟨θ, hθ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩)
    -- Extract the `Γ`-free dependency path reading `p`.
    simp only [coneSystem, depCone, Finset.mem_filter, Finset.mem_univ, true_and] at hpN
    obtain ⟨ρ, hdep, hfree, hrd⟩ := hpN
    -- Since `p ∈ S_ind`, `rawRowOf p ∈ bucketR cStar ⊆ R_suf`, forcing `a 0 = t_suf ≤ t_last`.
    have hp_suf : rawRowOf p ∈ R_suf := hbucket_sub cStar hpR
    have ht_last_ge : a 0 ≤ ((appendTime τ₀ T (tposOf d b q) :: ρ).getLastD
        (appendTime τ₀ T (tposOf d b q))) := by
      rw [ha0]
      by_contra hlt_suf
      have hin_eq : τ₀.input ((appendTime τ₀ T (tposOf d b q) :: ρ).getLastD
          (appendTime τ₀ T (tposOf d b q))) = (p.1 : ℤ) :=
        readPos_eq_some_iff.mp hrd
      exact hno_pre _ (Nat.lt_of_not_ge hlt_suf) p hin_eq hp_suf
    set ℓ := (tposOf d b q).1
    set t₀ := appendTime τ₀ T ℓ
    have hℓ_bounds := (coord_row_bounds q).2
    have hlo_ℓ : loOut (outRow q) ≤ ℓ := hℓ_bounds.1
    have hℓ_hi : ℓ ≤ hiOut (outRow q) := hℓ_bounds.2
    have hℓ_lt : ℓ < L := (tposOf d b q).2
    have ht₀_lt : t₀ < T := appendTime_lt τ₀ T (by rw [hlen]; exact hℓ_lt)
    have ht₀_ge : a 0 ≤ t₀ := happ_a0 ℓ hℓ_lt
    have ht0_lo : appendTime τ₀ T (loOut (outRow q)) ≤ t₀ := happ_mono hlo_ℓ hℓ_lt
    have ht0_hi : t₀ ≤ appendTime τ₀ T (hiOut (outRow q)) :=
      happ_mono hℓ_hi (hlo_hi_lt (outRow q)).2
    have hph_t₀ : phaseOf M_ph a t₀ = α₀ (outRow q) := by
      have hlo_lt_L : loOut (outRow q) < L :=
        (hlo_hi_lt (outRow q)).1.trans_lt (hlo_hi_lt (outRow q)).2
      have hlo_lt_T : appendTime τ₀ T (loOut (outRow q)) < T :=
        appendTime_lt τ₀ T (by rwa [hlenL])
      obtain ⟨hαM, ha_lo, _⟩ :=
        phaseOf_spec_of_ge haM (happ_a0 (loOut (outRow q)) hlo_lt_L) hlo_lt_T
      have hmemΘ : a (α₀ (outRow q) + 1) ∈ Θ_all :=
        Finset.mem_union_left _ (Finset.mem_image_of_mem a
          (Finset.mem_range.mpr (by dsimp only [α₀] at *; omega)))
      have hns := hnot_splits _ hmemΘ
      have hhi_lt : appendTime τ₀ T (hiOut (outRow q)) < a (α₀ (outRow q) + 1) := by
        dsimp [SplitsRow] at hns
        dsimp only [α₀] at *
        omega
      exact (phaseOf_eq_iff_of_ge haM ha ht₀_ge ht₀_lt hαM).mpr
        ⟨ha_lo.trans ht0_lo, ht0_hi.trans_lt hhi_lt⟩
    have hlen_ρ : ρ.length ≤ D := by
      have h1 := hpath (t₀ :: ρ) hdep hfree
      simp at h1; omega
    have hΔ_ρ : ρ.length * τ_cut ≤ Δ := Nat.mul_le_mul_right τ_cut hlen_ρ
    have havoid_X : ∀ x ∈ t₀ :: ρ, x ∉ X_bad := by
      intro x hx hx_bad
      have ht0_anc := ancestors_mono τ₀.work T X_bad hlen_ρ
        (head_mem_ancestors_of_mem_path ρ t₀ hdep hx hx_bad)
      exact hqNotZ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht0_anc⟩)
    have havoid_guard : ∀ x ∈ t₀ :: ρ,
        x ∉ longWorkHopsSuffix τ₀.work B_bank (a 0) T τ_cut ∧ x ∉ phaseStartGuard M_ph a τ_cut := by
      intro x hx
      refine ⟨fun h => havoid_X x hx (Finset.mem_union_left _ (Finset.mem_union_left _ h)),
        fun h => havoid_X x hx (Finset.mem_union_left _ (Finset.mem_union_right _ h))⟩
    obtain ⟨s, hs⟩ := depPath_signature_exists_suffix (L := L) (Δ := Δ) hτ haM ha hin hbank
      (α₀ (outRow q)) (hα₀_lt (outRow q)) ht₀_lt hph_t₀ ht_last_ge hdep hΔ_ρ havoid_guard hrd
    apply hcNotF
    refine Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, rawRowOf p, hpR, fun m => ?_⟩
    have hp_mem_P : pThresh m ∈ P_set := Finset.mem_image_of_mem pThresh (Finset.mem_univ m)
    have hnowin : ∀ x ∈ t₀ :: ρ,
        x ∉ windowsOf τ₀ L T Δ B_bank a (α₀ (outRow q)) (liftSig s) (pThresh m) := by
      intro x hx hmem
      apply havoid_X x hx
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_biUnion.mpr ⟨α₀ (outRow q), Finset.mem_range.mpr (hα₀_lt (outRow q)),
        Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _,
          Finset.mem_biUnion.mpr ⟨pThresh m, hp_mem_P, hmem⟩⟩⟩
    have htcut_t₀ := hs (pThresh m) hnowin
    let c₀ := cutOf τ₀ L T B_bank a (α₀ (outRow q)) (liftSig s) (pThresh m)
    have hc₀_mem : c₀.2 ∈ Θ_all := by
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_biUnion.mpr ⟨α₀ (outRow q), Finset.mem_range.mpr (hα₀_lt (outRow q)),
        Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _,
          Finset.mem_image.mpr ⟨pThresh m, hp_mem_P, rfl⟩⟩⟩
    have hns_c₀ := hnot_splits c₀.2 hc₀_mem
    have htcut_unsplit : tcut c₀.1 c₀.2 t₀ ↔
        tcut c₀.1 c₀.2 (appendTime τ₀ T (loOut (outRow q))) := by
      dsimp [SplitsRow] at hns_c₀
      cases c₀.1 <;> simp only [tcut, ↓reduceIte, Bool.false_eq_true] <;> omega
    exact ((coord_row_bounds p).1 (rThresh m)).trans (htcut_t₀.symm.trans htcut_unsplit)
  · -- Lower-bound `Rect.card` and deduce the size bound on `S_ind`.
    let ProdSet := (bucketR cStar ×ˢ J_of cStar) ×ˢ (Finset.univ : Finset (Fin b))
    let g : (Fin d × Fin d) × Fin b → Fin L := fun x =>
      ⟨(x.1.1.1 * d + x.1.2.1) * b + x.2.1, by
        calc (x.1.1.1 * d + x.1.2.1) * b + x.2.1
            < (x.1.1.1 * d + x.1.2.1) * b + b := Nat.add_lt_add_left x.2.2 _
          _ = (x.1.1.1 * d + x.1.2.1 + 1) * b := by ring
          _ ≤ (x.1.1.1 * d + d) * b := Nat.mul_le_mul_right b (by omega)
          _ = (x.1.1.1 + 1) * d * b := by ring
          _ ≤ d * d * b := Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))⟩
    have hg_parts : ∀ x : (Fin d × Fin d) × Fin b,
        (g x).1 / b = x.1.1.1 * d + x.1.2.1 ∧ (g x).1 % b = x.2.1 ∧
        (g x).1 / b / d = x.1.1.1 ∧ (g x).1 / b % d = x.1.2.1 := by
      intro x
      have hdivb : ((x.1.1.1 * d + x.1.2.1) * b + x.2.1) / b = x.1.1.1 * d + x.1.2.1 := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt x.2.2, zero_add]
      have hmodb : ((x.1.1.1 * d + x.1.2.1) * b + x.2.1) % b = x.2.1 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt x.2.2]
      have hdivd : (x.1.1.1 * d + x.1.2.1) / d = x.1.1.1 := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt x.1.2.2, zero_add]
      have hmodd : (x.1.1.1 * d + x.1.2.1) % d = x.1.2.1 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt x.1.2.2]
      refine ⟨hdivb, hmodb, ?_, ?_⟩
      · dsimp [g]; rw [hdivb, hdivd]
      · dsimp [g]; rw [hdivb, hmodd]
    have hg_inj : Set.InjOn g ProdSet := by
      intro x₁ _ x₂ _ heq
      have hv : (g x₁).1 = (g x₂).1 := congrArg Fin.val heq
      obtain ⟨_, hs1, hu1, hj1⟩ := hg_parts x₁
      obtain ⟨_, hs2, hu2, hj2⟩ := hg_parts x₂
      ext
      · rw [← hu1, ← hu2, hv]
      · rw [← hj1, ← hj2, hv]
      · rw [← hs1, ← hs2, hv]
    have hg_sub : ProdSet.image g ⊆ Rect := by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hp_pair, -⟩ := Finset.mem_product.mp hx
      obtain ⟨hu_mem, hj_mem⟩ := Finset.mem_product.mp hp_pair
      obtain ⟨-, -, hu_eq, hj_eq⟩ := hg_parts x
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · have : rawRowOf (g x) = x.1.1 := Fin.ext hu_eq
        rwa [this]
      · have : outRow (g x) = x.1.2 := Fin.ext hj_eq
        rwa [this]
    have hRect_card : (N / B) * ((d - ((M_ph + 1) + M_ph * (K₀ * B))) / 2) * b ≤ Rect.card := by
      have hJgood_ge : d - ((M_ph + 1) + M_ph * (K₀ * B)) ≤ J_good.card := by
        have hadd := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin d)) J_split
        change J_good.card + (Finset.univ ∩ J_split).card =
          (Finset.univ : Finset (Fin d)).card at hadd
        have hinter : (Finset.univ ∩ J_split).card = J_split.card := by simp
        have huniv : (Finset.univ : Finset (Fin d)).card = d := by simp
        omega
      have hJof_ge : (d - ((M_ph + 1) + M_ph * (K₀ * B))) / 2 ≤ (J_of cStar).card := by omega
      have hR_ge : N / B ≤ (bucketR cStar).card := hbucket_card cStar
      calc (N / B) * ((d - ((M_ph + 1) + M_ph * (K₀ * B))) / 2) * b
          ≤ (bucketR cStar).card * (J_of cStar).card * b :=
            Nat.mul_le_mul_right b (Nat.mul_le_mul hR_ge hJof_ge)
        _ = ProdSet.card := by simp [ProdSet]
        _ = (ProdSet.image g).card := (Finset.card_image_of_injOn hg_inj).symm
        _ ≤ Rect.card := Finset.card_le_card hg_sub
    have hRect_sub : Rect ⊆ S_ind ∪ Z_cone := by
      intro q hq
      by_cases hqZ : q ∈ Z_cone
      · exact Finset.mem_union_right _ hqZ
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hq, hqZ⟩)
    have hRect_le : Rect.card ≤ S_ind.card + Z_cone.card :=
      (Finset.card_le_card hRect_sub).trans (Finset.card_union_le _ _)
    exact hRect_card.trans (hRect_le.trans (Nat.add_le_add_left hZ_card S_ind.card))

/-- Asymptotic/rounding transfer from `(N / B) * ((d - C_split) / 2) * b ≤ S_card + C_cone * τ_cut`
with `δ₀ * d ≤ N` to `(δ₀ / (4 * K₀) - η) * L ≤ m`. -/
private theorem crux_bound_of_suffix_card_bound (K₀ C_split C_cone : ℕ) (hK₀_pos : 1 ≤ K₀)
    {C δ₀ η : ℝ} (hC : 1 ≤ C) (hδ₀ : 0 < δ₀) (hη : 0 < η) {S : ℕ → ℕ}
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    ∃ d_asymp : ℕ, ∀ d ≥ d_asymp, ∀ T N S_card m : ℕ,
      let b := entryBits d
      let L := d * d * b
      let B := 2 * K₀
      let τ_cut := Nat.sqrt (max 1 (S d) * (T + 1)) + 1
      (T : ℝ) ≤ C * ((L : ℝ) + 1) →
      δ₀ * (d : ℝ) ≤ (N : ℝ) →
      (N / B) * ((d - C_split) / 2) * b ≤ S_card + C_cone * τ_cut →
      (S_card : ℝ) ≤ (m : ℝ) →
      (δ₀ / (4 * (K₀ : ℝ)) - η) * (L : ℝ) ≤ (m : ℝ) := by
  set B := 2 * K₀
  have hB_pos : 2 ≤ B := by omega
  set δ : ℝ := η / (4 * ((C_cone : ℝ) + 1))
  have hδ : 0 < δ := by positivity
  have h2C1 : 0 < 2 * C + 1 := by linarith
  set ε_S : ℝ := δ ^ 2 / (2 * C + 1)
  have hε_S : 0 < ε_S := by positivity
  rw [Metric.tendsto_atTop] at hS
  obtain ⟨d_S, hd_S⟩ := hS ε_S hε_S
  let coef_lin : ℝ := δ₀ * ((C_split : ℝ) + 1) + 2
  have hcoef_pos : 0 < coef_lin := by positivity
  let d_lin := ⌈(8 * coef_lin) / η⌉₊ + ⌈(B : ℝ) / δ₀⌉₊ + C_split + B + 2
  let d_one := ⌈1 / ε_S⌉₊ + ⌈1 / δ⌉₊ + 1
  refine ⟨max d_S (max d_lin d_one), fun d hd T N S_card m hT hN_ge hcard_nat hm_ge => ?_⟩
  have hd_ge_S : d_S ≤ d := (le_max_left _ _).trans hd
  have hd_ge_lin : d_lin ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hd_ge_one : d_one ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
  have hd1 : 1 ≤ d := by omega
  set b := entryBits d
  have hb1 : 1 ≤ b := one_le_entryBits d
  set L := d * d * b
  have hL_ge_d : d ≤ L := by
    calc d = d * 1 * 1 := by ring
      _ ≤ d * d * b := Nat.mul_le_mul (Nat.mul_le_mul_left d hd1) hb1
  have hL1 : 1 ≤ L := hd1.trans hL_ge_d
  have hLr_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  set τ_cut := Nat.sqrt (max 1 (S d) * (T + 1)) + 1
  have hS_lt : (S d : ℝ) ≤ ε_S * (L : ℝ) := by
    have hdist := hd_S d hd_ge_S
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hdist
    exact (div_lt_iff₀ hLr_pos).mp hdist |>.le
  have h1_le_εL : (1 : ℝ) ≤ ε_S * (L : ℝ) := by
    have hceil : 1 / ε_S ≤ (d : ℝ) := by
      calc 1 / ε_S ≤ (⌈1 / ε_S⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (d_one : ℝ) := by exact_mod_cast (show ⌈1 / ε_S⌉₊ ≤ d_one by omega)
        _ ≤ (d : ℝ) := by exact_mod_cast hd_ge_one
    have hdL : (d : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge_d
    exact (div_le_iff₀' hε_S).mp (hceil.trans hdL)
  have hmax_le : ((max 1 (S d) : ℕ) : ℝ) ≤ ε_S * (L : ℝ) := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le h1_le_εL hS_lt
  have hT1_le : ((T + 1 : ℕ) : ℝ) ≤ (2 * C + 1) * (L : ℝ) := by
    change (T : ℝ) ≤ C * ((L : ℝ) + 1) at hT
    have hL1r : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
    have hCL : C ≤ C * (L : ℝ) := le_mul_of_one_le_right (by linarith) hL1r
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hM_le : ((max 1 (S d) * (T + 1) : ℕ) : ℝ) ≤ (δ * (L : ℝ)) ^ 2 := by
    rw [Nat.cast_mul]
    calc ((max 1 (S d) : ℕ) : ℝ) * ((T + 1 : ℕ) : ℝ)
        ≤ (ε_S * (L : ℝ)) * ((2 * C + 1) * (L : ℝ)) := by gcongr
      _ = (δ * (L : ℝ)) ^ 2 := by
          dsimp [ε_S]
          field_simp
  have hsqrt_le : (Nat.sqrt (max 1 (S d) * (T + 1)) : ℝ) ≤ δ * (L : ℝ) := by
    have hsq_nat := Nat.sqrt_le (max 1 (S d) * (T + 1))
    have hsq_r : (Nat.sqrt (max 1 (S d) * (T + 1)) : ℝ) *
        (Nat.sqrt (max 1 (S d) * (T + 1)) : ℝ) ≤ ((max 1 (S d) * (T + 1) : ℕ) : ℝ) := by
      exact_mod_cast hsq_nat
    have hnn1 : (0 : ℝ) ≤ (Nat.sqrt (max 1 (S d) * (T + 1)) : ℝ) := by positivity
    have hnn2 : (0 : ℝ) ≤ δ * (L : ℝ) := by positivity
    nlinarith
  have h1_le_δL : (1 : ℝ) ≤ δ * (L : ℝ) := by
    have hceil : 1 / δ ≤ (d : ℝ) := by
      calc 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (d_one : ℝ) := by exact_mod_cast (show ⌈1 / δ⌉₊ ≤ d_one by omega)
        _ ≤ (d : ℝ) := by exact_mod_cast hd_ge_one
    have hdL : (d : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge_d
    exact (div_le_iff₀' hδ).mp (hceil.trans hdL)
  have hcone_err : (C_cone : ℝ) * (τ_cut : ℝ) ≤ (η / 2) * (L : ℝ) := by
    have hτ_r : (τ_cut : ℝ) ≤ 2 * δ * (L : ℝ) := by
      show ((Nat.sqrt (max 1 (S d) * (T + 1)) + 1 : ℕ) : ℝ) ≤ 2 * δ * (L : ℝ)
      push_cast
      linarith
    have hC_nn : (0 : ℝ) ≤ (C_cone : ℝ) := by positivity
    calc (C_cone : ℝ) * (τ_cut : ℝ)
        ≤ (C_cone : ℝ) * (2 * δ * (L : ℝ)) := mul_le_mul_of_nonneg_left hτ_r hC_nn
      _ ≤ ((C_cone : ℝ) + 1) * (2 * δ * (L : ℝ)) := by nlinarith
      _ = (η / 2) * (L : ℝ) := by
          dsimp [δ]
          field_simp
          ring
  have hd_sub : C_split ≤ d := by omega
  have hBr : (0 : ℝ) < (B : ℝ) := by positivity
  have hdivB_r : (δ₀ * (d : ℝ)) / (B : ℝ) - 1 ≤ ((N / B : ℕ) : ℝ) := by
    have hmod := Nat.div_add_mod N B
    have hlt := Nat.mod_lt N (show 0 < B by omega)
    have h1 : (N : ℝ) ≤ ((B * (N / B) + B : ℕ) : ℝ) := by
      exact_mod_cast (by omega : N ≤ B * (N / B) + B)
    push_cast at h1
    have hNB_div : (N : ℝ) / (B : ℝ) - 1 ≤ ((N / B : ℕ) : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hBr]
      linarith
    have hδN : (δ₀ * (d : ℝ)) / (B : ℝ) ≤ (N : ℝ) / (B : ℝ) :=
      div_le_div_of_nonneg_right hN_ge hBr.le
    linarith
  have hdiv2_r : ((d : ℝ) - (C_split : ℝ) - 1) / 2 ≤ (((d - C_split) / 2 : ℕ) : ℝ) := by
    have h1 : d - C_split ≤ 2 * ((d - C_split) / 2) + 1 := by omega
    have h1r : ((d - C_split : ℕ) : ℝ) ≤ ((2 * ((d - C_split) / 2) + 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [Nat.cast_sub hd_sub] at h1r
    push_cast at h1r
    linarith
  have hpos_f1 : (0 : ℝ) ≤ (δ₀ * (d : ℝ)) / (B : ℝ) - 1 := by
    rw [sub_nonneg, le_div_iff₀ hBr]
    have hceil_B : (B : ℝ) / δ₀ ≤ (d : ℝ) := by
      calc (B : ℝ) / δ₀ ≤ (⌈(B : ℝ) / δ₀⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (d_lin : ℝ) := Nat.cast_le.mpr (by omega)
        _ ≤ (d : ℝ) := Nat.cast_le.mpr hd_ge_lin
    have hmul_B := (div_le_iff₀ hδ₀).mp hceil_B
    linarith
  have hpos_f2 : (0 : ℝ) ≤ ((d : ℝ) - (C_split : ℝ) - 1) / 2 := by
    have : C_split + 1 ≤ d := by omega
    have hr : ((C_split + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast this
    push_cast at hr
    linarith
  have hrect_r : ((δ₀ / (4 * (K₀ : ℝ)) - η / 2) * (L : ℝ)) ≤
      (((N / B) * ((d - C_split) / 2) * b : ℕ) : ℝ) := by
    have hprod : ((δ₀ * (d : ℝ)) / (B : ℝ) - 1) * (((d : ℝ) - (C_split : ℝ) - 1) / 2) * (b : ℝ) ≤
        (((N / B) * ((d - C_split) / 2) * b : ℕ) : ℝ) := by
      rw [Nat.cast_mul ((N / B) * ((d - C_split) / 2)) b,
        Nat.cast_mul (N / B) ((d - C_split) / 2)]
      have hb_nn : (0 : ℝ) ≤ (b : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul hdivB_r hdiv2_r hpos_f2
        (hpos_f1.trans hdivB_r)) hb_nn
    have hB_eq : (B : ℝ) = 2 * (K₀ : ℝ) := by simp [B]
    have hK₀_r : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀_pos
    let ceil_term := ⌈(8 * coef_lin) / η⌉₊
    have hlin_ge : (8 * coef_lin) / η ≤ (d : ℝ) := by
      calc (8 * coef_lin) / η
          ≤ (ceil_term : ℝ) := Nat.le_ceil _
        _ ≤ (d_lin : ℝ) := Nat.cast_le.mpr (by omega)
        _ ≤ (d : ℝ) := Nat.cast_le.mpr hd_ge_lin
    have hηd : 8 * coef_lin ≤ η * (d : ℝ) := by
      have h1 := (div_le_iff₀ hη).mp hlin_ge
      linarith only [h1]
    have hL_eq : (L : ℝ) = (d : ℝ) * (d : ℝ) * (b : ℝ) := by simp [L]
    have hident :
        ((δ₀ * (d : ℝ)) / (B : ℝ) - 1) * (((d : ℝ) - (C_split : ℝ) - 1) / 2) * (b : ℝ) =
          (δ₀ / (4 * (K₀ : ℝ))) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) -
            ((δ₀ * ((C_split : ℝ) + 1)) / (4 * (K₀ : ℝ)) + 1 / 2) * ((d : ℝ) * (b : ℝ)) +
            (((C_split : ℝ) + 1) / 2) * (b : ℝ) := by
      rw [hB_eq]
      field_simp
      ring
    have herr_lin : ((δ₀ * ((C_split : ℝ) + 1)) / (4 * (K₀ : ℝ)) + 1 / 2) * ((d : ℝ) * (b : ℝ)) ≤
        (η / 2) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) := by
      have hcoef_le : (δ₀ * ((C_split : ℝ) + 1)) / (4 * (K₀ : ℝ)) + 1 / 2 ≤ coef_lin := by
        have hdiv_le : (δ₀ * ((C_split : ℝ) + 1)) / (4 * (K₀ : ℝ)) ≤ δ₀ * ((C_split : ℝ) + 1) :=
          div_le_self (by positivity) (by linarith only [hK₀_r])
        dsimp [coef_lin]
        linarith only [hdiv_le]
      have hdb_nn : (0 : ℝ) ≤ (d : ℝ) * (b : ℝ) := by positivity
      calc ((δ₀ * ((C_split : ℝ) + 1)) / (4 * (K₀ : ℝ)) + 1 / 2) * ((d : ℝ) * (b : ℝ))
          ≤ coef_lin * ((d : ℝ) * (b : ℝ)) := mul_le_mul_of_nonneg_right hcoef_le hdb_nn
        _ ≤ ((η * (d : ℝ)) / 8) * ((d : ℝ) * (b : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ hdb_nn
            linarith only [hηd]
        _ = (η / 8) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) := by ring
        _ ≤ (η / 2) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) := by
            have hddb : (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) * (b : ℝ) := by positivity
            exact mul_le_mul_of_nonneg_right (by linarith only [hη]) hddb
    have hb_nn : (0 : ℝ) ≤ (((C_split : ℝ) + 1) / 2) * (b : ℝ) := by positivity
    rw [hL_eq]
    linarith only [hprod, hident, herr_lin, hb_nn]
  have hcard_r : (((N / B) * ((d - C_split) / 2) * b : ℕ) : ℝ) ≤
      (S_card : ℝ) + (C_cone : ℝ) * (τ_cut : ℝ) := by
    exact_mod_cast hcard_nat
  linarith only [hrect_r, hcard_r, hcone_err, hm_ge]

/-- **Theorem B, suffix form (`suffixMacroBank_has_crux`)**: every machine satisfying
`BoundedSuffixMacroBank M C M_ph δ₀ B_bank S` with `δ₀ > 0` and sublinear suffix workspace bound
`S(d) / (d² entryBits(d)) → 0` satisfies the depth-independent machine crux
`MachineCrux M C (δ₀ / (4 * K₀))`, where `K₀ = (B_bank.card + 1) ^ (M_ph - 1)`. -/
theorem suffixMacroBank_has_crux {M : TM} {C δ₀ : ℝ} {M_ph : ℕ}
    {B_bank : Finset (Fin M.k)} {S : ℕ → ℕ}
    (hC : 1 ≤ C) (hMph : 1 ≤ M_ph) (hδ₀ : 0 < δ₀)
    (hSBM : BoundedSuffixMacroBank M C M_ph δ₀ B_bank S)
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    MachineCrux M C (δ₀ / (4 * (((B_bank.card + 1) ^ (M_ph - 1) : ℕ) : ℝ))) := by
  intro D η hη
  obtain ⟨d_suf, hd_suf⟩ := hSBM
  have hK₀_pos : 1 ≤ (B_bank.card + 1) ^ (M_ph - 1) := Nat.one_le_pow _ _ (by omega)
  obtain ⟨d_asymp, hd_asymp⟩ := crux_bound_of_suffix_card_bound
    ((B_bank.card + 1) ^ (M_ph - 1))
    ((M_ph + 1) + M_ph * (((B_bank.card + 1) ^ (M_ph - 1)) *
      (2 * ((B_bank.card + 1) ^ (M_ph - 1)))))
    ((M.k + 2) ^ D * (M.k + M_ph + M_ph * (((B_bank.card + 1) ^ (M_ph - 1)) *
      ((2 * ((B_bank.card + 1) ^ (M_ph - 1))) * (M_ph * (D + 1))))))
    hK₀_pos hC hδ₀ hη hS
  refine ⟨max d_suf (max d_asymp 1), fun d hd I hI m E hE => ?_⟩
  have hd_ge_suf : d_suf ≤ d := (le_max_left _ _).trans hd
  have hd_ge_asymp : d_asymp ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hd1 : 1 ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
  have hb1 : 1 ≤ entryBits d := one_le_entryBits d
  obtain ⟨T, Γ, hobl, hT, hlen, hpath, rfl⟩ := hI
  obtain ⟨t_suf, R_suf, ht_suf, happ, ⟨a, ha0, haM, ha, hin, hbank⟩, hwork, hR_card, hno_pre⟩ :=
    hd_suf d hd_ge_suf T hobl hT
  obtain ⟨S_ind, hInd, hcard_nat⟩ := suffixMacroBank_independent_exists hMph hd1 hb1 ht_suf happ
    hlen hpath ha0 haM ha hin hbank hwork hno_pre
  exact hd_asymp d hd_ge_asymp T R_suf.card S_ind.card m hT hR_card hcard_nat
    (indexCode_length_ge_of_independent hE hInd)

/-- **Theorem B, suffix form (`suffixMacroBank_excludes`)**: no machine satisfying
`BoundedSuffixMacroBank` with `δ₀ > 0` and `S(d) / (d² entryBits(d)) → 0` can transpose in
oblivious linear time. -/
theorem suffixMacroBank_excludes {M : TM} {C δ₀ : ℝ} {M_ph : ℕ}
    {B_bank : Finset (Fin M.k)} {S : ℕ → ℕ}
    (hC : 1 ≤ C) (hMph : 1 ≤ M_ph) (hδ₀ : 0 < δ₀)
    (hSBM : BoundedSuffixMacroBank M C M_ph δ₀ B_bank S)
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ T : ℕ, ¬ ObliviousLinTime M d (entryBits d) C T := by
  have hcrux := suffixMacroBank_has_crux hC hMph hδ₀ hSBM hS
  set K₀ : ℝ := (((B_bank.card + 1) ^ (M_ph - 1) : ℕ) : ℝ)
  have hK₀_pos : (0 : ℝ) < K₀ := by positivity
  refine machine_crux_excludes hC (ε := δ₀ / (8 * K₀)) (ρ := δ₀ / (4 * K₀)) (by positivity) ?_
    (hcrux _)
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ## §5. Whole-Run `BoundedMacroBank` Corollaries (`δ₀ = 1` Specialization) -/

/-- **Theorem B (`boundedMacroBank_has_crux`)**: every machine in Class BM with sublinear workspace
cell bound `S(d) / (d² entryBits(d)) → 0` satisfies the depth-independent machine crux
`MachineCrux M C (1 / (4 * K₀))`, where `K₀ = (B_bank.card + 1) ^ (M_ph - 1)`: the `δ₀ = 1` case of
`suffixMacroBank_has_crux`. -/
theorem boundedMacroBank_has_crux {M : TM} {C : ℝ} {M_ph : ℕ} {B_bank : Finset (Fin M.k)}
    {S : ℕ → ℕ} (hC : 1 ≤ C) (hMph : 1 ≤ M_ph)
    (hBM : BoundedMacroBank M C M_ph B_bank S)
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    MachineCrux M C (1 / (4 * (((B_bank.card + 1) ^ (M_ph - 1) : ℕ) : ℝ))) :=
  suffixMacroBank_has_crux hC hMph one_pos (boundedSuffixMacroBank_of_boundedMacroBank hBM) hS

/-- **Theorem B (`boundedMacroBank_excludes`)**: no machine in Class BM with sublinear workspace
cell bound `S(d) / (d² entryBits(d)) → 0` can transpose in oblivious linear time: the `δ₀ = 1` case
of `suffixMacroBank_excludes`. -/
theorem boundedMacroBank_excludes {M : TM} {C : ℝ} {M_ph : ℕ} {B_bank : Finset (Fin M.k)}
    {S : ℕ → ℕ} (hC : 1 ≤ C) (hMph : 1 ≤ M_ph)
    (hBM : BoundedMacroBank M C M_ph B_bank S)
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ T : ℕ, ¬ ObliviousLinTime M d (entryBits d) C T :=
  suffixMacroBank_excludes hC hMph one_pos (boundedSuffixMacroBank_of_boundedMacroBank hBM) hS

end NativeRelations
