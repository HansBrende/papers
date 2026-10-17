import Transpose.Tape.CEMain
import Transpose.Tape.CEEquiv
import Transpose.Tape.CEProfile
import Transpose.Tape.CESweep
import Transpose.Tape.CEForms
import Transpose.Tape.CEHint
import Transpose.Tape.CoarseTrace

/-!
# The rungs of the ladder: weaker sufficient conditions for ¬(T)

* `O(n)`-bit oracle hints suffice: `hintCodes_linear_of_linearTimeTransposable` (a fast transposer
  gives hint codes with an `O(n)`-bit hint, not `O(n w)`; `hintCodes_of_linearTimeTransposable` is its
  `O(n w)` corollary), `hintLinear_iff_coentLinear` and `not_linearTimeTransposable_of_noCode_hintLinear`.
* Infinitely many `n` at one superlinear level: `not_linearTimeTransposable_of_coent_io`
  (`NoCode_TM_coent_io`), `coent_io_of_coent`, `coent_io_nw_of_robustNoCode_io`; by a diagonal
  argument (`diag_io`) the single level is equivalent to the linear io family
  (`coentLinear_io_iff_exists_coent_io`; `coentLinear_io_of_robustNoCode_io`).
* `traceClass_coent_lt`: what each rung rules out (correct trace classes of fast machines have
  co-entropy `> m n`).
* `robustCE_TM_gamma_iff`, `robustCE_TM_gamma_per_iff`: the γ-form of robust CE_TM, with one `γ`
  or per constants, is `RobustNoCode_TM` (through `rate_lt`).
* The flow form at co-entropy `C n`: `robustCE_TM_lin_iff` (`RobustCE_TM_lin` is the linear rung),
  `not_linearTimeTransposable_of_robustCE_TM_lin`.

The reduction behind the linear rung (`codes_coent_on`), the output-at-end forms and the non-uniform
forms (`no_fast_transposer_of_coent`) are in `CoarseTrace.lean`.
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

variable {M : TM}

/-! ### `O(n)`-bit hints -/

/-- `L + 1 ≤ 2^{4n}` for `n ≥ 1`. -/
theorem succ_L_le (n : ℕ) (hn : 1 ≤ n) : n * n * entryBits n + 1 ≤ 2 ^ (4 * n) := by
  have hw : entryBits n ≤ n := entryBits_le_self hn
  calc n * n * entryBits n + 1 ≤ 2 ^ (3 * entryBits n + 1) := inputLength_succ_le n
    _ ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **(T) gives hint codes with an `O(n)`-bit hint** (not `O(n w)`). -/
theorem hintCodes_linear_of_linearTimeTransposable (h : LinearTimeTransposable) :
    ∃ (k G c C : ℕ), 1 ≤ G ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ (D : TSDiagram k) (hint : (Fin (n * n * entryBits n) → Bool) → ℕ) (codes : ℕ → NetCode),
        D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧
        (∀ x, hint x < 2 ^ (C * n)) ∧
        ∀ x, D.Solves n G (D.profileCap n G) {x} (codes (hint x)) := by
  obtain ⟨k, G, c, C, hG, n₀, hcodes⟩ := codes_coentLinear_of_linearTimeTransposable h
  refine ⟨k, G, c, C + 4, hG, max n₀ 1, fun n hn => ?_⟩
  obtain ⟨D, F, code, hDv, hDT, hco, hsol, -⟩ := hcodes n (le_trans (le_max_left _ _) hn)
  obtain ⟨hint, codes, hh, hsolx⟩ := hint_of_code D hsol hco
  refine ⟨D, hint, codes, hDv, hDT, fun x => ?_, hsolx⟩
  calc hint x < 2 ^ (C * n) * (n * n * entryBits n + 1) := hh x
    _ ≤ 2 ^ (C * n) * 2 ^ (4 * n) :=
        Nat.mul_le_mul_left _ (succ_L_le n (le_trans (le_max_right _ _) hn))
    _ = 2 ^ ((C + 4) * n) := by rw [← pow_add]; ring_nf

/-- **(T) gives hint codes with an `O(n w)`-bit hint**: a corollary of the `O(n)`-bit form. -/
theorem hintCodes_of_linearTimeTransposable (h : LinearTimeTransposable) :
    ∃ (k G c C : ℕ), 1 ≤ G ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ (D : TSDiagram k) (hint : (Fin (n * n * entryBits n) → Bool) → ℕ) (codes : ℕ → NetCode),
        D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧
        (∀ x, hint x < 2 ^ (C * n * entryBits n)) ∧
        ∀ x, D.Solves n G (D.profileCap n G) {x} (codes (hint x)) := by
  obtain ⟨k, G, c, C, hG, n₀, h⟩ := hintCodes_linear_of_linearTimeTransposable h
  refine ⟨k, G, c, C, hG, n₀, fun n hn => ?_⟩
  obtain ⟨D, hint, codes, hD, hT, hh, hs⟩ := h n hn
  have hb : 1 ≤ entryBits n := by unfold entryBits; omega
  exact ⟨D, hint, codes, hD, hT, fun x => lt_of_lt_of_le (hh x)
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hb)), hs⟩

/-- The linear hint rung is the linear co-entropy rung. -/
theorem hintLinear_iff_coentLinear :
    (∀ C : ℕ, NoCode_TM_hintBits (fun n => C * n)) ↔ ∀ C : ℕ, NoCode_TM_coent (fun n => C * n) := by
  constructor
  · intro h C
    refine coent_of_hintBits ⟨1, fun n hn => ?_⟩ (h (C + 4))
    have hw : entryBits n ≤ n := entryBits_le_self hn
    show C * n + 3 * entryBits n + 1 ≤ (C + 4) * n
    nlinarith
  · intro h C
    exact hintBits_of_coent (h C)

/-- **An `O(n)`-bit oracle hint suffices to refute (T).** -/
theorem not_linearTimeTransposable_of_noCode_hintLinear
    (h : ∀ C : ℕ, NoCode_TM_hintBits (fun n => C * n)) : ¬ LinearTimeTransposable :=
  not_linearTimeTransposable_of_coentLinear (hintLinear_iff_coentLinear.1 h)

/-! ### Infinitely many `n` -/

/-- The single-level io hypothesis implies the linear io family (no code at co-entropy `C n` for
infinitely many `n`, for every `C`): a set of co-entropy `≤ C n` has co-entropy `≤ f n` once
`C n ≤ f n`. -/
theorem coentLinear_io_of_coent_io {f : ℕ → ℕ}
    (hf : ∀ C : ℕ, ∃ N, ∀ n, N ≤ n → C * n ≤ f n) (h : NoCode_TM_coent_io f) (C : ℕ) :
    NoCode_TM_coent_io (fun n => C * n) := by
  intro k G c hG n₀
  obtain ⟨N, hN⟩ := hf C
  obtain ⟨n, hn, hno⟩ := h k G c hG (max n₀ N)
  refine ⟨n, le_trans (le_max_left _ _) hn, fun D hD hT F hF code => hno D hD hT F ?_ code⟩
  exact le_trans hF (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num)
    (hN n (le_trans (le_max_right _ _) hn))))

/-- **One superlinear co-entropy level, for infinitely many `n`**, refutes (T). (By `diag_io` this
single level is equivalent to the linear io family: `coentLinear_io_iff_exists_coent_io`.) -/
theorem not_linearTimeTransposable_of_coent_io {f : ℕ → ℕ}
    (hf : ∀ C : ℕ, ∃ N, ∀ n, N ≤ n → C * n ≤ f n) (h : NoCode_TM_coent_io f) :
    ¬ LinearTimeTransposable :=
  not_linearTimeTransposable_of_coentLinear_io fun k G c C hG n₀ =>
    coentLinear_io_of_coent_io hf h C k G c hG n₀

/-- The robust io target gives the io target at the level `n w`, which is superlinear. -/
theorem coent_io_nw_of_robustNoCode_io (h : RobustNoCode_TM_io) :
    NoCode_TM_coent_io (fun n => n * entryBits n) := by
  intro k G c hG n₀
  obtain ⟨n, hn, hno⟩ := h k G c 1 hG n₀
  exact ⟨n, hn, fun D hD hT F hF code => hno D hD hT F (by rwa [Nat.one_mul]) code⟩

/-- The robust io target implies the linear io target at every `C`. -/
theorem coentLinear_io_of_robustNoCode_io (h : RobustNoCode_TM_io) (C : ℕ) :
    NoCode_TM_coent_io (fun n => C * n) :=
  coentLinear_io_of_coent_io superlinear_nw (coent_io_nw_of_robustNoCode_io h) C

/-- The all-large-`n` single level implies the io single level. -/
theorem coent_io_of_coent {f : ℕ → ℕ} (h : NoCode_TM_coent f) : NoCode_TM_coent_io f := by
  intro k G c hG n₀
  obtain ⟨n₁, hn₁⟩ := h k G c hG
  exact ⟨max n₀ n₁, le_max_left _ _, hn₁ _ (le_max_right _ _)⟩

/-! ### What each rung rules out -/

/-- **What each rung of the ladder rules out.** Under `NoCode_TM_coent m`, for all large `n`, every
trace class on which a machine (`k` tapes, alphabet `g + 1`, at most `2^{C₁ n w}` states, time
`≤ c L`) is correct has `2^{m n} |F| < 2^L`. -/
theorem traceClass_coent_lt {m : ℕ → ℕ} (h : NoCode_TM_coent m) (k g c C₁ : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ M : TM, M.k = k → M.g = g →
      Nat.clog 2 (M.q + 1) ≤ C₁ * (n * entryBits n) →
      ∀ (T : ℕ), T ≤ c * (n * n * entryBits n) → ∀ (F : Set (List Bool)) (w₀ : List Bool),
        TraceClass M n (entryBits n) (slotLen M n) T F w₀ → ClassCorrect M n (entryBits n) T F →
        2 ^ m n * F.ncard < 2 ^ (n * n * entryBits n) := by
  set Gk := max 1 (Nat.clog 2 (g + 1)) with hGk
  obtain ⟨n₁, hn₁⟩ := h (k + (C₁ + 1)) Gk c (le_max_left _ _)
  refine ⟨max n₁ (slotSize k c), fun n hn M hk hg hq T hT F w₀ hF hcorr => ?_⟩
  subst hk
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hG : cellBits M = Gk := by unfold cellBits; rw [hg]
  have hpos := pos_bits_le (le_trans (le_max_right _ _) hn) hT
  have hrG := slotLen_mul_ge M n
  have hr := one_le_slotLen M hn1
  have hs : Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1) ≤
      (C₁ + 1) * (slotLen M n * cellBits M) := by
    have : (C₁ + 1) * (n * entryBits n) ≤ (C₁ + 1) * (slotLen M n * cellBits M) :=
      Nat.mul_le_mul_left _ hrG
    nlinarith
  obtain ⟨code, hDv, hsol⟩ := code_bits_of_class hn1 le_rfl hF hcorr
  have hsol' := solves_profileCap_addTapes (a := C₁ + 1) hr hs hsol
  have hFm : F ⊆ matrixInputs n (entryBits n) := fun w hw => (hF.2 w hw).1
  by_contra hcon
  push Not at hcon
  rw [hG] at hsol'
  exact hn₁ n (le_trans (le_max_left _ _) hn) (addTapes (runDiagram M w₀ T) (C₁ + 1))
    (valid_addTapes _ hDv _) (by rw [T_addTapes]; exact hT) {v | List.ofFn v ∈ F}
    (by rw [ncard_ofFn_preimage hFm]; exact hcon) code hsol'

/-! ### The γ-form -/

theorem gamma_of_robustNoCode (h : RobustNoCode_TM) : RobustCE_TM_gamma := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun ε hε => ?_, fun k G c C hG => ?_⟩
  · obtain ⟨K, hK⟩ := exists_nat_ge (1 / ε)
    refine ⟨2 ^ K, fun n hn => ?_⟩
    have hKw : (K : ℝ) ≤ entryBits n := by exact_mod_cast le_entryBits_of_two_pow_le hn
    have : 1 / ε ≤ entryBits n := le_trans hK hKw
    rw [div_le_iff₀ hε] at this
    linarith
  · obtain ⟨n₀, hn₀⟩ := h k G c C hG
    exact ⟨n₀, fun n hn D hD hT _ hcap F hF code hsol =>
      absurd (solves_mono D (le_profileCap D hcap) hsol) (hn₀ n hn D hD hT F hF code)⟩

theorem gamma_per_of_gamma (h : RobustCE_TM_gamma) : RobustCE_TM_gamma_per := by
  obtain ⟨γ, hγpos, hγ, hroute⟩ := h
  exact fun k G c C hG => ⟨γ, hγpos, hγ, hroute k G c C hG⟩

/-- The per-constant γ-form gives no code: a routing at rate `1/γ(n)` with `γ(n) ≤ w/(2E)` would
beat the rate bound `E/w` (`rate_lt`). -/
theorem robustNoCode_of_gamma_per (h : RobustCE_TM_gamma_per) : RobustNoCode_TM := by
  intro k G c C hG
  obtain ⟨γ, hγpos, hγ, n₀, hn₀⟩ := h k G c C hG
  have hEpos : (0 : ℝ) < ceE k G c := by exact_mod_cast one_le_ceE k G c hG
  obtain ⟨N, hN⟩ := hγ (1 / (2 * ceE k G c)) (by positivity)
  refine ⟨max (max n₀ N) (ceSize k G c C), fun n hn D hD hT F hF code hsol => ?_⟩
  have hcap := capProfile_profileCap D n G
  obtain ⟨ρ, hρ⟩ := hn₀ n (le_of_max_le_left (le_of_max_le_left hn)) D hD hT _ hcap F hF code hsol
  have hr := rate_lt hG (le_of_max_le_right hn) hD hT hcap (unattached_le hF hsol) hρ
  have hγn := hN n (le_of_max_le_right (le_of_max_le_left hn))
  have hw : (0 : ℝ) < entryBits n := by
    exact_mod_cast (show 1 ≤ entryBits n by unfold entryBits; omega)
  have hg := hγpos n
  rw [div_lt_div_iff₀ hg hw, one_mul] at hr
  have : γ n * ceE k G c ≤ entryBits n / 2 := by
    have := mul_le_mul_of_nonneg_right hγn hEpos.le
    rw [show 1 / (2 * (ceE k G c : ℝ)) * entryBits n * ceE k G c = entryBits n / 2 by
      field_simp] at this
    linarith
  linarith

theorem robustNoCode_of_gamma (h : RobustCE_TM_gamma) : RobustNoCode_TM :=
  robustNoCode_of_gamma_per (gamma_per_of_gamma h)

theorem robustCE_TM_gamma_iff : RobustCE_TM_gamma ↔ RobustNoCode_TM :=
  ⟨robustNoCode_of_gamma, gamma_of_robustNoCode⟩

/-- **The per-constant γ-form is also `RobustNoCode_TM`.** -/
theorem robustCE_TM_gamma_per_iff : RobustCE_TM_gamma_per ↔ RobustNoCode_TM :=
  ⟨robustNoCode_of_gamma_per, fun h => gamma_per_of_gamma (gamma_of_robustNoCode h)⟩

/-! ### The flow form at co-entropy `C n` -/

theorem coentLinear_of_robustCE_TM_lin (h : RobustCE_TM_lin) :
    ∀ C : ℕ, NoCode_TM_coent (fun n => C * n) := by
  intro C k G c hG
  have hE := one_le_ceE k G c hG
  obtain ⟨n₀, hn₀⟩ := h k G c C hG (1 / (ceE k G c : ℝ)) (by positivity)
  refine ⟨max (max n₀ (ceSize k G c C)) 1, fun n hn D hD hT F hF code hsol => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hb1 : 1 ≤ entryBits n := by unfold entryBits; omega
  have hcap := capProfile_profileCap D n G
  have hF' : 2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard :=
    le_trans hF (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num)
      (Nat.le_mul_of_pos_right _ hb1)))
  obtain ⟨ρ, hρ⟩ := hn₀ n (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)) D hD hT _
    hcap F hF code hsol
  exact not_dist_of_gap hE
    (dist_gap hG (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)) hD hT hcap hF' hsol)
    (dist_of_routes (by positivity) hρ)

/-- **The flow form at co-entropy `C n` is the linear rung**: the converse holds vacuously. -/
theorem robustCE_TM_lin_iff : RobustCE_TM_lin ↔ ∀ C : ℕ, NoCode_TM_coent (fun n => C * n) := by
  refine ⟨coentLinear_of_robustCE_TM_lin, fun h k G c C hG ε _ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h C k G c hG
  exact ⟨n₀, fun n hn D hD hT _ hcap F hF code hsol =>
    absurd (solves_mono D (le_profileCap D hcap) hsol) (hn₀ n hn D hD hT F hF code)⟩

theorem not_linearTimeTransposable_of_robustCE_TM_lin (h : RobustCE_TM_lin) :
    ¬ LinearTimeTransposable :=
  not_linearTimeTransposable_of_coentLinear (coentLinear_of_robustCE_TM_lin h)


/-! ### The single io level and the linear io family are equivalent -/

/-- **A diagonal lemma**: if for every index `i` and every `C` some `n ≥ n₀` has `Q i n (C n)`,
with `Q` antitone in the level, then a single level `f`, eventually above every `C n`, has
`Q i n (f n)` for infinitely many `n`, for every `i` (the indices being enumerated with infinite
repetition by `e`). -/
theorem diag_io {ι : Type} (e : ℕ → ι) (he : ∀ i n₀, ∃ s, n₀ ≤ s ∧ e s = i)
    (Q : ι → ℕ → ℕ → Prop)
    (hanti : ∀ i n m m', m ≤ m' → Q i n m' → Q i n m)
    (h : ∀ i C n₀, ∃ n, n₀ ≤ n ∧ Q i n (C * n)) :
    ∃ f : ℕ → ℕ, (∀ C : ℕ, ∃ N, ∀ n, N ≤ n → C * n ≤ f n) ∧
      ∀ i n₀, ∃ n, n₀ ≤ n ∧ Q i n (f n) := by
  classical
  choose nxt hnxt using fun s b => h (e s) s b
  obtain ⟨pts, hpts0, hptsS⟩ : ∃ pts : ℕ → ℕ, pts 0 = nxt 0 0 ∧
      ∀ s, pts (s + 1) = nxt (s + 1) (pts s + 1) :=
    ⟨fun s => Nat.rec (motive := fun _ => ℕ) (nxt 0 0) (fun s p => nxt (s + 1) (p + 1)) s,
      rfl, fun s => rfl⟩
  have hQ : ∀ s, Q (e s) (pts s) (s * pts s) := by
    intro s
    cases s with
    | zero => rw [hpts0]; exact (hnxt 0 0).2
    | succ s => rw [hptsS]; exact (hnxt (s + 1) (pts s + 1)).2
  have hlt : ∀ s, pts s < pts (s + 1) := fun s => by
    rw [hptsS]; exact (hnxt (s + 1) (pts s + 1)).1
  have hmono : StrictMono pts := strictMono_nat_of_lt_succ hlt
  have hge : ∀ s, s ≤ pts s := fun s => hmono.id_le s
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℕ → ℕ, ∀ n, Cf n = Nat.findGreatest (fun s : ℕ => pts s ≤ n) n :=
    ⟨_, fun n => rfl⟩
  refine ⟨fun n => Cf n * n, fun C₀ => ⟨pts C₀, fun n hn => ?_⟩, fun i n₀ => ?_⟩
  · have : C₀ ≤ Cf n := by
      rw [hCf]; exact Nat.le_findGreatest (le_trans (hge C₀) hn) hn
    exact Nat.mul_le_mul_right n this
  · obtain ⟨s, hs, hes⟩ := he i n₀
    refine ⟨pts s, le_trans hs (hge s), ?_⟩
    have hCs : Cf (pts s) ≤ s := by
      by_contra hcon
      push Not at hcon
      have hspec : pts (Cf (pts s)) ≤ pts s := by
        rw [hCf]
        exact Nat.findGreatest_spec (P := fun s' : ℕ => pts s' ≤ pts s) (hge s) le_rfl
      exact absurd hspec (not_le.2 (hmono hcon))
    have := hQ s
    rw [hes] at this
    exact hanti i (pts s) _ _ (Nat.mul_le_mul_right _ hCs) this

/-- The linear io family, spelled out, gives a single superlinear io level. -/
theorem newIoHyp_of_oldIoHyp
    (H : ∀ (k G c C : ℕ), 1 ≤ G → ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n) * F.ncard →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code) :
    ∃ f : ℕ → ℕ, (∀ C : ℕ, ∃ N, ∀ n, N ≤ n → C * n ≤ f n) ∧ NoCode_TM_coent_io f := by
  let Q : ℕ × ℕ × ℕ → ℕ → ℕ → Prop := fun i n m =>
    1 ≤ i.2.1 →
    ∀ (D : TSDiagram i.1), D.Valid (n * n * entryBits n) → D.T ≤ i.2.2 * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ m * F.ncard →
      ∀ code : NetCode, ¬ D.Solves n i.2.1 (D.profileCap n i.2.1) F code
  let e : ℕ → ℕ × ℕ × ℕ := fun s =>
    ((Nat.unpair (Nat.unpair s).1).1, (Nat.unpair (Nat.unpair (Nat.unpair s).1).2).1,
      (Nat.unpair (Nat.unpair (Nat.unpair s).1).2).2)
  have he : ∀ i n₀, ∃ s, n₀ ≤ s ∧ e s = i := by
    rintro ⟨k, G, c⟩ n₀
    exact ⟨Nat.pair (Nat.pair k (Nat.pair G c)) n₀, Nat.right_le_pair _ _, by
      simp [e, Nat.unpair_pair]⟩
  have hanti : ∀ i n m m', m ≤ m' → Q i n m' → Q i n m := by
    intro i n m m' hm hQ hG D hD hT F hF code
    exact hQ hG D hD hT F
      (le_trans hF (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hm))) code
  have hQ : ∀ i C n₀, ∃ n, n₀ ≤ n ∧ Q i n (C * n) := by
    rintro ⟨k, G, c⟩ C n₀
    by_cases hG : 1 ≤ G
    · obtain ⟨n, hn, hno⟩ := H k G c C hG n₀
      exact ⟨n, hn, fun _ => hno⟩
    · exact ⟨n₀, le_rfl, fun h1 => absurd h1 hG⟩
  obtain ⟨f, hf, hio⟩ := diag_io e he Q hanti hQ
  refine ⟨f, hf, fun k G c hG n₀ => ?_⟩
  obtain ⟨n, hn, hq⟩ := hio (k, G, c) n₀
  exact ⟨n, hn, hq hG⟩

/-- **The linear io family implies the single-level io hypothesis** (by `diag_io`). -/
theorem exists_coent_io_of_coentLinear_io (H : ∀ C : ℕ, NoCode_TM_coent_io (fun n => C * n)) :
    ∃ f : ℕ → ℕ, (∀ C : ℕ, ∃ N, ∀ n, N ≤ n → C * n ≤ f n) ∧ NoCode_TM_coent_io f :=
  newIoHyp_of_oldIoHyp fun k G c C hG n₀ => H C k G c hG n₀

/-- **The single superlinear io level is equivalent to the linear io family.** -/
theorem coentLinear_io_iff_exists_coent_io :
    (∀ C : ℕ, NoCode_TM_coent_io (fun n => C * n)) ↔
      ∃ f : ℕ → ℕ, (∀ C : ℕ, ∃ N, ∀ n, N ≤ n → C * n ≤ f n) ∧ NoCode_TM_coent_io f :=
  ⟨exists_coent_io_of_coentLinear_io, fun ⟨_, hf, h⟩ C => coentLinear_io_of_coent_io hf h C⟩

end Transpose.Tape.Impl
