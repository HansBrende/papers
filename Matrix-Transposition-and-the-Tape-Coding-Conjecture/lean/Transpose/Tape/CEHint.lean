import Transpose.Tape.CEMain

/-!
# Robust versus plain: the robust target is the plain target with an oracle hint

A **hint code** with `2^s` hint values is a family of causal codes `codes h` together with a function
`hint` of the whole input such that, on every input `x`, the code `codes (hint x)` solves complete
exchange. It models an oracle coordinator that sees the whole input and tells every node `s` bits;
the hint is uncharged (no edge carries it and no node computes it). Per diagram and capacities
(TM-free):
* `code_of_hint`: a hint code with `2^s` hint values gives a code on a set of co-entropy `s` (the
  most popular hint value);
* `hint_of_code`: a code on a set `F` of co-entropy `m` gives a hint code with `2^m (L + 1)` hint
  values. A code for `F` is a code for every shift of `F` (`solves_shiftCode`), and `2^m (L + 1)`
  shifts of `F` cover every input (`exists_shift_cover`, by counting).

Hence `robustNoCode_iff_hint`: `RobustNoCode_TM ⟺ NoCode_TM_hint`. With `noCode_bits_iff` (a side
channel of `O(n w)` bits per memory edge, whose contents the code computes itself, is free for
independent sources), this locates the gap between the plain and the robust target exactly: an
`O(n w)`-bit broadcast supplied by an oracle rather than computed by the network. Timing alone is not
the issue: after a prepended input sweep every row is read before the original diagram starts
(`row_mem_prefix`, `PlainRobust/CEPrefix.lean`).
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-! ### Shifting a code -/

/-- The vector `x` shifted by `z`. -/
def xorVec {L : ℕ} (x z : Fin L → Bool) : Fin L → Bool := fun d => xor (x d) (z d)

theorem xorVec_xorVec_left {L : ℕ} (x y : Fin L → Bool) : xorVec x (xorVec x y) = y := by
  funext d; simp only [xorVec]; cases x d <;> cases y d <;> rfl

/-- The bit of `z` at position `d` (`false` beyond `L`). -/
def zbit {L : ℕ} (z : Fin L → Bool) (d : ℕ) : Bool := if h : d < L then z ⟨d, h⟩ else false

/-- Transposing positions twice is the identity. -/
theorem tpos_tpos {n b d : ℕ} (hd : d < n * n * b) : tpos n b (tpos n b d) = d := by
  obtain ⟨hi, hj, ht, hdec⟩ := pos_decomp hd
  have h1 := tpos_spec (i := d / b / n) hj ht
  rw [← hdec] at h1
  rw [h1, tpos_spec hi ht]
  exact hdec.symm

section Shift

variable {k : ℕ} (D : TSDiagram k)

/-- The visible input `v` of node `y`, shifted by `z` on the rows attached at `y`. -/
noncomputable def shiftVis (n w r y : ℕ) {L : ℕ} (z : Fin L → Bool) (v : ℕ → Bool) : ℕ → Bool :=
  fun d => if d / (n * w) ∈ D.rowsAt n w r y then xor (v d) (zbit z d) else v d

theorem shiftVis_visible (n w r y : ℕ) {L : ℕ} (x z : Fin L → Bool) :
    shiftVis D n w r y z (D.visible n w r y x) = D.visible n w r y (xorVec x z) := by
  funext d
  simp only [shiftVis, TSDiagram.visible, zbit, xorVec]
  by_cases hd : d < L <;> by_cases hrow : d / (n * w) ∈ D.rowsAt n w r y <;> simp [hd, hrow]

/-- **The shifted code**: `C` run on the input shifted by `z`. Each node shifts its visible rows by
`z`, and each output bit is shifted back by the bit of `z` that it transposes. -/
noncomputable def shiftCode (n w r : ℕ) {L : ℕ} (C : NetCode) (z : Fin L → Bool) : NetCode where
  enc e f v := C.enc e f (shiftVis D n w r e.1 z v)
  dec o f v := xor (C.dec o f (shiftVis D n w r (D.outNode r o) z v)) (zbit z (tpos n w o))

/-- **A code for `F` is a code for every shift of `F`**, within the same capacities. -/
theorem solves_shiftCode {n G : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {C : NetCode} (hsol : D.Solves n G cap F C)
    (z : Fin (n * n * entryBits n) → Bool) :
    D.Solves n G cap {x | xorVec x z ∈ F} (shiftCode D n (entryBits n) (blockSize G n) C z) := by
  intro x hx
  have hin : ∀ v, (shiftCode D n (entryBits n) (blockSize G n) C z).inVals
      (D.edges (blockSize G n)) (fun y => D.visible n (entryBits n) (blockSize G n) y x) v =
      C.inVals (D.edges (blockSize G n))
        (fun y => D.visible n (entryBits n) (blockSize G n) y (xorVec x z)) v := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
    funext e
    rw [inVals_eq, inVals_eq]
    by_cases h : e ∈ D.edges (blockSize G n) ∧ e.2 = v ∧ e.1 < v
    · rw [ite_eq_left h, ite_eq_left h]
      show C.enc e _ (shiftVis D n (entryBits n) (blockSize G n) e.1 z _) = _
      rw [ih e.1 h.2.2, shiftVis_visible]
    · rw [ite_eq_right h, ite_eq_right h]
  obtain ⟨hedge, hout⟩ := hsol (xorVec x z) hx
  refine ⟨fun e he => ?_, fun d hd => ?_⟩
  · show C.enc e _ (shiftVis D n (entryBits n) (blockSize G n) e.1 z _) < _
    rw [hin e.1, shiftVis_visible]
    exact hedge e he
  · show xor (C.dec _ _ (shiftVis D n (entryBits n) (blockSize G n) _ z _)) _ = _
    rw [hin, shiftVis_visible, tpos_tpos hd]
    have h1 := hout d hd
    simp only [NetCode.outVal] at h1
    rw [h1]
    simp only [xorVec, zbit, hd, ↓reduceDIte]
    cases x ⟨d, hd⟩ <;> cases z ⟨d, hd⟩ <;> rfl

/-- `Solves` on a set is `Solves` at each of its points. -/
theorem solves_iff_forall_singleton {n G : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {C : NetCode} :
    D.Solves n G cap F C ↔ ∀ x ∈ F, D.Solves n G cap {x} C := by
  constructor
  · intro h x hx y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h y hx
  · intro h x hx
    exact h x hx x (Set.mem_singleton x)

end Shift

/-! ### Covering by shifts -/

/-- `2 M^{M+1} ≤ (M + 1)^{M+1}` (Bernoulli's inequality). -/
theorem two_mul_pow_le (M : ℕ) : 2 * M ^ (M + 1) ≤ (M + 1) ^ (M + 1) := by
  rcases Nat.eq_zero_or_pos M with h | hM
  · subst h; norm_num
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have h0 : (0 : ℚ) ≤ 1 / (M : ℚ) := by positivity
  have hb := one_add_mul_le_pow (show (-2 : ℚ) ≤ 1 / (M : ℚ) by linarith) (M + 1)
  have hsum : (1 : ℚ) + ((M + 1 : ℕ) : ℚ) * (1 / (M : ℚ)) = 2 + 1 / (M : ℚ) := by
    push_cast; field_simp; ring
  have h2 : (2 : ℚ) ≤ (1 + 1 / (M : ℚ)) ^ (M + 1) := by linarith
  have h3 : (1 + 1 / (M : ℚ)) ^ (M + 1) * (M : ℚ) ^ (M + 1) = ((M : ℚ) + 1) ^ (M + 1) := by
    rw [← mul_pow]; congr 1; field_simp
  have h4 : (2 : ℚ) * (M : ℚ) ^ (M + 1) ≤ ((M : ℚ) + 1) ^ (M + 1) := by
    rw [← h3]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
  exact_mod_cast h4

/-- The count behind the covering: `2^L (a - f)^K < a^K` for `K = N (L + 1)`, when `f ≤ a ≤ N f`
and `1 ≤ a`. -/
theorem cover_count {a f N L : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a) (hfa : f ≤ a) (haf : a ≤ N * f) :
    2 ^ L * (a - f) ^ (N * (L + 1)) < a ^ (N * (L + 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨g, rfl⟩ : ∃ g, a = f + g := ⟨a - f, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have h1 : (M + 1) * g ≤ M * (f + g) := by nlinarith
  have h2 : ((M + 1) * g) ^ ((M + 1) * (L + 1)) ≤ (M * (f + g)) ^ ((M + 1) * (L + 1)) :=
    Nat.pow_le_pow_left h1 _
  rw [mul_pow, mul_pow] at h2
  have h3 : 2 ^ (L + 1) * M ^ ((M + 1) * (L + 1)) ≤ (M + 1) ^ ((M + 1) * (L + 1)) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (two_mul_pow_le M) _
  have hpos : 0 < (M + 1) ^ ((M + 1) * (L + 1)) := by positivity
  have h4 : (M + 1) ^ ((M + 1) * (L + 1)) * (2 ^ (L + 1) * g ^ ((M + 1) * (L + 1))) ≤
      (M + 1) ^ ((M + 1) * (L + 1)) * (f + g) ^ ((M + 1) * (L + 1)) := by
    calc (M + 1) ^ ((M + 1) * (L + 1)) * (2 ^ (L + 1) * g ^ ((M + 1) * (L + 1)))
        = 2 ^ (L + 1) * ((M + 1) ^ ((M + 1) * (L + 1)) * g ^ ((M + 1) * (L + 1))) := by ring
      _ ≤ 2 ^ (L + 1) * (M ^ ((M + 1) * (L + 1)) * (f + g) ^ ((M + 1) * (L + 1))) :=
          Nat.mul_le_mul_left _ h2
      _ = (2 ^ (L + 1) * M ^ ((M + 1) * (L + 1))) * (f + g) ^ ((M + 1) * (L + 1)) := by ring
      _ ≤ (M + 1) ^ ((M + 1) * (L + 1)) * (f + g) ^ ((M + 1) * (L + 1)) :=
          Nat.mul_le_mul_right _ h3
  have h5 := Nat.le_of_mul_le_mul_left h4 hpos
  have h6 : 1 ≤ (f + g) ^ ((M + 1) * (L + 1)) := Nat.one_le_pow _ _ ha
  have h7 : 2 * (2 ^ L * g ^ ((M + 1) * (L + 1))) ≤ (f + g) ^ ((M + 1) * (L + 1)) := by
    calc 2 * (2 ^ L * g ^ ((M + 1) * (L + 1))) = 2 ^ (L + 1) * g ^ ((M + 1) * (L + 1)) := by ring
      _ ≤ _ := h5
  omega

/-- **Shifts of a large set cover everything**: if `2^L ≤ 2^m |F|`, then some `2^m (L + 1)` shifts
of `F` cover every vector of length `L`. (Counting: the tuples of shifts that miss a given vector
number `(2^L - |F|)^K`, and `2^L (2^L - |F|)^K < (2^L)^K`.) -/
theorem exists_shift_cover {L m : ℕ} (F : Set (Fin L → Bool)) (hF : 2 ^ L ≤ 2 ^ m * F.ncard) :
    ∃ z : Fin (2 ^ m * (L + 1)) → (Fin L → Bool), ∀ x, ∃ i, xorVec x (z i) ∈ F := by
  classical
  by_contra hcon
  push Not at hcon
  -- the shifts that miss `x`
  let S : (Fin L → Bool) → Finset (Fin L → Bool) :=
    fun x => Finset.univ.filter (fun y => xorVec x y ∉ F)
  have hsub : (Finset.univ : Finset (Fin (2 ^ m * (L + 1)) → (Fin L → Bool))) ⊆
      Finset.univ.biUnion (fun x => Fintype.piFinset (fun _ : Fin (2 ^ m * (L + 1)) => S x)) := by
    intro z _
    obtain ⟨x, hx⟩ := hcon z
    exact Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _,
      Fintype.mem_piFinset.2 (fun i => Finset.mem_filter.2 ⟨Finset.mem_univ _, hx i⟩)⟩
  have hcardV : Fintype.card (Fin L → Bool) = 2 ^ L := by simp
  have hFcard : F.ncard = (Finset.univ.filter (· ∈ F)).card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext y; simp
  have hFle : F.ncard ≤ 2 ^ L := by
    rw [hFcard, ← hcardV]; exact Finset.card_le_univ _
  have hcardS : ∀ x, (S x).card = 2 ^ L - F.ncard := by
    intro x
    have hbij : (S x).card = (Finset.univ.filter (fun y : Fin L → Bool => y ∉ F)).card := by
      apply Finset.card_bij' (fun y _ => xorVec x y) (fun u _ => xorVec x u)
      · intro y hy
        simp only [S, Finset.mem_filter] at hy ⊢
        exact ⟨Finset.mem_univ _, hy.2⟩
      · intro u hu
        simp only [S, Finset.mem_filter] at hu ⊢
        exact ⟨Finset.mem_univ _, by rw [xorVec_xorVec_left]; exact hu.2⟩
      · intro y _; exact xorVec_xorVec_left x y
      · intro u _; exact xorVec_xorVec_left x u
    rw [hbij, hFcard]
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin L → Bool)))
      (fun y => y ∈ F)
    rw [Finset.card_univ, hcardV] at this
    omega
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin L → Bool)))
    (t := fun x => Fintype.piFinset (fun _ : Fin (2 ^ m * (L + 1)) => S x))
  have hU : (Finset.univ : Finset (Fin (2 ^ m * (L + 1)) → (Fin L → Bool))).card =
      (2 ^ L) ^ (2 ^ m * (L + 1)) := by
    rw [Finset.card_univ, Fintype.card_fun, hcardV, Fintype.card_fin]
  have hT : ∑ x : Fin L → Bool, (Fintype.piFinset (fun _ : Fin (2 ^ m * (L + 1)) => S x)).card =
      2 ^ L * (2 ^ L - F.ncard) ^ (2 ^ m * (L + 1)) := by
    rw [Finset.sum_congr rfl (fun x _ => by rw [Fintype.card_piFinset_const, hcardS x]),
      Finset.sum_const, Finset.card_univ, hcardV, smul_eq_mul]
  have h3 := cover_count (L := L) (N := 2 ^ m) Nat.one_le_two_pow Nat.one_le_two_pow hFle hF
  rw [hT] at h2
  rw [hU] at h1
  omega

/-! ### Hint codes and codes on large sets -/

section Hint

variable {k : ℕ} (D : TSDiagram k)

/-- **A code on a large set gives a hint code**: if `C` solves complete exchange on `F` with
`2^L ≤ 2^m |F|`, then shifted copies of `C`, indexed by a hint `< 2^m (L + 1)` (the first shift
taking the input into `F`), solve it on every input, within the same capacities. -/
theorem hint_of_code {n G : ℕ} {cap : ℕ × ℕ → ℕ} {F : Set (Fin (n * n * entryBits n) → Bool)}
    {C : NetCode} {m : ℕ} (hsol : D.Solves n G cap F C)
    (hF : 2 ^ (n * n * entryBits n) ≤ 2 ^ m * F.ncard) :
    ∃ (hint : (Fin (n * n * entryBits n) → Bool) → ℕ) (codes : ℕ → NetCode),
      (∀ x, hint x < 2 ^ m * (n * n * entryBits n + 1)) ∧
      ∀ x, D.Solves n G cap {x} (codes (hint x)) := by
  classical
  obtain ⟨z, hz⟩ := exists_shift_cover F hF
  choose i hi using hz
  refine ⟨fun x => (i x).1, fun j => if h : j < 2 ^ m * (n * n * entryBits n + 1) then
    shiftCode D n (entryBits n) (blockSize G n) C (z ⟨j, h⟩) else C, fun x => (i x).2,
    fun x => ?_⟩
  show D.Solves n G cap {x} (if h : (i x).1 < 2 ^ m * (n * n * entryBits n + 1) then
    shiftCode D n (entryBits n) (blockSize G n) C (z ⟨(i x).1, h⟩) else C)
  rw [dite_eq_left (i x).2]
  exact (solves_iff_forall_singleton D).1 (solves_shiftCode D hsol (z (i x))) x (hi x)

/-- **A hint code gives a code on a large set**: if codes indexed by a hint `< 2^s` solve complete
exchange on every input, then the code of the most popular hint value solves it on a set `F` with
`2^L ≤ 2^s |F|`, within the same capacities. -/
theorem code_of_hint {n G : ℕ} {cap : ℕ × ℕ → ℕ} {s : ℕ}
    (hint : (Fin (n * n * entryBits n) → Bool) → ℕ) (codes : ℕ → NetCode)
    (hh : ∀ x, hint x < 2 ^ s) (hsol : ∀ x, D.Solves n G cap {x} (codes (hint x))) :
    ∃ (F : Set (Fin (n * n * entryBits n) → Bool)) (C : NetCode),
      2 ^ (n * n * entryBits n) ≤ 2 ^ s * F.ncard ∧ D.Solves n G cap F C := by
  classical
  have hcardV : Fintype.card (Fin (n * n * entryBits n) → Bool) = 2 ^ (n * n * entryBits n) := by
    simp
  have hsum : ∑ h ∈ Finset.range (2 ^ s),
      (Finset.univ.filter (fun x : Fin (n * n * entryBits n) → Bool => hint x = h)).card =
      2 ^ (n * n * entryBits n) := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_range.2 (hh x)),
      Finset.card_univ, hcardV]
  obtain ⟨h, -, hle⟩ : ∃ h ∈ Finset.range (2 ^ s), 2 ^ (n * n * entryBits n) ≤
      (Finset.range (2 ^ s)).card *
        (Finset.univ.filter (fun x : Fin (n * n * entryBits n) → Bool => hint x = h)).card := by
    apply Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.2 (Nat.two_pow_pos s)⟩
    rw [Finset.sum_const, ← Finset.mul_sum, hsum, smul_eq_mul]
  refine ⟨{x | hint x = h}, codes h, ?_, ?_⟩
  · rw [Finset.card_range] at hle
    have hF : ({x | hint x = h} : Set (Fin (n * n * entryBits n) → Bool)).ncard =
        (Finset.univ.filter (fun x : Fin (n * n * entryBits n) → Bool => hint x = h)).card := by
      rw [← Set.ncard_coe_finset]; congr 1; ext x; simp
    rw [hF]; exact hle
  · rw [solves_iff_forall_singleton]
    intro x hx
    have hxh : hint x = h := hx
    rw [← hxh]; exact hsol x

end Hint

/-- `L + 1 ≤ 2^{3w + 1}`, as `n ≤ 2^w` and `w < 2^w`. -/
theorem inputLength_succ_le (n : ℕ) : n * n * entryBits n + 1 ≤ 2 ^ (3 * entryBits n + 1) := by
  have h1 := le_two_pow_entryBits n
  have h2 : entryBits n ≤ 2 ^ entryBits n := Nat.lt_two_pow_self.le
  have h3 : n * n * entryBits n ≤ 2 ^ entryBits n * 2 ^ entryBits n * 2 ^ entryBits n :=
    Nat.mul_le_mul (Nat.mul_le_mul h1 h1) h2
  have h4 : 2 ^ (3 * entryBits n + 1) =
      2 * (2 ^ entryBits n * 2 ^ entryBits n * 2 ^ entryBits n) := by
    rw [pow_succ]; ring
  have h5 : 0 < 2 ^ entryBits n * 2 ^ entryBits n * 2 ^ entryBits n := by positivity
  omega

/-! ### The ladder between the plain and the robust target -/

/-- The robust target is the top of the co-entropy ladder. -/
theorem robustNoCode_iff_coent :
    RobustNoCode_TM ↔ ∀ C : ℕ, NoCode_TM_coent (fun n => C * n * entryBits n) :=
  ⟨fun h C k G c hG => h k G c C hG, fun h k G c C hG => h C k G c hG⟩

/-- The plain target is the bottom of the co-entropy ladder: a set of co-entropy `0` is everything. -/
theorem noCode_iff_coent_zero : NoCode_TM ↔ NoCode_TM_coent (fun _ => 0) := by
  constructor
  · intro h k G c hG
    obtain ⟨n₀, hn₀⟩ := h k G c hG
    refine ⟨n₀, fun n hn D hD hT F hF code hsol => hn₀ n hn D hD hT code ?_⟩
    have hFu : F = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ F) _ (Set.toFinite _)
      rw [ncard_univ_vec]
      simpa using hF
    rw [hFu] at hsol
    exact hsol
  · intro h k G c hG
    obtain ⟨n₀, hn₀⟩ := h k G c hG
    exact ⟨n₀, fun n hn D hD hT code hsol => hn₀ n hn D hD hT Set.univ
      (by rw [ncard_univ_vec]; simp) code hsol⟩

/-- A smaller co-entropy budget is a weaker target. -/
theorem coent_mono {m m' : ℕ → ℕ} (hm : ∃ N, ∀ n, N ≤ n → m n ≤ m' n)
    (h : NoCode_TM_coent m') : NoCode_TM_coent m := by
  obtain ⟨N, hN⟩ := hm
  intro k G c hG
  obtain ⟨n₀, hn₀⟩ := h k G c hG
  exact ⟨max n₀ N, fun n hn D hD hT F hF code hsol =>
    hn₀ n (le_trans (le_max_left _ _) hn) D hD hT F
      (le_trans hF (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num)
        (hN n (le_trans (le_max_right _ _) hn))))) code hsol⟩

/-- **Co-entropy `s` ⟹ hint of `s` bits** (pigeonhole: the most popular hint value). -/
theorem hintBits_of_coent {s : ℕ → ℕ} (h : NoCode_TM_coent s) : NoCode_TM_hintBits s := by
  intro k G c hG
  obtain ⟨n₀, hn₀⟩ := h k G c hG
  refine ⟨n₀, fun n hn D hD hT hint codes hh hsol => ?_⟩
  obtain ⟨F, Cd, hF, hsolF⟩ := code_of_hint D hint codes hh hsol
  exact hn₀ n hn D hD hT F hF Cd hsolF

/-- **Hint of `m + 3w + 1` bits ⟹ co-entropy `m`** (shifts of a code cover all inputs). -/
theorem coent_of_hintBits {m s : ℕ → ℕ}
    (hs : ∃ N, ∀ n, N ≤ n → m n + 3 * entryBits n + 1 ≤ s n)
    (h : NoCode_TM_hintBits s) : NoCode_TM_coent m := by
  obtain ⟨N, hN⟩ := hs
  intro k G c hG
  obtain ⟨n₀, hn₀⟩ := h k G c hG
  refine ⟨max n₀ N, fun n hn D hD hT F hF code hsol => ?_⟩
  obtain ⟨hint, codes, hh, hsolx⟩ := hint_of_code D hsol hF
  refine hn₀ n (le_trans (le_max_left _ _) hn) D hD hT hint codes (fun x => ?_) hsolx
  calc hint x < 2 ^ m n * (n * n * entryBits n + 1) := hh x
    _ ≤ 2 ^ m n * 2 ^ (3 * entryBits n + 1) := Nat.mul_le_mul_left _ (inputLength_succ_le n)
    _ = 2 ^ (m n + 3 * entryBits n + 1) := by rw [← pow_add, Nat.add_assoc]
    _ ≤ 2 ^ s n := Nat.pow_le_pow_right (by norm_num) (hN n (le_trans (le_max_right _ _) hn))

/-- **Robust ⟺ plain with an oracle `O(n w)`-bit hint.** -/
theorem robustNoCode_iff_hint : RobustNoCode_TM ↔ NoCode_TM_hint := by
  rw [robustNoCode_iff_coent]
  constructor
  · intro h C
    exact hintBits_of_coent (h C)
  · intro h C
    refine coent_of_hintBits ⟨4, fun n hn => ?_⟩ (h (C + 1))
    have hw : 1 ≤ entryBits n := by unfold entryBits; omega
    have h3 : 3 * entryBits n + 1 ≤ n * entryBits n := by nlinarith
    calc C * n * entryBits n + 3 * entryBits n + 1 ≤ C * n * entryBits n + n * entryBits n := by
          omega
      _ = (C + 1) * n * entryBits n := by ring

/-- The hint target gives the plain target (it is the robust target). -/
theorem noCode_of_noCode_hint (h : NoCode_TM_hint) : NoCode_TM :=
  noCode_of_robustNoCode (robustNoCode_iff_hint.2 h)

end Transpose.Tape.Impl
