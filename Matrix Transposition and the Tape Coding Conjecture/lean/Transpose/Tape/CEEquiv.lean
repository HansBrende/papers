import Transpose.Tape.CECount
import Transpose.Tape.MStarTM

/-!
# The forms of the Tape Coding Conjecture are equivalent

A code that solves complete exchange in a block network has rate `1`. But at radius
`j ≈ log_{2k+3} √n` almost every input bit is at distance `≥ j` from its sink (`rowDist_sum_ge`),
while the capacities sum to `O(L)` (`sum_cap_le`). So the volume bound fails by a factor `Θ(log n)`
(`volume_gap`, a property of the networks alone; `dist_gap` for codes): **a code exists only if
the distance form fails**. Hence:
* `RobustCE_TM ⟹ RobustCE_TM_dist` (weak duality);
* `RobustCE_TM_dist ⟹ RobustNoCode_TM` (`dist_gap`);
* `RobustNoCode_TM ⟹ RobustCE_TM` (vacuously);

and the same for the plain forms, and for the infinitely-often forms (the gap works one size at a
time). Also: `rate_lt`, every routing within the profile has rate `< E/w`; and the forms with every
capacity in the profile (`robustNoCode_iff_forall_cap`, `noCode_iff_forall_cap`). (The block-size
lemmas `one_le_blockSize`, `blockSize_le`, `blockSize_mul_ge` are in `MStarTM.lean`.)
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-! ### The constants -/

/-- `m = ⌈log₂(2k+3)⌉`: a ball of radius `j` has at most `2^{m j}` nodes. -/
def ceM (k : ℕ) : ℕ := Nat.clog 2 (2 * k + 3)

/-- `K = (4k+1) G (c+1)`: capacities within the block profile sum to at most `K L`. The `+1` is needed:
`sum_cap_le` gives `4k`, but with `4k` the constant `E` would vanish at `k = 0`, and `volume_gap`
would claim `w · 0 < 0`. -/
def ceK (k G c : ℕ) : ℕ := (4 * k + 1) * G * (c + 1)

/-- `E = 4 m K`: when a code exists, the distance form fails at `ε = 1/E`. -/
def ceE (k G c : ℕ) : ℕ := 4 * ceM k * ceK k G c

/-- `B = 4 (c+1) G + C`. -/
def ceB (G c C : ℕ) : ℕ := 4 * (c + 1) * G + C

/-- The size from which the counting argument applies. -/
def ceSize (k G c C : ℕ) : ℕ := max (2 ^ (6 * ceM k) + 1) (16 * ceB G c C ^ 2 + 2)

theorem one_le_ceE (k G c : ℕ) (hG : 1 ≤ G) : 1 ≤ ceE k G c := by
  have hm : 0 < ceM k := Nat.clog_pos (by norm_num) (by omega)
  unfold ceE ceK
  have : 0 < 4 * ceM k * ((4 * k + 1) * G * (c + 1)) := by positivity
  omega

/-! ### The gap -/

/-- **The volume bound caps the flow rate at `E/w`** (network only). For `n ≥ ceSize k G c C`, in the
block network of every valid `k`-tape diagram of length `≤ c L` with at most `C` rows without a source
node, capacities within the block profile satisfy `w Σ_e cap e < E Σ_d rowDist d`. -/
theorem volume_gap {k G c C n : ℕ} (hG : 1 ≤ G) (hn : ceSize k G c C ≤ n) {D : TSDiagram k}
    (hD : D.Valid (n * n * entryBits n)) (hT : D.T ≤ c * (n * n * entryBits n))
    {cap : ℕ × ℕ → ℕ} (hcap : D.CapProfile n G cap)
    (hu : ((Finset.range n).filter (fun i => ∀ a < D.nodes (blockSize G n),
      i ∉ D.rowsAt n (entryBits n) (blockSize G n) a)).card ≤ C) :
    entryBits n * ∑ e ∈ D.edges (blockSize G n), cap e <
      ceE k G c * ∑ d ∈ Finset.range (n * n * entryBits n),
        D.rowDist n (entryBits n) (blockSize G n) d := by
  have hn6 : 2 ^ (6 * ceM k) + 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnB : 16 * ceB G c C ^ 2 + 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn2 : 2 ≤ n := by omega
  have hb1 : 1 ≤ entryBits n := by unfold entryBits; omega
  have hnw : 1 ≤ n * entryBits n :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  set u := ((Finset.range n).filter (fun i => ∀ a < D.nodes (blockSize G n),
      i ∉ D.rowsAt n (entryBits n) (blockSize G n) a)).card with hudef
  have huC : u ≤ C := hu
  by_contra hcon
  push Not at hcon
  set w := entryBits n with hwdef
  set r := blockSize G n with hrdef
  set N := D.nodes r with hNdef
  set m := ceM k with hmdef
  set K := ceK k G c with hKdef
  have hm1 : 1 ≤ m := Nat.clog_pos (by norm_num) (by omega)
  have hK1 : 1 ≤ K := by
    rw [hKdef]; unfold ceK
    have : 0 < (4 * k + 1) * G * (c + 1) := by positivity
    omega
  have hw6 : 6 * m + 1 ≤ w := by
    have h1 : 2 ^ (6 * m) ≤ n - 1 := by omega
    have h2 := (Nat.le_log2 (show n - 1 ≠ 0 by omega)).2 h1
    rw [hwdef]; unfold entryBits; omega
  have hr1 : 1 ≤ r := one_le_blockSize hG (by omega)
  have hrnw : r ≤ n * w := blockSize_le hG
  have hrG : n * w ≤ r * G := blockSize_mul_ge hG
  have hNr : N * r ≤ D.T + r - 1 := nodes_mul_le r
  have hnwL : n * w ≤ n * n * w := by
    calc n * w = 1 * (n * w) := (Nat.one_mul _).symm
      _ ≤ n * (n * w) := Nat.mul_le_mul_right _ (by omega)
      _ = n * n * w := by ring
  -- capacities: `Σ cap ≤ K L`
  have hcapsum : ∑ e ∈ D.edges r, cap e ≤ K * (n * n * w) := by
    have h1 := sum_cap_le hD hcap
    have h2 : N * r ≤ (c + 1) * (n * n * w) := by
      calc N * r ≤ D.T + r := by omega
        _ ≤ c * (n * n * w) + n * w := Nat.add_le_add hT hrnw
        _ ≤ c * (n * n * w) + n * n * w := Nat.add_le_add_left hnwL _
        _ = (c + 1) * (n * n * w) := by ring
    calc _ ≤ (4 * k + 1) * N * (r * G) :=
          le_trans h1 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
      _ = (4 * k + 1) * G * (N * r) := by ring
      _ ≤ (4 * k + 1) * G * ((c + 1) * (n * n * w)) := Nat.mul_le_mul_left _ h2
      _ = K * (n * n * w) := by rw [hKdef]; unfold ceK; ring
  -- the number of nodes: `N ≤ (c+1) G n`
  have hN : N ≤ (c + 1) * G * n := by
    have h1 : N * (n * w) ≤ ((c + 1) * G * n) * (n * w) := by
      calc N * (n * w) ≤ N * (r * G) := Nat.mul_le_mul_left _ hrG
        _ = (N * r) * G := by ring
        _ ≤ (D.T + r) * G := Nat.mul_le_mul_right _ (by omega)
        _ ≤ (c * (n * n * w) + n * w) * G := Nat.mul_le_mul_right _ (Nat.add_le_add hT hrnw)
        _ = ((c * n + 1) * G) * (n * w) := by ring
        _ ≤ ((c + 1) * G * n) * (n * w) := by
            apply Nat.mul_le_mul_right
            have : c * n + 1 ≤ (c + 1) * n := by nlinarith
            calc (c * n + 1) * G ≤ (c + 1) * n * G := Nat.mul_le_mul_right _ this
              _ = (c + 1) * G * n := by ring
    exact Nat.le_of_mul_le_mul_right h1 hnw
  -- the radius `j` and the ball size `s`
  set j := (w - 1) / (2 * m) with hjdef
  set s := (2 * k + 3) ^ j with hsdef
  have hs1 : 1 ≤ s := Nat.one_le_pow _ _ (by omega)
  have hss : s * s ≤ n - 1 := by
    have h1 : s ≤ 2 ^ (m * j) := by
      rw [hsdef, pow_mul]; exact Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _
    have h2 : 2 * m * j ≤ w - 1 := Nat.mul_div_le (w - 1) (2 * m)
    have h3 : 2 ^ (w - 1) ≤ n - 1 := by
      have := Nat.log2_self_le (show n - 1 ≠ 0 by omega)
      have e : w - 1 = Nat.log2 (n - 1) := by rw [hwdef]; unfold entryBits; omega
      rw [e]; exact this
    calc s * s ≤ 2 ^ (m * j) * 2 ^ (m * j) := Nat.mul_le_mul h1 h1
      _ = 2 ^ (2 * m * j) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by norm_num) h2
      _ ≤ n - 1 := h3
  -- distances
  have hdist₀ := rowDist_sum_ge hD hr1 hrnw j
  have hdist : j * (n * n * w) ≤ ∑ d ∈ Finset.range (n * n * w), D.rowDist n w r d +
      j * (4 * N * s * w + u * (n * w)) := by
    have hpow : (2 * k + 3) ^ (j - 1) ≤ s :=
      Nat.pow_le_pow_right (by omega) (Nat.sub_le j 1)
    have : 4 * N * (2 * k + 3) ^ (j - 1) * w ≤ 4 * N * s * w :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpow)
    exact le_trans hdist₀ (Nat.add_le_add_left (Nat.mul_le_mul_left _
      (Nat.add_le_add_right this _)) _)
  set S := ∑ d ∈ Finset.range (n * n * w), D.rowDist n w r d with hSdef
  set A := 4 * (c + 1) * G * s + C with hAdef
  have hbad : 4 * N * s * w + u * (n * w) ≤ (n * w) * A := by
    have h1 : 4 * N * s * w ≤ 4 * ((c + 1) * G * n) * s * w := by
      apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_left _ hN
    have h2 : u * (n * w) ≤ C * (n * w) := Nat.mul_le_mul_right _ huC
    calc 4 * N * s * w + u * (n * w) ≤ 4 * ((c + 1) * G * n) * s * w + C * (n * w) :=
          Nat.add_le_add h1 h2
      _ = (n * w) * A := by rw [hAdef]; ring
  -- `E j L ≤ w K L + E j (n w) A`
  set E := ceE k G c with hEdef
  have hmain : E * j * (n * (n * w)) ≤ w * K * (n * (n * w)) + E * j * ((n * w) * A) := by
    have h1 : E * (j * (n * n * w)) ≤ E * S + E * (j * ((n * w) * A)) := by
      rw [← Nat.mul_add]
      apply Nat.mul_le_mul_left
      calc j * (n * n * w) ≤ S + j * (4 * N * s * w + u * (n * w)) := hdist
        _ ≤ S + j * ((n * w) * A) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hbad) _
    have h2 : E * S ≤ w * K * (n * n * w) := by
      calc E * S ≤ w * ∑ e ∈ D.edges r, cap e := hcon
        _ ≤ w * (K * (n * n * w)) := Nat.mul_le_mul_left _ hcapsum
        _ = w * K * (n * n * w) := by ring
    have e1 : n * (n * w) = n * n * w := by ring
    rw [e1]
    calc E * j * (n * n * w) = E * (j * (n * n * w)) := by ring
      _ ≤ E * S + E * (j * ((n * w) * A)) := h1
      _ ≤ w * K * (n * n * w) + E * (j * ((n * w) * A)) := Nat.add_le_add_right h2 _
      _ = w * K * (n * n * w) + E * j * ((n * w) * A) := by ring
  have hmain' : E * j * n ≤ w * K * n + E * j * A := by
    have : (n * w) * (E * j * n) ≤ (n * w) * (w * K * n + E * j * A) := by
      calc (n * w) * (E * j * n) = E * j * (n * (n * w)) := by ring
        _ ≤ _ := hmain
        _ = (n * w) * (w * K * n + E * j * A) := by ring
    exact Nat.le_of_mul_le_mul_left this hnw
  -- `4 A ≤ n`
  have h4A : 4 * A ≤ n := by
    set B := ceB G c C with hBdef
    have hAB : A ≤ B * s := by
      have : C ≤ C * s := Nat.le_mul_of_pos_right _ hs1
      calc A = 4 * (c + 1) * G * s + C := rfl
        _ ≤ 4 * (c + 1) * G * s + C * s := Nat.add_le_add_left this _
        _ = B * s := by rw [hBdef]; unfold ceB; ring
    have hBn : 16 * B ^ 2 + 2 ≤ n := hnB
    by_cases hsB : s ≤ 4 * B
    · calc 4 * A ≤ 4 * (B * s) := Nat.mul_le_mul_left _ hAB
        _ ≤ 4 * (B * (4 * B)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsB)
        _ = 16 * B ^ 2 := by ring
        _ ≤ n := by omega
    · push Not at hsB
      calc 4 * A ≤ 4 * (B * s) := Nat.mul_le_mul_left _ hAB
        _ = (4 * B) * s := by ring
        _ ≤ s * s := Nat.mul_le_mul_right _ hsB.le
        _ ≤ n := by omega
  -- `3 m j ≤ w`
  have h3 : 3 * (E * j) ≤ 4 * (w * K) := by
    have : 4 * (E * j * n) ≤ 4 * (w * K * n) + E * j * n := by
      calc 4 * (E * j * n) ≤ 4 * (w * K * n + E * j * A) := Nat.mul_le_mul_left _ hmain'
        _ = 4 * (w * K * n) + E * j * (4 * A) := by ring
        _ ≤ 4 * (w * K * n) + E * j * n := Nat.add_le_add_left (Nat.mul_le_mul_left _ h4A) _
    have h' : 3 * (E * j * n) ≤ 4 * (w * K * n) := by
      generalize E * j * n = X at this ⊢
      generalize w * K * n = Y at this ⊢
      omega
    have h'' : (3 * (E * j)) * n ≤ (4 * (w * K)) * n := by
      calc (3 * (E * j)) * n = 3 * (E * j * n) := by ring
        _ ≤ 4 * (w * K * n) := h'
        _ = (4 * (w * K)) * n := by ring
    exact Nat.le_of_mul_le_mul_right h'' (by omega)
  have h3' : 3 * m * j ≤ w := by
    have : (4 * K) * (3 * m * j) ≤ (4 * K) * w := by
      calc (4 * K) * (3 * m * j) = 3 * (E * j) := by rw [hEdef]; unfold ceE; ring
        _ ≤ 4 * (w * K) := h3
        _ = (4 * K) * w := by ring
    exact Nat.le_of_mul_le_mul_left this (by omega)
  -- `w ≤ 2 m j + 2 m`
  have hjw : w ≤ 2 * m * j + 2 * m := by
    have := Nat.lt_mul_div_succ (w - 1) (show 0 < 2 * m by omega)
    rw [← hjdef] at this
    have e : 2 * m * (j + 1) = 2 * m * j + 2 * m := by ring
    omega
  have : 3 * w ≤ 2 * w + 6 * m := by
    calc 3 * w ≤ 3 * (2 * m * j + 2 * m) := Nat.mul_le_mul_left _ hjw
      _ = 2 * (3 * m * j) + 6 * m := by ring
      _ ≤ 2 * w + 6 * m := Nat.add_le_add_right (Nat.mul_le_mul_left _ h3') _
  omega

/-- **Co-entropy bounds the rows without a source node**: if a code solves complete exchange on a set
of co-entropy `≤ C n w`, at most `C` rows have no source node (`card_le_of_solves`). -/
theorem unattached_le {k : ℕ} {D : TSDiagram k} {n G C : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode}
    (hF : 2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard)
    (hsol : D.Solves n G cap F code) :
    ((Finset.range n).filter (fun i => ∀ a < D.nodes (blockSize G n),
      i ∉ D.rowsAt n (entryBits n) (blockSize G n) a)).card ≤ C := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hb1 : 1 ≤ entryBits n := by unfold entryBits; omega
  have h2 := Nat.le_of_mul_le_mul_right (le_trans (card_le_of_solves hsol) hF)
    (ncard_pos_of_coentropy hF)
  rw [Nat.pow_le_pow_iff_right (by norm_num), Nat.mul_assoc C] at h2
  exact Nat.le_of_mul_le_mul_right h2 (by positivity)

/-- **A code beats the volume bound by a factor `Ω(log n)`.** For `n ≥ ceSize k G c C`, if a causal
code solves complete exchange within the block profile on a set of inputs of co-entropy `≤ C n w`,
then `w Σ_e cap e < E Σ_d rowDist d`. -/
theorem dist_gap {k G c C n : ℕ} (hG : 1 ≤ G) (hn : ceSize k G c C ≤ n) {D : TSDiagram k}
    (hD : D.Valid (n * n * entryBits n)) (hT : D.T ≤ c * (n * n * entryBits n))
    {cap : ℕ × ℕ → ℕ} (hcap : D.CapProfile n G cap)
    {F : Set (Fin (n * n * entryBits n) → Bool)}
    (hF : 2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard)
    {code : NetCode} (hsol : D.Solves n G cap F code) :
    entryBits n * ∑ e ∈ D.edges (blockSize G n), cap e <
      ceE k G c * ∑ d ∈ Finset.range (n * n * entryBits n),
        D.rowDist n (entryBits n) (blockSize G n) d :=
  volume_gap hG hn hD hT hcap (unattached_le hF hsol)

/-! ### The equivalences -/

theorem ncard_univ_vec (L : ℕ) : (Set.univ : Set (Fin L → Bool)).ncard = 2 ^ L := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]

theorem coentropy_univ (n : ℕ) :
    2 ^ (n * n * entryBits n) ≤ 2 ^ (0 * n * entryBits n) *
      (Set.univ : Set (Fin (n * n * entryBits n) → Bool)).ncard := by
  rw [ncard_univ_vec]; simp

/-- From a routing to the volume bound (weak duality). -/
theorem dist_of_routes {k : ℕ} {D : TSDiagram k} {n G : ℕ} {cap : ℕ × ℕ → ℕ} {ρ : Routing}
    {ε : ℝ} (hε : 0 < ε) (hρ : D.RoutesAt n G cap ρ (1 / (ε * entryBits n))) :
    ((∑ d ∈ Finset.range (n * n * entryBits n),
        D.rowDist n (entryBits n) (blockSize G n) d : ℕ) : ℝ) ≤
      ε * entryBits n * ∑ e ∈ D.edges (blockSize G n), (cap e : ℝ) := by
  have hwd := weak_duality hρ
  have hw : (0 : ℝ) < entryBits n := by
    have : 1 ≤ entryBits n := by unfold entryBits; omega
    exact_mod_cast this
  rw [one_div, inv_mul_le_iff₀ (mul_pos hε hw)] at hwd
  exact hwd

/-- From the gap to the failure of the distance form at `ε = 1/E`. -/
theorem not_dist_of_gap {k : ℕ} {D : TSDiagram k} {n G E : ℕ} {cap : ℕ × ℕ → ℕ} (hE : 1 ≤ E)
    (hgap : entryBits n * ∑ e ∈ D.edges (blockSize G n), cap e <
      E * ∑ d ∈ Finset.range (n * n * entryBits n), D.rowDist n (entryBits n) (blockSize G n) d) :
    ¬ ((∑ d ∈ Finset.range (n * n * entryBits n),
        D.rowDist n (entryBits n) (blockSize G n) d : ℕ) : ℝ) ≤
      1 / (E : ℝ) * entryBits n * ∑ e ∈ D.edges (blockSize G n), (cap e : ℝ) := by
  intro hdist
  have hgapR : ((entryBits n * ∑ e ∈ D.edges (blockSize G n), cap e : ℕ) : ℝ) <
      ((E * ∑ d ∈ Finset.range (n * n * entryBits n),
        D.rowDist n (entryBits n) (blockSize G n) d : ℕ) : ℝ) := by exact_mod_cast hgap
  have hEpos : (0 : ℝ) < E := by exact_mod_cast hE
  have h1 := mul_le_mul_of_nonneg_left hdist hEpos.le
  have h2 : (E : ℝ) * (1 / (E : ℝ) * entryBits n * ∑ e ∈ D.edges (blockSize G n), (cap e : ℝ)) =
      entryBits n * ∑ e ∈ D.edges (blockSize G n), (cap e : ℝ) := by
    field_simp
  rw [h2] at h1
  push_cast at hgapR h1
  linarith

theorem robustCE_TM_dist_of_robustCE_TM (h : RobustCE_TM) : RobustCE_TM_dist := by
  intro k G c C hG ε hε
  obtain ⟨n₀, hn₀⟩ := h k G c C hG ε hε
  refine ⟨n₀, fun n hn D hD hT cap hcap F hF code hsol => ?_⟩
  obtain ⟨ρ, hρ⟩ := hn₀ n hn D hD hT cap hcap F hF code hsol
  exact dist_of_routes hε hρ

theorem robustNoCode_of_robustCE_TM_dist (h : RobustCE_TM_dist) : RobustNoCode_TM := by
  intro k G c C hG
  have hE := one_le_ceE k G c hG
  obtain ⟨n₀, hn₀⟩ := h k G c C hG (1 / (ceE k G c : ℝ)) (by positivity)
  refine ⟨max n₀ (ceSize k G c C), fun n hn D hD hT F hF code hsol => ?_⟩
  have hcap := capProfile_profileCap D n G
  exact not_dist_of_gap hE (dist_gap hG (le_trans (le_max_right _ _) hn) hD hT hcap hF hsol)
    (hn₀ n (le_trans (le_max_left _ _) hn) D hD hT _ hcap F hF code hsol)

theorem robustCE_TM_of_robustNoCode (h : RobustNoCode_TM) : RobustCE_TM := by
  intro k G c C hG ε _
  obtain ⟨n₀, hn₀⟩ := h k G c C hG
  exact ⟨n₀, fun n hn D hD hT _ hcap F hF code hsol =>
    absurd (solves_mono D (le_profileCap D hcap) hsol) (hn₀ n hn D hD hT F hF code)⟩

theorem ce_TM_dist_of_ce_TM (h : CE_TM) : CE_TM_dist := by
  intro k G c hG ε hε
  obtain ⟨n₀, hn₀⟩ := h k G c hG ε hε
  refine ⟨n₀, fun n hn D hD hT cap hcap code hsol => ?_⟩
  obtain ⟨ρ, hρ⟩ := hn₀ n hn D hD hT cap hcap code hsol
  exact dist_of_routes hε hρ

theorem noCode_of_ce_TM_dist (h : CE_TM_dist) : NoCode_TM := by
  intro k G c hG
  have hE := one_le_ceE k G c hG
  obtain ⟨n₀, hn₀⟩ := h k G c hG (1 / (ceE k G c : ℝ)) (by positivity)
  refine ⟨max n₀ (ceSize k G c 0), fun n hn D hD hT code hsol => ?_⟩
  have hcap := capProfile_profileCap D n G
  exact not_dist_of_gap hE
    (dist_gap hG (le_trans (le_max_right _ _) hn) hD hT hcap (coentropy_univ n) hsol)
    (hn₀ n (le_trans (le_max_left _ _) hn) D hD hT _ hcap code hsol)

theorem ce_TM_of_noCode (h : NoCode_TM) : CE_TM := by
  intro k G c hG ε _
  obtain ⟨n₀, hn₀⟩ := h k G c hG
  exact ⟨n₀, fun n hn D hD hT _ hcap code hsol =>
    absurd (solves_mono D (le_profileCap D hcap) hsol) (hn₀ n hn D hD hT code)⟩

theorem noCode_of_robustNoCode (h : RobustNoCode_TM) : NoCode_TM := by
  intro k G c hG
  obtain ⟨n₀, hn₀⟩ := h k G c 0 hG
  exact ⟨n₀, fun n hn D hD hT code => hn₀ n hn D hD hT Set.univ (coentropy_univ n) code⟩

/-- **The target with every capacity in the profile.** `RobustNoCode_TM`, stated at the profile
capacities, is equivalent to ruling out codes within every `cap` satisfying `CapProfile`. -/
theorem robustNoCode_iff_forall_cap : RobustNoCode_TM ↔
    ∀ (k G c C : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap → ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
      ∀ code : NetCode, ¬ D.Solves n G cap F code := by
  constructor
  · intro h k G c C hG
    obtain ⟨n₀, hn₀⟩ := h k G c C hG
    exact ⟨n₀, fun n hn D hD hT cap hcap F hF code =>
      ((not_solves_profileCap_iff D).1 (hn₀ n hn D hD hT F hF code)) cap hcap⟩
  · intro h k G c C hG
    obtain ⟨n₀, hn₀⟩ := h k G c C hG
    exact ⟨n₀, fun n hn D hD hT F hF code =>
      hn₀ n hn D hD hT _ (capProfile_profileCap D n G) F hF code⟩

/-- **The plain target with every capacity in the profile**: `NoCode_TM` is equivalent to ruling out
codes within every `cap` satisfying `CapProfile`. -/
theorem noCode_iff_forall_cap : NoCode_TM ↔
    ∀ (k G c : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (cap : ℕ × ℕ → ℕ), D.CapProfile n G cap →
      ∀ code : NetCode, ¬ D.Solves n G cap Set.univ code := by
  constructor
  · intro h k G c hG
    obtain ⟨n₀, hn₀⟩ := h k G c hG
    exact ⟨n₀, fun n hn D hD hT cap hcap code =>
      ((not_solves_profileCap_iff D).1 (hn₀ n hn D hD hT code)) cap hcap⟩
  · intro h k G c hG
    obtain ⟨n₀, hn₀⟩ := h k G c hG
    exact ⟨n₀, fun n hn D hD hT code => hn₀ n hn D hD hT _ (capProfile_profileCap D n G) code⟩

/-! ### Infinitely-often forms -/

theorem robustNoCode_io_of_robustNoCode (h : RobustNoCode_TM) : RobustNoCode_TM_io := by
  intro k G c C hG n₀
  obtain ⟨n₁, hn₁⟩ := h k G c C hG
  exact ⟨max n₀ n₁, le_max_left _ _, hn₁ _ (le_max_right _ _)⟩

theorem robustCE_TM_io_of_robustNoCode_io (h : RobustNoCode_TM_io) : RobustCE_TM_io := by
  intro k G c C hG ε _ n₀
  obtain ⟨n, hn, hno⟩ := h k G c C hG n₀
  exact ⟨n, hn, fun D hD hT _ hcap F hF code hsol =>
    absurd (solves_mono D (le_profileCap D hcap) hsol) (hno D hD hT F hF code)⟩

theorem robustCE_TM_dist_io_of_robustCE_TM_io (h : RobustCE_TM_io) : RobustCE_TM_dist_io := by
  intro k G c C hG ε hε n₀
  obtain ⟨n, hn, hall⟩ := h k G c C hG ε hε n₀
  refine ⟨n, hn, fun D hD hT cap hcap F hF code hsol => ?_⟩
  obtain ⟨ρ, hρ⟩ := hall D hD hT cap hcap F hF code hsol
  exact dist_of_routes hε hρ

/-- The gap works one size at a time, so the infinitely-often distance form gives no code
infinitely often. -/
theorem robustNoCode_io_of_robustCE_TM_dist_io (h : RobustCE_TM_dist_io) : RobustNoCode_TM_io := by
  intro k G c C hG n₀
  have hE := one_le_ceE k G c hG
  obtain ⟨n, hn, hall⟩ :=
    h k G c C hG (1 / (ceE k G c : ℝ)) (by positivity) (max n₀ (ceSize k G c C))
  refine ⟨n, le_trans (le_max_left _ _) hn, fun D hD hT F hF code hsol => ?_⟩
  have hcap := capProfile_profileCap D n G
  exact not_dist_of_gap hE (dist_gap hG (le_trans (le_max_right _ _) hn) hD hT hcap hF hsol)
    (hall D hD hT _ hcap F hF code hsol)

theorem noCode_io_of_robustNoCode_io (h : RobustNoCode_TM_io) : NoCode_TM_io := by
  intro k G c hG n₀
  obtain ⟨n, hn, hno⟩ := h k G c 0 hG n₀
  exact ⟨n, hn, fun D hD hT code => hno D hD hT Set.univ (coentropy_univ n) code⟩

/-! ### The flow rate -/

/-- **The flow rate is `O(1/log n)`** (network-only: weak duality plus `volume_gap`). For
`n ≥ ceSize k G c C`, on a valid `k`-tape diagram of length `≤ c L` with at most `C` rows without a
source node, every routing of the transposition demand within capacities in the block profile has
rate `< E / w`, with `E = ceE k G c`. -/
theorem rate_lt {k G c C n : ℕ} (hG : 1 ≤ G) (hn : ceSize k G c C ≤ n) {D : TSDiagram k}
    (hD : D.Valid (n * n * entryBits n)) (hT : D.T ≤ c * (n * n * entryBits n))
    {cap : ℕ × ℕ → ℕ} (hcap : D.CapProfile n G cap)
    (hu : ((Finset.range n).filter (fun i => ∀ a < D.nodes (blockSize G n),
      i ∉ D.rowsAt n (entryBits n) (blockSize G n) a)).card ≤ C)
    {ρ : Routing} {rate : ℝ} (hρ : D.RoutesAt n G cap ρ rate) :
    rate < (ceE k G c : ℝ) / entryBits n := by
  have hgap := volume_gap hG hn hD hT hcap hu
  have hwd := weak_duality hρ
  have hw : (0 : ℝ) < entryBits n := by
    have : 1 ≤ entryBits n := by unfold entryBits; omega
    exact_mod_cast this
  set S := ∑ e ∈ D.edges (blockSize G n), cap e with hS
  set R := ∑ d ∈ Finset.range (n * n * entryBits n), D.rowDist n (entryBits n) (blockSize G n) d
    with hR
  have hRpos : (0 : ℝ) < R := by
    have : 0 < R := by
      rcases Nat.eq_zero_or_pos R with h0 | h0
      · rw [h0, Nat.mul_zero] at hgap; omega
      · exact h0
    exact_mod_cast this
  have hgapR : (entryBits n : ℝ) * S < (ceE k G c : ℝ) * R := by exact_mod_cast hgap
  have hSR : (∑ e ∈ D.edges (blockSize G n), (cap e : ℝ)) = (S : ℝ) := by rw [hS]; push_cast; rfl
  rw [hSR] at hwd
  rw [lt_div_iff₀ hw]
  by_contra hcon
  push Not at hcon
  have h1 : (ceE k G c : ℝ) * R ≤ rate * entryBits n * R := mul_le_mul_of_nonneg_right hcon hRpos.le
  nlinarith

/-- **An explicit gain threshold suffices.** Suppose that for all constants and all large `n`, every
causal code solving complete exchange at the profile capacities satisfies
`E Σ_d rowDist d ≤ w Σ_e profileCap e` with `E = ceE k G c`: the volume bound allows routing at rate
`E/w`, i.e. the coding gain is at most `w/E`. Then no such code exists. -/
theorem robustNoCode_of_gainBound
    (h : ∀ (k G c C : ℕ), 1 ≤ G → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
      ∀ code : NetCode, D.Solves n G (D.profileCap n G) F code →
        ceE k G c * ∑ d ∈ Finset.range (n * n * entryBits n),
            D.rowDist n (entryBits n) (blockSize G n) d ≤
          entryBits n * ∑ e ∈ D.edges (blockSize G n), D.profileCap n G e) :
    RobustNoCode_TM := by
  intro k G c C hG
  obtain ⟨n₀, hn₀⟩ := h k G c C hG
  refine ⟨max n₀ (ceSize k G c C), fun n hn D hD hT F hF code hsol => ?_⟩
  have hcap := capProfile_profileCap D n G
  have h1 := hn₀ n (le_trans (le_max_left _ _) hn) D hD hT F hF code hsol
  have h2 := dist_gap hG (le_trans (le_max_right _ _) hn) hD hT hcap hF hsol
  omega

end Transpose.Tape.Impl
