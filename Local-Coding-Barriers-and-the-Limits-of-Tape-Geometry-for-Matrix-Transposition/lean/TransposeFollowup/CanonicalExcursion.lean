import TransposeFollowup.ExcursionTransfer
import Transpose.Tape.MStarTM

/-! Canonical sizes and explicit stationary extra tapes for the finite
padding construction. The bound is for page-walk duration; producing its
graph/opcodes and implementing them on a uniform machine remain separate. -/

namespace TransposeFollowup

open Classical Transpose Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram
set_option autoImplicit false

def paddingVertices (n : ℕ) : ℕ := 4 * (n / 4)

theorem paddingVertices_bounds {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ paddingVertices n ∧ paddingVertices n ≤ n ∧ n ≤ 2 * paddingVertices n := by
  dsimp [paddingVertices]
  omega

/-- Stretch and stationary-tape counts can be chosen once for a fixed positive
expansion constant and degree/page bound, independently of the input size. -/
theorem exists_padding_parameters (eta : ℝ) (heta : 0 < eta) (q k : ℕ) :
    ∃ K extra : ℕ, 0 < K ∧ 4 ≤ (4 * K - 1 : ℕ) * eta ∧
      4 * (q : ℝ) ≤ 3 * (k + extra : ℕ) * eta := by
  obtain ⟨K, hK⟩ := exists_nat_gt (1 + 4 / eta)
  have hdiv : 0 < (4 : ℝ) / eta := by positivity
  have hKn : 0 < K := by exact_mod_cast (show (0 : ℝ) < K by linarith)
  have hKe : 4 < (K : ℝ) * eta := (div_lt_iff₀ heta).mp (by linarith)
  have hKm : (K : ℝ) ≤ (4 * K - 1 : ℕ) := by exact_mod_cast (show K ≤ 4 * K - 1 by omega)
  have hstretch : 4 ≤ (4 * K - 1 : ℕ) * eta :=
    hKe.le.trans (mul_le_mul_of_nonneg_right hKm heta.le)
  obtain ⟨extra, he⟩ := exists_nat_gt (4 * (q : ℝ) / (3 * eta))
  have hex : 4 * (q : ℝ) < (extra : ℝ) * (3 * eta) :=
    (div_lt_iff₀ (by positivity : 0 < 3 * eta)).mp he
  refine ⟨K, extra, hKn, hstretch, ?_⟩
  have hk : (extra : ℝ) ≤ (k + extra : ℕ) := by exact_mod_cast (Nat.le_add_left extra k)
  have hm := mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ 3 * eta)
  nlinarith

namespace NestedMatchingPages

variable {v k : ℕ} {G : SimpleGraph (Fin v)} [DecidableRel G.Adj]
    (D : NestedMatchingPages G k)

noncomputable def paddedWalk (r K offset extra : ℕ) (hr : 0 < r) (hK : 0 < K) :
    Fin (k + extra) → ℕ → ℤ := Fin.addCases (D.walk r K offset hr hK) (fun _ _ => 0)

theorem paddedWalk_page (r K offset extra : ℕ) (hr : 0 < r) (hK : 0 < K)
    (p : Fin k) (t : ℕ) :
    D.paddedWalk r K offset extra hr hK (Fin.castAddEmb extra p) t =
      D.walk r K offset hr hK p t := by
  simp [paddedWalk]

theorem paddedWalk_unitSteps (r K offset extra : ℕ) (hr : 0 < r) (hK : 0 < K)
    (p : Fin (k + extra)) : UnitSteps (D.paddedWalk r K offset extra hr hK p) := by
  refine Fin.addCases (fun p => ?_) (fun p => ?_) p
  · simpa [paddedWalk] using D.walk_unitSteps r K offset hr hK p
  · simp [paddedWalk, UnitSteps]

theorem paddedWalk_zero (r K offset extra : ℕ) (hr : 0 < r) (hK : 0 < K)
    (p : Fin (k + extra)) : D.paddedWalk r K offset extra hr hK p 0 = 0 := by
  refine Fin.addCases (fun p => ?_) (fun p => ?_) p
  · simpa [paddedWalk] using D.walk_zero r K offset hr hK p
  · simp [paddedWalk]

theorem paddedWalk_reset (r K offset extra : ℕ) (hr : 0 < r) (hK : 0 < K)
    (p : Fin (k + extra)) {t : ℕ} (ht : horizon (v := v) r K offset ≤ t) :
    D.paddedWalk r K offset extra hr hK p t = 0 := by
  refine Fin.addCases (fun p => ?_) (fun p => ?_) p
  · simpa [paddedWalk] using D.walk_reset r K offset hr hK p ht
  · simp [paddedWalk]

theorem paddedWalk_cutIneq {r K offset extra : ℕ} (hr : 0 < r) (hK : 0 < K)
    (eta : ℝ) (heta : 0 < eta)
    (hexp : ∀ S : Finset (Fin v), 2 * S.card ≤ v →
      eta * S.card ≤ (outsideNeighbors G S).card)
    (q : ℕ) (hdegree : ∀ i, G.degree i ≤ q)
    (hstretch : 4 ≤ (4 * K - 1 : ℕ) * eta)
    (hheads : 4 * (q : ℝ) ≤ 3 * (k + extra : ℕ) * eta)
    (hv : 2 ≤ v) (n cellBits : ℕ) (hn : n ≤ 2 * v)
    (hscale : n * entryBits n ≤ r * cellBits) :
    CutIneq n cellBits r (horizon (v := v) r K offset) 0 0
      (D.paddedWalk r K offset extra hr hK) := by
  apply D.cutIneq_after hr hK (Fin.castAddEmb extra) (le_refl _)
    (fun p t _ => D.paddedWalk_page r K offset extra hr hK p t)
    eta heta hexp q hdegree hstretch hheads hv n cellBits hn hscale

/-- The exact forward page-motion horizon is bounded using the original
paper's canonical block size. No cost of graph generation is hidden here. -/
theorem horizon_linear {n cellBits : ℕ} (hG : 1 ≤ cellBits) (hv : v ≤ n)
    (K offset : ℕ) :
    horizon (v := v) (blockSize cellBits n) K offset ≤
      offset + 7 * K * (n * n * entryBits n) := by
  have hr := blockSize_le (n := n) hG
  have hm := Nat.mul_le_mul hr hv
  have hm' := Nat.mul_le_mul_left (7 * K) hm
  dsimp [horizon]
  nlinarith

theorem horizon_with_setup {n cellBits : ℕ} (hG : 1 ≤ cellBits) (hv : v ≤ n)
    (K offset a : ℕ) (hoff : offset ≤ a * (n * n * entryBits n)) :
    horizon (v := v) (blockSize cellBits n) K offset ≤
      (a + 7 * K) * (n * n * entryBits n) := by
  have hh := horizon_linear hG hv K offset
  nlinarith

end NestedMatchingPages

/-- Specialize the constructed walk to v=4 floor(n/4), r=ceil(n b/G), and
stationary extra tapes. Every geometric obligation is derived; only the
expanding nested-matching graph and fixed numerical choices are inputs. -/
theorem canonical_padding_cutIneq {n k : ℕ}
    {G : SimpleGraph (Fin (paddingVertices n))} [DecidableRel G.Adj]
    (D : NestedMatchingPages G k) (hn : 4 ≤ n) (cellBits K offset extra : ℕ)
    (hG : 1 ≤ cellBits) (hK : 0 < K) (eta : ℝ) (heta : 0 < eta)
    (hexp : ∀ S : Finset (Fin (paddingVertices n)), 2 * S.card ≤ paddingVertices n →
      eta * S.card ≤ (outsideNeighbors G S).card)
    (q : ℕ) (hdegree : ∀ i, G.degree i ≤ q)
    (hstretch : 4 ≤ (4 * K - 1 : ℕ) * eta)
    (hheads : 4 * (q : ℝ) ≤ 3 * (k + extra : ℕ) * eta) :
    CutIneq n cellBits (blockSize cellBits n)
      (NestedMatchingPages.horizon (v := paddingVertices n) (blockSize cellBits n) K offset) 0 0
      (D.paddedWalk (blockSize cellBits n) K offset extra
        (by have := one_le_blockSize hG (show 1 ≤ n by omega); omega) hK) := by
  obtain ⟨hv, _, hnv⟩ := paddingVertices_bounds hn
  exact D.paddedWalk_cutIneq _ hK eta heta hexp q hdegree hstretch hheads hv n cellBits hnv
    (blockSize_mul_ge hG)

end TransposeFollowup
