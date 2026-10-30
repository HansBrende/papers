import MergeDepth.Trimming

/-!
# The paired-distance condition for skeleton classes

`skel_paired_separation` plugs the transport estimate of Lemma 4.10 (`skel_disjoint_paths_transport`)
into the fifth paper's `path_transport_implies_paired_distance_separation`: along any sequence of
skeleton data at a fixed scale `w`, depth `D` and time constant `c`, with `d → ∞`, whose cone
relations have incidence graphs of bounded degree, the cone relations satisfy the paired-distance
condition `HasPairedDistanceSeparation`. No hypothesis on transport remains.
-/

namespace MergeDepth

open Finset BoundedNesting DirectedRecovery Filter

variable {k : ℕ}

open Classical in
/-- **The paired-distance condition on skeleton classes.** -/
theorem skel_paired_separation {w D Δ : ℕ} (hw : 1 ≤ w) {c : ℝ} (hc : 0 ≤ c)
    (d b T : ℕ → ℕ) (hd : Tendsto d atTop atTop) (hb : ∀ n, 1 ≤ b n)
    (z : ℕ → Tp k → ℕ → ℤ) (hz : ∀ n c', IsWalk (z n c')) (Γ : ℕ → Finset ℕ) (ot : ℕ → ℕ → ℕ)
    (hdepth : ∀ n π, IsDepPath (fun j => skel w (z n (some (some j)))) (T n) π →
      LinNet.GFree (Γ n) π → π.length ≤ D + 1)
    (hot : ∀ n (q : Fin (d n * d n * b n)), ot n (tpos (d n) (b n) q) < T n ∧
      (tpos (d n) (b n) q : ℤ) / w = z n (some none) (ot n (tpos (d n) (b n) q)) / w)
    (hT : ∀ n, (T n : ℝ) ≤ c * (d n * d n * b n + 1))
    (hdeg : ∀ᶠ n in atTop, ∀ v, (pairedIncidenceGraph (coneRel w (z n) (T n) (Γ n) (ot n)
      (fun q : Fin (d n * d n * b n) => tpos (d n) (b n) q))).degree v ≤ Δ) :
    HasPairedDistanceSeparation (fun n => coneRel w (z n) (T n) (Γ n) (ot n)
      (fun q : Fin (d n * d n * b n) => tpos (d n) (b n) q)) := by
  apply path_transport_implies_paired_distance_separation _ d b hd hb
    (fun n => by simp only [Fintype.card_fin]; ring)
  intro r _
  refine ⟨Δ, fun s => 2 * s * c * (w * ∑ h ∈ range (D + 1), (k + 1) ^ h : ℕ) *
      ((k + 2) * (2 * w - 1) : ℕ) * (((k + 2) * (2 * w - 1) : ℕ) + 1) + 3,
    fun s => by positivity, hdeg, ?_⟩
  filter_upwards [hd.eventually (eventually_ge_atTop (2 * w))] with n hn
  have hd2 : 2 ≤ d n := by omega
  have hdbw : 2 * w - 1 ≤ d n * b n := by
    have := Nat.mul_le_mul hn (hb n)
    omega
  exact skel_disjoint_paths_transport hw hd2 (hb n) hdbw (hz n) (hdepth n) (ot n) (hot n) hc (hT n) r

end MergeDepth
