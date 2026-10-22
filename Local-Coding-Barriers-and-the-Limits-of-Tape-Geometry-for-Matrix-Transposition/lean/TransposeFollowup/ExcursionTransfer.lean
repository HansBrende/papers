import TransposeFollowup.MatchingExcursion

/-! Preserve the constructed finite witnesses in a larger tape family and
under arbitrary later motion. This is a statement about trajectories; it does
not substitute for a native machine compiler or its resource analysis. -/

namespace TransposeFollowup

open Classical Transpose Transpose.Tape
set_option autoImplicit false

theorem NestedExcursion.congr_upto {r K a c : ℕ} {z : ℤ} {h h' : ℕ → ℤ}
    (E : NestedExcursion r K a c z h)
    (heq : ∀ t, t ≤ c + 4 * K * r → h' t = h t) : NestedExcursion r K a c z h' := by
  refine ⟨E.r_pos, E.K_pos, E.separated, ?_, ?_, ?_⟩
  · intro t ha ht
    rw [heq t (by have := E.separated; omega)]
    exact E.rise t ha ht
  · intro t ha ht
    rw [heq t (by omega)]
    exact E.middle t ha ht
  · intro t hc ht
    rw [heq t ht]
    exact E.fall t hc ht

namespace ExcursionLayout

variable {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r K k T : ℕ} {h : Fin k → ℕ → ℤ}
    (D : ExcursionLayout G r K k T h)

def transfer {k' T' : ℕ} {h' : Fin k' → ℕ → ℤ} (pages : Fin k ↪ Fin k')
    (hT : T ≤ T') (heq : ∀ p t, t ≤ T → h' (pages p) t = h p t) :
    ExcursionLayout G r K k' T' h' where
  r_pos := D.r_pos
  K_pos := D.K_pos
  start := D.start
  separated := D.separated
  within i := (D.within i).trans hT
  src := D.src
  dst := D.dst
  edge_eq := D.edge_eq
  page e := pages (D.page e)
  base := D.base
  excursion e := (D.excursion e).congr_upto (by
    intro t ht
    apply heq (D.page e) t
    exact ht.trans (Nat.le_of_lt (D.close_before_end e)))
  slabs e f hne hp := D.slabs e f hne (pages.injective hp)

end ExcursionLayout

namespace NestedMatchingPages

variable {v k : ℕ} {G : SimpleGraph (Fin v)} [DecidableRel G.Adj]
    (D : NestedMatchingPages G k)

/-- Every later continuation of the explicit walk satisfies the original
finite inequality, including when other tapes have arbitrary trajectories. -/
theorem cutIneq_after {r K offset : ℕ} (hr : 0 < r) (hK : 0 < K)
    {k' T : ℕ} {h : Fin k' → ℕ → ℤ} (pages : Fin k ↪ Fin k')
    (hT : horizon (v := v) r K offset ≤ T)
    (heq : ∀ p t, t ≤ horizon (v := v) r K offset →
      h (pages p) t = D.walk r K offset hr hK p t)
    (eta : ℝ) (heta : 0 < eta)
    (hexp : ∀ S : Finset (Fin v), 2 * S.card ≤ v →
      eta * S.card ≤ (outsideNeighbors G S).card)
    (q : ℕ) (hdegree : ∀ i, G.degree i ≤ q)
    (hstretch : 4 ≤ (4 * K - 1 : ℕ) * eta) (hheads : 4 * (q : ℝ) ≤ 3 * k' * eta)
    (hv : 2 ≤ v) (n cellBits : ℕ) (hn : n ≤ 2 * v)
    (hscale : n * entryBits n ≤ r * cellBits) : CutIneq n cellBits r T 0 0 h := by
  let A := (D.layout r K offset hr hK).transfer pages hT heq
  exact A.cutIneq eta heta (by simpa only [Fintype.card_fin] using hexp) q hdegree
    hstretch hheads (by simpa only [Fintype.card_fin] using hv) n cellBits
    (by simpa only [Fintype.card_fin] using hn) hscale

end NestedMatchingPages
end TransposeFollowup
