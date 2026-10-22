import TransposeFollowup.ExcursionTransfer

/-! Only the time interval used by each excursion is needed to transfer
its witness. Arbitrary computation before its opening is immaterial. -/
namespace TransposeFollowup
set_option autoImplicit false

theorem NestedExcursion.congr_on {r K a c : ℕ} {z : ℤ} {h h' : ℕ → ℤ}
    (E : NestedExcursion r K a c z h)
    (heq : ∀ t,a ≤ t → t ≤ c+4*K*r → h' t=h t) : NestedExcursion r K a c z h' := by
  refine ⟨E.r_pos,E.K_pos,E.separated,?_,?_,?_⟩
  · intro t ha ht
    rw [heq t ha (by have := E.separated;omega)]
    exact E.rise t ha ht
  · intro t ha hc
    rw [heq t (by omega) (by omega)]
    exact E.middle t ha hc
  · intro t hc ht
    rw [heq t (by have := E.separated;omega) ht]
    exact E.fall t hc ht

namespace ExcursionLayout
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {r K k T : ℕ} {h : Fin k → ℕ → ℤ} (D : ExcursionLayout G r K k T h)

def transfer_on_excursions {k' T' : ℕ} {h' : Fin k' → ℕ → ℤ} (pages : Fin k ↪ Fin k')
    (hT : T ≤ T')
    (heq : ∀ e t,D.openTime e ≤ t → t ≤ D.closeTime e+4*K*r → h' (pages (D.page e)) t=h (D.page e) t) :
    ExcursionLayout G r K k' T' h' where
  r_pos:=D.r_pos
  K_pos:=D.K_pos
  start:=D.start
  separated:=D.separated
  within i:=(D.within i).trans hT
  src:=D.src
  dst:=D.dst
  edge_eq:=D.edge_eq
  page e:=pages (D.page e)
  base:=D.base
  excursion e:=(D.excursion e).congr_on (heq e)
  slabs e f hne hp:=D.slabs e f hne (pages.injective hp)

end ExcursionLayout
end TransposeFollowup
