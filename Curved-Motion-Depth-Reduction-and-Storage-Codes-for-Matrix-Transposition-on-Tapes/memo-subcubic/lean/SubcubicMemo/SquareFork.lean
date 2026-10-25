import SubcubicMemo.SquareCubeCap
import Mathlib.Data.Fin.VecNotation

/-! Local obstructions in a hypothetical component without the desired map.
The hypotheses here are used only inside the eventual contradiction proof. -/

namespace SubcubicMemo.Squares

open Finset MotionDepthCodes
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (h : Hyp G) (hc : G.Preconnected)
  (hn : ¬ Nonempty (G →g circularClique 8 3))

include h hc hn in
theorem no_three_common {p q a b c : V} (hpq : p ≠ q)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpa : G.Adj p a) (hpb : G.Adj p b) (hpc : G.Adj p c)
    (hqa : G.Adj q a) (hqb : G.Adj q b) (hqc : G.Adj q c) : False := by
  apply hn (hom_of_three_common h hpq {a,b,c} (by simp [hab,hac,hbc]) ?_ ?_ hc)
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption

include h hc hn in
theorem common_pair_unique {p q a b c : V} (hpq : p ≠ q)
    (hab : a ≠ b) (hpa : G.Adj p a) (hpb : G.Adj p b)
    (hqa : G.Adj q a) (hqb : G.Adj q b)
    (hpc : G.Adj p c) (hqc : G.Adj q c) : c = a ∨ c = b := by
  by_contra hh
  push_neg at hh
  exact no_three_common h hc hn hpq hab (Ne.symm hh.1) (Ne.symm hh.2)
    hpa hpb hpc hqa hqb hqc

include h hc hn in
/-- Three different square wedges at a vertex would force one of the already
closed bipartite caps. -/
theorem no_three_wedges {u a b c x y z : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hx : Square G u a x b) (hy : Square G u b y c)
    (hz : Square G u c z a) : False := by
  rcases hx with ⟨hua,hax,hxb,hbu,hux,hab'⟩
  rcases hy with ⟨hub,hby,hyc,hcu,huy,hbc'⟩
  rcases hz with ⟨huc,hcz,hza,hau,huz,hca'⟩
  have hxy : x ≠ y := by
    intro he; subst y
    exact no_three_common h hc hn hux hab hac hbc hua hub huc hax.symm hxb hyc
  have hxz : x ≠ z := by
    intro he; subst z
    exact no_three_common h hc hn hux hab hac hbc hua hub huc hax.symm hxb hcz.symm
  have hyz : y ≠ z := by
    intro he; subst z
    exact no_three_common h hc hn huy hab hac hbc hua hub huc hza hby.symm hyc
  have hxc : x ≠ c := by
    intro he; subst c
    exact no_triangle G h.triangle hua huc hax
  have hya : y ≠ a := by
    intro he; subst a
    exact no_triangle G h.triangle hub hua hby
  have hzb : z ≠ b := by
    intro he; subst b
    exact no_triangle G h.triangle huc hub hcz
  let f : Fin 7 → V := ![u,a,b,c,x,y,z]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f] at hij ⊢ <;>
      first | rfl | exact False.elim (by
        have := hua.ne; have := hub.ne; have := huc.ne
        have := hax.ne; have := hxb.ne; have := hby.ne
        have := hyc.ne; have := hcz.ne; have := hza.ne
        grind)
  have hm : ∀ i j, cubeCap.Adj i j → G.Adj (f i) (f j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [cubeCap, SimpleGraph.fromRel_adj, f, SimpleGraph.adj_comm]
  exact hn (hom_of_cubeCap h hc ⟨f,fun {i j} => hm i j⟩ hf)

end SubcubicMemo.Squares
