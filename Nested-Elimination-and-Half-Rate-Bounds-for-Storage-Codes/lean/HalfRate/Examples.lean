import HalfRate.Corollaries

/-! Sanity checks: the certificate conditions are satisfiable on concrete relations. -/

namespace HalfRate

open Finset MotionDepthCodes

/-- One edge `0 — 1` (each vertex recovered from the other). -/
def edgeN : Fin 2 → Finset (Fin 2) := ![{1}, {0}]

/-- A one-piece decomposition of the edge (two records, list `[0, 1]`). -/
def edgeCert : PieceCert edgeN ∅ univ where
  m := 2
  P := ![{0}, {1}]
  disj := by decide
  cover := by decide
  l := [0, 1]
  hl := by decide
  a := fun v => v
  b := fun v => if v = 0 then 1 else 0
  par := fun _ => none
  own := by decide
  ab := by decide
  charged := by
    simp only [RelCharged]
    exact ⟨by decide, by decide, trivial⟩

example : RateBound edgeN (1 / 2) :=
  rateBound_of_decomp (pcs := [univ]) ⟨by simp, ⟨edgeCert⟩, by simp [Decomp]⟩

/-- The 5-cycle maps to `And(2) = K_{5/2}`, so the direct instance applies. -/
example : RateBound (nbhd (circularClique 5 2)) (1 / 2) :=
  rateBound_of_circularHom' (p := 5) (q := 2) (by norm_num) (by norm_num) SimpleGraph.Hom.id

end HalfRate
