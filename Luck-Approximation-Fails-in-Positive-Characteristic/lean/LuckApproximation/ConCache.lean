import LuckApproximation.Construction
import LuckApproximation.Data
import Mathlib.Data.List.GetD

/-!
# The packed caches agree with the construction

`Data.lean` stores the incidences and the blocks packed into natural numbers, so that the certificate checks read
them quickly. Here the kernel checks that they agree with the construction (`blockNat_eq_cache`,
`edgeOfNat_eq_cache`); nothing in the proof trusts them.
-/

namespace Luck.Con

open Luck.ConData Luck.Data

/-! ### The caches -/

def blocksCached : Bool :=
  (List.range 110).all fun e => (List.range 100).all fun k => blockNat e (k / 10) (k % 10) == couplingNat e (k / 10) (k % 10)

theorem blocksCached_ok : blocksCached = true := by decide +kernel

def edgesCached : Bool :=
  (List.range 11).all fun v => (List.range 11).all fun w => Con.edgeOfNat v w == Data.edgeOfNat v w

theorem edgesCached_ok : edgesCached = true := by decide +kernel

theorem blockNat_eq_cache (e : Fin 110) (a b : Fin 10) : blockNat e a b = couplingNat e a b := by
  have hc := blocksCached_ok
  simp only [blocksCached, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  have := hc e e.2 (10 * a + b) (by omega)
  rwa [show (10 * (a : ℕ) + b) / 10 = a by omega, show (10 * (a : ℕ) + b) % 10 = b by omega] at this

theorem edgeOfNat_eq_cache (v w : Fin 11) : Con.edgeOfNat v w = Data.edgeOfNat v w := by
  have hc := edgesCached_ok
  simp only [edgesCached, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  exact hc v v.2 w w.2

end Luck.Con
