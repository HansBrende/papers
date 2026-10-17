import Transpose.Tape.CESweep

/-!
# The equivalent forms of the Tape Coding Conjecture, in one place

* `robust_tfae`: the robust forms are equivalent: the flow form (`RobustCE_TM`), the distance form,
  "no code", "no code" and the flow form on diagrams with every row attached, "no code" with the
  uniform profile of `3k` blocks, and "no code" with `(3k + 4) w` extra bits per memory edge.
* `plain_tfae`: the same for independent sources (`CE_TM`, `CE_TM_dist`, `NoCode_TM`).
* `robust_io_tfae`: the infinitely-often robust forms are equivalent (the gap works one size at a
  time).
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-- **The robust forms are equivalent.** -/
theorem robust_tfae : List.TFAE [RobustCE_TM, RobustCE_TM_dist, RobustNoCode_TM,
    RobustNoCode_TM_att, RobustCE_TM_att, RobustNoCode_TM_with (fun k => 3 * k),
    RobustNoCode_TM_bits (fun k n => (3 * k + 4) * entryBits n)] := by
  tfae_have 1 → 2 := robustCE_TM_dist_of_robustCE_TM
  tfae_have 2 → 3 := robustNoCode_of_robustCE_TM_dist
  tfae_have 3 → 1 := robustCE_TM_of_robustNoCode
  tfae_have 3 ↔ 4 := robustNoCode_iff_attached
  tfae_have 5 ↔ 3 := robustCE_TM_att_iff
  tfae_have 6 ↔ 3 := robustNoCode_with_iff (fun _ => ⟨0, le_rfl⟩)
  tfae_have 7 ↔ 3 := robustNoCode_logBits_iff
  tfae_finish

/-- **The plain forms are equivalent.** -/
theorem plain_tfae : List.TFAE [CE_TM, CE_TM_dist, NoCode_TM] := by
  tfae_have 1 → 2 := ce_TM_dist_of_ce_TM
  tfae_have 2 → 3 := noCode_of_ce_TM_dist
  tfae_have 3 → 1 := ce_TM_of_noCode
  tfae_finish

/-- **The infinitely-often robust forms are equivalent.** -/
theorem robust_io_tfae : List.TFAE [RobustCE_TM_io, RobustCE_TM_dist_io, RobustNoCode_TM_io] := by
  tfae_have 1 → 2 := robustCE_TM_dist_io_of_robustCE_TM_io
  tfae_have 2 → 3 := robustNoCode_io_of_robustCE_TM_dist_io
  tfae_have 3 → 1 := robustCE_TM_io_of_robustNoCode_io
  tfae_finish

end Transpose.Tape.Impl
