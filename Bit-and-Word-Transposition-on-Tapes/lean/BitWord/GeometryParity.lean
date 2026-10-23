import BitWord.GeometrySplit
import BitWord.GeometryOperations

namespace BitWord.Geometry

 theorem split_lt {P x : ℕ} (he : P % 2 = 0) (hx : x < P) : split P x < P := by
   unfold split
   split_ifs <;> omega
 theorem interleave_lt {P x : ℕ} (he : P % 2 = 0) (hx : x < P) : interleave P x < P := by
   unfold interleave
   split_ifs <;> omega
 theorem interleave_split {P x : ℕ} (he : P % 2 = 0) (hx : x < P) :
     interleave P (split P x) = x := by
   unfold split interleave
   split_ifs <;> omega
 theorem split_interleave {P x : ℕ} (_he : P % 2 = 0) (_hx : x < P) :
     split P (interleave P x) = x := by
   unfold split interleave
   split_ifs <;> omega

 /-- The actual raw-position stable parity split, with half-interleave inverse. -/
 def splitEquiv (P : ℕ) (he : P % 2 = 0) : Equiv.Perm (Fin P) where
   toFun x := ⟨split P x.val, split_lt he x.isLt⟩
   invFun x := ⟨interleave P x.val, interleave_lt he x.isLt⟩
   left_inv x := Fin.ext (interleave_split he x.isLt)
   right_inv x := Fin.ext (split_interleave he x.isLt)

 theorem finiteAct_splitEquiv {P x : ℕ} (he : P % 2 = 0) (hx : x < P) :
     finiteAct (splitEquiv P he) x = split P x := by simp [finiteAct, hx, splitEquiv]
 theorem finiteAct_splitEquiv_symm {P x : ℕ} (he : P % 2 = 0) (hx : x < P) :
     finiteAct (splitEquiv P he).symm x = interleave P x := by simp [finiteAct, hx, splitEquiv]

end BitWord.Geometry
