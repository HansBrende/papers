import TransposeFollowup.PageOpcodeWalk

/-! A nested-page schedule with the caller's actual row spacing and fetch
delay. Its times are native step times; pauses are never compressed. -/
namespace TransposeFollowup.NestedMatchingPages
open Classical Transpose.Tape
set_option autoImplicit false
variable {v k : ℕ} {G : SimpleGraph (Fin v)} [DecidableRel G.Adj]

def timedStart (stride offset delay : ℕ) (i : Fin v) : ℕ := offset+stride*i.val+delay
def timedHorizon (stride offset : ℕ) : ℕ := offset+stride*v

theorem timedStart_gap (stride offset delay : ℕ) {i j : Fin v} (hij : i.val<j.val) :
    timedStart stride offset delay i+stride ≤ timedStart stride offset delay j := by
  have hm:=Nat.mul_le_mul_left stride (Nat.succ_le_of_lt hij)
  unfold timedStart
  nlinarith

theorem timedStart_within (R stride offset delay : ℕ) (hs : delay+7*R ≤ stride) (i : Fin v) :
    timedStart stride offset delay i+7*R ≤ timedHorizon (v:=v) stride offset := by
  have hm:=Nat.mul_le_mul_left stride (Nat.succ_le_of_lt i.isLt)
  unfold timedStart timedHorizon
  nlinarith

variable (D : NestedMatchingPages G k)

def timedSchedule (R stride offset delay : ℕ) (hR : 0<R) (hs : 7*R ≤ stride) :
    NestedPulseSchedule G.edgeFinset k (7*R) where
  gap_pos:=by omega
  page:=D.page
  opening e:=timedStart stride offset delay (D.src e)+R
  closing e:=timedStart stride offset delay (D.dst e)+R
  self_gap e:=by have hg:=timedStart_gap stride offset delay (D.forward e);omega
  nested e f hne hp:=by
    rcases D.nested e f hne hp with hg|hg
    · exact Or.inl ⟨by have := timedStart_gap stride offset delay hg.1;omega,
        by have := timedStart_gap stride offset delay hg.2;omega⟩
    · exact Or.inr ⟨by have := timedStart_gap stride offset delay hg.1;omega,
        by have := timedStart_gap stride offset delay hg.2;omega⟩

noncomputable def timedWalk (R stride offset delay : ℕ) (hR : 0<R) (hs : 7*R ≤ stride) : Fin k → ℕ → ℤ :=
  (D.timedSchedule R stride offset delay hR hs).walk (4*R)

noncomputable def timedBase (r K stride offset delay : ℕ) (hr : 0<r) (hK : 0<K) (hs : 7*(K*r) ≤ stride)
    (e : G.edgeFinset) : ℤ := 4*(K:ℤ)*(D.timedSchedule (K*r) stride offset delay (Nat.mul_pos hK hr) hs).depth e

theorem timedWalk_opcode_sum (R stride offset delay : ℕ) (hR : 0<R) (hs : 7*R ≤ stride) (p : Fin k) (t : ℕ) :
    D.timedWalk R stride offset delay hR hs p t=
      ∑ u : Fin v,(D.opcode u p).direction*cappedRamp (4*R) (timedStart stride offset delay u+R) t := by
  rw [D.opcode_weight_sum]
  rfl

theorem timedWalk_unitSteps (R stride offset delay : ℕ) (hR : 0<R) (hs : 7*R ≤ stride) (p : Fin k) :
    UnitSteps (D.timedWalk R stride offset delay hR hs p) :=
  (D.timedSchedule R stride offset delay hR hs).walk_unitSteps (by omega) p

theorem timedWalk_reset (R stride offset delay : ℕ) (hR : 0<R) (hs : delay+7*R ≤ stride)
    (p : Fin k) {t : ℕ} (ht : timedHorizon (v:=v) stride offset ≤ t) :
    D.timedWalk R stride offset delay hR (by omega) p t=0 := by
  apply (D.timedSchedule R stride offset delay hR (by omega)).walk_reset (T:=timedHorizon (v:=v) stride offset) _ p ht
  intro e
  have h:=timedStart_within R stride offset delay hs (D.dst e)
  change timedStart stride offset delay (D.dst e)+R+4*R ≤ _
  omega

end TransposeFollowup.NestedMatchingPages
