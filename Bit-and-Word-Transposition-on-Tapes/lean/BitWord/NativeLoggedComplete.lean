import BitWord.NativeLoggedInit
import BitWord.NativeLoggedUndo

/-! Complete checked logging, execution, reverse replay and history erasure.
Only the selected source tapes are retained; every other tape and physical
head is restored exactly. -/
namespace BitWord.NativeLogged
open FixedTapeCompiler TransposeFollowup
set_option autoImplicit false
variable {T L : Type*} [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L]

@[simp] theorem retain_self (keep : T → Bool) (c : SourceConfig (T := T) (L := L)) :
    retain keep c c=c := by
  rcases c with ⟨⟨pc,tapes⟩,pos⟩
  simp [retain]

noncomputable def resetCost (T L : Type*) [Fintype T] [Fintype L] (n : ℕ) : ℕ := by
  classical
  exact (n+1)*(Fintype.card T+1)+(Fintype.card (Record T L)+5)*n+5

theorem reset_execution (p : Microcode.Program T L) (keep : T → Bool)
    {n : ℕ} {c d : SourceConfig (T := T) (L := L)}
    (ht : OperationalTrace.Trace (NativeMicrocode.step p) (NativeMicrocode.Active p) n c d)
    (hh : p d.core.pc=.halt) :
    NativeLoggedInit.Trace p keep c.core.pc (resetCost T L n)
      (NativeLoggedInit.initialConfig c)
      (NativeLoggedInit.mapConfig (cleared (retain keep c d))) := by
  obtain ⟨history,hist,hforward⟩ := logged_execution p keep c.core.pc ht hh
  have hundo := undo_history p keep c.core.pc hist d
  simp only [retain_self] at hundo
  have hrun := NativeCountedLoop.trace_trans hforward hundo
  have hinit := NativeLoggedInit.initialize_trace p keep c
  have hwhole := NativeCountedLoop.trace_trans hinit (NativeLoggedInit.map_trace p keep c.core.pc hrun)
  convert hwhole using 1 <;> simp [resetCost] <;> ring

theorem resetCost_mono {n N : ℕ} (h : n≤N) : resetCost T L n≤resetCost T L N := by
  unfold resetCost
  gcongr

end BitWord.NativeLogged
