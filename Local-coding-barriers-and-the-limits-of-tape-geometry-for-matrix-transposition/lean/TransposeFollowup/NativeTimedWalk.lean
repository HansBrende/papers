import TransposeFollowup.GeneratorRowsPreparedGeometry
import TransposeFollowup.TimedRowCoverage
import TransposeFollowup.TimedMatchingLayout

namespace TransposeFollowup.GeneratorRows
open Classical FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def stride (F : Fin (r+1) → RationalMobius) (R : ℕ) : ℕ := 14*R+4*rationalPageCount F+6
def fetchDelay (F : Fin (r+1) → RationalMobius) : ℕ := 4*rationalPageCount F+2
noncomputable def preparedPaths (F : Fin (r+1) → RationalMobius) (R : ℕ) (w : List Bool)
    (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) : Fin (nativeMachine F).k → ℕ → ℤ := fun p t =>
  (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine F) w) t
    (NativeIOFusion.denote (nativeEncoding F) (program F) (selected F)
      (join (.inl (OpcodeGenerator.start F)) (first F gpos outRev) (Counter.marked (SevenPhaseClock.word R)) (fun _ => 0)))).workPos p
noncomputable def pagePorts (F : Fin (r+1) → RationalMobius) : Fin (rationalPageCount F) ↪ Fin (nativeMachine F).k where
  toFun p:=(nativeEncoding F).port (.inr (some p))
  inj':=by intro p q h;exact Option.some.inj (Sum.inr.inj ((nativeEncoding F).port.injective h))

theorem prepared_row_walk (F : Fin (r+1) → RationalMobius) (R : ℕ) (w : List Bool) (n : ℕ) (hn : 1 ≤ n)
    (hw : w.length=Transpose.inputLength n) (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) :
    ∃ a ≤ OpcodeGenerator.coefficient F*w.length+8*n*rationalPageCount F+5,
      ∀ p t,a ≤ t → t ≤ a+stride F R*(2*n) →
        preparedPaths F R w gpos outRev (pagePorts F p) t=
          TimedRowWalk.walk R (stride F R) (fetchDelay F) a (GeneratedRowClock.rows F n) p t := by
  obtain ⟨xs,_hx,_hv,_hl,a,ha,_boundaries,paths⟩:=prepared_geometry F (SevenPhaseClock.word R) (fun _ => 0) w n hn hw gpos outRev
  have hp : RowLoop.period (rationalPageCount F) (SevenPhaseClock.word R)=stride F R:=by
    unfold RowLoop.period stride
    rw [SevenPhaseClock.word_length]
    omega
  have hne : GeneratedRowClock.rows F n≠[]:=by simp [GeneratedRowClock.rows];omega
  refine ⟨a,ha,?_⟩
  intro p t hl hu
  apply TimedRowWalk.rowwise_eq R (stride F R) (fetchDelay F) a (by unfold stride fetchDelay;omega)
    (by unfold stride;omega) (GeneratedRowClock.rows F n) hne p (preparedPaths F R w gpos outRev (pagePorts F p)) _ t hl
    (by simpa only [GeneratedRowClock.rows,List.length_ofFn] using hu)
  intro front tail ops he s hs
  have h:=paths front tail ops he s (by rwa [hp]) p
  rw [hp,TimedRowWalk.finishPos_eq,SevenPhaseClock.count_ramp] at h
  simpa only [preparedPaths,show pagePorts F p=(nativeEncoding F).port (.inr (some p)) from rfl,fetchDelay,zero_add,add_assoc] using h

theorem generated_walk_eq (F : Fin (r+1) → RationalMobius) (n R period offset delay : ℕ)
    (hR : 0<R) (hs : 7*R ≤ period) (p : Fin (rationalPageCount F)) (t : ℕ) :
    TimedRowWalk.walk R period delay offset (GeneratedRowClock.rows F n) p t=
      (overlapPages (rationalFamilyMaps F) n).timedWalk R period offset delay hR hs p t := by
  classical
  rw [NestedMatchingPages.timedWalk_opcode_sum]
  unfold GeneratedRowClock.rows
  rw [TimedRowWalk.ofFn_eq_sum]
  simp only [rationalPageOpcode_eq,NestedMatchingPages.timedStart]

end TransposeFollowup.GeneratorRows
