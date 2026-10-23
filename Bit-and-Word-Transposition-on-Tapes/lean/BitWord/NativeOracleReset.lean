import BitWord.NativeOracleRun
import BitWord.NativeLoggedComplete

/-! The captured arbitrary oracle followed by checked reverse replay. Its
input is restored and its actual output is retained; no time-dependent bound
is used by the finite controller to decide when to halt or erase. -/
namespace BitWord.NativeOracleReset
open FixedTapeCompiler TransposeFollowup
open CopyMachine (Sym)
set_option autoImplicit false

abbrev SourcePort (M : Transpose.TM) := NativeOracle.Port M
abbrev SourceLabel (M : Transpose.TM) := NativeOracle.Label M

def keep (M : Transpose.TM) : SourcePort M → Bool
  | .capture => true | _ => false

def sourceInitial (M : Transpose.TM) (w : List Bool) :=
  NativeOracle.cfg M (NativeOracle.start M) (NativeOracle.prepared M w) (fun _ => 0)

def sourceFinal (M : Transpose.TM) (w out : List Bool) :
    NativeLogged.SourceConfig (T := SourcePort M) (L := SourceLabel M) :=
  ⟨⟨NativeOracle.start M,fun p => match p with
    | .capture => Turing.Tape.mk₂ (out.reverse.map Sym.data ++ [.start]) []
    | _ => NativeOracle.prepared M w p⟩,
    fun p => match p with | .capture => out.length | _ => 0⟩

noncomputable def program (M : Transpose.TM) :=
  NativeLoggedInit.program (NativeOracle.program M) (keep M) (NativeOracle.start M)

noncomputable def budget (M : Transpose.TM) (T : ℕ) :=
  NativeLogged.resetCost (SourcePort M) (SourceLabel M) ((T+1)*(NativeOracle.workCount M+2))

noncomputable def overhead (M : Transpose.TM) : ℕ := by
  classical
  exact (Fintype.card (SourcePort M)+Fintype.card (NativeLogged.Record (SourcePort M) (SourceLabel M))+6)*
    (NativeOracle.workCount M+2)+Fintype.card (SourcePort M)+6

theorem budget_le (M : Transpose.TM) (T : ℕ) : budget M T≤overhead M*(T+1) := by
  classical
  simp only [budget,NativeLogged.resetCost,overhead]
  simp only [Fintype.card_prod,Fintype.card_fun]
  nlinarith

noncomputable def encoding (M : Transpose.TM) :=
  NativeMicrocode.initialEncoding
    (T := NativeLoggedInit.Port (T := SourcePort M) (L := SourceLabel M))
    (none : NativeLoggedInit.Label (T := SourcePort M) (L := SourceLabel M))

noncomputable def machine (M : Transpose.TM) := NativeMicrocode.machine (encoding M) (program M)

theorem fixed_resources (M : Transpose.TM) :
    (machine M).k=Fintype.card (NativeLoggedInit.Port (T := SourcePort M) (L := SourceLabel M)) ∧
    (machine M).g+1=5 ∧ (encoding M).label none=0 :=
  ⟨rfl,rfl,NativeMicrocode.initialEncoding_start _⟩

theorem prepared_reset_call (M : Transpose.TM) (w out : List Bool) (T : ℕ)
    (h : Transpose.ComputesWithin M w out T) :
    ∃ t≤budget M T,
      OperationalTrace.Trace (NativeMicrocode.step (program M)) (NativeMicrocode.Active (program M)) t
        (NativeLoggedInit.initialConfig (sourceInitial M w))
        (NativeLoggedInit.mapConfig (NativeLogged.cleared (sourceFinal M w out))) := by
  obtain ⟨n,hn,tapes,pos,htrace,hcapture⟩ := NativeOracle.prepared_call M w out T h
  have hh : NativeOracle.program M (NativeOracle.cfg M .done tapes pos).core.pc=.halt := rfl
  have hr := NativeLogged.reset_execution (NativeOracle.program M) (keep M) htrace hh
  refine ⟨_,NativeLogged.resetCost_mono hn,?_⟩
  have he : NativeLogged.retain (keep M) (sourceInitial M w)
      (NativeOracle.cfg M .done tapes pos)=sourceFinal M w out := by
    rcases hcapture with ⟨ht,hp⟩
    unfold NativeLogged.retain sourceInitial sourceFinal NativeOracle.cfg
    congr 1
    · congr 1
      funext p; cases p <;> simp [keep,ht]
    · funext p; cases p <;> simp [keep,hp]
  change NativeLoggedInit.Trace (NativeOracle.program M) (keep M) (NativeOracle.start M)
    (NativeLogged.resetCost (SourcePort M) (SourceLabel M) n)
    (NativeLoggedInit.initialConfig (sourceInitial M w))
    (NativeLoggedInit.mapConfig (NativeLogged.cleared
      (NativeLogged.retain (keep M) (sourceInitial M w) (NativeOracle.cfg M .done tapes pos)))) at hr
  rw [he] at hr
  exact hr

end BitWord.NativeOracleReset
