import BitWord.NativeLogged

/-! Exact data/history layouts for the logging controller. -/
namespace BitWord.NativeLogged
open FixedTapeCompiler TransposeFollowup
open CopyMachine (Sym)
set_option autoImplicit false
variable {T L : Type*} [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L]

abbrev SourceConfig := NativeMicrocode.Config T L
abbrev LoggedConfig := NativeMicrocode.Config (Port T L) (Label T L)

def record (c : SourceConfig (T := T) (L := L)) : Record T L :=
  (c.core.pc,fun t => (c.core.tapes t).head)

def logSymbols (history : List (Record T L)) (r : Record T L) : List (Sym Bool) :=
  history.map (fun a => .data (decide (a=r)))

def bank (c : SourceConfig (T := T) (L := L)) (history : List (Record T L)) :
    Port T L → Turing.Tape (Sym Bool)
  | .data t => c.core.tapes t
  | .log r => Turing.Tape.mk₂ (logSymbols history r ++ [.start]) []

def positions (c : SourceConfig (T := T) (L := L)) (history : List (Record T L)) : Port T L → ℤ
  | .data t => c.pos t | .log _ => history.length

def loaded (pc : Label T L) (c : SourceConfig (T := T) (L := L)) (history : List (Record T L)) :
    LoggedConfig (T := T) (L := L) := ⟨⟨pc,bank c history⟩,positions c history⟩

def forward (c : SourceConfig (T := T) (L := L)) (history : List (Record T L)) :
    LoggedConfig (T := T) (L := L) := loaded (start c.core.pc) c history

/-- Keep selected tapes and their physical head positions from the retained
configuration; restore every other tape from the base configuration. -/
def retain (keep : T → Bool) (base saved : SourceConfig (T := T) (L := L)) : SourceConfig (T := T) (L := L) :=
  ⟨⟨base.core.pc,fun t => if keep t then saved.core.tapes t else base.core.tapes t⟩,
    fun t => if keep t then saved.pos t else base.pos t⟩

/-- This certificate is generated from the actual source execution. Its
records are facts about old scanned symbols, not assumed input advice. -/
inductive History (p : Microcode.Program T L) (initial : SourceConfig (T := T) (L := L)) :
    ℕ → SourceConfig (T := T) (L := L) → List (Record T L) → Prop
  | nil : History p initial 0 initial []
  | more {n c history} : History p initial n c history → NativeMicrocode.Active p c →
      History p initial (n+1) (NativeMicrocode.step p c) (record c::history)

theorem History.length {p : Microcode.Program T L} {initial c : SourceConfig (T := T) (L := L)}
    {n : ℕ} {history : List (Record T L)} (h : History p initial n c history) : history.length=n := by
  induction h with
  | nil => rfl
  | more _ _ ih => simpa using congrArg Nat.succ ih

abbrev Trace (p : Microcode.Program T L) (keep : T → Bool) (initial : L) :=
  OperationalTrace.Trace (NativeMicrocode.step (program p keep initial))
    (NativeMicrocode.Active (program p keep initial))

end BitWord.NativeLogged
