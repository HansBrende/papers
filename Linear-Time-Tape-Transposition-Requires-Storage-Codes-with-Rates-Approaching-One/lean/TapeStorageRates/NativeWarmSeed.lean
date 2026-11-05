import TapeStorageRates.NativeMachine

/-! Seeding the aligned simulator after an arbitrary native prefix. -/

namespace TapeStorageRates.Native

open Transpose

def warmRegs {M : TM} {s : ℕ} (hs : 0<s) (c : Config M) : Registers M s :=
  { initialRegs M hs with q := c.state }

/-- Use the current head positions as the translated grid origins. The whole
source work tapes and the output already printed are preserved. -/
noncomputable def warmSeed (M : TM) {s : ℕ} (hs : 0<s) (c : Config M) :
    Config (machine M hs) where
  state := labelEquiv M hs (.left ⟨0,hs⟩, warmRegs hs c)
  inPos := c.inPos
  workPos := c.workPos
  work := c.work
  outRev := c.outRev

end TapeStorageRates.Native
