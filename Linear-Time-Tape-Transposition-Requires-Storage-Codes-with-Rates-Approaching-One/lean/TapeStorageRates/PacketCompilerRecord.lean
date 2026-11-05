import Transpose.Statement
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-! # Finite alphabet of the eleven-tick packed computation

Addresses, phase, and time are public on the frozen schedule. These records store the bounded
parts of the native state, the three packet windows, all symbols written on this tick, and any
complete output packet.
-/

namespace TapeStorageRates.PacketCompiler

open Transpose

set_option autoImplicit false
set_option synthInstance.maxSize 4096

abbrev InputWord (s r : ℕ) := Fin (s + r) → Option Bool
abbrev WorkWord (M : TM) (s : ℕ) := Fin s → Fin (M.g + 1)

@[ext] structure Boundary (M : TM) (s r : ℕ) where
  state : Fin (M.q+1)
  inputOffset : Fin (s+r)
  workOffset : Fin M.k → Fin s
  pending : Fin (s+r) → Option Bool
  deriving Fintype

@[ext] structure StepRecord (M : TM) (s r : ℕ) where
  boundary : Boundary M s r
  inputCells : Fin 3 → InputWord s r
  workCells : Fin 3 → Fin M.k → WorkWord M s
  written : Fin M.k → WorkWord M s
  output : Option (Fin s → Bool)
  deriving Fintype

end TapeStorageRates.PacketCompiler
