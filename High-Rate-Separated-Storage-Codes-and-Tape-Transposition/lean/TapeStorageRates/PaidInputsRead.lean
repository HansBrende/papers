import TapeStorageRates.PacketCompilerBatch
import TapeStorageRates.PacketOutput

/-! # Data available at one coarse input cell with a fixed tail pattern -/

namespace TapeStorageRates.PaidInputs

open Transpose Transpose.Tape Transpose.Tape.Impl PacketCompiler

set_option autoImplicit false

/-- The physical input visible in a masked coarse cell is determined by its
own payload packet and the common tail. Exterior cells supply only end markers.
This applies at any integer cell address. -/
theorem input_cell_eq {d a s r : ℕ} (ha : 0 < a) (hs : 0 < s)
    (z : Raw d r) {x y : Payload d a s} (u : ℤ)
    (hag : ∀ q : Fin (d*d*a), (q : ℤ) = u → x q = y q) :
    tapeCell (raggedLayout d a s r ha) none
      (readInput (List.ofFn ((splitWord d a s r).symm (x,z)))) u =
    tapeCell (raggedLayout d a s r ha) none
      (readInput (List.ofFn ((splitWord d a s r).symm (y,z)))) u := by
  let L := raggedLayout d a s r ha
  funext i
  change (if L.start u + i.val < L.start (u+1) then _ else none) =
    (if L.start u + i.val < L.start (u+1) then _ else none)
  split_ifs with hinside
  · apply readInput_eq_of_nth (List.length_ofFn) (List.length_ofFn)
    intro m hm hmL
    let v : Fin (d*d*(a*s+r)) := ⟨m,hmL⟩
    have hbit : (splitWord d a s r).symm (x,z) v = (splitWord d a s r).symm (y,z) v := by
      obtain ⟨t,ht⟩ := (raggedAddress d a s r).surjective v
      rw [← ht]
      cases t with
      | inr q => simp
      | inl pair =>
        obtain ⟨q,l⟩ := pair
        have hraw : ((raggedAddress d a s r (.inl (q,l))).val : ℤ) = L.start u+i.val := by
          rw [ht]
          exact hm
        have hnn : 0 ≤ L.start (q : ℤ) := by
          have hi := (L.strictMono hs).monotone (Int.natCast_nonneg q.val)
          rwa [L.zero] at hi
        have hpos : L.start (q : ℤ)+l.val = L.start u+i.val := by
          have hlane := ragged_start_lane (r := r) ha q l
          have hcast : ((L.start (q : ℤ)).toNat : ℤ) + (l.val : ℤ) =
              ((raggedAddress d a s r (.inl (q,l))).val : ℤ) := by exact_mod_cast hlane
          rw [Int.toNat_of_nonneg hnn] at hcast
          exact hcast.trans hraw
        have hl : (l.val : ℤ) < s := by exact_mod_cast l.isLt
        have hspan := L.lower (q : ℤ)
        have hq : (q : ℤ) = u :=
          (L.cell_eq hs (p := L.start u+i.val) (q := (q : ℤ)) (by omega) (by omega)).symm.trans
            (L.cell_eq hs (by omega) hinside)
        simp only [rebuild_payload]
        exact congrFun (hag q hq) l
    simpa only [nth_eq_getElem?, List.getElem?_ofFn, dite_eq_left hmL, Option.some.injEq] using hbit
  · rfl

end TapeStorageRates.PaidInputs
