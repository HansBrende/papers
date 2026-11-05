import TapeStorageRates.PacketCompilerCells
import TapeStorageRates.PaidInputsSuccess

/-! # Append-only packet framing

Once the packet counter is fixed by a schedule, a bounded suffix of the raw output and the
new batch output suffice to update the suffix and to recover the packet, if one is completed.
These identities use the physical append order on arbitrary ragged widths.
-/

namespace TapeStorageRates.PacketCompiler

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth PaidInputs

set_option autoImplicit false

variable {s r : ℕ} (L : CellLayout s r)

/-- Pending raw output at a packet boundary known from the common schedule. -/
def CellLayout.pendingAt (q : ℤ) (past : List Bool) : List Bool :=
  past.drop (L.start q).toNat

/-- The first s lanes of a packet. All application sites read them after its completion. -/
def CellLayout.payloadAt (q : ℤ) (past : List Bool) : Fin s → Bool :=
  fun i => past[(L.start q).toNat + i.val]?.getD false

theorem CellLayout.cell_mono (hs : 0 < s) : Monotone (L.cell hs) := by
  intro x y hxy
  by_contra! h
  have hle := (L.strictMono hs).monotone (show L.cell hs y + 1 ≤ L.cell hs x by omega)
  have hx := L.contains hs x
  have hy := L.contains hs y
  omega

/-- A batch appending at most s raw bits completes zero or one whole packet at any offset. -/
theorem CellLayout.output_cell_step (hs : 0 < s) (past fresh : List Bool) (hf : fresh.length ≤ s) :
    L.cell hs (past.length : ℤ) ≤ L.cell hs ((past ++ fresh).length : ℤ) ∧
    L.cell hs ((past ++ fresh).length : ℤ) ≤ L.cell hs (past.length : ℤ) + 1 := by
  rw [List.length_append, Nat.cast_add]
  constructor
  · exact L.cell_mono hs (by omega)
  · have h := L.near_cell hs (p := (past.length : ℤ) + fresh.length) (q := past.length) (by
      rw [add_sub_cancel_left, abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast hf)
    have := (abs_le.mp h).2
    omega

theorem CellLayout.pendingAt_length_lt (hs : 0 < s) (past : List Bool) :
    (L.pendingAt (L.cell hs past.length) past).length < s+r := by
  have hp := L.contains hs past.length
  have hu := L.upper (L.cell hs past.length)
  simp only [CellLayout.pendingAt, List.length_drop]
  omega

/-- The new pending suffix is a function of the old pending suffix, this batch's output,
and the two public packet boundaries. -/
theorem CellLayout.pendingAt_append (q q' : ℤ) (past fresh : List Bool)
    (hp : (L.start q).toNat ≤ past.length) (hq : (L.start q).toNat ≤ (L.start q').toNat) :
    L.pendingAt q' (past ++ fresh) =
      (L.pendingAt q past ++ fresh).drop ((L.start q').toNat - (L.start q).toNat) := by
  simp only [CellLayout.pendingAt]
  rw [← List.drop_append_of_le_length hp, List.drop_drop, Nat.add_sub_of_le hq]

/-- The bits to emit are also available from that same bounded word. -/
theorem CellLayout.payloadAt_append (q : ℤ) (past fresh : List Bool)
    (hp : (L.start q).toNat ≤ past.length) :
    L.payloadAt q (past ++ fresh) = fun i => (L.pendingAt q past ++ fresh)[i.val]?.getD false := by
  funext i
  simp only [CellLayout.payloadAt, CellLayout.pendingAt, ← List.drop_append_of_le_length hp,
    List.getElem?_drop]

/-- Raw cell zero starts at zero; until the end of an n-bit past its current packet
starts at a nonnegative physical address at most n. -/
theorem CellLayout.prefix_start (hs : 0 < s) (n : ℕ) :
    0 ≤ L.start (L.cell hs n) ∧ (L.start (L.cell hs n)).toNat ≤ n := by
  have hq : 0 ≤ L.cell hs n := by
    simpa only [L.cell_zero hs] using L.cell_mono hs (Int.natCast_nonneg n)
  have h := L.contains hs n
  have h0 := (L.strictMono hs).monotone hq
  rw [L.zero] at h0
  exact ⟨h0, by omega⟩

/-- The layout's contiguous physical lane is exactly the canonical flattened address used
by the transposition theorem on raw bits. -/
theorem ragged_start_lane {d a s r : ℕ} (ha : 0 < a) (q : Fin (d*d*a)) (i : Fin s) :
    ((raggedLayout d a s r ha).start (q : ℤ)).toNat + i.val =
      (raggedAddress d a s r (.inl (q,i)) : ℕ) := by
  have hdiv : q.val / a < d*d := (Nat.div_lt_iff_lt_mul ha).mpr q.isLt
  have hdivz : ((q.val : ℤ) / a) ≤ (d*d : ℕ) := by exact_mod_cast hdiv.le
  have hnn : 0 ≤ (q.val : ℤ) / a := Int.ediv_nonneg (by omega) (by omega)
  push_cast at hdivz
  have hstart : (raggedLayout d a s r ha).start (q : ℤ) = ((q.val*s + q.val/a*r : ℕ) : ℤ) := by
    simp [raggedLayout, pastTails, min_eq_right hdivz, max_eq_right hnn]
  rw [hstart, Int.toNat_natCast, payload_address_val]
  have hq := Nat.div_add_mod q.val a
  nlinarith only [congrArg (fun x : ℕ => x*s) hq]

/-- A successfully transposed bit stream identifies the actual packet at every past
that has already emitted all its lanes. The tail pattern is arbitrary. -/
theorem identified_output_packet {d a s r : ℕ} (ha : 0 < a) (x : Payload d a s)
    (q : Fin (d*d*a)) (pre rest : List Bool)
    (hfull : ∀ i : Fin s,
      (pre ++ rest)[(raggedAddress d a s r (.inl (tposOf d a q,i)) : ℕ)]? = some (x q i))
    (hready : ((raggedLayout d a s r ha).start (tposOf d a q : ℤ)).toNat + s ≤ pre.length) :
    (raggedLayout d a s r ha).payloadAt (tposOf d a q : ℤ) pre = x q := by
  funext i
  have hi := hfull i
  rw [← ragged_start_lane ha, List.getElem?_append_left (by omega)] at hi
  simp [CellLayout.payloadAt, hi]

/-- An actual native batch appends a word of at most its number of ticks, including after halt. -/
theorem native_output_append (M : TM) (w : List Bool) (t n : ℕ) :
    ∃ fresh : List Bool, fresh.length ≤ n ∧
      (run M w (t+n)).outRev.reverse = (run M w t).outRev.reverse ++ fresh := by
  obtain ⟨fresh, h⟩ := exists_outRev_append (M := M) w t n
  refine ⟨fresh, ?_, h⟩
  have hh := congrArg List.length h
  simp only [List.length_reverse, List.length_append] at hh
  have hlen : (run M w (t+n)).outRev.length ≤ (run M w t).outRev.length + n := by
    clear h hh
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← Nat.add_assoc, outRev_length_succ]
      split <;> omega
  omega

/-- Any increasing integer output counter starting at zero and moving by at most one per
batch attains the transition for each completed packet, at a prehalt batch. -/
theorem exists_output_crossing (count : ℕ → ℤ) (hzero : count 0 = 0)
    (hstep : ∀ j, count (j+1) ≤ count j + 1) (R q : ℕ) (hend : (q : ℤ) < count R) :
    ∃ j < R, count j = q ∧ count (j+1) = (q : ℤ) + 1 := by
  induction R with
  | zero => omega
  | succ R ih =>
    by_cases h : (q : ℤ) < count R
    · obtain ⟨j, hj, he⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, he⟩
    · have := hstep R
      exact ⟨R, Nat.lt_succ_self _, by omega, by omega⟩

/-- The ragged packet counter reaches precisely the number of payload packets at the true
end of a matrix output, regardless of the tail length. -/
theorem ragged_end {d a s r : ℕ} (ha : 0 < a) (hs : 0 < s) :
    (raggedLayout d a s r ha).cell hs (d*d*(a*s+r) : ℕ) = (d*d*a : ℕ) := by
  let L := raggedLayout d a s r ha
  have hstart : L.start ((d*d*a : ℕ) : ℤ) = ((d*d*(a*s+r) : ℕ) : ℤ) := by
    have h : ((d*d*a : ℕ) : ℤ) / a = (d*d : ℕ) := by
      rw [← Int.natCast_div, Nat.mul_div_cancel _ ha]
    change ((d*d*a : ℕ) : ℤ) * s + max 0 (min ((d*d : ℕ) : ℤ) (_ / a)) * r = _
    rw [h, min_self, max_eq_right (Int.natCast_nonneg _)]
    push_cast
    ring
  apply L.cell_eq hs hstart.le
  have := L.lower ((d*d*a : ℕ) : ℤ)
  omega

/-- Locate the actual source batch that completes each required output packet. The source may
already have halted when the common padded horizon of R batches is reached. -/
theorem native_output_crossing (M : TM) (w : List Bool) {d a s r R : ℕ}
    (ha : 0 < a) (hs : 0 < s)
    (hfinal : (run M w (R*s)).outRev.length = d*d*(a*s+r)) (q : Fin (d*d*a)) :
    let L := raggedLayout d a s r ha
    ∃ j < R, L.cell hs (run M w (j*s)).outRev.length = (q : ℤ) ∧
      L.cell hs (run M w ((j+1)*s)).outRev.length = (q : ℤ) + 1 := by
  intro L
  let count := fun j => L.cell hs ((run M w (j*s)).outRev.length : ℤ)
  have hzero : count 0 = 0 := by simp [count, run, init, L.cell_zero hs]
  have hstep (j : ℕ) : count (j+1) ≤ count j + 1 := by
    obtain ⟨fresh, hlen, heq⟩ := native_output_append M w (j*s) s
    have h := (L.output_cell_step hs (run M w (j*s)).outRev.reverse fresh hlen).2
    simpa only [← heq, List.length_reverse, count, Nat.add_mul, one_mul] using h
  have hq : (q.val : ℤ) < count R := by
    simp only [count, hfinal, L, ragged_end ha hs]
    exact_mod_cast q.isLt
  exact exists_output_crossing count hzero hstep R q hq

/-- On a correct completed stream, the payload read at that actual batch already equals
the transposed input packet. The proof uses no assumption about future bit values except
that the final stream has the prescribed transpose. -/
theorem native_output_at_crossing {M : TM} {w : List Bool} {d a s r R : ℕ}
    (ha : 0 < a) (hs : 0 < s) (u : Payload d a s) (q : Fin (d*d*a))
    (hfinal : (run M w (R*s)).outRev.length = d*d*(a*s+r))
    (hout : ∀ i, (run M w (R*s)).outRev.reverse[
      (raggedAddress d a s r (.inl (tposOf d a q, i)) : ℕ)]? = some (u q i)) :
    let L := raggedLayout d a s r ha
    let addr : ℤ := tposOf d a q
    ∃ j < R, L.cell hs (run M w (j*s)).outRev.length = addr ∧
      L.cell hs (run M w ((j+1)*s)).outRev.length = addr + 1 ∧
      L.payloadAt addr (run M w ((j+1)*s)).outRev.reverse = u q := by
  intro L addr
  obtain ⟨j, hj, hq, hq'⟩ := native_output_crossing M w ha hs hfinal (tposOf d a q)
  refine ⟨j, hj, hq, hq', ?_⟩
  have ht : (j+1)*s ≤ R*s := Nat.mul_le_mul_right _ hj
  obtain ⟨rest, hrest⟩ := exists_outRev_append (M := M) w ((j+1)*s) (R*s - (j+1)*s)
  rw [Nat.add_sub_of_le ht] at hrest
  apply identified_output_packet ha u q _ rest
  · simpa only [← hrest] using hout
  · have hlow := (L.contains hs ((run M w ((j+1)*s)).outRev.length : ℤ)).1
    change L.cell hs (run M w ((j+1)*s)).outRev.length = addr + 1 at hq'
    rw [hq'] at hlow
    have hb := L.lower addr
    have hnn := (L.strictMono hs).monotone (show 0 ≤ addr by dsimp [addr]; positivity)
    rw [L.zero] at hnn
    simp only [List.length_reverse]
    change (L.start addr).toNat + s ≤ _
    omega

end TapeStorageRates.PacketCompiler
