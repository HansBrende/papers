import TapeStorageRates.PaidClassesTime
import TapeStorageRates.PacketCompilerSchedule
import TapeStorageRates.PacketOutput

/-! # A common append-time map on each attained padded schedule -/

namespace TapeStorageRates.PaidClasses

open Finset MergeDepth PaidInputs PacketCompiler
open Transpose Transpose.Tape Transpose.Tape.Impl

set_option autoImplicit false

/-- The actual raw input produced by stitching payloads to a fixed public tail. -/
def rawWord {d a s r : ℕ} (z : Raw d r) (x : Payload d a s) : List Bool :=
  List.ofFn ((splitWord d a s r).symm (x,z))

/-- The bounded list of carries and flush flags from the actual frozen-after-halt run. -/
noncomputable def schedule {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM)
    (R : ℕ) (w : List Bool) : Fin R → Native.Descriptor M.k :=
  fun j => descriptor (centres L hs M w j) (centres L hs M w (j.val+1))

theorem centres_of_schedule_eq {s r R : ℕ} {L : CellLayout s r} {hs : 0<s} {M : TM}
    {v w : List Bool} (h : schedule L hs M R v = schedule L hs M R w) :
    ∀ j ≤ R, centres L hs M v j = centres L hs M w j :=
  centres_agree fun j hj => congrFun h ⟨j,hj⟩

/-- A successful word has completed every correct output bit by the end of
the common padded batch horizon. -/
theorem completed_output {M : TM} {c : ℝ} {d a s r R : ℕ} (hs : 0<s)
    (z : Raw d r) {x : Payload d a s}
    (hx : x ∈ payloadFibre (successfulInputsAt M c d (a*s+r)) z)
    (hR : ⌊c*(((d*d*(a*s+r) : ℕ) : ℝ)+1)⌋₊ / s + 1 ≤ R) :
    (run M (rawWord z x) (R*s)).outRev.length = d*d*(a*s+r) ∧
    ∀ q l, (run M (rawWord z x) (R*s)).outRev.reverse[
      (raggedAddress d a s r (.inl (tposOf d a q,l))).val]? = some (x q l) := by
  obtain ⟨t,ht,hhalt,hlen,hout,_⟩ := successful_payload_output x z hx
  let limit := ⌊c*(((d*d*(a*s+r) : ℕ) : ℝ)+1)⌋₊
  have hpad : limit ≤ (limit/s+1)*s := by
    have h := Nat.div_add_mod' limit s
    have hr := Nat.mod_lt limit hs
    rw [Nat.add_mul, one_mul]
    omega
  have htime : t ≤ R*s := ht.trans (hpad.trans (Nat.mul_le_mul_right s hR))
  rw [run_of_le_of_none (M := M) (w := rawWord z x) hhalt.2 htime]
  exact ⟨by simpa only [List.length_reverse,rawWord] using hlen, hout⟩

private theorem unique_crossing {f : ℕ → ℤ} (hm : Monotone f) {j j' : ℕ} {q : ℤ}
    (h : f j=q) (h1 : f (j+1)=q+1) (h' : f j'=q) (h1' : f (j'+1)=q+1) : j=j' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · have hv : f (j+1) ≤ f j' := hm hlt
    rw [h1,h'] at hv
    omega
  · exact heq
  · have hv : f (j'+1) ≤ f j := hm hgt
    rw [h1',h] at hv
    omega

/-- The same batch completes each demanded packet on every member of the
class. Its emitted value there is the packet of that input. -/
theorem common_crossing {M : TM} {c : ℝ} {d a s r R : ℕ} (ha : 0<a) (hs : 0<s)
    (z : Raw d r) (S : Finset (Payload d a s)) (hne : S.Nonempty)
    (hgood : S ⊆ payloadFibre (successfulInputsAt M c d (a*s+r)) z)
    (hR : ⌊c*(((d*d*(a*s+r) : ℕ) : ℝ)+1)⌋₊ / s + 1 ≤ R)
    (w₀ : List Bool)
    (hgeo : ∀ x ∈ S, ∀ j ≤ R,
      centres (raggedLayout d a s r ha) hs M (rawWord z x) j =
      centres (raggedLayout d a s r ha) hs M w₀ j) :
    let L := raggedLayout d a s r ha
    ∃ b : Fin (d*d*a) → ℕ, ∀ q, b q<R ∧
      (centres L hs M w₀ (b q)).output = ((tposOf d a q).val : ℤ) ∧
      ∀ x ∈ S,
        (centres L hs M (rawWord z x) (b q)).output = ((tposOf d a q).val : ℤ) ∧
        (centres L hs M (rawWord z x) (b q+1)).output = ((tposOf d a q).val : ℤ)+1 ∧
        L.payloadAt ((tposOf d a q).val : ℤ) (run M (rawWord z x) ((b q+1)*s)).outRev.reverse = x q := by
  intro L
  let count (w : List Bool) (j : ℕ) := (centres L hs M w j).output
  have eqc (x) (hx : x∈S) (j) (hj : j≤R) : count (rawWord z x) j = count w₀ j :=
    congrArg Centres.output (hgeo x hx j hj)
  have hm : Monotone (count w₀) := monotone_nat_of_le_succ fun j => by
    rcases centres_output_step L hs M w₀ j with h | h <;> dsimp [count] <;> omega
  have hX (x) (hx : x ∈ S) (q : Fin (d*d*a)) :
      ∃ j<R, count (rawWord z x) j = ((tposOf d a q).val : ℤ) ∧
        count (rawWord z x) (j+1) = ((tposOf d a q).val : ℤ)+1 ∧
        L.payloadAt ((tposOf d a q).val : ℤ) (run M (rawWord z x) ((j+1)*s)).outRev.reverse = x q := by
    have h := completed_output hs z (hgood hx) hR
    exact native_output_at_crossing ha hs x q h.1 (h.2 q)
  obtain ⟨x₀,hx₀⟩ := hne
  choose b hb hb₀ hb₁ _ using hX x₀ hx₀
  refine ⟨b, fun q => ?_⟩
  have h0 := (eqc x₀ hx₀ (b q) (hb q).le).symm.trans (hb₀ q)
  have h1 := (eqc x₀ hx₀ (b q+1) (hb q)).symm.trans (hb₁ q)
  refine ⟨hb q,h0,fun x hx => ?_⟩
  obtain ⟨j,hj,hj0,hj1,hbits⟩ := hX x hx q
  have hj' := unique_crossing hm ((eqc x hx j hj.le).symm.trans hj0)
    ((eqc x hx (j+1) hj).symm.trans hj1) h0 h1
  subst j
  exact ⟨hj0,hj1,hbits⟩

/-- A map on physical output indices from completion batches indexed by original demand. -/
def outputClock {d a : ℕ} (b : Fin (d*d*a) → ℕ) (q : ℕ) : ℕ :=
  if h : q < d*d*a then 11*b (tposOf d a ⟨q,h⟩)+10 else 0

@[simp] theorem outputClock_at {d a : ℕ} (b : Fin (d*d*a) → ℕ) (q : Fin (d*d*a)) :
    outputClock b (MergeDepth.tpos d a q) = 11*b q+10 := by
  have he : (tposOf d a q).val = MergeDepth.tpos d a q := (tposOf_val d a q).trans (tape_tpos_eq _ _ _)
  rw [← he]
  simp [outputClock, (tposOf d a q).isLt, tposOf_tposOf]

end TapeStorageRates.PaidClasses
