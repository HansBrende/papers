import BitWord.NativeCrossPad
import BitWord.CanonicalGates
import TransposeFollowup.EntryBitsRun
import TransposeFollowup.NativeExpanderShearHalf

/-! Binary parameter words for the large canonical gate recipe. Their widths
match the literal addition/subtraction callers; all padding is paid separately. -/
namespace BitWord.CanonicalMetadata
open FixedTapeCompiler TransposeFollowup
set_option autoImplicit false

theorem entryBits_eq_clog {n : ℕ} (hn : 2 ≤ n) : Transpose.entryBits n=Nat.clog 2 n := by
  have hs : (n-1).size=Nat.clog 2 n := by
    apply le_antisymm
    · apply Nat.size_le.mpr
      have := Nat.le_pow_clog (by decide : 1<2) n
      omega
    · apply Nat.clog_le_of_le_pow
      have := Nat.size_le.mp (le_refl (n-1).size)
      omega
  rw [EntryBits.entryBits_eq,hs]
  exact max_eq_right (Nat.clog_pos (by decide) (by omega))

def hword (h : ℕ) := MeasuredWord.result h
def uword (h : ℕ) := MeasuredWord.result (laneBits h)
def width (h : ℕ) := h+laneBits h+2

def H (h : ℕ) := NativeCrossPad.padded 2 (hword h) (uword h)
def U (h : ℕ) := NativeCrossPad.padded 3 (uword h) (hword h)
def zero (h : ℕ) := (U h).map (fun _ => false)
def increment (h : ℕ) := (BinaryCarry.result false true (U h) (zero h)).1
def V (h : ℕ) := (increment h).tail

def W (h : ℕ) := (BinaryCarry.result false false (V h) (V h)).1
def N (h : ℕ) := (BinaryCarry.result false false (H h) (V h)).1
def R (h : ℕ) := (BinaryCarry.result true true (H h) (V h)).1

@[simp] theorem hword_length (h : ℕ) : (hword h).length=h := MeasuredWord.result_length h
@[simp] theorem hword_value (h : ℕ) : Counter.value (hword h)=h := MeasuredWord.result_value h
@[simp] theorem uword_length (h : ℕ) : (uword h).length=laneBits h := MeasuredWord.result_length _
@[simp] theorem uword_value (h : ℕ) : Counter.value (uword h)=laneBits h := MeasuredWord.result_value _
@[simp] theorem H_length (h : ℕ) : (H h).length=width h := by simp [H,width]
@[simp] theorem H_value (h : ℕ) : Counter.value (H h)=h := by simp [H]
@[simp] theorem U_length (h : ℕ) : (U h).length=width h+1 := by simp [U,width]; omega
@[simp] theorem U_value (h : ℕ) : Counter.value (U h)=laneBits h := by simp [U]
@[simp] theorem zero_length (h : ℕ) : (zero h).length=width h+1 := by simp [zero]
@[simp] theorem zero_value (h : ℕ) : Counter.value (zero h)=0 := by
  simp only [zero,List.map_const']
  exact PaddedWord.value_zeroes _
@[simp] theorem increment_length (h : ℕ) : (increment h).length=width h+1 := by
  rw [increment,BinaryCarry.result_length _ _ _ _ (by simp),U_length]
@[simp] theorem V_length (h : ℕ) : (V h).length=width h := by simp [V]

private theorem parameter_capacity (h : ℕ) : h+laneBits h+2 < 2^width h := by
  exact Nat.lt_two_pow_self

theorem increment_value (h : ℕ) : Counter.value (increment h)=laneBits h+1 := by
  have hi := BinaryCarry.result_identity false true (U h) (zero h) (by simp)
  simp only [←NativeCounter.word_value,BinaryCarry.operandWord_false,Bool.toNat_true,
    U_length,U_value,zero_value] at hi
  have hc : (BinaryCarry.result false true (U h) (zero h)).2=false := by
    have hp := parameter_capacity h
    cases hv : (BinaryCarry.result false true (U h) (zero h)).2
    · rfl
    · simp only [hv,Bool.toNat_true,Nat.mul_one] at hi
      rw [pow_succ] at hi
      omega
  rw [hc] at hi
  simpa [increment] using hi

theorem V_value (h : ℕ) : Counter.value (V h)=(laneBits h+1)/2 := by
  have hn : increment h ≠ [] := by intro hz; have := increment_length h; simp [hz] at this
  cases he : increment h with
  | nil => exact False.elim (hn he)
  | cons a xs =>
    have hv := NativeExpanderShearHalf.half_value a xs
    rw [←he,increment_value] at hv
    simpa only [V,he,List.tail_cons] using hv

theorem twice_half (u : ℕ) : 2*((u+1)/2)=u+u%2 := by omega

theorem W_value (h : ℕ) : Counter.value (W h)=tailBits h := by
  have hp := parameter_capacity h
  have he := twice_half (laneBits h)
  have ha := BinaryCarry.add_value (V h) (V h) rfl
  simp only [←NativeCounter.word_value,V_value,V_length] at ha
  have hb : (laneBits h+1)/2+(laneBits h+1)/2 < 2^width h := by omega
  have hv := ha hb
  simpa [W,tailBits,dummyBits,←he,two_mul] using hv

@[simp] theorem W_length (h : ℕ) : (W h).length=width h := by
  rw [W,BinaryCarry.result_length _ _ _ _ rfl,V_length]

theorem N_value (h : ℕ) : Counter.value (N h)=halfAddress h := by
  have hp := parameter_capacity h
  have ha := BinaryCarry.add_value (H h) (V h) (by simp)
  simp only [←NativeCounter.word_value,H_value,V_value,H_length] at ha
  have hb : h+(laneBits h+1)/2 < 2^width h := by omega
  have hv := ha hb
  have he := twice_half (laneBits h)
  simpa [N,halfAddress,tailBits,dummyBits,←he] using hv

@[simp] theorem N_length (h : ℕ) : (N h).length=width h := by
  rw [N,BinaryCarry.result_length _ _ _ _ (by simp),H_length]

theorem R_value {h : ℕ} (hh : 32 ≤ h) : Counter.value (R h)=halfAddress h-tailBits h := by
  have hs := large_halfAddress hh
  have he := twice_half (laneBits h)
  have hv : (laneBits h+1)/2 ≤ h := by
    simp only [halfAddress,tailBits,dummyBits,←he] at hs
    omega
  have ha := BinaryCarry.subtract_value (H h) (V h) (by simp)
  simp only [←NativeCounter.word_value,H_value,V_value] at ha
  have hb := ha hv
  change Counter.value (R h)=h-(laneBits h+1)/2 at hb
  rw [hb]
  simp only [halfAddress,tailBits,dummyBits,←he]
  omega

@[simp] theorem R_length (h : ℕ) : (R h).length=width h := by
  rw [R,BinaryCarry.result_length _ _ _ _ (by simp),H_length]

end BitWord.CanonicalMetadata
