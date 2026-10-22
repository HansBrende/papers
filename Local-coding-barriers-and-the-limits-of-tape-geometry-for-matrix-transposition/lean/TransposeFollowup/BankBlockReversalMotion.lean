import TransposeFollowup.BankBlockReversal
import TransposeFollowup.ScheduledMotionError

/-! An integer reference path for every prefix of block reversal. The
only non-exact phase is the repeated block transfer; its within-block
excursions cost at most five block widths. -/
namespace TransposeFollowup.BlockReverseTransfer
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CopyMachine (Sym)
set_option autoImplicit false
variable {M : Type*}

theorem coarse_error (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)
    (B n : ℕ) (hB : 0<B) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (t : Fin 2) (m : ℕ) (hm : m ≤ n*(4*B)) :
    |(trajectory (schedule read write reset B n) w c m).work.pos t-c.work.pos t-
      (if t=0 then -((m/4 : ℕ) : ℤ) else (m/4 : ℕ))| ≤ 5*B := by
  have h := repeat_block_error (blockSchedule read write reset B) (action 0 ⟨none,.stay⟩)
    (4*B) (by omega) w t (drift B t) (fun d => block_endpoint read write reset B w d t) n c m hm
  change |(trajectory (schedule read write reset B n) w c m).work.pos t-c.work.pos t-
    (m/(4*B) : ℕ)*drift B t| ≤ (4*B : ℕ) at h
  have he : (m/(4*B))*B+(m/4)%B=m/4 := by
    simpa only [Nat.div_div_eq_div_mul] using Nat.div_add_mod' (m/4) B
  have hr := Nat.mod_lt (m/4) hB
  have hez : ((m/(4*B) : ℕ) : ℤ)*B+((m/4)%B : ℕ)=(m/4 : ℕ) := by exact_mod_cast he
  have hrz : (((m/4)%B : ℕ) : ℤ)<B := by exact_mod_cast hr
  have hz : (0 : ℤ) ≤ ((m/4)%B : ℕ) := Nat.cast_nonneg _
  rw [abs_le] at h ⊢
  by_cases ht : t=0 <;> simp only [drift,ht,ite_true,ite_false,Nat.cast_mul,Nat.cast_ofNat] at h ⊢
  · constructor <;> nlinarith
  · constructor <;> nlinarith

end TransposeFollowup.BlockReverseTransfer

namespace TransposeFollowup.BankBlockReversal
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CopyMachine (Sym)
set_option autoImplicit false
variable {M : Type*}

def path (P : ℕ) (t : Fin 2) (m : ℕ) : ℤ :=
  if t=0 then ((min m P : ℕ) : ℤ)-(min ((m-P)/4) P : ℕ)+
    (min ((m-6*P)/2) P : ℕ)-(min (m-8*P) P : ℕ)
  else ((min ((m-P)/4) P : ℕ) : ℤ)-(min (m-5*P) P : ℕ)+
    (min ((m-6*P)/2) P : ℕ)-(min (m-9*P) P : ℕ)

theorem path_zero (P : ℕ) (t : Fin 2) : path P t 0=0 := by simp [path]

theorem path_after (P : ℕ) (t : Fin 2) (m : ℕ) (hm : 10*P ≤ m) : path P t m=0 := by
  have h0 : min m P=P := by omega
  have h1 : min ((m-P)/4) P=P := by omega
  have h2 : min (m-5*P) P=P := by omega
  have h3 : min ((m-6*P)/2) P=P := by omega
  have h4 : min (m-8*P) P=P := by omega
  have h5 : min (m-9*P) P=P := by omega
  simp only [path,h0,h1,h2,h3,h4,h5,sub_self,zero_add,ite_self]

theorem path_frozen (P : ℕ) (t : Fin 2) (m : ℕ) : path P t (min m (10*P))=path P t m := by
  by_cases hm : m ≤ 10*P
  · rw [Nat.min_eq_left hm]
  · rw [Nat.min_eq_right (by omega),path_after P t _ le_rfl,path_after P t m (by omega)]

theorem schedule_path_error (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)
    (B n : ℕ) (hB : 0<B) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (m : ℕ) (hm : m ≤ ticks B n) (t : Fin 2) :
    |(trajectory (schedule read write reset B n) w c m).work.pos t-c.work.pos t-path (n*B) t m| ≤ 5*B := by
  let P := n*B
  have hr (p : Fin 2) (d : NativeIO.Config (Fin 2) M) (j : ℕ) :
      (trajectory (fun _ => action p ⟨none,.left⟩) w d j).work.pos t=
        d.work.pos t+(-(if t=p then (j : ℤ) else 0)) := by
    by_cases ht : t=p <;> simpa [rewind,ht,sub_eq_add_neg] using rewind_position p w d j t
  have ha (d : NativeIO.Config (Fin 2) M) (j : ℕ) :
      (trajectory (fun _ => action 0 ⟨none,.right⟩) w d j).work.pos t=
        d.work.pos t+(if t=0 then (j : ℤ) else 0) := by
    by_cases ht : t=0 <;> simpa [advance,ht] using advance_position 0 w d j t
  have hc (d : NativeIO.Config (Fin 2) M) (j : ℕ) :
      (trajectory (ScheduledTransfer.schedule true true false read write reset) w d j).work.pos t=
        d.work.pos t+(j/2 : ℕ) := by
    have h := ScheduledTransfer.schedule_positions true true false read write reset w d j
    fin_cases t
    · simpa [ScheduledTransfer.target] using h.2
    · simpa [ScheduledTransfer.source,ScheduledTransfer.offset] using h.1
  have h5 := append_position _ _ P P w t _ _ (fun d j _ => hr 0 d j) (fun d j _ => hr 1 d j)
  have h4 := append_position _ _ (2*P) (P+P) w t _ _ (fun d j _ => hc d j) h5
  have h3 := append_position _ _ P (2*P+(P+P)) w t _ _ (fun d j _ => hr 1 d j) h4
  let g (j : ℕ) : ℤ := -(if t=1 then ((min j P : ℕ) : ℤ) else 0)+
    ((min (j-P) (2*P)/2 : ℕ)+(-(if t=0 then ((min (j-P-2*P) P : ℕ) : ℤ) else 0)+
      -(if t=1 then ((j-P-2*P-P : ℕ) : ℤ) else 0)))
  have h2 := append_position_error (BlockReverseTransfer.schedule read write reset B n) _
    (n*(4*B)) (P+(2*P+(P+P))) w t
    (fun j => if t=0 then -((j/4 : ℕ) : ℤ) else (j/4 : ℕ)) g (5*B) 0 le_rfl
    (by simp [g]) (fun d j hj => BlockReverseTransfer.coarse_error read write reset B n hB w d t j hj)
    (fun d j hj => by rw [h3 d j hj]; simp [g])
  have h1 := append_position_error (fun _ => action 0 ⟨none,.right⟩) _ P
    (n*(4*B)+(P+(2*P+(P+P)))) w t (fun j => if t=0 then (j : ℤ) else 0)
    (fun j => (if t=0 then -((min j (n*(4*B))/4 : ℕ) : ℤ) else (min j (n*(4*B))/4 : ℕ))+
      g (j-n*(4*B))) 0 (5*B)
    (by positivity) (by simp [g]) (fun d j _ => by rw [ha d j]; simp)
    (fun d j hj => by simpa only [add_zero] using h2 d j hj)
  have h := h1 c m hm
  change |(trajectory (schedule read write reset B n) w c m).work.pos t-c.work.pos t-_| ≤ 0+5*B at h
  have hN : n*(4*B)=4*P := by dsimp [P]; ring
  have he0 : min (m-P) (n*(4*B))/4=min ((m-P)/4) P := by rw [hN]; omega
  have he1 : min (m-P-n*(4*B)) P=min (m-5*P) P := by rw [hN]; omega
  have he2 : min (m-P-n*(4*B)-P) (2*P)/2=min ((m-6*P)/2) P := by rw [hN]; omega
  have he3 : min (m-P-n*(4*B)-P-2*P) P=min (m-8*P) P := by rw [hN]; omega
  have he4 : m-P-n*(4*B)-P-2*P-P=min (m-9*P) P := by
    rw [ticks_eq] at hm
    change m ≤ 10*P at hm
    rw [hN]; omega
  dsimp only [g] at h
  rw [he0,he1,he2,he3,he4] at h
  fin_cases t <;> simpa [path,sub_eq_add_neg,add_assoc,P] using h

end TransposeFollowup.BankBlockReversal
