import TapeStorageRates.NativeCoarseReplay
import TapeStorageRates.NativeCoarseFloor
import TapeStorageRates.BatchCoarseningGeometry

namespace TapeStorageRates.Native

open Transpose MergeDepth BoundedNesting

/-- Nine padded coarse slots for every complete native batch; the final drain
and the frozen suffix remain at the final anchor. -/
def coarseHead {k : ℕ} (as : List (Descriptor k)) (h : Option (Fin k)) (q : ℕ) : ℤ :=
  if hj : q/9<as.length then
    batchAnchor as h (q/9)+coarseOffset (headCarry as[q/9] h) (q%9)
  else batchAnchor as h as.length

def coarseWork {k : ℕ} (as : List (Descriptor k)) (h : Fin k) : ℕ → ℤ :=
  coarseHead as (some h)

def coarseTime (s N t : ℕ) : ℕ :=
  if t/(10*s+1)<N then 9*(t/(10*s+1))+fineSlot s (t%(10*s+1)) else 9*N

theorem batchAnchor_succ {k : ℕ} (as : List (Descriptor k)) (h : Option (Fin k))
    (j : ℕ) (hj : j<as.length) :
    batchAnchor as h (j+1)=batchAnchor as h j+moveInt (direction (headCarry as[j] h)) := by
  unfold batchAnchor
  rw [List.take_succ_eq_append_getElem hj]
  simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,
    List.sum_cons,List.sum_nil,add_zero]

theorem coarseHead_walk {k : ℕ} (as : List (Descriptor k)) (h : Option (Fin k)) :
    IsWalk (coarseHead as h) := by
  intro q
  by_cases hj : q/9<as.length
  · by_cases hr : q%9<8
    · have he : (q+1)/9=q/9 := by omega
      have hm : (q+1)%9=q%9+1 := by omega
      simpa [coarseHead,hj,he,hm] using coarseOffset_step (headCarry as[q/9] h) (q%9) hr
    · have hm : q%9=8 := by omega
      have he : (q+1)/9=q/9+1 := by omega
      have hm' : (q+1)%9=0 := by omega
      have ha := batchAnchor_succ as h (q/9) hj
      by_cases hn : q/9+1<as.length
      · simp [coarseHead,hj,he,hm,hm',hn,ha,coarseOffset]
      · have hn' : q/9+1=as.length := by omega
        simp [coarseHead,he,hm,← hn',ha,coarseOffset]
  · have hn : ¬(q+1)/9<as.length := by omega
    simp [coarseHead,hj,hn]

theorem coarseWork_isWalk {k : ℕ} (as : List (Descriptor k)) (h : Fin k) :
    IsWalk (coarseWork as h) := coarseHead_walk as (some h)

theorem coarseTime_lt (s N t : ℕ) : coarseTime s N t<9*N+1 := by
  have hslot := fineSlot_lt s (t%(10*s+1))
  unfold coarseTime
  split_ifs <;> omega

theorem coarseTime_owner (s N t : ℕ) (ht : t<(10*s+1)*N+s) :
    coarseTime s N t/9=t/(10*s+1) := by
  have hd := Nat.div_add_mod t (10*s+1)
  have hm := Nat.mod_lt t (show 0<10*s+1 by omega)
  have hslot := fineSlot_lt s (t%(10*s+1))
  unfold coarseTime
  split_ifs with he
  · omega
  · have hn : t/(10*s+1)=N := by
      have hmul : (10*s+1)*(t/(10*s+1))≤t := Nat.mul_div_le t (10*s+1)
      nlinarith
    omega

theorem coarseTime_mono (s N : ℕ) : Monotone (coarseTime s N) := by
  intro a b hab
  have hd : a/(10*s+1)≤b/(10*s+1) := Nat.div_le_div_right hab
  have sa := fineSlot_lt s (a%(10*s+1))
  have sb := fineSlot_lt s (b%(10*s+1))
  unfold coarseTime
  split_ifs with ha hb
  · by_cases he : a/(10*s+1)=b/(10*s+1)
    · have hr : a%(10*s+1)≤b%(10*s+1) := by
        have ea := Nat.div_add_mod a (10*s+1)
        have eb := Nat.div_add_mod b (10*s+1)
        rw [he] at ea
        omega
      have := fineSlot_mono s hr
      omega
    · omega
  · omega
  · omega
  · omega

theorem fineOffset_ediv {s : ℕ} (hs : 0<s) (e : Fin 3) (i : ℕ)
    (hi : i<10*s+1) : fineOffset s e i/(s : ℤ)=coarseOffset e (fineSlot s i) := by
  obtain ⟨lo,hi'⟩ := fineOffset_block hs e i hi
  have sp : (0 : ℤ)<s := by omega
  apply le_antisymm
  · have := (Int.ediv_lt_iff_lt_mul sp).mpr (by nlinarith :
      fineOffset s e i<(coarseOffset e (fineSlot s i)+1)*(s : ℤ))
    omega
  · exact (Int.le_ediv_iff_mul_le sp).mpr (by nlinarith)

theorem coarseHead_position {k s : ℕ} (hs : 0<s) (r : Fin s) (as : List (Descriptor k))
    (h : Option (Fin k)) (t : ℕ) :
    coarseHead as h (coarseTime s as.length t)=headPosition (replay r as) h t/(s : ℤ) := by
  let j := t/(10*s+1)
  let i := t%(10*s+1)
  have hi : i<10*s+1 := Nat.mod_lt _ (by omega)
  have split : (10*s+1)*j+i=t := Nat.div_add_mod _ _
  have sp : (s : ℤ)≠0 := by omega
  by_cases hj : j<as.length
  · have e : coarseTime s as.length t=9*j+fineSlot s i := by simp [coarseTime,j,i,hj]
    have jq : (9*j+fineSlot s i)/9=j := by have := fineSlot_lt s i; omega
    have iq : (9*j+fineSlot s i)%9=fineSlot s i := by have := fineSlot_lt s i; omega
    rw [e]
    simp only [coarseHead,jq,iq,hj,↓reduceDIte]
    rw [← split,
      replay_head_batch hs r as h j hj i hi.le]
    rw [show (s : ℤ)*batchAnchor as h j+fineOffset s (headCarry as[j] h) i=
      fineOffset s (headCarry as[j] h) i+batchAnchor as h j*(s : ℤ) by ring,
      Int.add_mul_ediv_right _ _ sp,fineOffset_ediv hs _ i hi]
    omega
  · have he : coarseTime s as.length t=9*as.length := by simp [coarseTime,j,hj]
    have hn : (10*s+1)*as.length≤t := by
      have hm := Nat.mul_div_le t (10*s+1)
      dsimp [j] at hj
      nlinarith
    rw [he,coarseHead,dite_eq_right (by omega),
      show t=(10*s+1)*as.length+(t-(10*s+1)*as.length) by omega,
      replay_head_drain hs r as h,Int.mul_ediv_cancel_left _ sp]

theorem coarseOffset_bounds (e : Fin 3) (u : ℕ) (hu : u<9) :
    -1 ≤ coarseOffset e u ∧ coarseOffset e u ≤ 1 := by
  interval_cases u <;> fin_cases e <;> norm_num [coarseOffset,direction,moveInt]

/-- A complete batch visits every physical cell in each of its coarse blocks.
The reading sweep alone supplies every witness, regardless of the carry. -/
theorem replay_full_block {k s : ℕ} (hs : 0<s) (r : Fin s)
    (as : List (Descriptor k)) (h : Option (Fin k)) (q : ℕ) (c : ℤ)
    (hj : q/9<as.length) (hc : c/(s : ℤ)=coarseHead as h q) :
    ∃ t<(10*s+1)*as.length+s,
      t/(10*s+1)=q/9 ∧ headPosition (replay r as) h t=c := by
  let j := q/9
  let a := batchAnchor as h j
  let e := headCarry as[j] h
  let u := coarseOffset e (q%9)
  have hu : -1≤u ∧ u≤1 := coarseOffset_bounds e (q%9) (Nat.mod_lt _ (by omega))
  have he : c/(s : ℤ)=a+u := by simpa [coarseHead,hj,j,a,e,u] using hc
  have sp : (0 : ℤ)<s := by omega
  have hlo : (a+u)*(s : ℤ)≤c :=
    (Int.le_ediv_iff_mul_le sp).mp he.ge
  have hhi : c<(a+u+1)*(s : ℤ) :=
    (Int.ediv_lt_iff_lt_mul sp).mp (by omega)
  let z := c-(s : ℤ)*a+s
  have hz : 0≤z ∧ z<3*(s : ℤ) := by
    have hl := mul_nonneg (by linarith [hu.1] : 0≤u+1) sp.le
    have hh := mul_nonneg (by linarith [hu.2] : 0≤1-u) sp.le
    dsimp [z]
    constructor <;> nlinarith
  let i := z.toNat
  have hiCast : (i : ℤ)=z := Int.toNat_of_nonneg hz.1
  have hi : i<3*s := by omega
  have hoff : s+i<10*s+1 := by omega
  let t := (10*s+1)*j+(s+i)
  have ht : t<(10*s+1)*as.length+s := by
    have hm := Nat.mul_le_mul_left (10*s+1) hj
    dsimp [t,j]
    nlinarith
  refine ⟨t,ht,?_,?_⟩
  · dsimp [t,j]
    rw [Nat.mul_add_div (by omega : 0<10*s+1),Nat.div_eq_of_lt hoff,Nat.add_zero]
  · dsimp [t]
    rw [replay_head_batch hs r as h j hj (s+i) hoff.le,fineOffset_read hs e i hi]
    dsimp [a,e,z] at hiCast ⊢
    omega

/-- The exact native replay, including its final partial drain, satisfies the
complete-block interface needed to lift dependency paths. -/
def replay_completeCover {k s : ℕ} (hs : 0<s) (r : Fin s)
    (as : List (Descriptor k)) :
    BatchCoarsening.CompleteBlockCover (replay r as).work
      ((10*s+1)*as.length+s) (coarseWork as) (9*as.length+1)
      (10*s+1) s as.length where
  positive := by omega
  phi := coarseTime s as.length
  owner := fun q => q/9
  phi_lt := fun t _ => coarseTime_lt s as.length t
  phi_mono := fun _ _ hab _ => coarseTime_mono s as.length hab
  owner_mono := fun _ _ hab => Nat.div_le_div_right hab
  owns := coarseTime_owner s as.length
  positions := fun h t _ => coarseHead_position hs r as (some h) t
  batch_bound := by
    intro t ht
    have hm := Nat.mul_div_le t (10*s+1)
    by_contra! hn
    have hmul := Nat.mul_le_mul_left (10*s+1) hn
    nlinarith
  full := fun h q c _ hj hc => replay_full_block hs r as (some h) q c hj hc

end TapeStorageRates.Native
