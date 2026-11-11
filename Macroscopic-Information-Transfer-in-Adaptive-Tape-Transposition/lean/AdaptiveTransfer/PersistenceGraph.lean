import LeanMachine.FiniteTapeGraph
import AdaptiveTransfer.PrefixOutput
import Transpose.Tape.CutTrace

/-! Actual native tape vertices in a fixed finite horizon. The graph includes
frozen ticks, so successful prefixes and halting endpoints need no separate
graph or supplied movement certificate. -/

namespace AdaptiveTransfer.PersistenceGraph

open Transpose Transpose.Tape Transpose.Tape.Impl LeanMachine
open FiniteTapeGraph Finset

def address (T : ℕ) (i : Fin (2 * T + 1)) : ℤ := (i.val : ℤ) - T

theorem address_posCode {T : ℕ} {z : ℤ} (hz : |z| ≤ T) :
    address T (posCode T z) = z := by
  have hh := abs_le.mp hz
  have hp : (z + T).toNat < 2 * T + 1 := by omega
  simp only [address, posCode, Nat.mod_eq_of_lt hp]
  omega

theorem posCode_address (T : ℕ) (i : Fin (2 * T + 1)) :
    posCode T (address T i) = i := by
  apply Fin.ext
  simp only [posCode, address]
  have hp := i.isLt
  have he : (((i.val : ℤ) - T) + T).toNat = i.val := by omega
  rw [he, Nat.mod_eq_of_lt hp]

def vertex (M : TM) (w : List Bool) (T t : ℕ) (h : Fin M.k) :
    Vertex (Fin (M.g + 1)) (2 * T + 1) :=
  (fun i => (run M w (min t T)).work h (address T i),
    posCode T ((run M w (min t T)).workPos h))

theorem vertex_head_address (M : TM) (w : List Bool) (T t : ℕ) (h : Fin M.k) :
    address T (vertex M w T t h).2 = (run M w (min t T)).workPos h := by
  apply address_posCode
  exact (abs_workPos_le w _ h).trans (by exact_mod_cast min_le_right t T)

theorem native_step (M : TM) (w : List Bool) (T : ℕ) (h : Fin M.k)
    {t : ℕ} (ht : t < T) : Step (vertex M w T t h) (vertex M w T (t + 1) h) := by
  have ht0 : min t T = t := min_eq_left ht.le
  have ht1 : min (t + 1) T = t + 1 := min_eq_left (by omega)
  have haddr0 := vertex_head_address M w T t h
  have haddr1 := vertex_head_address M w T (t + 1) h
  rw [ht0] at haddr0
  rw [ht1] at haddr1
  refine ⟨?_, writtenSym M w t h, ?_⟩
  · have hm : (run M w (t + 1)).workPos h ≤ (run M w t).workPos h + 1 ∧
        (run M w t).workPos h ≤ (run M w (t + 1)).workPos h + 1 := by
      rw [run_succ_workPos]
      cases he : transAt M w t with
      | none => simp
      | some inst =>
        rcases inst with ⟨q, d, acts, out⟩
        cases hd : (acts h).2 <;> simp [hd, Dir.shift] <;> omega
    dsimp [Near]
    dsimp [address] at haddr0 haddr1
    omega
  · funext i
    change (run M w (min (t + 1) T)).work h (address T i) =
      Function.update (fun j => (run M w (min t T)).work h (address T j))
        (posCode T ((run M w (min t T)).workPos h)) (writtenSym M w t h) i
    rw [ht0, ht1, run_succ_work, Function.update_apply]
    have he : address T i = (run M w t).workPos h ↔
        i = posCode T ((run M w t).workPos h) := by
      constructor
      · intro he
        rw [← he, posCode_address]
      · intro he
        rw [he]
        exact address_posCode ((abs_workPos_le w t h).trans (by exact_mod_cast ht.le))
    simp only [he]

theorem native_ball (M : TM) (w : List Bool) (T : ℕ) (h : Fin M.k)
    {u t R : ℕ} (hut : u ≤ t) (ht : t ≤ T) (hR : t - u ≤ R) :
    vertex M w T t h ∈ GraphBall.closedBall (graph (Fin (M.g + 1)) (2 * T + 1))
      (vertex M w T u h) R := by
  have hd := path_edist_le (fun s => vertex M w T s h)
    (u := u) (l := t - u) (fun j hj => native_step M w T h (by omega))
  rw [Nat.add_sub_of_le hut] at hd
  exact mem_filter.mpr ⟨mem_univ _, hd.trans (by exact_mod_cast hR)⟩

theorem native_ball_card (M : TM) (w : List Bool) (T u R : ℕ) (h : Fin M.k) :
    (GraphBall.closedBall (graph (Fin (M.g + 1)) (2 * T + 1))
      (vertex M w T u h) R).card ≤ (6 * (M.g + 1)) ^ (R + 1) := by
  simpa using card_ball_le (vertex M w T u h) R

/-- The finite word really determines the whole native work word: cells
outside the horizon window have never been visited and remain blank. -/
theorem word_eq_of_vertex_word {M : TM} {w w' : List Bool} {T t t' : ℕ}
    (h : Fin M.k) (ht : t ≤ T) (ht' : t' ≤ T)
    (he : (vertex M w T t h).1 = (vertex M w' T t' h).1) :
    (run M w t).work h = (run M w' t').work h := by
  funext z
  by_cases hz : |z| ≤ T
  · have hf := congr_fun he (posCode T z)
    simpa only [vertex, min_eq_left ht, min_eq_left ht', address_posCode hz] using hf
  · have hblank (v : List Bool) (s : ℕ) (hs : s ≤ T) : (run M v s).work h z = 0 := by
      apply work_eq_blank
      intro u hu he
      have hb := abs_workPos_le (M := M) v u h
      rw [he] at hb
      exact hz (hb.trans (by exact_mod_cast hu.le.trans hs))
    rw [hblank w t ht, hblank w' t' ht']

end AdaptiveTransfer.PersistenceGraph
