import AdaptiveTransfer.PersistenceFuture
import AdaptiveTransfer.PersistenceWholeWord

/-! Actual input-dependent future horizons in one common finite tape window.
The future horizon and the observation window are separate: a probability law
can use one vertex type while every input retains only its own successful
future reads. No native access to future information is asserted.
-/

namespace AdaptiveTransfer.PersistenceFutureWindow

open Transpose Transpose.Tape Transpose.Tape.Impl LeanMachine
open PersistenceGraph PersistenceFuture FiniteTapeGraph Finset BoundedNesting
attribute [local instance] Classical.propDecidable

noncomputable def vertex (M : TM) (w : List Bool) (τ T t : ℕ) (h : Fin M.k) :
    Vertex (Fin (M.g + 1)) (2 * T + 1) :=
  (fun i => word M w τ (min t T) h (address T i), (PersistenceGraph.vertex M w T t h).2)

theorem native_step (M : TM) (w : List Bool) (τ T : ℕ) (h : Fin M.k)
    {t : ℕ} (ht : t < T) : Step (vertex M w τ T t h) (vertex M w τ T (t + 1) h) := by
  refine ⟨(PersistenceGraph.native_step M w T h ht).1,
    word M w τ (t + 1) h ((run M w t).workPos h), ?_⟩
  funext i
  change word M w τ (min (t + 1) T) h (address T i) =
    Function.update (fun j => word M w τ (min t T) h (address T j))
      (PersistenceGraph.vertex M w T t h).2
      (word M w τ (t + 1) h ((run M w t).workPos h)) i
  rw [min_eq_left (show t + 1 ≤ T by omega), min_eq_left ht.le, Function.update_apply,
    word_update M w τ t h (address T i)]
  have haddr : address T (PersistenceGraph.vertex M w T t h).2 = (run M w t).workPos h := by
    simpa only [min_eq_left ht.le] using vertex_head_address M w T t h
  by_cases hi : i = (PersistenceGraph.vertex M w T t h).2
  · simp [hi, haddr]
  · have hz : address T i ≠ (run M w t).workPos h := by
      intro he
      apply hi
      have hh := congrArg (posCode T) (he.trans haddr.symm)
      simpa only [posCode_address] using hh
    simp [hi, hz]

theorem native_ball (M : TM) (w : List Bool) (τ T : ℕ) (h : Fin M.k)
    {u t R : ℕ} (hut : u ≤ t) (ht : t ≤ T) (hR : t - u ≤ R) :
    vertex M w τ T t h ∈ GraphBall.closedBall (graph (Fin (M.g + 1)) (2 * T + 1))
      (vertex M w τ T u h) R := by
  have hd := path_edist_le (fun s => vertex M w τ T s h)
    (u := u) (l := t - u) (fun j hj => native_step M w τ T h (by omega))
  rw [Nat.add_sub_of_le hut] at hd
  simp only [GraphBall.closedBall, mem_filter, mem_univ, true_and]
  exact hd.trans (by exact_mod_cast hR)

theorem vertex_initial (M : TM) (w : List Bool) (τ T : ℕ) (h : Fin M.k) :
    vertex M w τ T 0 h = PersistenceGraph.vertex M [] T 0 h := by
  apply Prod.ext
  · funext i
    simp only [vertex, PersistenceGraph.vertex, Nat.zero_min, word]
    change (if FutureVisit M w τ 0 h (address T i) then 0 else 0) = 0
    simp
  · rfl

theorem extendWord_vertex (M : TM) (w : List Bool) (τ T t : ℕ) (h : Fin M.k) (ht : t ≤ T) :
    PersistenceGraph.extendWord (0 : Fin (M.g + 1)) T (vertex M w τ T t h).1 =
      word M w τ t h := by
  funext z
  by_cases hz : |z| ≤ T
  · simp only [PersistenceGraph.extendWord, hz, ite_true, vertex, min_eq_left ht,
      address_posCode hz]
  · simp only [PersistenceGraph.extendWord, hz, ite_false, word]
    have hblank : (run M w t).work h z = 0 := by
      apply work_eq_blank
      intro u hu he
      have hb := abs_workPos_le (M := M) w u h
      rw [he] at hb
      exact hz (hb.trans (by exact_mod_cast hu.le.trans ht))
    simp only [hblank, ite_self]

noncomputable def masked (M : TM) (w : List Bool) (τ T t H : ℕ) (h : Fin M.k) :
    Fin (2 * T + 1) → Fin (M.g + 1) :=
  FiniteMaskFibres.maskedVertex 0 (FiniteMaskFibres.headWindow H) (vertex M w τ T t h)

noncomputable def remoteWord (M : TM) (w : List Bool) (τ T t H : ℕ) (h : Fin M.k) :
    ℤ → Fin (M.g + 1) := PersistenceGraph.extendWord 0 T (masked M w τ T t H h)

theorem remote_word_fibre (M : TM) (T H : ℕ) (v : ℤ → Fin (M.g + 1)) :
    (univ.filter fun x : Vertex (Fin (M.g + 1)) (2 * T + 1) =>
      PersistenceGraph.extendWord 0 T
        (FiniteMaskFibres.maskedVertex 0 (FiniteMaskFibres.headWindow H) x) = v).card ≤
      (2 * T + 1) * (M.g + 1) ^ (2 * H + 1) := by
  let target := fun i => v (address T i)
  apply le_trans (card_le_card (t := univ.filter fun x : Vertex (Fin (M.g + 1)) (2 * T + 1) =>
    FiniteMaskFibres.maskedVertex 0 (FiniteMaskFibres.headWindow H) x = target) ?_)
    (PersistenceFuture.remote_mask_fibre M T H target)
  intro x hx
  refine mem_filter.mpr ⟨mem_univ _, ?_⟩
  funext i
  have hh := congrFun (mem_filter.mp hx).2 (address T i)
  simpa only [PersistenceGraph.extendWord_address] using hh

/-- The finite mask followed by blank extension is exactly the whole actual
future word with the specified current-head window erased. -/
theorem remoteWord_eq (M : TM) (w : List Bool) (τ T t H : ℕ) (h : Fin M.k) (ht : t ≤ T) (z : ℤ) :
    remoteWord M w τ T t H h z =
      if |z - (run M w t).workPos h| ≤ H then 0 else word M w τ t h z := by
  have hword := congrFun (extendWord_vertex M w τ T t h ht) z
  by_cases hz : |z| ≤ T
  · have hhead : address T (vertex M w τ T t h).2 = (run M w t).workPos h := by
      simpa only [vertex, min_eq_left ht] using vertex_head_address M w T t h
    have hdist : ((posCode T z).val : ℤ) - (vertex M w τ T t h).2.val =
        z - (run M w t).workPos h := by
      have hh := address_posCode hz
      dsimp only [address] at hh hhead
      omega
    simp only [remoteWord, PersistenceGraph.extendWord, hz, ite_true, masked,
      FiniteMaskFibres.maskedVertex, FiniteMaskFibres.masked, FiniteMaskFibres.headWindow,
      mem_filter, mem_univ, true_and, hdist]
    congr 1
    simpa only [PersistenceGraph.extendWord, hz, ite_true] using hword
  · simp only [remoteWord, PersistenceGraph.extendWord, hz, ite_false]
    have he : word M w τ t h z = 0 := by
      simpa only [PersistenceGraph.extendWord, hz, ite_false] using hword.symm
    simp only [he, ite_self]

theorem remoteWord_successful_return (M : TM) (w : List Bool) (τ T t H : ℕ)
    (hhalt : HaltsAt M w τ) (h : Fin M.k) (ht : t ≤ T) (z : ℤ)
    (hi : remoteWord M w τ T t H h z ≠ 0) :
    ∃ p q, p < t ∧ t < q ∧ IsHop (fun s => (run M w s).workPos h) τ p q ∧
      transAt M w p ≠ none ∧ transAt M w q ≠ none ∧
      (run M w p).workPos h = z ∧
      (H : ℤ) < |(run M w t).workPos h - (run M w p).workPos h| := by
  rw [remoteWord_eq M w τ T t H h ht z] at hi
  have hfar : ¬ |z - (run M w t).workPos h| ≤ H := by intro hh; simp [hh] at hi
  have hnonzero : word M w τ t h z ≠ 0 := by simpa only [ite_eq_right hfar] using hi
  obtain ⟨p, q, hpt, htq, hhop, hz, hdist⟩ :=
    nonblank_remote_return M w τ t H h z hnonzero (lt_of_not_ge hfar)
  exact ⟨p, q, hpt, htq, hhop, hhalt.1 p (hpt.trans (htq.trans hhop.2.1)),
    hhalt.1 q hhop.2.1, hz, hdist⟩

end AdaptiveTransfer.PersistenceFutureWindow
