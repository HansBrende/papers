import AdaptiveTransfer.PersistenceGraph
import AdaptiveTransfer.IncomingReturns
import LeanMachine.FiniteMaskFibres

/-! Literal future-readable words use visits below the chosen horizon; at an
actual halting horizon these are precisely successful source times. Their
one-step graph and the remote consecutive-return
witness are mathematical properties of the actual run; they do not provide
the native source with future-read access.
-/

namespace AdaptiveTransfer.PersistenceFuture

open Transpose Transpose.Tape Transpose.Tape.Impl LeanMachine
open PersistenceGraph FiniteTapeGraph Finset BoundedNesting
attribute [local instance] Classical.propDecidable

def FutureVisit (M : TM) (w : List Bool) (T t : ℕ) (h : Fin M.k) (z : ℤ) : Prop :=
  ∃ u, t ≤ u ∧ u < T ∧ (run M w u).workPos h = z

noncomputable def word (M : TM) (w : List Bool) (T t : ℕ) (h : Fin M.k) : ℤ → Fin (M.g + 1) :=
  fun z => if FutureVisit M w T t h z then (run M w t).work h z else 0

theorem word_after (M : TM) (w : List Bool) (T t : ℕ) (h : Fin M.k) (ht : T ≤ t) :
    word M w T t h = fun _ => 0 := by
  funext z
  have hn : ¬FutureVisit M w T t h z := by rintro ⟨u, hu, huT, _⟩; omega
  simp [word, hn]

theorem future_succ_away (M : TM) (w : List Bool) (T t : ℕ) (h : Fin M.k) (z : ℤ)
    (hz : z ≠ (run M w t).workPos h) :
    FutureVisit M w T (t + 1) h z ↔ FutureVisit M w T t h z := by
  constructor
  · rintro ⟨u, hu, hT, he⟩
    exact ⟨u, by omega, hT, he⟩
  · rintro ⟨u, hu, hT, he⟩
    have hu' : t + 1 ≤ u := by
      by_contra hn
      have hut : u = t := by omega
      exact hz (by simpa only [hut] using he.symm)
    exact ⟨u, hu', hT, he⟩

theorem word_update (M : TM) (w : List Bool) (T t : ℕ) (h : Fin M.k) (z : ℤ) :
    word M w T (t + 1) h z =
      if z = (run M w t).workPos h then word M w T (t + 1) h z
      else word M w T t h z := by
  by_cases hz : z = (run M w t).workPos h
  · simp [hz]
  · simp only [hz, ite_false, word, future_succ_away M w T t h z hz, run_succ_work]

noncomputable def vertex (M : TM) (w : List Bool) (T t : ℕ) (h : Fin M.k) :
    Vertex (Fin (M.g + 1)) (2 * T + 1) :=
  (fun i => word M w T (min t T) h (address T i), (PersistenceGraph.vertex M w T t h).2)

theorem native_step (M : TM) (w : List Bool) (T : ℕ) (h : Fin M.k)
    {t : ℕ} (ht : t < T) : Step (vertex M w T t h) (vertex M w T (t + 1) h) := by
  refine ⟨(PersistenceGraph.native_step M w T h ht).1,
    word M w T (t + 1) h ((run M w t).workPos h), ?_⟩
  funext i
  change word M w T (min (t + 1) T) h (address T i) =
    Function.update (fun j => word M w T (min t T) h (address T j))
      (PersistenceGraph.vertex M w T t h).2
      (word M w T (t + 1) h ((run M w t).workPos h)) i
  rw [min_eq_left (show t + 1 ≤ T by omega), min_eq_left ht.le, Function.update_apply,
    word_update M w T t h (address T i)]
  have haddr : address T (PersistenceGraph.vertex M w T t h).2 =
      (run M w t).workPos h := by
    simpa only [min_eq_left ht.le] using vertex_head_address M w T t h
  by_cases hi : i = (PersistenceGraph.vertex M w T t h).2
  · simp [hi, haddr]
  · have hz : address T i ≠ (run M w t).workPos h := by
      intro he
      apply hi
      have hh := congrArg (posCode T) (he.trans haddr.symm)
      simpa only [posCode_address] using hh
    simp [hi, hz]

theorem native_ball (M : TM) (w : List Bool) (T : ℕ) (h : Fin M.k)
    {u t R : ℕ} (hut : u ≤ t) (ht : t ≤ T) (hR : t - u ≤ R) :
    vertex M w T t h ∈ GraphBall.closedBall (graph (Fin (M.g + 1)) (2 * T + 1))
      (vertex M w T u h) R := by
  have hd := path_edist_le (fun s => vertex M w T s h)
    (u := u) (l := t - u) (fun j hj => native_step M w T h (by omega))
  rw [Nat.add_sub_of_le hut] at hd
  simp only [GraphBall.closedBall, mem_filter, mem_univ, true_and]
  exact hd.trans (by exact_mod_cast hR)

/-- Every nonblank future-readable cell beyond the current head window has
a last past and first future visit, forming a consecutive actual return. -/
theorem nonblank_remote_return (M : TM) (w : List Bool) (T t H : ℕ)
    (h : Fin M.k) (z : ℤ) (hword : word M w T t h z ≠ 0)
    (hfar : (H : ℤ) < |z - (run M w t).workPos h|) :
    ∃ p q, p < t ∧ t < q ∧ IsHop (fun s => (run M w s).workPos h) T p q ∧
      (run M w p).workPos h = z ∧ (H : ℤ) < |(run M w t).workPos h - (run M w p).workPos h| := by
  classical
  have hf : FutureVisit M w T t h z := by
    by_contra hn
    simp [word, hn] at hword
  have hw : (run M w t).work h z ≠ 0 := by simpa only [word, ite_eq_left hf] using hword
  have hpast : (univ.filter fun u : Fin t => (run M w u).workPos h = z).Nonempty := by
    by_contra hn
    apply hw
    apply work_eq_blank
    intro u hu he
    exact hn ⟨⟨u, hu⟩, mem_filter.mpr ⟨mem_univ _, he⟩⟩
  let past := (range t).filter fun u => (run M w u).workPos h = z
  have hpn : past.Nonempty := by
    obtain ⟨u, hu⟩ := hpast
    exact ⟨u.val, mem_filter.mpr ⟨mem_range.mpr u.isLt, (mem_filter.mp hu).2⟩⟩
  let future := (Ico t T).filter fun u => (run M w u).workPos h = z
  have hfn : future.Nonempty := by
    obtain ⟨u, hut, huT, he⟩ := hf
    exact ⟨u, mem_filter.mpr ⟨mem_Ico.mpr ⟨hut, huT⟩, he⟩⟩
  let p := past.max' hpn
  let q := future.min' hfn
  have hpm := mem_filter.mp (max'_mem past hpn)
  have hqm := mem_filter.mp (min'_mem future hfn)
  have hpz : (run M w p).workPos h = z := hpm.2
  have hqz : (run M w q).workPos h = z := hqm.2
  have hqT : q < T := (mem_Ico.mp hqm.1).2
  have hpt : p < t := mem_range.mp hpm.1
  have htq : t < q := by
    have hh := mem_Ico.mp hqm.1
    have hne : t ≠ q := by
      intro he
      have hz : (run M w t).workPos h = z := he ▸ hqm.2
      simp [hz] at hfar
      omega
    omega
  refine ⟨p, q, hpt, htq, ⟨by omega, hqT, ?_, ?_⟩, hpz, ?_⟩
  · exact hqz.trans hpz.symm
  · intro u hu he
    have huz : (run M w u).workPos h = z := he.trans hpm.2
    by_cases hut : u < t
    · have hup := le_max' past u (mem_filter.mpr ⟨mem_range.mpr hut, huz⟩)
      have hu' := mem_Ioo.mp hu
      omega
    · have huq := min'_le future u (mem_filter.mpr
        ⟨mem_Ico.mpr ⟨by omega, by have := mem_Ioo.mp hu; omega⟩, huz⟩)
      have hu' := mem_Ioo.mp hu
      omega
  · simpa only [hpz, abs_sub_comm] using hfar

noncomputable def remoteWord (M : TM) (w : List Bool) (T t H : ℕ) (h : Fin M.k) :
    Fin (2 * T + 1) → Fin (M.g + 1) :=
  FiniteMaskFibres.maskedVertex 0 (FiniteMaskFibres.headWindow H) (vertex M w T t h)

theorem remote_mask_fibre (M : TM) (T H : ℕ) (v : Fin (2 * T + 1) → Fin (M.g + 1)) :
    (univ.filter fun x : Vertex (Fin (M.g + 1)) (2 * T + 1) =>
      FiniteMaskFibres.maskedVertex 0 (FiniteMaskFibres.headWindow H) x = v).card ≤
      (2 * T + 1) * (M.g + 1) ^ (2 * H + 1) := by
  simpa only [Fintype.card_fin] using FiniteMaskFibres.masked_headWindow_fiber_le 0 H v

theorem remoteWord_return (M : TM) (w : List Bool) (T t H : ℕ) (h : Fin M.k)
    (ht : t ≤ T) (i : Fin (2 * T + 1)) (hi : remoteWord M w T t H h i ≠ 0) :
    ∃ p q, p < t ∧ t < q ∧ IsHop (fun s => (run M w s).workPos h) T p q ∧
      (run M w p).workPos h = address T i ∧
      (H : ℤ) < |(run M w t).workPos h - (run M w p).workPos h| := by
  have hout : i ∉ FiniteMaskFibres.headWindow H (vertex M w T t h).2 := by
    intro hm
    simp [remoteWord, FiniteMaskFibres.maskedVertex, FiniteMaskFibres.masked, hm] at hi
  have hnonzero : word M w T t h (address T i) ≠ 0 := by
    change i ∉ FiniteMaskFibres.headWindow H (PersistenceGraph.vertex M w T t h).2 at hout
    simpa only [remoteWord, FiniteMaskFibres.maskedVertex, FiniteMaskFibres.masked,
      vertex, min_eq_left ht, ite_eq_right hout] using hi
  have hdist : (H : ℤ) < |(i.val : ℤ) - (vertex M w T t h).2.val| := by
    simpa only [FiniteMaskFibres.headWindow, mem_filter, mem_univ, true_and, not_le] using hout
  have hhead : address T (vertex M w T t h).2 = (run M w t).workPos h := by
    exact (vertex_head_address M w T t h).trans (by rw [min_eq_left ht])
  apply nonblank_remote_return M w T t H h (address T i) hnonzero
  rw [← hhead]
  simpa only [address, sub_sub_sub_cancel_right] using hdist

/-- At the actual first halt, both endpoints of every returned witness are
successful source transitions. The unused halt-test tuple is excluded. -/
theorem remoteWord_successful_return (M : TM) (w : List Bool) (T t H : ℕ)
    (hhalt : HaltsAt M w T) (h : Fin M.k) (ht : t ≤ T)
    (i : Fin (2 * T + 1)) (hi : remoteWord M w T t H h i ≠ 0) :
    ∃ p q, p < t ∧ t < q ∧ IsHop (fun s => (run M w s).workPos h) T p q ∧
      transAt M w p ≠ none ∧ transAt M w q ≠ none ∧
      (run M w p).workPos h = address T i ∧
      (H : ℤ) < |(run M w t).workPos h - (run M w p).workPos h| := by
  obtain ⟨p, q, hpt, htq, hhop, hz, hfar⟩ := remoteWord_return M w T t H h ht i hi
  exact ⟨p, q, hpt, htq, hhop, hhalt.1 p (hpt.trans_le ht), hhalt.1 q hhop.2.1, hz, hfar⟩

end AdaptiveTransfer.PersistenceFuture
