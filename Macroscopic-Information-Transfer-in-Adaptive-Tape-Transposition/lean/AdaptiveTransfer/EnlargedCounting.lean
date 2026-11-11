import AdaptiveTransfer.EnlargedReplay
import AdaptiveTransfer.GetterGeometry

/-! Actual finite records for the entire enlarged rule. A replay class consists
of inputs with the same literal geometry; it does not contain a decoder,
injection, recovered prefix, or agreed fine trace as a field.
-/

namespace AdaptiveTransfer.Enlarged

open Finset NativeRelations
open scoped BigOperators

variable {Q Γ Λ : Type*} {p R P : ℕ}

/-- Fixed geometry extracted from actual enlarged executions. The state and
label remain unrecorded until `encode` below. -/
structure ReplayClass (M : System Q Γ Λ 1 p R) (P : ℕ) (π : Fin P → Fin P) where
  inputs : Finset (Fin P → Bool)
  labels : inputs → Λ
  finish : inputs → ℕ
  start : ℕ
  stop : ℕ
  times : Finset ℕ
  cells : Finset ℤ
  times_before : ∀ t ∈ times, t < stop
  times_after : ∀ t ∈ times, start ≤ t
  finish_after : ∀ X, stop ≤ finish X
  carrier : ∀ X : inputs, ∀ t : ℕ, start ≤ t → t < stop →
    (t ∈ times ↔ (M.run (labels X) (List.ofFn X.val) t).workPos 0 ∈ cells)
  live : ∀ X : inputs, ∀ t ∈ times, M.live (labels X) (List.ofFn X.val) t = true
  workEntry : ℕ → ℤ
  portEntry : ℕ → Fin p → ℤ
  portLo : ℕ → Fin p → ℤ
  portHi : ℕ → Fin p → ℤ
  outLo : ℕ → ℕ
  outHi : ℕ → ℕ
  work_entry : ∀ X : inputs, ∀ r ∈ runStarts times,
    (M.run (labels X) (List.ofFn X.val) r).workPos 0 = workEntry r
  port_entry : ∀ X : inputs, ∀ r ∈ runStarts times,
    (M.run (labels X) (List.ofFn X.val) r).ports = portEntry r
  output_entry : ∀ X : inputs, ∀ r ∈ runStarts times,
    (M.run (labels X) (List.ofFn X.val) r).outRev.length = outLo r
  output_exit : ∀ X : inputs, ∀ r ∈ runStarts times,
    (M.run (labels X) (List.ofFn X.val) (runEnd times stop r)).outRev.length = outHi r
  extrema : ∀ X : inputs, ∀ r ∈ runStarts times, ∀ t ∈ Ico r (runEnd times stop r), ∀ j,
    portLo r j ≤ (M.run (labels X) (List.ofFn X.val) t).ports j ∧
      (M.run (labels X) (List.ofFn X.val) t).ports j ≤ portHi r j
  correct : ∀ X : inputs,
    (M.run (labels X) (List.ofFn X.val) (finish X)).outRev.reverse = List.ofFn (fun j => X.val (π j))

namespace ReplayClass
variable {M : System Q Γ Λ 1 p R} {π : Fin P → Fin P} (g : ReplayClass M P π)

def extent : Set ℤ := Getter.portExtent g.times g.portLo g.portHi R
noncomputable def omitted : Finset (Fin P) := Getter.omittedByExtent π g.times g.outLo g.outHi g.extent

abbrev Message :=
  (↑g.omittedᶜ → Bool) × Λ × (runStarts g.times → Q) × (snapshotCells g.start g.cells → Γ)

noncomputable def encode (X : g.inputs) : g.Message :=
  ((fun q => X.val q.val), g.labels X,
    (fun r => (M.run (g.labels X) (List.ofFn X.val) r.val).state),
    (fun z => (M.run (g.labels X) (List.ofFn X.val) g.start).work 0 z.val))

/-- Actual entry/exit counters supply every demanded append witness. -/
theorem output_cover (X : g.inputs) :
    ∀ q ∈ g.omitted, ∃ t ∈ g.times, ∃ j : Fin P,
      π j = q ∧ (M.run (g.labels X) (List.ofFn X.val) t).outRev.length = j.val ∧
        (M.emitted (g.labels X) (List.ofFn X.val) t).isSome := by
  classical
  intro q hq
  obtain ⟨j, hj, hjq⟩ := mem_image.mp (mem_sdiff.mp hq).1
  obtain ⟨r, hr, hj⟩ := mem_biUnion.mp hj
  have hj' := (mem_filter.mp hj).2
  have he := runEnd_spec g.times_before hr
  have hlo : (PrefixOutput.word (M.emitted (g.labels X) (List.ofFn X.val)) r).length ≤ j.val := by
    rw [← M.count_eq_word, g.output_entry X r hr]
    exact hj'.1
  have hhi : j.val < (PrefixOutput.word (M.emitted (g.labels X) (List.ofFn X.val))
      (runEnd g.times g.stop r)).length := by
    rw [← M.count_eq_word, g.output_exit X r hr]
    exact hj'.2
  obtain ⟨t, hrt, hte, hc, ho⟩ := PrefixOutput.exists_append_between _ he.1.le hlo hhi
  exact ⟨t, he.2.2.2 t (mem_Ico.mpr ⟨hrt, hte⟩), j, hjq, (M.count_eq_word _ _ _).trans hc, ho⟩

theorem raw_in_extent (X : g.inputs) :
    ∀ t ∈ g.times, ∀ j i, windowAddress ((M.run (g.labels X) (List.ofFn X.val) t).ports j) R i ∈ g.extent :=
  Getter.portExtent_contains_windows _ g.times g.times_before g.portLo g.portHi R (g.extrema X)

/-- Injectivity is proved from actual final correctness and the whole-rule
replay theorem. Labels are compared once; positions remain geometry. -/
theorem encode_injective (hπ : Function.Injective π) : Function.Injective g.encode := by
  classical
  intro X Y hxy
  have hext : ∀ q ∉ g.omitted, X.val q = Y.val q := by
    intro q hq
    exact congrFun (congrArg Prod.fst hxy) ⟨q, mem_compl.mpr hq⟩
  have hl : g.labels X = g.labels Y := congrArg (fun m => m.2.1) hxy
  have hstates : ∀ r ∈ runStarts g.times,
      (M.run (g.labels X) (List.ofFn X.val) r).state =
      (M.run (g.labels Y) (List.ofFn Y.val) r).state := by
    intro r hr
    exact congrFun (congrArg (fun m => m.2.2.1) hxy) ⟨r, hr⟩
  let entry := replayEntry g.times g.stop g.times_before
  have hentry (t : ℕ) (ht : t ∈ g.times) : g.start ≤ entry t ∧ entry t ≤ t := by
    have he := replayEntry_spec g.times_before ht
    exact ⟨g.times_after _ (mem_filter.mp he.1).1, he.2.1⟩
  have hfill (t : ℕ) (ht : t ∈ g.times) (u : ℕ) (heu : entry t ≤ u) (hut : u ≤ t) : u ∈ g.times := by
    have he := replayEntry_spec g.times_before ht
    exact (runEnd_spec g.times_before he.1).2.2.2 u (mem_Ico.mpr ⟨heu, hut.trans_lt he.2.2⟩)
  have hcontrol (t : ℕ) (ht : t ∈ g.times) :
      SameControl (M.run (g.labels X) (List.ofFn X.val) (entry t))
        (M.run (g.labels X) (List.ofFn Y.val) (entry t)) := by
    have hr := (replayEntry_spec g.times_before ht).1
    rw [hl]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [hl] using hstates _ hr
    · funext h
      have hh : h = 0 := Subsingleton.elim _ _
      subst h
      simpa only [hl] using (g.work_entry X _ hr).trans (g.work_entry Y _ hr).symm
    · simpa only [hl] using (g.port_entry X _ hr).trans (g.port_entry Y _ hr).symm
    · simpa only [hl] using (g.output_entry X _ hr).trans (g.output_entry Y _ hr).symm
  have hslab : ∀ z ∈ (g.cells : Set ℤ),
      (M.run (g.labels X) (List.ofFn X.val) g.start).work 0 z =
      (M.run (g.labels X) (List.ofFn Y.val) g.start).work 0 z := by
    intro z hz
    by_cases ha : g.start = 0
    · rw [ha]; rfl
    · have hz' : z ∈ snapshotCells g.start g.cells := by
        simpa only [snapshotCells, ite_eq_right ha, Finset.mem_coe] using hz
      have hh := congrFun (congrArg (fun m => m.2.2.2) hxy) ⟨z, hz'⟩
      simpa only [encode, ← hl] using hh
  have hdisjoint := Getter.omittedByExtent_disjoint π g.times g.outLo g.outHi g.extent
  have hr := M.replay_agreement (g.labels X) π hπ (g.finish X) (g.finish Y) g.start g.stop
    (g.finish_after X) (g.finish_after Y) (g.correct X) (by simpa only [← hl] using g.correct Y)
    g.cells g.times entry g.omitted (fun t ht => ⟨g.times_after t ht, g.times_before t ht⟩)
    (g.carrier X) (by simpa only [← hl, Finset.mem_coe] using g.carrier Y) hentry hfill hcontrol
    (fun t ht => ⟨g.live X t ht, by simpa only [← hl] using g.live Y t ht⟩)
    hslab g.extent (g.raw_in_extent X) hdisjoint hext (g.output_cover X)
  apply Subtype.ext
  funext q
  by_cases hq : q ∈ g.omitted
  · obtain ⟨t, ht, j, hjq, hc, he⟩ := g.output_cover X q hq
    obtain ⟨bit, hb⟩ := Option.isSome_iff_exists.mp he
    have hf : M.emitted (g.labels X) (List.ofFn Y.val) t = some bit :=
      (congrArg (fun v => v.bind Instruction.append) (hr.2 t ht).2).symm.trans hb
    have heq := PrefixOutput.emitted_at_count (M.emitted (g.labels X) (List.ofFn X.val))
      ((g.times_before t ht).trans_le (g.finish_after X)) hb
    have hfq := PrefixOutput.emitted_at_count (M.emitted (g.labels X) (List.ofFn Y.val))
      ((g.times_before t ht).trans_le (g.finish_after Y)) hf
    rw [← M.output_eq_word, g.correct X, ← M.count_eq_word, hc] at heq
    rw [← M.output_eq_word, hl, g.correct Y, ← M.count_eq_word, ← hl,
      ← (hr.2 t ht).1.2.2.2, hc] at hfq
    have hh := heq.trans hfq.symm
    simpa only [List.getElem?_ofFn, dite_eq_left j.isLt, Option.some.injEq, hjq] using hh
  · exact hext q hq

variable [Fintype Q] [Fintype Γ] [Fintype Λ]

theorem message_card : Fintype.card g.Message =
    2 ^ (P - g.omitted.card) * Fintype.card Λ * Fintype.card Q ^ (runStarts g.times).card *
      Fintype.card Γ ^ (if g.start = 0 then 0 else g.cells.card) := by
  simp only [Message, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, card_compl, snapshotCells_card, Fintype.card_fin]
  ring

/-- Finite bound for the entire enlarged transition, with the actual raw-window
union removed from the demanded coordinates and one immutable label bill. -/
theorem card_bound (hπ : Function.Injective π) :
    g.inputs.card ≤ 2 ^ (P - g.omitted.card) * Fintype.card Λ *
      Fintype.card Q ^ (runStarts g.times).card *
      Fintype.card Γ ^ (if g.start = 0 then 0 else g.cells.card) := by
  have hc := Fintype.card_le_of_injective _ (g.encode_injective hπ)
  rw [Fintype.card_coe, g.message_card] at hc
  exact hc

/-- Complete mutable state and the immutable label have distinct bills. -/
theorem bits_card_bound (hπ : Function.Injective π) (q z a : ℕ)
    (hq : Fintype.card Q ≤ 2 ^ q) (hz : Fintype.card Λ ≤ 2 ^ z)
    (ha : Fintype.card Γ ≤ 2 ^ a) :
    g.inputs.card ≤ 2 ^ (P - g.omitted.card + z + (runStarts g.times).card * q +
      a * (if g.start = 0 then 0 else g.cells.card)) := by
  calc
    g.inputs.card ≤ 2 ^ (P - g.omitted.card) * Fintype.card Λ *
        Fintype.card Q ^ (runStarts g.times).card *
        Fintype.card Γ ^ (if g.start = 0 then 0 else g.cells.card) := g.card_bound hπ
    _ ≤ 2 ^ (P - g.omitted.card) * 2 ^ z *
        (2 ^ q) ^ (runStarts g.times).card *
        (2 ^ a) ^ (if g.start = 0 then 0 else g.cells.card) := by gcongr
    _ = _ := by simp only [pow_add, pow_mul]; ring

theorem saving_card_bound (hπ : Function.Injective π) (q z a N : ℕ)
    (hq : Fintype.card Q ≤ 2 ^ q) (hz : Fintype.card Λ ≤ 2 ^ z)
    (ha : Fintype.card Γ ≤ 2 ^ a) (hN : (runStarts g.times).card ≤ N)
    (saving : ℝ) (hsaving : saving ≤ (g.omitted.card : ℝ) -
      (a : ℝ) * (if g.start = 0 then 0 else (g.cells.card : ℝ))) :
    (g.inputs.card : ℝ) ≤ (2 : ℝ) ^ ((P : ℝ) - saving + z + (N : ℝ) * q) := by
  have hcard : g.omitted.card ≤ P := by
    simpa only [Fintype.card_fin] using card_le_univ g.omitted
  have hexp : ((P - g.omitted.card + z + (runStarts g.times).card * q +
      a * (if g.start = 0 then 0 else g.cells.card) : ℕ) : ℝ) ≤
        (P : ℝ) - saving + z + (N : ℝ) * q := by
    have hr : ((runStarts g.times).card : ℝ) * q ≤ (N : ℝ) * q := by
      exact_mod_cast Nat.mul_le_mul_right q hN
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hcard]
    split_ifs at hsaving ⊢ <;> first | linarith | (simp only [Nat.cast_zero, mul_zero] at *; linarith)
  have hh : (g.inputs.card : ℝ) ≤
      (2 : ℝ) ^ ((P - g.omitted.card + z + (runStarts g.times).card * q +
        a * (if g.start = 0 then 0 else g.cells.card) : ℕ) : ℝ) := by
    exact_mod_cast g.bits_card_bound hπ q z a hq hz ha
  exact hh.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

end ReplayClass
end AdaptiveTransfer.Enlarged
