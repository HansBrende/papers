import AdaptiveTransfer.NativeReplayAdapters
import LeanMachine.SparseRecords

/-! Actual adaptive replay records and their finite cardinality. The support of
the incoming Option-valued record is paid jointly with its nonblank values. -/

namespace AdaptiveTransfer

open Transpose Finset LeanMachine
open scoped BigOperators

abbrev OtherHeads {M : TM} (f : Fin M.k) := {h : Fin M.k // h ≠ f}

theorem otherHeads_card {M : TM} (f : Fin M.k) :
    Fintype.card (OtherHeads f) = M.k - 1 := by
  simp [OtherHeads, Fintype.card_subtype_compl]

def windowAddress (center : ℤ) (H : ℕ) (i : Fin (2 * H + 1)) : ℤ :=
  center + i.val - H

theorem windowAddress_covers {center z : ℤ} {H : ℕ}
    (hz : (z - center).natAbs ≤ H) :
    ∃ i : Fin (2 * H + 1), windowAddress center H i = z := by
  have ha : |z - center| ≤ (H : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hz
  have hab := abs_le.mp ha
  have hp : 0 ≤ z - center + H := by omega
  have hc : (((z - center + H).toNat : ℕ) : ℤ) = z - center + H :=
    Int.toNat_of_nonneg hp
  refine ⟨⟨(z - center + H).toNat, ?_⟩, ?_⟩
  · omega
  · dsimp [windowAddress]
    omega

noncomputable def snapshotCells (a : ℕ) (S : Finset ℤ) : Finset ℤ :=
  if a = 0 then ∅ else S

theorem snapshotCells_card (a : ℕ) (S : Finset ℤ) :
    (snapshotCells a S).card = if a = 0 then 0 else S.card := by
  split_ifs <;> simp_all [snapshotCells]

abbrev ReplayImports (M : TM) (N : ℕ) (f : Fin M.k) (J : ℕ) :=
  {v : Fin N × OtherHeads f → Option (Fin (M.g + 1)) //
    (recordSupport (fun _ => none) v).card ≤ J}

noncomputable instance (M : TM) (N : ℕ) (f : Fin M.k) (J : ℕ) :
    Fintype (ReplayImports M N f J) := Fintype.ofFinite _

theorem replayImports_card_le (M : TM) (N : ℕ) (f : Fin M.k) (J : ℕ) :
    Fintype.card (ReplayImports M N f J) ≤
      ∑ j ∈ range (J + 1), ((M.k - 1) * N).choose j * (M.g + 1) ^ j := by
  have hc := sparse_record_card_le
    (I := Fin N × OtherHeads f) (A := fun _ => Option (Fin (M.g + 1)))
    (fun _ => none) (M.g + 1) J (fun _ => by simp [Fintype.card_subtype_compl])
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin,
    otherHeads_card, Nat.mul_comm N] using hc

noncomputable def incomingFields {M : TM} {P T : ℕ} {X : Fin P → Bool}
    (E : ExecutionPrefix M (List.ofFn X) T) (N H : ℕ) (C : Finset ℕ)
    (entry : ℕ → ℕ) (f : Fin M.k) : Fin N × OtherHeads f → Option (Fin (M.g + 1)) :=
  fun slot => if slot.1.val ∈ C then E.incomingRecord H (entry slot.1.val) slot.1.val slot.2.val
    else none

abbrev ReplayMessage (M : TM) (P : ℕ) (U : Finset (Fin P)) (R : Finset ℕ)
    (S : Finset ℤ) (a H N : ℕ) (f : Fin M.k) (J : ℕ) :=
  (↑Uᶜ → Bool) × (R → Fin (M.q + 1)) ×
    (snapshotCells a S → Fin (M.g + 1)) ×
    (R → OtherHeads f → Fin (2 * H + 1) → Fin (M.g + 1)) × ReplayImports M N f J

theorem replayMessage_card_le (M : TM) (P : ℕ) (U : Finset (Fin P)) (R : Finset ℕ)
    (S : Finset ℤ) (a H N : ℕ) (f : Fin M.k) (J : ℕ) :
    Fintype.card (ReplayMessage M P U R S a H N f J) ≤
      2 ^ (P - U.card) * (M.q + 1) ^ R.card *
        (M.g + 1) ^ ((if a = 0 then 0 else S.card) + (M.k - 1) * R.card * (2 * H + 1)) *
        ∑ j ∈ range (J + 1), ((M.k - 1) * N).choose j * (M.g + 1) ^ j := by
  have hc := replayImports_card_le M N f J
  simp only [ReplayMessage, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, card_compl, Fintype.card_fin, otherHeads_card, snapshotCells_card]
  calc
    _ ≤ 2 ^ (P - U.card) * ((M.q + 1) ^ R.card *
        ((M.g + 1) ^ (if a = 0 then 0 else S.card) *
        ((((M.g + 1) ^ (2 * H + 1)) ^ (M.k - 1)) ^ R.card *
        ∑ j ∈ range (J + 1), ((M.k - 1) * N).choose j * (M.g + 1) ^ j))) := by
      gcongr
    _ = _ := by
      rw [← pow_mul, ← pow_mul,
        show (2 * H + 1) * ((M.k - 1) * R.card) = (M.k - 1) * R.card * (2 * H + 1) by ring,
        pow_add]
      ac_rfl

section Encoding

variable {M : TM} {P T : ℕ} (D : Finset (Fin P → Bool))
  (E : ∀ X : D, ExecutionPrefix M (List.ofFn X.val) T)
  (U : Finset (Fin P)) (R C : Finset ℕ) (S : Finset ℤ)
  (a H N J : ℕ) (f : Fin M.k) (entry : ℕ → ℕ)
  (workEntry : ℕ → Fin M.k → ℤ)
  (htag : ∀ X, (recordSupport (fun _ => none) (incomingFields (E X) N H C entry f)).card ≤ J)

/-- Every component is an actual field of the indicated successful execution. -/
noncomputable def encodeReplay (X : D) : ReplayMessage M P U R S a H N f J :=
  ((fun p => X.val p.val), (fun r => ((E X).config r.val).state),
    (fun z => ((E X).config a).work f z.val),
    (fun r h i => ((E X).config r.val).work h.val (windowAddress (workEntry r.val h.val) H i)),
    ⟨incomingFields (E X) N H C entry f, htag X⟩)

variable (π : Fin P → Fin P) (rawEntry : ℕ → ℤ) (counter : ℕ → ℕ)
  (finish : D → ℕ) (I : Set ℤ)
  (hC : ∀ t ∈ C, a ≤ t ∧ t < T)
  (hN : T ≤ N)
  (hcarrier : ∀ X : D, ∀ t, a ≤ t → t < T →
    (t ∈ C ↔ ((E X).config t).workPos f ∈ S))
  (hentry : ∀ t ∈ C, a ≤ entry t ∧ entry t ≤ t)
  (hfill : ∀ t ∈ C, ∀ u, entry t ≤ u → u ≤ t → u ∈ C)
  (hentryR : ∀ t ∈ C, entry t ∈ R)
  (hwork : ∀ X : D, ∀ r ∈ R, ((E X).config r).workPos = workEntry r)
  (hrawEntry : ∀ X : D, ∀ r ∈ R, ((E X).config r).inPos = rawEntry r)
  (hcounter : ∀ X : D, ∀ r ∈ R, ((E X).config r).outRev.length = counter r)
  (hraw : ∀ X : D, ∀ t ∈ C, ((E X).config t).inPos ∈ I)
  (hdisjoint : ∀ p : Fin P, (p.val : ℤ) ∈ I → p ∉ U)
  (hcover : ∀ X : D, ∀ p ∈ U, ∃ t ∈ C, ∃ j : Fin P,
    π j = p ∧ ((E X).config t).outRev.length = j.val ∧ ((E X).emitted t).isSome)
  (hfinish : ∀ X, T ≤ finish X)
  (houtput : ∀ X : D,
    (Transpose.Tape.run M (List.ofFn X.val) (finish X)).outRev.reverse =
      List.ofFn (fun j => X.val (π j)))

include hC hN hcarrier hentry hfill hentryR hwork hrawEntry hcounter hraw
  hdisjoint hcover hfinish houtput in
theorem encodeReplay_injective :
    Function.Injective (encodeReplay D E U R C S a H N J f entry workEntry htag) := by
  intro X Y hxy
  have hext : ∀ p ∉ U, X.val p = Y.val p := by
    intro p hp
    exact congrFun (congrArg Prod.fst hxy) ⟨p, mem_compl.mpr hp⟩
  have hstates : ∀ r ∈ R, ((E X).config r).state = ((E Y).config r).state := by
    intro r hr
    exact congrFun (congrArg (fun m => m.2.1) hxy) ⟨r, hr⟩
  have hcontrols : ∀ t ∈ C,
      SameControl ((E X).config (entry t)) ((E Y).config (entry t)) := by
    intro t ht
    have hr := hentryR t ht
    exact ⟨hstates _ hr, (hrawEntry X _ hr).trans (hrawEntry Y _ hr).symm,
      (hwork X _ hr).trans (hwork Y _ hr).symm⟩
  have hwindows : ∀ t ∈ C, ∀ h, h ≠ f → ∀ z,
      (z - ((E X).config (entry t)).workPos h).natAbs ≤ H →
      ((E X).config (entry t)).work h z = ((E Y).config (entry t)).work h z := by
    intro t ht h hh z hz
    have hr := hentryR t ht
    rw [hwork X _ hr] at hz
    obtain ⟨i, hi⟩ := windowAddress_covers hz
    have hv := congrFun (congrFun (congrFun
      (congrArg (fun m => m.2.2.2.1) hxy) ⟨entry t, hr⟩) ⟨h, hh⟩) i
    simpa only [encodeReplay, hi] using hv
  have himport : ∀ t ∈ C, ∀ h, h ≠ f →
      (E X).incomingRecord H (entry t) t h = (E Y).incomingRecord H (entry t) t h := by
    intro t ht h hh
    have htN : t < N := (hC t ht).2.trans_le hN
    have hv := congrFun (congrArg (fun m => m.2.2.2.2.val) hxy) (⟨t, htN⟩, ⟨h, hh⟩)
    simpa only [encodeReplay, incomingFields, ite_eq_left ht] using hv
  have hsnapshot : ∀ z ∈ (S : Set ℤ),
      ((E X).config a).work f z = ((E Y).config a).work f z := by
    intro z hz
    change z ∈ S at hz
    by_cases ha : a = 0
    · rw [ha, (E X).initial, (E Y).initial]
    · have hz' : z ∈ snapshotCells a S := by simpa only [snapshotCells, ite_eq_right ha] using hz
      exact congrFun (congrArg (fun m => m.2.2.1) hxy) ⟨z, hz'⟩
  have hreplay := (E X).adaptive_replay_agreement (E Y) (a := a) (b := T)
    (H := H) le_rfl f S C entry hC (hcarrier X) (hcarrier Y) hentry hfill
    hcontrols hwindows himport hsnapshot I (hraw X)
    (fun _ hz => readInput_eq_of_exterior U I hext hdisjoint hz)
  have hcounters := (E X).replay_output_count_agreement (E Y) C entry
    (fun t ht => (hC t ht).2) (fun t ht => (hentry t ht).2) hfill
    (fun t ht => (hcounter X _ (hentryR t ht)).trans (hcounter Y _ (hentryR t ht)).symm)
    (fun t ht => (hreplay.2 t ht).2)
  apply Subtype.ext
  apply (E X).replay_recovers_input (E Y) π C U (fun t ht => (hC t ht).2)
    (hcover X) hcounters (fun t ht => (hreplay.2 t ht).2)
  · intro t ht j bit hc hb
    exact (E X).output_correct π (hfinish X) (houtput X) ht j bit hc hb
  · intro t ht j bit hc hb
    exact (E Y).output_correct π (hfinish Y) (houtput Y) ht j bit hc hb
  · exact hext

include htag hC hN hcarrier hentry hfill hentryR hwork hrawEntry hcounter hraw
  hdisjoint hcover hfinish houtput in
/-- Exact native adaptive bound for one actual paid geometry. All ordinary
fields and the joint import payload are constructed from the executions. -/
theorem adaptive_replay_card_bound :
    D.card ≤ 2 ^ (P - U.card) * (M.q + 1) ^ R.card *
      (M.g + 1) ^ ((if a = 0 then 0 else S.card) + (M.k - 1) * R.card * (2 * H + 1)) *
      ∑ j ∈ range (J + 1), ((M.k - 1) * N).choose j * (M.g + 1) ^ j := by
  have hi := encodeReplay_injective D E U R C S a H N J f entry workEntry htag
    π rawEntry counter finish I hC hN hcarrier hentry hfill hentryR hwork hrawEntry
    hcounter hraw hdisjoint hcover hfinish houtput
  have hc := Fintype.card_le_of_injective _ hi
  rw [Fintype.card_coe] at hc
  exact hc.trans (replayMessage_card_le M P U R S a H N f J)

end Encoding

end AdaptiveTransfer
