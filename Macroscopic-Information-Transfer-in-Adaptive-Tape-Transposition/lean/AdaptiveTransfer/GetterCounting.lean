import AdaptiveTransfer.GetterReplay
import AdaptiveTransfer.ReplayGeometry

/-! Finite actual getter replay messages. The existing native message type is
reused with correction payloads in its sparse Option slots, plus one immutable
label and the paid observer state at each run entry.
-/

namespace AdaptiveTransfer.Getter

open Transpose Finset LeanMachine
open scoped BigOperators

variable {M : TM} {U Λ : Type*} {v R P T : ℕ}

noncomputable def errorFields {X : Fin P → Bool}
    (E : ExecutionPrefix M (List.ofFn X) T) (A : Observer M U v R)
    (G : Getters M U Λ v R) (label : Λ) (N H : ℕ) (C : Finset ℕ)
    (entry : ℕ → ℕ) (f : Fin M.k) : Fin N × OtherHeads f → Option (Fin (M.g + 1)) :=
  fun slot => if slot.1.val ∈ C then errorRecord E A G f label H (entry slot.1.val) slot.1.val slot.2.val
    else none

abbrev Message (M : TM) (U Λ : Type*) (P : ℕ) (omitted : Finset (Fin P))
    (starts : Finset ℕ) (slab : Finset ℤ) (a H N : ℕ) (f : Fin M.k) (J : ℕ) :=
  ReplayMessage M P omitted starts slab a H N f J × Λ × (starts → U)

theorem message_card_le [Fintype U] [Fintype Λ]
    (M : TM) (P : ℕ) (omitted : Finset (Fin P)) (starts : Finset ℕ)
    (slab : Finset ℤ) (a H N : ℕ) (f : Fin M.k) (J : ℕ) :
    Fintype.card (Message M U Λ P omitted starts slab a H N f J) ≤
      2 ^ (P - omitted.card) * Fintype.card Λ * ((M.q + 1) * Fintype.card U) ^ starts.card *
        (M.g + 1) ^ ((if a = 0 then 0 else slab.card) + (M.k - 1) * starts.card * (2 * H + 1)) *
        ∑ j ∈ range (J + 1), ((M.k - 1) * N).choose j * (M.g + 1) ^ j := by
  have hc := replayMessage_card_le M P omitted starts slab a H N f J
  change Fintype.card (ReplayMessage M P omitted starts slab a H N f J × (Λ × (starts → U))) ≤ _
  rw [Fintype.card_prod (α := ReplayMessage M P omitted starts slab a H N f J)
    (β := Λ × (starts → U)), Fintype.card_prod (α := Λ) (β := starts → U),
    Fintype.card_fun, Fintype.card_coe]
  calc
    _ ≤ (2 ^ (P - omitted.card) * (M.q + 1) ^ starts.card *
        (M.g + 1) ^ ((if a = 0 then 0 else slab.card) + (M.k - 1) * starts.card * (2 * H + 1)) *
        ∑ j ∈ range (J + 1), ((M.k - 1) * N).choose j * (M.g + 1) ^ j) *
        (Fintype.card Λ * Fintype.card U ^ starts.card) := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [mul_pow]; ring

section Encoding
variable (D : Finset (Fin P → Bool)) (E : ∀ X : D, ExecutionPrefix M (List.ofFn X.val) T)
  (A : Observer M U v R) (G : Getters M U Λ v R) (labels : D → Λ)
  (omitted : Finset (Fin P)) (starts C : Finset ℕ) (slab : Finset ℤ)
  (a H N J : ℕ) (f : Fin M.k) (entry : ℕ → ℕ) (workEntry : ℕ → Fin M.k → ℤ)
  (htag : ∀ X, (recordSupport (fun _ => none)
    (errorFields (E X) A G (labels X) N H C entry f)).card ≤ J)

noncomputable def encode (X : D) : Message M U Λ P omitted starts slab a H N f J :=
  (((fun q => X.val q.val), (fun r => ((E X).config r.val).state),
    (fun z => ((E X).config a).work f z.val),
    (fun r h i => ((E X).config r.val).work h.val (windowAddress (workEntry r.val h.val) H i)),
    ⟨errorFields (E X) A G (labels X) N H C entry f, htag X⟩),
    labels X, fun r => (A.run (List.ofFn X.val) r.val).1)

variable (π : Fin P → Fin P) (hπ : Function.Injective π)
  (rawEntry : ℕ → ℤ) (virtualEntry : ℕ → Fin v → ℤ)
  (pastEntry : ℕ → Fin M.k → Finset ℤ) (counter : ℕ → ℕ)
  (finish : D → ℕ) (I : Set ℤ)
  (hC : ∀ t ∈ C, a ≤ t ∧ t < T) (hN : T ≤ N)
  (hcarrier : ∀ X : D, ∀ t, a ≤ t → t < T →
    (t ∈ C ↔ ((E X).config t).workPos f ∈ slab))
  (hentry : ∀ t ∈ C, a ≤ entry t ∧ entry t ≤ t)
  (hfill : ∀ t ∈ C, ∀ u, entry t ≤ u → u ≤ t → u ∈ C)
  (hentryR : ∀ t ∈ C, entry t ∈ starts)
  (hwork : ∀ X : D, ∀ r ∈ starts, ((E X).config r).workPos = workEntry r)
  (hrawEntry : ∀ X : D, ∀ r ∈ starts, ((E X).config r).inPos = rawEntry r)
  (hvirtual : ∀ X : D, ∀ r ∈ starts, (A.run (List.ofFn X.val) r).2 = virtualEntry r)
  (hpast : ∀ X : D, ∀ r ∈ starts, ∀ h, h ≠ f → visitedBefore (E X) r h = pastEntry r h)
  (hcounter : ∀ X : D, ∀ r ∈ starts, ((E X).config r).outRev.length = counter r)
  (hrawWindows : ∀ X : D, ∀ t ∈ C, ∀ j i, windowAddress (A.allPorts (List.ofFn X.val) t j) R i ∈ I)
  (hdisjoint : ∀ q : Fin P, (q.val : ℤ) ∈ I → q ∉ omitted)
  (hcover : ∀ X : D, ∀ q ∈ omitted, ∃ t ∈ C, ∃ j : Fin P,
    π j = q ∧ ((E X).config t).outRev.length = j.val ∧ ((E X).emitted t).isSome)
  (hfinish : ∀ X, T ≤ finish X)
  (houtput : ∀ X : D,
    (Transpose.Tape.run M (List.ofFn X.val) (finish X)).outRev.reverse = List.ofFn (fun j => X.val (π j)))

include hπ hC hN hcarrier hentry hfill hentryR hwork hrawEntry hvirtual hpast hcounter
  hrawWindows hdisjoint hcover hfinish houtput in
/-- Injection of actual records; the strict prefix and all source-observer
updates are reconstructed by the preceding theorem. -/
theorem encode_injective : Function.Injective (encode D E A G labels omitted starts C slab a H N J f entry workEntry htag) := by
  intro X Y hxy
  have hext : ∀ q ∉ omitted, X.val q = Y.val q := by
    intro q hq
    exact congrFun (congrArg (fun m => m.1.1) hxy) ⟨q, mem_compl.mpr hq⟩
  have hlabel : labels X = labels Y := congrArg (fun m => m.2.1) hxy
  have hstates : ∀ r ∈ starts, ((E X).config r).state = ((E Y).config r).state := by
    intro r hr
    exact congrFun (congrArg (fun m => m.1.2.1) hxy) ⟨r, hr⟩
  have hcontrols : ∀ t ∈ C, SameControl ((E X).config (entry t)) ((E Y).config (entry t)) := by
    intro t ht
    have hr := hentryR t ht
    exact ⟨hstates _ hr, (hrawEntry X _ hr).trans (hrawEntry Y _ hr).symm,
      (hwork X _ hr).trans (hwork Y _ hr).symm⟩
  have hobservers : ∀ t ∈ C, A.run (List.ofFn X.val) (entry t) = A.run (List.ofFn Y.val) (entry t) := by
    intro t ht
    have hr := hentryR t ht
    exact Prod.ext (congrFun (congrArg (fun m => m.2.2) hxy) ⟨entry t, hr⟩)
      ((hvirtual X _ hr).trans (hvirtual Y _ hr).symm)
  have hwindows : ∀ t ∈ C, ∀ h, h ≠ f → ∀ z,
      (z - ((E X).config (entry t)).workPos h).natAbs ≤ H →
      ((E X).config (entry t)).work h z = ((E Y).config (entry t)).work h z := by
    intro t ht h hh z hz
    have hr := hentryR t ht
    rw [hwork X _ hr] at hz
    obtain ⟨i, hi⟩ := windowAddress_covers hz
    have hv := congrFun (congrFun (congrFun
      (congrArg (fun m => m.1.2.2.2.1) hxy) ⟨entry t, hr⟩) ⟨h, hh⟩) i
    simpa only [encode, hi] using hv
  have herrors : ∀ t ∈ C, ∀ h, h ≠ f →
      errorRecord (E X) A G f (labels X) H (entry t) t h =
      errorRecord (E Y) A G f (labels X) H (entry t) t h := by
    intro t ht h hh
    have htN : t < N := (hC t ht).2.trans_le hN
    have hv := congrFun (congrArg (fun m => m.1.2.2.2.2.val) hxy) (⟨t, htN⟩, ⟨h, hh⟩)
    simpa only [encode, errorFields, ite_eq_left ht, ← hlabel] using hv
  have hsnapshot : ∀ z ∈ (slab : Set ℤ), ((E X).config a).work f z = ((E Y).config a).work f z := by
    intro z hz
    change z ∈ slab at hz
    by_cases ha : a = 0
    · rw [ha, (E X).initial, (E Y).initial]
    · have hz' : z ∈ snapshotCells a slab := by simpa only [snapshotCells, ite_eq_right ha] using hz
      exact congrFun (congrArg (fun m => m.1.2.2.1) hxy) ⟨z, hz'⟩
  have hraw : ∀ X : D, ∀ t ∈ C, ((E X).config t).inPos ∈ I := by
    intro X t ht
    have hh := hrawWindows X t ht 0 ⟨R, by omega⟩
    have he : windowAddress (A.allPorts (List.ofFn X.val) t 0) R ⟨R, by omega⟩ =
        ((E X).config t).inPos := by
      rw [Observer.allPorts_zero, ← (E X).config_eq_run (hC t ht).2.le]
      dsimp [windowAddress]
      omega
    rwa [he] at hh
  have hcount : ∀ t ∈ C, ((E X).config (entry t)).outRev.length = ((E Y).config (entry t)).outRev.length :=
    fun t ht => (hcounter X _ (hentryR t ht)).trans (hcounter Y _ (hentryR t ht)).symm
  have himports := import_reconstruction (E X) (E Y) A G (labels X) π hπ
    (finish X) (finish Y) (hfinish X) (hfinish Y) (houtput X) (houtput Y)
    (a := a) (b := T) (H := H) le_rfl f slab C entry omitted hC (hcarrier X) (hcarrier Y)
    hentry hfill hcontrols hobservers hwindows
    (fun t ht h hh => (hpast X _ (hentryR t ht) h hh).trans (hpast Y _ (hentryR t ht) h hh).symm)
    herrors hsnapshot I (hraw X) (hrawWindows X) hdisjoint hext hcount (hcover X)
  have hreplay := (E X).adaptive_replay_agreement (E Y) (a := a) (b := T) (H := H)
    le_rfl f slab C entry hC (hcarrier X) (hcarrier Y) hentry hfill hcontrols hwindows
    (fun t ht => (himports t ht).1) hsnapshot I (hraw X)
    (fun _ hz => readInput_eq_of_exterior omitted I hext hdisjoint hz)
  have hcounters := (E X).replay_output_count_agreement (E Y) C entry
    (fun t ht => (hC t ht).2) (fun t ht => (hentry t ht).2) hfill hcount
    (fun t ht => (hreplay.2 t ht).2)
  apply Subtype.ext
  apply (E X).replay_recovers_input (E Y) π C omitted (fun t ht => (hC t ht).2)
    (hcover X) hcounters (fun t ht => (hreplay.2 t ht).2)
  · intro t ht j bit hc hb
    exact (E X).output_correct π (hfinish X) (houtput X) ht j bit hc hb
  · intro t ht j bit hc hb
    exact (E Y).output_correct π (hfinish Y) (houtput Y) ht j bit hc hb
  · exact hext

include htag hπ hC hN hcarrier hentry hfill hentryR hwork hrawEntry hvirtual hpast hcounter
  hrawWindows hdisjoint hcover hfinish houtput in
/-- Exact fixed-record-class getter bound, before deriving the canonical
port-extremum/ordinal geometry in the next adapter. -/
theorem card_bound [Fintype U] [Fintype Λ] :
    D.card ≤ 2 ^ (P - omitted.card) * Fintype.card Λ *
      ((M.q + 1) * Fintype.card U) ^ starts.card *
      (M.g + 1) ^ ((if a = 0 then 0 else slab.card) + (M.k - 1) * starts.card * (2 * H + 1)) *
      ∑ j ∈ range (J + 1), ((M.k - 1) * N).choose j * (M.g + 1) ^ j := by
  have hi := encode_injective D E A G labels omitted starts C slab a H N J f entry workEntry htag
    π hπ rawEntry virtualEntry pastEntry counter finish I hC hN hcarrier hentry hfill hentryR
    hwork hrawEntry hvirtual hpast hcounter hrawWindows hdisjoint hcover hfinish houtput
  have hc := Fintype.card_le_of_injective _ hi
  rw [Fintype.card_coe] at hc
  exact hc.trans (message_card_le M P omitted starts slab a H N f J)

end Encoding
end AdaptiveTransfer.Getter
