import AdaptiveTransfer.ScanLoaderMachine
import AdaptiveTransfer.ScanCheckpoints

/-! A direct simultaneous native scan loader. Its controller is independent of
the input length, and its preparation consumes exactly `2 * length + 4` steps.
-/

namespace AdaptiveTransfer.ScanLoader

open Transpose
open Transpose.Tape.Impl
open scoped BigOperators

variable {r : ℕ} {S A : Fin r → Type*} {Q B : Type*}

abbrev ScanStates (S : Fin r → Type*) := (j : Fin r) → S j
abbrev Symbol (A : Fin r → Type*) (B : Type*) :=
  Option (Option (Option ((Sigma A) ⊕ B)))
abbrev Phase (Q S : Type*) := Option (Option (Option (Q ⊕ S)))

def blank : Symbol A B := none
def leftMarker : Symbol A B := some none
def rightMarker : Symbol A B := some (some none)
def data (j : Fin r) (a : A j) : Symbol A B := some (some (some (.inl ⟨j, a⟩)))
def auxiliary (b : B) : Symbol A B := some (some (some (.inr b)))

def start : Phase Q (ScanStates S) := none
def mark : Phase Q (ScanStates S) := some none
def rewind : Phase Q (ScanStates S) := some (some none)
def consume (q : Q) : Phase Q (ScanStates S) := some (some (some (.inl q)))
def load (s : ScanStates S) : Phase Q (ScanStates S) := some (some (some (.inr s)))

abbrev Consumer (Q : Type*) (A : Fin r → Type*) (B : Type*) := Table Q (Symbol A B) (r + 1)

/-- The carrier is tape zero; archive `j` is tape `j.succ`. -/
def archiveActs (scanned : Fin (r + 1) → Symbol A B)
    (write : (j : Fin r) → Symbol A B) (move : Dir) :
    Fin (r + 1) → Symbol A B × Dir :=
  Fin.cases (scanned 0, .stay) (fun j => (write j, move))

def preserveActs (scanned : Fin (r + 1) → Symbol A B) (move : Dir) :
    Fin (r + 1) → Symbol A B × Dir :=
  archiveActs scanned (fun j => scanned j.succ) move

/-- One transition reads the old raw bit and all old scan states, then writes,
updates and moves simultaneously. Rewind tests the raw left endmarker. -/
def table (F : (j : Fin r) → S j → Bool → S j)
    (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S) (q₀ : Q)
    (C : Consumer Q A B) : Table (Phase Q (ScanStates S)) (Symbol A B) (r + 1)
  | none, _, scanned => some (mark, .stay, preserveActs scanned .left, none)
  | some none, _, scanned => some (load s₀, .stay,
      archiveActs scanned (fun _ => leftMarker) .right, none)
  | some (some none), raw, scanned => match raw with
      | some _ => some (rewind, .left, preserveActs scanned .left, none)
      | none => some (consume q₀, .right, preserveActs scanned .right, none)
  | some (some (some (.inl q))), raw, scanned =>
      (C q raw scanned).map (fun (q', move, acts, out) => (consume q', move, acts, out))
  | some (some (some (.inr s))), raw, scanned => match raw with
      | some b => some (load (fun j => F j (s j) b), .right,
          archiveActs scanned (fun j => data j (D j (s j) b)) .right, none)
      | none => some (rewind, .left,
          archiveActs scanned (fun _ => rightMarker) .left, none)

def scan (F : (j : Fin r) → S j → Bool → S j) (s₀ : ScanStates S)
    (w : List Bool) : ℕ → ScanStates S
  | 0 => s₀
  | i + 1 => fun j => F j (scan F s₀ w i j) (w[i]?.getD false)

def codeSymbol (F : (j : Fin r) → S j → Bool → S j)
    (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S)
    (w : List Bool) (j : Fin r) (i : ℕ) : Symbol A B :=
  data j (D j (scan F s₀ w i j) (w[i]?.getD false))

def partialArchive (F : (j : Fin r) → S j → Bool → S j)
    (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S)
    (w : List Bool) (i : ℕ) (j : Fin r) (z : ℤ) : Symbol A B :=
  if z = -1 then leftMarker else
    if 0 ≤ z ∧ z < i then codeSymbol F D s₀ w j z.toNat else blank

def archive (F : (j : Fin r) → S j → Bool → S j)
    (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S)
    (w : List Bool) (j : Fin r) (z : ℤ) : Symbol A B :=
  if z = w.length then rightMarker else partialArchive F D s₀ w w.length j z

def positions (i : ℤ) : Fin (r + 1) → ℤ := Fin.cases 0 (fun _ => i)

def partialWork (F : (j : Fin r) → S j → Bool → S j)
    (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S)
    (w : List Bool) (i : ℕ) : Fin (r + 1) → ℤ → Symbol A B :=
  Fin.cases (fun _ => blank) (fun j => partialArchive F D s₀ w i j)

def completedWork (F : (j : Fin r) → S j → Bool → S j)
    (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S)
    (w : List Bool) : Fin (r + 1) → ℤ → Symbol A B :=
  Fin.cases (fun _ => blank) (fun j => archive F D s₀ w j)

def markConfig : Config (Phase Q (ScanStates S)) (Symbol A B) (r + 1) :=
  ⟨mark, 0, fun _ _ => blank, positions (-1), []⟩

def loadConfig (F : (j : Fin r) → S j → Bool → S j)
    (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S)
    (w : List Bool) (i : ℕ) : Config (Phase Q (ScanStates S)) (Symbol A B) (r + 1) :=
  ⟨load (scan F s₀ w i), i, partialWork F D s₀ w i, positions i, []⟩

def rewindConfig (F : (j : Fin r) → S j → Bool → S j)
    (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S)
    (w : List Bool) (i : ℤ) : Config (Phase Q (ScanStates S)) (Symbol A B) (r + 1) :=
  ⟨rewind, i, completedWork F D s₀ w, positions i, []⟩

def readyConfig (F : (j : Fin r) → S j → Bool → S j)
    (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S) (q₀ : Q)
    (w : List Bool) : Config (Phase Q (ScanStates S)) (Symbol A B) (r + 1) :=
  ⟨consume q₀, 0, completedWork F D s₀ w, positions 0, []⟩

variable (F : (j : Fin r) → S j → Bool → S j)
  (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S) (q₀ : Q)
  (C : Consumer Q A B)

theorem partialArchive_succ (w : List Bool) (i : ℕ) (j : Fin r) (z : ℤ) :
    partialArchive (B := B) F D s₀ w (i + 1) j z =
      if z = i then codeSymbol F D s₀ w j i else partialArchive F D s₀ w i j z := by
  by_cases hz : z = (i : ℤ)
  · subst z
    have hn : (i : ℤ) ≠ -1 := by omega
    have hi : (0 : ℤ) ≤ i ∧ (i : ℤ) < ↑(i + 1) := by omega
    simp [partialArchive, hn, hi]
  · simp only [partialArchive, hz, ite_false]
    by_cases hleft : z = -1
    · simp [hleft]
    · have hiff : (0 ≤ z ∧ z < (↑(i + 1) : ℤ)) ↔ (0 ≤ z ∧ z < (i : ℤ)) := by omega
      simp only [hleft, ite_false, hiff]

theorem start_step (w : List Bool) :
    next (table F D s₀ q₀ C) w (initial start blank) = some markConfig := by
  simp only [next, initial, start, table, markConfig, preserveActs, archiveActs]
  congr 1
  apply Config.ext <;> try rfl
  · funext t z
    dsimp
    refine Fin.cases ?_ (fun j => ?_) t <;> dsimp <;> exact ite_self _
  · funext t
    refine Fin.cases ?_ (fun j => ?_) t <;> rfl

theorem mark_step (w : List Bool) :
    next (table F D s₀ q₀ C) w markConfig = some (loadConfig F D s₀ w 0) := by
  simp only [next, markConfig, mark, table, loadConfig, scan, archiveActs, positions]
  congr 1
  apply Config.ext <;> try rfl
  · funext t z
    refine Fin.cases ?_ (fun j => ?_) t
    · dsimp [partialWork, positions]
      exact ite_self _
    · dsimp [partialWork, positions, partialArchive]
      have hn : ¬ (0 ≤ z ∧ z < 0) := by omega
      simp only [hn, ite_false]
      rfl
  · funext t
    refine Fin.cases ?_ (fun j => ?_) t <;> rfl


theorem load_step (w : List Bool) (i : ℕ) (hi : i < w.length) :
    next (table F D s₀ q₀ C) w (loadConfig F D s₀ w i) =
      some (loadConfig F D s₀ w (i + 1)) := by
  have hr : readInput w (i : ℤ) = some (w[i]'hi) := by
    rw [readInput_natCast, nth_eq_getElem?, List.getElem?_eq_getElem hi]
  simp only [next, loadConfig, load, table, hr, archiveActs]
  congr 1
  apply Config.ext
  · simp only [scan, List.getElem?_eq_getElem hi, Option.getD_some]
  · simp [Dir.shift]
  · funext t z
    refine Fin.cases ?_ (fun j => ?_) t
    · dsimp [partialWork, positions]
      exact ite_self _
    · dsimp [partialWork, positions]
      rw [partialArchive_succ]
      simp only [codeSymbol, List.getElem?_eq_getElem hi, Option.getD_some]
      rfl
  · funext t
    refine Fin.cases ?_ (fun j => ?_) t
    · rfl
    · simp [positions, Dir.shift]
  · rfl

theorem eof_step (w : List Bool) :
    next (table F D s₀ q₀ C) w (loadConfig F D s₀ w w.length) =
      some (rewindConfig F D s₀ w (w.length - 1)) := by
  have hr : readInput w (w.length : ℤ) = none := readInput_eq_none (Or.inr le_rfl)
  simp only [next, loadConfig, load, table, hr, archiveActs, rewindConfig]
  congr 1
  apply Config.ext <;> try rfl
  · funext t z
    refine Fin.cases ?_ (fun j => ?_) t
    · dsimp [partialWork, completedWork, positions]
      exact ite_self _
    · rfl
  · funext t
    refine Fin.cases ?_ (fun j => ?_) t <;> rfl

theorem rewind_step (w : List Bool) (i : ℕ) (hi : i < w.length) :
    next (table F D s₀ q₀ C) w (rewindConfig F D s₀ w i) =
      some (rewindConfig F D s₀ w (i - 1)) := by
  have hr : readInput w (i : ℤ) = some (w[i]'hi) := by
    rw [readInput_natCast, nth_eq_getElem?, List.getElem?_eq_getElem hi]
  simp only [next, rewindConfig, rewind, table, hr, preserveActs, archiveActs]
  congr 1
  apply Config.ext <;> try rfl
  · funext t z
    refine Fin.cases ?_ (fun j => ?_) t
    · dsimp [completedWork, positions]
      exact ite_self _
    · dsimp [completedWork, positions]
      by_cases hz : z = (i : ℤ)
      · subst z; exact ite_eq_left rfl
      · exact ite_eq_right hz
  · funext t
    refine Fin.cases ?_ (fun j => ?_) t <;> rfl

theorem finish_step (w : List Bool) :
    next (table F D s₀ q₀ C) w (rewindConfig F D s₀ w (-1)) =
      some (readyConfig F D s₀ q₀ w) := by
  have hr : readInput w (-1) = none := readInput_eq_none (Or.inl (by omega))
  simp only [next, rewindConfig, rewind, table, hr, preserveActs, archiveActs, readyConfig]
  congr 1
  apply Config.ext <;> try rfl
  · funext t z
    refine Fin.cases ?_ (fun j => ?_) t
    · dsimp [completedWork, positions]
      exact ite_self _
    · dsimp [completedWork, positions]
      by_cases hz : z = -1
      · subst z; exact ite_eq_left rfl
      · exact ite_eq_right hz
  · funext t
    refine Fin.cases ?_ (fun j => ?_) t <;> rfl


/-- The load invariant after every number of input bits, not an assumed scan/run
correspondence. -/
theorem load_run (w : List Bool) (n : ℕ) (hn : n ≤ w.length) :
    run (table F D s₀ q₀ C) w n (loadConfig F D s₀ w 0) =
      some (loadConfig F D s₀ w n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply run_trans (table F D s₀ q₀ C) w (ih (by omega))
    rw [run, load_step F D s₀ q₀ C w n (by omega)]
    rfl

/-- Rewind preserves the completed code words and reaches the consumer in
exactly n+1 transitions from position n-1, including the marker-return step. -/
theorem rewind_run (w : List Bool) (n : ℕ) (hn : n ≤ w.length) :
    run (table F D s₀ q₀ C) w (n + 1) (rewindConfig F D s₀ w (n - 1)) =
      some (readyConfig F D s₀ q₀ w) := by
  induction n with
  | zero =>
    rw [run, show (↑(0 : ℕ) : ℤ) - 1 = -1 by rfl, finish_step]
    rfl
  | succ n ih =>
    rw [show (↑(n + 1) : ℤ) - 1 = n by omega, run,
      rewind_step F D s₀ q₀ C w n (by omega)]
    exact ih (by omega)

/-- Exactly two setup transitions, one transition per bit, one EOF seal,
and length+1 rewind transitions. Empty inputs are included. -/
theorem complete_run (w : List Bool) :
    run (table F D s₀ q₀ C) w (2 * w.length + 4) (initial start blank) =
      some (readyConfig F D s₀ q₀ w) := by
  have hstart : run (table F D s₀ q₀ C) w 1 (initial start blank) = some markConfig := by
    rw [run, start_step]; rfl
  have hmark : run (table F D s₀ q₀ C) w 1 markConfig = some (loadConfig F D s₀ w 0) := by
    rw [run, mark_step]; rfl
  have heof : run (table F D s₀ q₀ C) w 1 (loadConfig F D s₀ w w.length) =
      some (rewindConfig F D s₀ w (w.length - 1)) := by
    rw [run, eof_step]; rfl
  have h := run_trans _ _ hstart (run_trans _ _ hmark
    (run_trans _ _ (load_run F D s₀ q₀ C w w.length le_rfl)
      (run_trans _ _ heof (rewind_run F D s₀ q₀ C w w.length le_rfl))))
  rw [show 2 * w.length + 4 = 1 + (1 + (w.length + (1 + (w.length + 1)))) by omega]
  exact h

/-- During loading, even the EOF location is a virgin blank archive cell. -/
theorem load_scanned_blank (w : List Bool) (i : ℕ) (j : Fin r) :
    (loadConfig (Q := Q) (B := B) F D s₀ w i).work j.succ
      ((loadConfig (Q := Q) (B := B) F D s₀ w i).workPos j.succ) = blank := by
  have hn : (i : ℤ) ≠ -1 := by omega
  simp [loadConfig, partialWork, positions, partialArchive, hn]

theorem archive_left (w : List Bool) (j : Fin r) :
    archive (B := B) F D s₀ w j (-1) = leftMarker := by
  have hn : (-1 : ℤ) ≠ w.length := by omega
  simp [archive, partialArchive, hn]

theorem archive_right (w : List Bool) (j : Fin r) :
    archive (B := B) F D s₀ w j w.length = rightMarker := by simp [archive]

theorem archive_data (w : List Bool) (j : Fin r) (i : ℕ) (hi : i < w.length) :
    archive (B := B) F D s₀ w j i = data j (D j (scan F s₀ w i j) (w[i]'hi)) := by
  have hn : (i : ℤ) ≠ -1 := by omega
  have he : (i : ℤ) ≠ w.length := by omega
  have hh : (0 : ℤ) ≤ i ∧ (i : ℤ) < w.length := by omega
  simp [archive, partialArchive, hn, he, hh, codeSymbol, List.getElem?_eq_getElem hi]

theorem archive_exterior (w : List Bool) (j : Fin r) (z : ℤ)
    (hz : z < -1 ∨ (w.length : ℤ) < z) : archive (B := B) F D s₀ w j z = blank := by
  have hn : z ≠ -1 := by omega
  have he : z ≠ w.length := by omega
  have hh : ¬ (0 ≤ z ∧ z < w.length) := by omega
  simp [archive, partialArchive, hn, he, hh]

/-- The preparation states are the same forward scans used by checkpoint getters. -/
theorem scan_eq_scanState (w : List Bool) (i : ℕ) (j : Fin r) :
    scan F s₀ w i j = AdaptiveTransfer.scanState (fun _ => F j) (s₀ j)
      (fun n => w[n]?.getD false) i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [scan, AdaptiveTransfer.scanState, ih]

section Native
variable [Fintype Q] [∀ j, Fintype (S j)] [∀ j, Fintype (A j)] [Fintype B]

noncomputable def nativeProducer : TM := machine start blank (table F D s₀ q₀ C)

/-- A literal frozen native execution from its blank initial configuration. -/
theorem native_load (w : List Bool) :
    Transpose.stepN (nativeProducer F D s₀ q₀ C) w (2 * w.length + 4)
      (Transpose.init (nativeProducer F D s₀ q₀ C)) =
      some (denote start blank (table F D s₀ q₀ C) (readyConfig F D s₀ q₀ w)) := by
  unfold nativeProducer
  rw [← denote_initial, stepN_denote, complete_run]
  rfl

/-- Exact finite resources; no counter or hidden scan state is added. -/
theorem native_resources :
    (nativeProducer F D s₀ q₀ C).k = r + 1 ∧
    (nativeProducer F D s₀ q₀ C).q + 1 = Fintype.card Q +
      (∏ j : Fin r, Fintype.card (S j)) + 3 ∧
    (nativeProducer F D s₀ q₀ C).g + 1 =
      (∑ j : Fin r, Fintype.card (A j)) + Fintype.card B + 3 := by
  have h := machine_resources start blank (table F D s₀ q₀ C)
  simp only [Phase, Symbol, ScanStates, Fintype.card_option, Fintype.card_sum,
    Fintype.card_sigma, Fintype.card_pi] at h
  exact ⟨h.1, by dsimp [nativeProducer]; omega, by dsimp [nativeProducer]; omega⟩

theorem native_ready_properties (w : List Bool) :
    let c := denote start blank (table F D s₀ q₀ C) (readyConfig F D s₀ q₀ w)
    c.state = pointCode (start (Q := Q) (S := S)) (consume q₀) ∧
    c.inPos = 0 ∧ (∀ t, c.workPos t = 0) ∧ c.outRev = [] ∧
    (∀ z, c.work (0 : Fin (r + 1)) z = 0) ∧
    (∀ (j : Fin r) z, c.work j.succ z = pointCode (blank (A := A) (B := B))
      (archive F D s₀ w j z)) := by
  dsimp [denote, readyConfig, positions, completedWork]
  refine ⟨rfl, rfl, ?_, rfl, ?_, fun _ _ => rfl⟩
  · intro t; exact Fin.cases rfl (fun _ => rfl) t
  · intro z; exact pointCode_initial _

end Native
end AdaptiveTransfer.ScanLoader
