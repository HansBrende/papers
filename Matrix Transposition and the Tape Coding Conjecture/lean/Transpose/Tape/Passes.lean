import Transpose.Tape.DefsP
import Transpose.Tape.Run

/-!
# Passes: monotonicity, the Fresh-Cell Lemma, greedy passes, the address count
-/

namespace Transpose.Tape.Impl

open Transpose

/-! ### Monotone trajectories -/

/-- A monotone trajectory compares any two times of its interval. -/
theorem monoOn_cases {h : ℕ → ℤ} {s e : ℕ} (hm : MonoOn h s e) :
    (∀ x y, s ≤ x → x ≤ y → y ≤ e → h x ≤ h y) ∨
      (∀ x y, s ≤ x → x ≤ y → y ≤ e → h y ≤ h x) := by
  rcases hm with up | dn
  · left
    intro x y hx hxy hy
    induction y, hxy using Nat.le_induction with
    | base => exact le_rfl
    | succ y hxy ih => exact le_trans (ih (by omega)) (up y (by omega) (by omega))
  · right
    intro x y hx hxy hy
    induction y, hxy using Nat.le_induction with
    | base => exact le_rfl
    | succ y hxy ih => exact le_trans (dn y (by omega) (by omega)) (ih (by omega))

theorem monoOn_mono {h : ℕ → ℤ} {s e s' e' : ℕ} (hm : MonoOn h s e) (hs : s ≤ s') (he : e' ≤ e) :
    MonoOn h s' e' := by
  rcases hm with up | dn
  · exact Or.inl (fun τ h1 h2 => up τ (by omega) (by omega))
  · exact Or.inr (fun τ h1 h2 => dn τ (by omega) (by omega))

theorem allMono_mono {M : TM} {w : List Bool} {s e s' e' : ℕ} (hm : AllMono M w s e)
    (hs : s ≤ s') (he : e' ≤ e) : AllMono M w s' e' :=
  ⟨monoOn_mono hm.1 hs he, fun t => monoOn_mono (hm.2 t) hs he⟩

/-- **The Fresh-Cell Lemma**: if `h` is monotone on `[s, e]`, `a ≤ τ ≤ e` and `h τ ≠ h a`, then no
step `ρ ∈ [s, a)` visits the cell `h τ`. -/
theorem pass_fresh {h : ℕ → ℤ} {s e a τ ρ : ℕ} (hmono : MonoOn h s e) (hsρ : s ≤ ρ) (hρa : ρ < a)
    (haτ : a ≤ τ) (hτe : τ ≤ e) (hne : h τ ≠ h a) : h ρ ≠ h τ := by
  intro heq
  rcases monoOn_cases hmono with up | dn
  · have h1 := up ρ a hsρ (by omega) (by omega)
    have h2 := up a τ (by omega) haτ hτe
    exact hne (by omega)
  · have h1 := dn ρ a hsρ (by omega) (by omega)
    have h2 := dn a τ (by omega) haτ hτe
    exact hne (by omega)

/-! ### Pass partitions -/

theorem pp_mono {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ r) : p i ≤ p j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact le_trans (ih (by omega)) (hp.2.2.1 j (by omega))

theorem pp_le_T {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) {i : ℕ} (hi : i ≤ r) : p i ≤ T := by
  rw [← hp.2.1]; exact pp_mono hp hi le_rfl

/-- Every step before `T` lies in a pass. -/
theorem pp_exists_pass {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) {σ : ℕ} (hσ : σ < T) :
    ∃ P < r, p P ≤ σ ∧ σ < p (P + 1) := by
  classical
  have h0 : p 0 ≤ σ := by rw [hp.1]; exact Nat.zero_le _
  set P := Nat.findGreatest (fun i => p i ≤ σ) r with hP
  have hPσ : p P ≤ σ := Nat.findGreatest_spec (P := fun i => p i ≤ σ) (Nat.zero_le r) h0
  have hPr : P ≤ r := Nat.findGreatest_le r
  have hPlt : P < r := by
    rcases Nat.lt_or_ge P r with h | h
    · exact h
    · have : P = r := le_antisymm hPr h
      rw [this, hp.2.1] at hPσ; omega
  refine ⟨P, hPlt, hPσ, ?_⟩
  by_contra hc
  push Not at hc
  exact Nat.findGreatest_is_greatest (P := fun i => p i ≤ σ) (Nat.lt_succ_self P) hPlt hc

/-! ### Greedy passes -/

theorem allMono_self (M : TM) (w : List Bool) (a : ℕ) : AllMono M w a a :=
  ⟨Or.inl (fun τ h1 h2 => by omega), fun t => Or.inl (fun τ h1 h2 => by omega)⟩

theorem monoOn_succ (h : ℕ → ℤ) (a : ℕ) : MonoOn h a (a + 1) := by
  rcases le_total (h a) (h (a + 1)) with hle | hle
  · exact Or.inl (fun τ h1 h2 => by
      have : τ = a := by omega
      subst this; exact hle)
  · exact Or.inr (fun τ h1 h2 => by
      have : τ = a := by omega
      subst this; exact hle)

theorem allMono_succ (M : TM) (w : List Bool) (a : ℕ) : AllMono M w a (a + 1) :=
  ⟨monoOn_succ _ a, fun _ => monoOn_succ _ a⟩

theorem greedyBound_le (M : TM) (w : List Bool) (T i : ℕ) : greedyBound M w T i ≤ T := by
  classical
  cases i with
  | zero => simp [greedyBound]
  | succ i => simp only [greedyBound]; exact Nat.findGreatest_le _

theorem greedyBound_spec (M : TM) (w : List Bool) (T i : ℕ) :
    greedyBound M w T i ≤ greedyBound M w T (i + 1) ∧
      AllMono M w (greedyBound M w T i) (greedyBound M w T (i + 1)) := by
  classical
  have hP : greedyBound M w T i ≤ greedyBound M w T i ∧
      AllMono M w (greedyBound M w T i) (greedyBound M w T i) := ⟨le_rfl, allMono_self _ _ _⟩
  have := Nat.findGreatest_spec (P := fun e => greedyBound M w T i ≤ e ∧
      AllMono M w (greedyBound M w T i) e) (greedyBound_le M w T i) hP
  simpa [greedyBound] using this

/-- The greedy step reaches at least every admissible end point. -/
theorem le_greedyBound_succ (M : TM) (w : List Bool) (T i e : ℕ) (he : e ≤ T)
    (hge : greedyBound M w T i ≤ e) (hm : AllMono M w (greedyBound M w T i) e) :
    e ≤ greedyBound M w T (i + 1) := by
  classical
  have := Nat.le_findGreatest (P := fun e => greedyBound M w T i ≤ e ∧
      AllMono M w (greedyBound M w T i) e) he ⟨hge, hm⟩
  simpa [greedyBound] using this

theorem greedyBound_ge (M : TM) (w : List Bool) (T i : ℕ) : min i T ≤ greedyBound M w T i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rcases lt_or_ge (greedyBound M w T i) T with h | h
    · have := le_greedyBound_succ M w T i (greedyBound M w T i + 1) (by omega) (by omega)
        (allMono_succ _ _ _)
      omega
    · have := (greedyBound_spec M w T i).1; omega

theorem exists_greedyBound_eq (M : TM) (w : List Bool) (T : ℕ) :
    ∃ i, greedyBound M w T i = T :=
  ⟨T, le_antisymm (greedyBound_le _ _ _ _) (by simpa using greedyBound_ge M w T T)⟩

theorem greedyPasses_eq (M : TM) (w : List Bool) (T : ℕ) :
    greedyPasses M w T = Nat.find (exists_greedyBound_eq M w T) := by
  classical
  simp [greedyPasses, exists_greedyBound_eq M w T]

theorem greedy_passPartition (M : TM) (w : List Bool) (T : ℕ) :
    PassPartition M w T (greedyPasses M w T) (greedyBound M w T) := by
  classical
  refine ⟨rfl, ?_, fun i _ => (greedyBound_spec M w T i).1, fun i _ => (greedyBound_spec M w T i).2⟩
  rw [greedyPasses_eq]; exact Nat.find_spec (exists_greedyBound_eq M w T)

/-- **The greedy partition is optimal.** -/
theorem greedyPasses_le {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) : greedyPasses M w T ≤ r := by
  classical
  -- p i ≤ greedyBound i for all i ≤ r
  have key : ∀ i ≤ r, p i ≤ greedyBound M w T i := by
    intro i
    induction i with
    | zero => intro _; rw [hp.1]; exact Nat.zero_le _
    | succ i ih =>
      intro hi
      have hpi := ih (by omega)
      have hpT : p (i + 1) ≤ T := pp_le_T hp hi
      rcases le_or_gt (p (i + 1)) (greedyBound M w T i) with hle | hlt
      · exact le_trans hle (greedyBound_spec M w T i).1
      · apply le_greedyBound_succ M w T i _ hpT (le_of_lt hlt)
        exact allMono_mono (hp.2.2.2 i (by omega)) hpi le_rfl
  have hr : greedyBound M w T r = T :=
    le_antisymm (greedyBound_le _ _ _ _) (by have := key r le_rfl; rw [hp.2.1] at this; exact this)
  rw [greedyPasses_eq]
  exact Nat.find_min' _ hr

/-- Past the greedy pass count, the greedy bounds stay at `T` (padding with empty passes): they are
monotone and bounded by `T`. -/
theorem greedyBound_eq_T_of_ge (M : TM) (w : List Bool) (T : ℕ) :
    ∀ i, greedyPasses M w T ≤ i → greedyBound M w T i = T := fun i hi =>
  le_antisymm (greedyBound_le M w T i) (by
    have h := monotone_nat_of_le_succ (fun j => (greedyBound_spec M w T j).1) hi
    rwa [(greedy_passPartition M w T).2.1] at h)

/-- **A pass partition with `r` passes exists exactly when the greedy count is at most `r`.** -/
theorem passPartition_iff (M : TM) (w : List Bool) (T r : ℕ) :
    (∃ p, PassPartition M w T r p) ↔ greedyPasses M w T ≤ r := by
  constructor
  · rintro ⟨p, hp⟩; exact greedyPasses_le hp
  · intro hr
    exact ⟨greedyBound M w T, rfl, greedyBound_eq_T_of_ge M w T r hr,
      fun i _ => (greedyBound_spec M w T i).1, fun i _ => (greedyBound_spec M w T i).2⟩

/-- On an oblivious class the pass partitions do not depend on the input. -/
theorem passPartition_indep {M : TM} {W : Set (List Bool)} {T r : ℕ} (hobl : ObliviousOn M W T)
    {w w' : List Bool} (hw : w ∈ W) (hw' : w' ∈ W) (p : ℕ → ℕ) :
    PassPartition M w T r p ↔ PassPartition M w' T r p := by
  have hin : inTraj M w = inTraj M w' := funext fun τ => (hobl.2 w hw w' hw' τ).1
  have hwk : workTraj M w = workTraj M w' := funext fun τ => (hobl.2 w hw w' hw' τ).2.1
  simp only [PassPartition, AllMono, hin, hwk]

/-- On an oblivious class the greedy pass count does not depend on the input. -/
theorem greedyPasses_indep {M : TM} {W : Set (List Bool)} {T : ℕ} (hobl : ObliviousOn M W T)
    {w w' : List Bool} (hw : w ∈ W) (hw' : w' ∈ W) :
    greedyPasses M w T = greedyPasses M w' T := by
  have key : ∀ r, greedyPasses M w T ≤ r ↔ greedyPasses M w' T ≤ r := by
    intro r
    rw [← passPartition_iff, ← passPartition_iff]
    exact exists_congr (fun p => passPartition_indep hobl hw hw' p)
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

/-! ### The address count -/

theorem addrCount_mul (k r : ℕ) : k * addrCount k r + 1 = (k + 1) ^ r := by
  induction r with
  | zero => simp [addrCount]
  | succ r ih =>
    simp only [addrCount, Finset.sum_range_succ] at ih ⊢
    rw [mul_add, pow_succ]
    nlinarith [ih]

end Transpose.Tape.Impl
