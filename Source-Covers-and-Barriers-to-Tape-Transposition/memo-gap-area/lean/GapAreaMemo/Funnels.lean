import GapAreaMemo.GapArea
import LeanMachine.IntervalGapArea

set_option autoImplicit false

/-!
# Funnels

A funnel is a property of the full family system of a geometry: time sets
`D 0, …, D m` such that each `D i` with `i < m` is fed by a single family,
which moves into `D i` only times of `D (i + 1)`, and no family feeds `D m`.
Every orbit, under any set of families, then meets `D 0` in at most `m + 1`
times. If all times that read a raw interval lie in `D 0`, the frozen point
area of every column, at every selection and phase, is bounded below.
-/

namespace SourceCovers

open Classical Finset Filter LeanMachine LeanMachine.SourceBank
open scoped BigOperators Topology
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}

namespace ActualFamily

/-- A family feeds a time set if its shadow moves some time into the set. -/
def Feeds (q : ActualFamily xs T) (D : Set ℕ) : Prop :=
  ∃ t, q.shadow t ≠ t ∧ q.shadow t ∈ D

end ActualFamily

/-- A funnel of depth `m`. No root time is involved. -/
structure Funnel (xs : Fin k → ℕ → ℤ) (T m : ℕ) where
  D : ℕ → Set ℕ
  f : ℕ → ActualFamily xs T
  feeds_unique : ∀ i < m, ∀ q : ActualFamily xs T, q.Feeds (D i) → q = f i
  pull : ∀ i < m, ∀ t, (f i).shadow t ≠ t → (f i).shadow t ∈ D i → t ∈ D (i + 1)
  terminal : ∀ q : ActualFamily xs T, ¬ q.Feeds (D m)

namespace Funnel

variable {m : ℕ} (F : Funnel xs T m)

/-- The times of `D (m - n)` reachable from the root `s`: the root and its
images under `f (m - n), …, f (m - 1)` applied innermost first. -/
def reach (s : ℕ) : ℕ → Finset ℕ
  | 0 => {s}
  | n + 1 => insert s ((reach s n).image (F.f (m - (n + 1))).shadow)

theorem reach_card (s : ℕ) (n : ℕ) : (F.reach s n).card ≤ n + 1 := by
  induction n with
  | zero => simp [reach]
  | succ n ih =>
    simp only [reach]
    exact (card_insert_le _ _).trans (by
      have := (card_image_le (s := F.reach s n) (f := (F.f (m - (n + 1))).shadow)).trans ih
      omega)

theorem self_mem_reach (s : ℕ) (n : ℕ) : s ∈ F.reach s n := by
  cases n with
  | zero => simp [reach]
  | succ n => simp [reach]

theorem shadowEndpoint_concat (w : List (ActualFamily xs T)) (q : ActualFamily xs T) (t : ℕ) :
    shadowEndpoint (w ++ [q]) t = q.shadow (shadowEndpoint w t) := by
  simp only [shadowEndpoint, List.map_append, List.map_cons, List.map_nil,
    MonotonePatches.Action.endpoint_append]
  rfl

/-- Every word, over any families, that ends in `D (m - n)` ends in `reach s n`. -/
theorem endpoint_mem_reach (s : ℕ) (w : List (ActualFamily xs T)) :
    ∀ n ≤ m, shadowEndpoint w s ∈ F.D (m - n) → shadowEndpoint w s ∈ F.reach s n := by
  induction w using List.reverseRecOn with
  | nil => intro n _ _; exact F.self_mem_reach s n
  | append_singleton w q ih =>
    intro n hn hmem
    rw [shadowEndpoint_concat] at hmem ⊢
    by_cases hq : q.shadow (shadowEndpoint w s) = shadowEndpoint w s
    · rw [hq] at hmem ⊢
      exact ih n hn hmem
    · cases n with
      | zero => exact absurd ⟨_, hq, by simpa using hmem⟩ (F.terminal q)
      | succ n =>
        have hi : m - (n + 1) < m := by omega
        have hfeed : q.Feeds (F.D (m - (n + 1))) := ⟨_, hq, hmem⟩
        have hqf := F.feeds_unique _ hi q hfeed
        subst hqf
        have hprev := F.pull _ hi _ hq hmem
        rw [show m - (n + 1) + 1 = m - n by omega] at hprev
        have hrec := ih n (by omega) hprev
        simp only [reach]
        exact mem_insert_of_mem (mem_image_of_mem _ hrec)

/-- Any orbit meets `D 0` in at most `m + 1` times. -/
theorem orbit_inter_subset (K : Finset (ActualFamily xs T)) (s : ℕ) :
    shadowOrbit K s ∩ F.D 0 ⊆ (F.reach s m : Set ℕ) := by
  rintro u ⟨⟨w, _, rfl⟩, hu⟩
  exact F.endpoint_mem_reach s w m le_rfl (by simpa using hu)

end Funnel

variable {K : Finset (ActualFamily xs T)}

/-- **Lemma A.** If every time that reads the open raw interval `(lo, hi)` lies
in `D 0`, the frozen point area at every legal phase and column is at least
`((hi - lo)/L)^2 / (2(m+3))`. -/
theorem phaseGapArea_ge_of_funnel (hc : HasSpanColoring K 2) {M ρ d b j m : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ)
    (hd : 0 < d) (hb : 0 < b) (hj : j < d) (hn : ∀ z < d * d * b, t z < T)
    (hx : ∀ s ≤ T - 1, x s < d * d * b)
    (F : Funnel xs T m) {lo hi : ℕ} (hlohi : lo ≤ hi) (hhi : hi ≤ d * d * b)
    (hread : ∀ s, lo < x s → x s < hi → s ∈ F.D 0) :
    (((hi - lo : ℕ) : ℝ) / (d * d * b)) ^ 2 / (2 * ((m : ℝ) + 3)) ≤
      phaseGapArea hc hM E x t d b ρ j := by
  set L := d * d * b with hLdef
  have hL : 0 < L := Nat.mul_pos (Nat.mul_pos hd hd) hb
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  set s := columnFirst t (d * b) j
  set S := rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x s
  have htime : s < T := by
    have := hn _ ((column_indices hd hb hj).1.trans_lt (column_indices hd hb hj).2)
    simpa only [s, columnFirst] using this
  have hSL : S ⊆ range L := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    apply mem_range.mpr
    apply hx
    have hu' := shadowOrbit_le ((exactSourceBank_exact hc hM hρ E _).subset hu)
    omega
  -- the raw values strictly inside the interval come from `reach s m`
  let P : Finset ℕ := (F.reach s m).image x
  have hPcard : P.card ≤ m + 1 := card_image_le.trans (F.reach_card s m)
  have hinside : ∀ z ∈ S, lo < z → z < hi → z ∈ P := by
    intro z hz hlo hhi'
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hz
    have horb : u ∈ shadowOrbit (retainedCore K M ρ ∪ E) s :=
      (exactSourceBank_exact hc hM hρ E s).subset hu
    have hD : u ∈ F.D 0 := hread u hlo hhi'
    exact mem_image_of_mem x (by exact_mod_cast F.orbit_inter_subset _ s ⟨horb, hD⟩)
  -- cover the raw set by two outer intervals and the inner singletons
  let I : Finset (Option (Option ℕ)) := insert none (insert (some none) (P.image (some ∘ some)))
  let loF : Option (Option ℕ) → ℕ := fun a => match a with
    | none => 0 | some none => hi | some (some z) => z
  let hiF : Option (Option ℕ) → ℕ := fun a => match a with
    | none => lo | some none => L | some (some z) => z
  have hcover : ∀ z ∈ S, ∃ a ∈ I, loF a ≤ z ∧ z ≤ hiF a := by
    intro z hz
    by_cases hz1 : z ≤ lo
    · exact ⟨none, mem_insert_self _ _, Nat.zero_le _, hz1⟩
    · by_cases hz2 : hi ≤ z
      · exact ⟨some none, mem_insert_of_mem (mem_insert_self _ _), hz2,
          (mem_range.mp (hSL hz)).le⟩
      · refine ⟨some (some z), ?_, le_rfl, le_rfl⟩
        apply mem_insert_of_mem (mem_insert_of_mem _)
        exact mem_image_of_mem _ (hinside z hz (by omega) (by omega))
  have hnone : (none : Option (Option ℕ)) ∉ insert (some none) (P.image (some ∘ some)) := by
    simp
  have hsome : (some none : Option (Option ℕ)) ∉ P.image (some ∘ some) := by simp
  have hzero : ∑ a ∈ P.image (some ∘ some), ((hiF a - loF a : ℕ) : ℝ) = 0 := by
    apply sum_eq_zero
    intro a ha
    obtain ⟨z, _, rfl⟩ := mem_image.mp ha
    simp [hiF, loF]
  have hlen : (∑ a ∈ I, ((hiF a - loF a : ℕ) : ℝ)) ≤ (1 - ((hi - lo : ℕ) : ℝ) / L) * L := by
    rw [sum_insert hnone, sum_insert hsome, hzero]
    have e1 : ((hiF none - loF none : ℕ) : ℝ) = lo := by simp [hiF, loF]
    have e2 : ((hiF (some none) - loF (some none) : ℕ) : ℝ) = (L : ℝ) - hi := by
      simp only [hiF, loF]
      rw [Nat.cast_sub hhi]
    rw [e1, e2, Nat.cast_sub hlohi]
    apply le_of_eq
    field_simp
    ring
  have hcard : (I.card : ℝ) ≤ (m : ℝ) + 3 := by
    have : I.card ≤ P.card + 2 := by
      refine (card_insert_le _ _).trans ?_
      have := (card_insert_le (some none) (P.image (some ∘ some))).trans
        (Nat.succ_le_succ (card_image_le (s := P) (f := some ∘ some)))
      omega
    have h2 : (I.card : ℝ) ≤ (P.card : ℝ) + 2 := by exact_mod_cast this
    have h3 : (P.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hPcard
    linarith
  have harea := IntervalGapArea.point_area_lower_of_budgets hL
    ⟨_, exactSourceBank_raw_root hc hM hρ E x s⟩ hSL I loF hiF hcover hlen hcard
  have hfrac : max (1 - (1 - ((hi - lo : ℕ) : ℝ) / L)) 0 = ((hi - lo : ℕ) : ℝ) / L := by
    rw [sub_sub_cancel]
    exact max_eq_left (by positivity)
  rw [hfrac] at harea
  rw [phaseGapArea_eq hc hM hρ E x t d b j]
  convert harea using 2
  rw [hLdef]
  push_cast
  ring

namespace AdmissibleGeometry

variable {c β : ℝ} {N q : ℕ} (G : AdmissibleGeometry c β N q)

/-- The geometry has a funnel of depth `m` whose raw interval has relative
length at least `δ`. -/
def HasFunnel (m : ℕ) (δ : ℝ) : Prop :=
  ∃ (F : Funnel G.xs G.T m) (lo hi : ℕ), lo ≤ hi ∧ hi ≤ G.inputLength ∧
    δ * G.inputLength ≤ ((hi - lo : ℕ) : ℝ) ∧ ∀ s, lo < G.x s → G.x s < hi → s ∈ F.D 0

/-- A funnel bounds the mean frozen point area below at every selection. -/
theorem prefixMeanGapArea_ge_of_funnel (O : SortedCore G.core) {J R M m : ℕ} {δ : ℝ}
    (hM : 2 ≤ M) (hRM : R < M) (hδ : 0 ≤ δ) (hF : G.HasFunnel m δ) :
    δ ^ 2 / (2 * ((m : ℝ) + 3)) ≤ G.prefixMeanGapArea O J R M hM := by
  obtain ⟨F, lo, hi, hlohi, hhi, hlen, hread⟩ := hF
  have hA := (protected_phase_average (O.selectedPrefix J) (O.subprefix J R)
    (O.subprefix_card_le J R) hRM).1
  set A := admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M
  have hAne : A.Nonempty := card_pos.mp (lt_of_lt_of_le (Nat.sub_pos_of_lt hRM) hA)
  have hLR : (0 : ℝ) < G.inputLength := by exact_mod_cast G.inputLength_pos
  have hfrac : δ ≤ ((hi - lo : ℕ) : ℝ) / (G.d * G.d * G.b) := by
    rw [le_div_iff₀ (by simpa [inputLength] using hLR)]
    simpa [inputLength, mul_comm] using hlen
  have hpoint : ∀ ρ ∈ A, ∀ j ∈ range G.d, δ ^ 2 / (2 * ((m : ℝ) + 3)) ≤
      phaseGapArea (G.core_coloring.mono (O.selectedPrefix_subset J)) hM
        G.exceptions G.x G.t G.d G.b ρ j := by
    intro ρ hρ j hj
    refine le_trans ?_ (phaseGapArea_ge_of_funnel _ hM (admissiblePhase_lt hρ) G.exceptions
      G.x G.t G.hd G.hb (mem_range.mp hj) G.append_lt G.raw_range F hlohi hhi hread)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ hδ hfrac 2
  have hden : (0 : ℝ) < A.card * G.d := mul_pos (by exact_mod_cast card_pos.mpr hAne)
    (by exact_mod_cast G.hd)
  unfold prefixMeanGapArea meanGapArea
  rw [le_div_iff₀ hden]
  calc
    δ ^ 2 / (2 * ((m : ℝ) + 3)) * (A.card * G.d) =
        ∑ ρ ∈ A, ∑ j ∈ range G.d, δ ^ 2 / (2 * ((m : ℝ) + 3)) := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      ring
    _ ≤ _ := sum_le_sum fun ρ hρ => sum_le_sum fun j hj => hpoint ρ hρ j hj

end AdmissibleGeometry

namespace NearFullSequence

variable {c β : ℝ} {N q : ℕ}

/-- **Theorem A.** No near-full sequence consists, from some point on, of
geometries with funnels of a fixed depth whose raw intervals have a fixed
positive relative length. Any number of exceptions and any size profile are
allowed. -/
theorem not_eventually_funnel (S : NearFullSequence c β N q) {m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ᶠ ν in atTop, (S.geometry ν).HasFunnel m δ) : False := by
  obtain ⟨P⟩ := S.exists_jointProfile
  set B : ℝ := δ ^ 2 / (2 * ((m : ℝ) + 3)) with hB
  have hBpos : 0 < B := by positivity
  have hsub : ∀ᶠ n in atTop, (S.geometry (P.subsequence n)).HasFunnel m δ :=
    P.strictMono.tendsto_atTop.eventually hF
  have hlimit : ∀ M (hM : 2 ≤ M), B ≤ P.gapAreaLimit 0 M hM := by
    intro M hM
    have hJ : ∀ J, B ≤ limsup (P.prefixGapArea J 0 M hM) atTop := by
      intro J
      apply BoundedLimsup.le_limsup
        (fun n => (P.prefixGapArea_bounds (J := J) hM (by omega) n).2.trans (by norm_num))
      filter_upwards [hsub] with n hn
      exact (S.geometry (P.subsequence n)).prefixMeanGapArea_ge_of_funnel
        (S.order (P.subsequence n)) hM (by omega) hδ.le hn
    exact BoundedLimsup.le_limsup
      (fun J => (P.prefixGapArea_limsup_bounds (J := J) hM (by omega)).2.trans (by norm_num))
      (Eventually.of_forall hJ)
  set C0 : ℝ := β * P.hopTail 0
  obtain ⟨M, hM2, hMC⟩ : ∃ M : ℕ, 2 ≤ M ∧ C0 < B * M := by
    refine ⟨Nat.ceil (|C0| / B) + 2, by omega, ?_⟩
    have h1 : |C0| / B ≤ (Nat.ceil (|C0| / B) : ℝ) := Nat.le_ceil _
    have h2 : |C0| ≤ B * (Nat.ceil (|C0| / B) : ℝ) := by
      rw [div_le_iff₀ hBpos] at h1
      linarith
    have h3 : C0 ≤ |C0| := le_abs_self C0
    push_cast
    nlinarith
  have hG := P.necessary_gap_area (R := 0) (M := M) hM2 (by omega)
  have hLow := hlimit M hM2
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have : B ≤ C0 / M := by
    simpa only [Nat.sub_zero, C0] using hLow.trans hG
  rw [le_div_iff₀ hMpos] at this
  linarith

/-- The same conclusion when funnels occur only along a subsequence. -/
theorem not_frequently_funnel (S : NearFullSequence c β N q) {m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hF : ∃ᶠ ν in atTop, (S.geometry ν).HasFunnel m δ) : False := by
  obtain ⟨φ, hφ, hφF⟩ := Filter.extraction_of_frequently_atTop hF
  exact (S.subseq φ hφ).not_eventually_funnel hδ (Eventually.of_forall hφF)

end NearFullSequence

end
end SourceCovers
