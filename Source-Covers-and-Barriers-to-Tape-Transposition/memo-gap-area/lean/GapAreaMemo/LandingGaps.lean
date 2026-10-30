import GapAreaMemo.LandingCounts

set_option autoImplicit false

/-!
# Single-sweep terminal-landing geometries: the finite gap bounds

The class has two designated families, an older `e` and a newer `g`. The raw
path is constant on the lower regions of all core families and of `g`, and
at every column root; it is monotone on the lower region of `e`; and no core
family and not `g` acts on the lower region of `e`. Then every raw value of
the exact source bank at a column root is the constant or the raw value of a
landing of `e`. Two finite bounds follow at every selection and legal phase:
a raw interval spanned by one core step between landing times contains few
raw values, and all raw values lie in linearly many short raw intervals.
-/

namespace SourceCovers

open Classical Finset Filter LeanMachine LeanMachine.SourceBank LeanMachine.MonotonePatches
open scoped BigOperators
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}

/-- A sparse raw interval forces point area. -/
theorem pointArea_ge_of_sparse {L : ℕ} (hL : 0 < L) {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) {lo hi p : ℕ} (hlohi : lo ≤ hi) (hhi : hi ≤ L)
    (hsparse : (S.filter (fun z => lo < z ∧ z < hi)).card ≤ p) :
    (((hi - lo : ℕ) : ℝ) / L) ^ 2 / (2 * ((p : ℝ) + 2)) ≤
      GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  set P := S.filter (fun z => lo < z ∧ z < hi)
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
        exact mem_image_of_mem _ (mem_filter.mpr ⟨hz, by omega, by omega⟩)
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
  have hcard : (I.card : ℝ) ≤ (p : ℝ) + 2 := by
    have : I.card ≤ P.card + 2 := by
      refine (card_insert_le _ _).trans ?_
      have := (card_insert_le (some none) (P.image (some ∘ some))).trans
        (Nat.succ_le_succ (card_image_le (s := P) (f := some ∘ some)))
      omega
    have h2 : (I.card : ℝ) ≤ (P.card : ℝ) + 2 := by exact_mod_cast this
    have h3 : (P.card : ℝ) ≤ p := by exact_mod_cast hsparse
    linarith
  have harea := IntervalGapArea.point_area_lower_of_budgets hL hS hSL I loF hiF hcover hlen hcard
  have hfrac : max (1 - (1 - ((hi - lo : ℕ) : ℝ) / L)) 0 = ((hi - lo : ℕ) : ℝ) / L := by
    rw [sub_sub_cancel]
    exact max_eq_left (by positivity)
  rwa [hfrac] at harea

namespace AdmissibleGeometry

variable {c β : ℝ} {N q : ℕ}

/-- **Single-sweep terminal-landing data** for a geometry. -/
structure TerminalLanding (G : AdmissibleGeometry c β N q) where
  e : ActualFamily G.xs G.T
  g : ActualFamily G.xs G.T
  x0 : ℕ
  exceptions_subset : G.exceptions ⊆ {e, g}
  core_const : ∀ F ∈ G.core, ∀ t, F.start < t → t ≤ F.owner → G.x t = x0
  newer_const : ∀ t, g.start < t → t ≤ g.owner → G.x t = x0
  root_const : ∀ j < G.d, G.x (columnFirst G.t (G.d * G.b) j) = x0
  older_mono : MonotoneOn G.x (Set.Ioc e.start e.owner)
  core_terminal : ∀ F ∈ G.core, ∀ t, e.start < t → t ≤ e.owner → ¬ (F.owner < t ∧ t ≤ F.stop)
  newer_terminal : ∀ t, e.start < t → t ≤ e.owner → ¬ (g.owner < t ∧ t ≤ g.stop)

variable {G : AdmissibleGeometry c β N q} (D : G.TerminalLanding)
variable {K : Finset (ActualFamily G.xs G.T)} (hK : K ⊆ G.core) (hc : HasSpanColoring K 2)

theorem mem_of_retainedCore {M ρ : ℕ} {F : ActualFamily G.xs G.T}
    (hF : F ∈ retainedCore K M ρ) : F ∈ K := by
  obtain ⟨p, _, rfl⟩ := mem_image.mp hF
  exact p.property

include hK in
/-- Every raw value at a column root is the constant or the raw value of a landing. -/
theorem TerminalLanding.raw_values {M ρ : ℕ} (hM : 2 ≤ M) (hρ : ρ < M) {j : ℕ} (hj : j < G.d)
    {z : ℕ} (hz : z ∈ rawBankValues (exactSourceBank (ρ := ρ) hc hM G.exceptions) G.x
      (columnFirst G.t (G.d * G.b) j)) :
    z = D.x0 ∨ ∃ v ∈ landingSet K M ρ D.g D.e (columnFirst G.t (G.d * G.b) j),
      z = G.x (D.e.shadow v) := by
  set s := columnFirst G.t (G.d * G.b) j
  obtain ⟨o, ho, rfl⟩ := mem_image.mp hz
  have ho' : o ∈ shadowOrbit ((retainedCore K M ρ ∪ {D.g}) ∪ {D.e}) s := by
    have h := (exactSourceBank_exact hc hM hρ G.exceptions s).subset ho
    refine shadowOrbit_mono ?_ s h
    intro F hF
    rcases mem_union.mp hF with hF | hF
    · exact mem_union_left _ (mem_union_left _ hF)
    · rcases mem_insert.mp (D.exceptions_subset hF) with rfl | hF
      · exact mem_union_right _ (mem_singleton_self _)
      · rw [mem_singleton.mp hF]; exact mem_union_left _ (mem_union_right _ (mem_singleton_self _))
  have hterm : ∀ F ∈ retainedCore K M ρ ∪ {D.g}, ∀ t, D.e.start < t → t ≤ D.e.owner →
      F.shadow t = t := by
    intro F hF t ht1 ht2
    by_contra hne
    have hact := (F.shadow_ne_self_iff t).mp hne
    rcases mem_union.mp hF with hF | hF
    · exact D.core_terminal F (hK (mem_of_retainedCore hF)) t ht1 ht2 hact
    · rw [mem_singleton.mp hF] at hact
      exact D.newer_terminal t ht1 ht2 hact
  rcases shadowOrbit_insert_terminal _ D.e s hterm o ho' with ho | ⟨u, hu, heu, rfl⟩
  · left
    rcases shadowOrbit_root_or_lower o ho with rfl | ⟨F, hF, h1, h2⟩
    · exact D.root_const j hj
    · rcases mem_union.mp hF with hF | hF
      · exact D.core_const F (hK (mem_of_retainedCore hF)) o h1 h2
      · rw [mem_singleton.mp hF] at h1 h2
        exact D.newer_const o h1 h2
  · right
    refine ⟨u, mem_filter.mpr ⟨shadowOrbit_newer_subset hc hρ D.g s hu, ?_⟩, rfl⟩
    exact (D.e.shadow_ne_self_iff u).mp heu

theorem columnFirst_lt (G : AdmissibleGeometry c β N q) {j : ℕ} (hj : j < G.d) :
    columnFirst G.t (G.d * G.b) j < G.T := by
  have := G.append_lt _ ((column_indices G.hd G.hb hj).1.trans_lt (column_indices G.hd G.hb hj).2)
  simpa only [columnFirst] using this

theorem rawBankValues_subset_range {M ρ : ℕ} (hM : 2 ≤ M) (hρ : ρ < M) {j : ℕ} (hj : j < G.d) :
    rawBankValues (exactSourceBank (ρ := ρ) hc hM G.exceptions) G.x
      (columnFirst G.t (G.d * G.b) j) ⊆ range (G.d * G.d * G.b) := by
  intro a ha
  obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
  apply mem_range.mpr
  apply G.raw_range
  have hu' := shadowOrbit_le ((exactSourceBank_exact hc hM hρ G.exceptions _).subset hu)
  have := columnFirst_lt G hj
  omega

include hK in
/-- **Finite bound for a step.** A raw interval spanned by a core step of the
selected core between landing times contains at most `1 + 11 (2M + 4)` raw
values; hence it bounds the point area at this selection and phase. -/
theorem TerminalLanding.gap_of_step {M ρ : ℕ} (hM : 2 ≤ M) (hρ : ρ < M) {j : ℕ} (hj : j < G.d)
    (b : CoreFamily K) {u : ℕ} (hbu : b.val.shadow u ≠ u)
    (hu : D.e.owner < u ∧ u ≤ D.e.stop) (ha : D.e.owner < b.val.shadow u ∧ b.val.shadow u ≤ D.e.stop)
    (huT : u < G.T) :
    (((G.x (D.e.shadow (b.val.shadow u)) - G.x (D.e.shadow u) : ℕ) : ℝ) / G.inputLength) ^ 2 /
        (2 * (((1 + (2 * M + 4) * 11 : ℕ) : ℝ) + 2)) ≤
      phaseGapArea hc hM G.exceptions G.x G.t G.d G.b ρ j := by
  set s := columnFirst G.t (G.d * G.b) j
  set S := rawBankValues (exactSourceBank (ρ := ρ) hc hM G.exceptions) G.x s
  have hbnd := b.val.shadow_active_bounds ((b.val.shadow_ne_self_iff u).mp hbu)
  set a := b.val.shadow u
  have hau : a ≤ u := b.val.shadowAction.apply_le u
  have hanti := raw_landing_antitone D.e G.x D.older_mono ha hu hau
  have hlo : G.x (D.e.shadow u) ≤ G.x (D.e.shadow a) := hanti
  have hhi : G.x (D.e.shadow a) ≤ G.d * G.d * G.b := by
    have hle : D.e.shadow a ≤ G.T - 1 := by
      have := D.e.shadowAction.apply_le a
      change D.e.shadow a ≤ a at this
      omega
    exact (G.raw_range _ hle).le
  have hsparse : (S.filter (fun z => G.x (D.e.shadow u) < z ∧ z < G.x (D.e.shadow a))).card ≤
      1 + (2 * M + 4) * 11 := by
    have hsub : S.filter (fun z => G.x (D.e.shadow u) < z ∧ z < G.x (D.e.shadow a)) ⊆
        insert D.x0 (((newerClosure K M ρ D.g s).filter (· ∈ Set.Ioo a u)).image
          (fun v => G.x (D.e.shadow v))) := by
      intro z hz
      obtain ⟨hzS, hz1, hz2⟩ := mem_filter.mp hz
      rcases D.raw_values hK hc hM hρ hj hzS with rfl | ⟨v, hv, rfl⟩
      · exact mem_insert_self _ _
      · apply mem_insert_of_mem
        have hvact := (mem_filter.mp hv).2
        have hav : a < v := by
          by_contra hle
          push Not at hle
          have := raw_landing_antitone D.e G.x D.older_mono hvact ha hle
          omega
        have hvu : v < u := by
          by_contra hle
          push Not at hle
          have := raw_landing_antitone D.e G.x D.older_mono hu hvact hle
          omega
        exact mem_image_of_mem _ (mem_filter.mpr ⟨(mem_filter.mp hv).1, hav, hvu⟩)
    refine (card_le_card hsub).trans ((card_insert_le _ _).trans ?_)
    have := (card_image_le (s := (newerClosure K M ρ D.g s).filter (· ∈ Set.Ioo a u))
      (f := fun v => G.x (D.e.shadow v))).trans
      (newerClosure_count_span hc hρ D.g s b hbnd.1 hbnd.2.2.2)
    omega
  rw [phaseGapArea_eq hc hM hρ G.exceptions G.x G.t G.d G.b j]
  have h := pointArea_ge_of_sparse (Nat.mul_pos (Nat.mul_pos G.hd G.hd) G.hb)
    ⟨_, exactSourceBank_raw_root hc hM hρ G.exceptions G.x s⟩
    (rawBankValues_subset_range hc hM hρ hj) hlo hhi hsparse
  simpa only [inputLength, Nat.cast_mul] using h

include hK in
/-- **Finite bound from the starts.** All raw values lie in `1 + 5 (2M + 4)`
intervals of total length at most `5 (2M + 4) (M + 1)` times the largest step jump. -/
theorem TerminalLanding.gap_of_starts {M ρ : ℕ} (hM : 2 ≤ M) (hρ : ρ < M) {j : ℕ} (hj : j < G.d) :
    max (1 - (((5 * (2 * M + 4) * ((M + 1) *
        stepMax K M ρ D.g D.e G.x (columnFirst G.t (G.d * G.b) j)) : ℕ) : ℝ) / G.inputLength)) 0 ^ 2 /
        (2 * ((1 + 5 * (2 * M + 4) : ℕ) : ℝ)) ≤
      phaseGapArea hc hM G.exceptions G.x G.t G.d G.b ρ j := by
  set s := columnFirst G.t (G.d * G.b) j
  set Γ := stepMax K M ρ D.g D.e G.x s
  set St := landingStarts K M ρ D.g D.e s
  have hL : 0 < G.d * G.d * G.b := Nat.mul_pos (Nat.mul_pos G.hd G.hd) G.hb
  let I : Finset (Option ℕ) := insert none (St.image some)
  let loF : Option ℕ → ℕ := fun a => match a with
    | none => D.x0 | some r => G.x (D.e.shadow r)
  let hiF : Option ℕ → ℕ := fun a => match a with
    | none => D.x0 | some r => G.x (D.e.shadow r) + (M + 1) * Γ
  have hcover : ∀ z ∈ rawBankValues (exactSourceBank (ρ := ρ) hc hM G.exceptions) G.x s,
      ∃ a ∈ I, loF a ≤ z ∧ z ≤ hiF a := by
    intro z hz
    rcases D.raw_values hK hc hM hρ hj hz with rfl | ⟨v, hv, rfl⟩
    · exact ⟨none, mem_insert_self _ _, le_rfl, le_rfl⟩
    · obtain ⟨r, hr, h1, h2⟩ := landing_cover hc hρ D.g D.e G.x D.older_mono s v hv
      exact ⟨some r, mem_insert_of_mem (mem_image_of_mem _ hr), h1, h2⟩
  have hlen : (∑ a ∈ I, ((hiF a - loF a : ℕ) : ℝ)) ≤
      (((5 * (2 * M + 4) * ((M + 1) * Γ) : ℕ) : ℝ) / (G.d * G.d * G.b : ℕ)) *
        (G.d * G.d * G.b : ℕ) := by
    have hLR : (0 : ℝ) < (G.d * G.d * G.b : ℕ) := by exact_mod_cast hL
    rw [div_mul_cancel₀ _ hLR.ne']
    have hnone : (none : Option ℕ) ∉ St.image some := by simp
    rw [sum_insert hnone, sum_image (fun _ _ _ _ h => Option.some_inj.mp h)]
    simp only [hiF, loF, Nat.sub_self, Nat.cast_zero, zero_add, Nat.add_sub_cancel_left]
    rw [sum_const, nsmul_eq_mul]
    have hSt : (St.card : ℝ) ≤ 5 * (2 * M + 4) := by
      exact_mod_cast landingStarts_card hc hρ D.g D.e s
    push_cast
    have : (0 : ℝ) ≤ (M + 1) * Γ := by positivity
    nlinarith
  have hcard : (I.card : ℝ) ≤ ((1 + 5 * (2 * M + 4) : ℕ) : ℝ) := by
    have : I.card ≤ 1 + 5 * (2 * M + 4) := by
      refine (card_insert_le _ _).trans ?_
      have := (card_image_le (s := St) (f := some)).trans (landingStarts_card hc hρ D.g D.e s)
      omega
    exact_mod_cast this
  rw [phaseGapArea_eq hc hM hρ G.exceptions G.x G.t G.d G.b j]
  have h := IntervalGapArea.point_area_lower_of_budgets hL
    ⟨_, exactSourceBank_raw_root hc hM hρ G.exceptions G.x s⟩
    (rawBankValues_subset_range hc hM hρ hj) I loF hiF hcover hlen hcard
  simpa only [inputLength, Nat.cast_mul] using h

end AdmissibleGeometry

end
end SourceCovers
