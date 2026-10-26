import BoundedNesting.ClockCost
import BoundedNesting.OneWalk

/-!
# Families of hops (Lemma "Structure of families")

Let `xs h`, `h < k`, be walks, `H'` a set of their long hops `(h, p, u)` (`IsHop`), and `own` an
assignment of owners strictly inside the hops. The *side* of a hop is upper if the walk steps up
after its start (`side`); seen from its side (`sw`, the walk reflected for the lower side) a hop
lies strictly above its cell (`sw_above`). The *family* of a key `(h, σ, o)` is the set of hops of
head `h` on side `σ` with owner `o` (`fam`). Its span `[P, U]` is its outermost hop, its height
`d` is the height of its owner above the cell of the span, and its depth is the number of families
of `(h, σ)` whose span contains its span. With owner-load at most `ℓ` (`hload`), the depth is at
most `ℓ` (`famDepth_le`), and `(h, σ, depth)` is coded as one of `2kℓ` virtual heads.

`famData_valid`: these data satisfy the hypotheses `Fam.Valid` of the family clock.
-/

namespace BoundedNesting

open Finset

/-! ### Walks -/

theorem IsWalk.neg {x : ℕ → ℤ} (hx : IsWalk x) : IsWalk (fun t => -x t) := by
  intro t
  have := hx t
  rw [show -x (t + 1) - -x t = -(x (t + 1) - x t) by ring, abs_neg]
  exact this

/-- A walk moves by at most one cell per step. -/
theorem IsWalk.lip {x : ℕ → ℤ} (hx : IsWalk x) {s t : ℕ} (h : s ≤ t) :
    x t - x s ≤ ((t - s : ℕ) : ℤ) ∧ x s - x t ≤ ((t - s : ℕ) : ℤ) := by
  have key : ∀ n, x (s + n) - x s ≤ n ∧ x s - x (s + n) ≤ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hx.step (s + n)
      rw [show s + (n + 1) = s + n + 1 by omega]
      push_cast
      omega
  have := key (t - s)
  rwa [show s + (t - s) = t by omega] at this

/-- A long hop whose first step goes up lies strictly above its cell. -/
theorem above_of_step {z : ℕ → ℤ} (hz : IsWalk z) {T p u : ℕ} (hh : IsHop z T p u)
    (hup : z p < z (p + 1)) : ∀ t, p < t → t < u → z p < z t := by
  intro t ht1 ht2
  by_contra hle
  push Not at hle
  have hne := hh.2.2.2 t (mem_Ioo.mpr ⟨ht1, ht2⟩)
  obtain ⟨s, hs1, hs2, hs3, -⟩ := exists_down_crossing hz (c := z p - 1) (t - (p + 1)) (p + 1)
    (by omega) (by rw [show p + 1 + (t - (p + 1)) = t by omega]; omega)
  exact hh.2.2.2 s (mem_Ioo.mpr ⟨by omega, by omega⟩) (by omega)

variable {k : ℕ}

/-- The side of a hop: upper (`true`) if the walk steps up after its start. -/
def side (xs : Fin k → ℕ → ℤ) (η : Fin k × ℕ × ℕ) : Bool :=
  decide (xs η.1 η.2.1 < xs η.1 (η.2.1 + 1))

/-- The walk of head `h` seen from the side `σ`: reflected for the lower side. -/
def sw (xs : Fin k → ℕ → ℤ) (h : Fin k) (σ : Bool) (t : ℕ) : ℤ := if σ then xs h t else -xs h t

theorem isWalk_sw {xs : Fin k → ℕ → ℤ} (hx : ∀ h, IsWalk (xs h)) (h : Fin k) (σ : Bool) :
    IsWalk (sw xs h σ) := by
  cases σ
  · exact (hx h).neg
  · exact hx h

theorem isHop_sw {xs : Fin k → ℕ → ℤ} {h : Fin k} {T p u : ℕ} (hh : IsHop (xs h) T p u)
    (σ : Bool) : IsHop (sw xs h σ) T p u := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  refine ⟨h1, h2, ?_, fun t ht => ?_⟩
  · cases σ <;> simp [sw, h3]
  · have := h4 t ht
    cases σ <;> simp [sw, this]

/-- Seen from its side, a hop lies strictly above its cell. -/
theorem sw_above {xs : Fin k → ℕ → ℤ} (hx : ∀ h, IsWalk (xs h)) {T : ℕ} {η : Fin k × ℕ × ℕ}
    (hh : IsHop (xs η.1) T η.2.1 η.2.2) :
    ∀ t, η.2.1 < t → t < η.2.2 → sw xs η.1 (side xs η) η.2.1 < sw xs η.1 (side xs η) t := by
  apply above_of_step (isWalk_sw hx _ _) (isHop_sw hh _)
  by_cases hs : xs η.1 η.2.1 < xs η.1 (η.2.1 + 1)
  · simp [sw, side, hs]
  · have hne := hh.2.2.2 (η.2.1 + 1) (mem_Ioo.mpr ⟨by omega, by have := hh.1; omega⟩)
    simp [sw, side, hs]
    omega

/-! ### Families -/

section Families

variable (xs : Fin k → ℕ → ℤ) (H' : Finset (Fin k × ℕ × ℕ)) (own : Fin k × ℕ × ℕ → ℕ)

/-- The key of a hop: its head, side and owner. -/
def key (η : Fin k × ℕ × ℕ) : Fin k × Bool × ℕ := (η.1, side xs η, own η)

/-- The keys of the families. -/
def keys : Finset (Fin k × Bool × ℕ) := H'.image (key xs own)

/-- The family of a key `(h, σ, o)`: the hops of head `h` on side `σ` with owner `o`. -/
def fam (q : Fin k × Bool × ℕ) : Finset (Fin k × ℕ × ℕ) := H'.filter (fun η => key xs own η = q)

/-- The families, as a type. -/
abbrev Keys := {q // q ∈ keys xs H' own}

theorem fam_nonempty (q : Keys xs H' own) : (fam xs H' own q.1).Nonempty := by
  obtain ⟨η, hη, he⟩ := mem_image.mp q.2
  exact ⟨η, mem_filter.mpr ⟨hη, he⟩⟩

/-- The start of the span of a family. -/
def famP (q : Keys xs H' own) : ℕ :=
  (fam xs H' own q.1).inf' (fam_nonempty xs H' own q) (fun η => η.2.1)

/-- The end of the span of a family. -/
def famU (q : Keys xs H' own) : ℕ := (fam xs H' own q.1).sup (fun η => η.2.2)

/-- The height of a family: that of its owner above the cell of its span, seen from its side. -/
def famd (q : Keys xs H' own) : ℕ :=
  (sw xs q.1.1 q.1.2.1 q.1.2.2 - sw xs q.1.1 q.1.2.1 (famP xs H' own q)).toNat

/-- The depth of a family: the families of its head and side whose span contains its span. -/
def famDepth (q : Keys xs H' own) : ℕ :=
  (univ.filter (fun q' : Keys xs H' own => q'.1.1 = q.1.1 ∧ q'.1.2.1 = q.1.2.1 ∧
    famP xs H' own q' ≤ famP xs H' own q ∧ famU xs H' own q ≤ famU xs H' own q')).card

/-- The code of the virtual head `(h, σ, depth)`. -/
def vcode (ℓ : ℕ) (q : Keys xs H' own) : ℕ :=
  (famDepth xs H' own q - 1) + ((q.1.1 : ℕ) * 2 + (if q.1.2.1 then 1 else 0)) * ℓ

/-- The family data of `H'`, with `2kℓ` virtual heads. -/
def famData (ℓ : ℕ) (hℓ : 0 < ℓ) : Fam (Keys xs H' own) (2 * k * ℓ) where
  vh q := ⟨vcode xs H' own ℓ q % (2 * k * ℓ),
    Nat.mod_lt _ (Nat.mul_pos (Nat.mul_pos two_pos q.1.1.pos) hℓ)⟩
  P := famP xs H' own
  U := famU xs H' own
  o q := q.1.2.2
  d := famd xs H' own
  H := univ.biUnion (fun q => (fam xs H' own q.1).image (fun η => (q, η.2.1, η.2.2)))

variable {xs H' own}

theorem mem_fam {q : Fin k × Bool × ℕ} {η : Fin k × ℕ × ℕ} :
    η ∈ fam xs H' own q ↔ η ∈ H' ∧ η.1 = q.1 ∧ side xs η = q.2.1 ∧ own η = q.2.2 := by
  simp only [fam, mem_filter, key, Prod.ext_iff]

theorem mem_famData_H {ℓ : ℕ} {hℓ : 0 < ℓ} {x : Keys xs H' own × ℕ × ℕ} :
    x ∈ (famData xs H' own ℓ hℓ).H ↔ ∃ η ∈ fam xs H' own x.1.1, η.2.1 = x.2.1 ∧ η.2.2 = x.2.2 := by
  simp only [famData, mem_biUnion, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨q, η, hη, rfl⟩
    exact ⟨η, hη, rfl, rfl⟩
  · rintro ⟨η, hη, h1, h2⟩
    exact ⟨x.1, η, hη, Prod.ext rfl (Prod.ext h1 h2)⟩

theorem fam_bounds {q : Keys xs H' own} {η : Fin k × ℕ × ℕ} (hη : η ∈ fam xs H' own q.1) :
    famP xs H' own q ≤ η.2.1 ∧ η.2.2 ≤ famU xs H' own q :=
  ⟨inf'_le _ hη, le_sup (f := fun η => η.2.2) hη⟩

variable {T : ℕ}

section Hyp

variable (hx : ∀ h, IsWalk (xs h)) (hH : ∀ η ∈ H', IsHop (xs η.1) T η.2.1 η.2.2)
  (hown : ∀ η ∈ H', η.2.1 < own η ∧ own η < η.2.2)

include hH in
theorem fam_hop {q : Fin k × Bool × ℕ} {η : Fin k × ℕ × ℕ} (hη : η ∈ fam xs H' own q) :
    IsHop (xs q.1) T η.2.1 η.2.2 := by
  obtain ⟨hηH, h1, -, -⟩ := mem_fam.mp hη
  have := hH η hηH
  rwa [h1] at this

include hx hH in
/-- Seen from its side, every hop of a family lies strictly above its cell. -/
theorem fam_up {q : Fin k × Bool × ℕ} {η : Fin k × ℕ × ℕ} (hη : η ∈ fam xs H' own q) :
    (∀ t, η.2.1 < t → t < η.2.2 → sw xs q.1 q.2.1 η.2.1 < sw xs q.1 q.2.1 t) ∧
      sw xs q.1 q.2.1 η.2.2 = sw xs q.1 q.2.1 η.2.1 := by
  obtain ⟨hηH, h1, h2, -⟩ := mem_fam.mp hη
  have := sw_above hx (hH η hηH)
  rw [h2, h1] at this
  exact ⟨this, (isHop_sw (fam_hop hH hη) q.2.1).2.2.1⟩

include hx hH hown in
/-- The hops of a family form a chain: the one that starts later ends earlier. -/
theorem fam_nested {q : Fin k × Bool × ℕ} {η η' : Fin k × ℕ × ℕ} (hη : η ∈ fam xs H' own q)
    (hη' : η' ∈ fam xs H' own q) (hle : η.2.1 ≤ η'.2.1) : η'.2.2 ≤ η.2.2 := by
  rcases eq_or_lt_of_le hle with he | hlt
  · have := hop_start_unique (fam_hop hH hη) (he ▸ fam_hop hH hη')
    omega
  · obtain ⟨hηH, -, -, ho⟩ := mem_fam.mp hη
    obtain ⟨hηH', -, -, ho'⟩ := mem_fam.mp hη'
    have h1 := hown η hηH
    have h2 := hown η' hηH'
    by_contra hgt
    push Not at hgt
    have u1 := fam_up hx hH hη
    have u2 := fam_up hx hH hη'
    have a1 := u1.1 η'.2.1 hlt (by omega)
    have a2 := u2.1 η.2.2 (by omega) hgt
    have := u1.2
    omega

include hx hH hown in
/-- The span of a family is one of its hops. -/
theorem fam_span (q : Keys xs H' own) :
    ∃ η₀ ∈ fam xs H' own q.1, η₀.2.1 = famP xs H' own q ∧ η₀.2.2 = famU xs H' own q := by
  obtain ⟨η₀, hη₀, he⟩ := exists_mem_eq_inf' (fam_nonempty xs H' own q) (fun η => η.2.1)
  refine ⟨η₀, hη₀, he.symm, le_antisymm (le_sup (f := fun η => η.2.2) hη₀) ?_⟩
  refine Finset.sup_le fun η hη => fam_nested hx hH hown hη₀ hη ?_
  rw [← he]
  exact inf'_le _ hη

include hx hH hown in
theorem famP_lt_famU (q : Keys xs H' own) : famP xs H' own q + 2 ≤ famU xs H' own q := by
  obtain ⟨η₀, hη₀, hP, hU⟩ := fam_span hx hH hown q
  have := (fam_hop hH hη₀).1
  omega

include hx hH hown in
/-- The owner of a family lies strictly inside its span, above the cell of the span. -/
theorem fam_owner (q : Keys xs H' own) :
    famP xs H' own q < q.1.2.2 ∧ q.1.2.2 < famU xs H' own q ∧
      sw xs q.1.1 q.1.2.1 (famP xs H' own q) < sw xs q.1.1 q.1.2.1 q.1.2.2 := by
  obtain ⟨η₀, hη₀, hP, hU⟩ := fam_span hx hH hown q
  obtain ⟨hηH, -, -, ho⟩ := mem_fam.mp hη₀
  have h1 := hown η₀ hηH
  have := (fam_up hx hH hη₀).1 q.1.2.2 (by omega) (by omega)
  rw [hP] at this
  exact ⟨by omega, by omega, this⟩

include hx hH hown in
/-- (a) Seen from its side, the cell of every hop of a family lies between the cell of its span,
included, and its owner, excluded. -/
theorem fam_cell_mem (q : Keys xs H' own) {η : Fin k × ℕ × ℕ} (hη : η ∈ fam xs H' own q.1) :
    sw xs q.1.1 q.1.2.1 (famP xs H' own q) ≤ sw xs q.1.1 q.1.2.1 η.2.1 ∧
      sw xs q.1.1 q.1.2.1 η.2.1 < sw xs q.1.1 q.1.2.1 q.1.2.2 := by
  obtain ⟨η₀, hη₀, hP, hU⟩ := fam_span hx hH hown q
  have hup₀ := fam_up hx hH hη₀
  obtain ⟨hηH, -, -, ho⟩ := mem_fam.mp hη
  have hb := fam_bounds hη
  have h1 := hown η hηH
  refine ⟨?_, (fam_up hx hH hη).1 q.1.2.2 (by omega) (by omega)⟩
  rcases eq_or_lt_of_le hb.1 with h | h
  · rw [h]
  · have := hup₀.1 η.2.1 (by omega) (by omega)
    rw [hP] at this
    exact this.le

include hx hH hown in
/-- (a) The hops of a family have distinct cells. -/
theorem fam_cell_injOn (q : Keys xs H' own) :
    Set.InjOn (fun η : Fin k × ℕ × ℕ => sw xs q.1.1 q.1.2.1 η.2.1)
      (↑(fam xs H' own q.1) : Set (Fin k × ℕ × ℕ)) := by
  intro η hη η' hη' he
  have hη := Finset.mem_coe.mp hη
  have hη' := Finset.mem_coe.mp hη'
  simp only at he
  obtain ⟨hηH, hh, -, ho⟩ := mem_fam.mp hη
  obtain ⟨hηH', hh', -, ho'⟩ := mem_fam.mp hη'
  have h1 := hown η hηH
  have h2 := hown η' hηH'
  rcases lt_trichotomy η.2.1 η'.2.1 with hlt | heq | hgt
  · have := fam_nested hx hH hown hη hη' hlt.le
    have := (fam_up hx hH hη).1 η'.2.1 hlt (by omega)
    omega
  · have hu := hop_start_unique (fam_hop hH hη) (heq ▸ fam_hop hH hη')
    exact Prod.ext (hh.trans hh'.symm) (Prod.ext heq hu)
  · have := fam_nested hx hH hown hη' hη hgt.le
    have := (fam_up hx hH hη').1 η.2.1 hgt (by omega)
    omega

include hx hH hown in
/-- (a) A family has at most `d` hops. -/
theorem card_fam_le (q : Keys xs H' own) : (fam xs H' own q.1).card ≤ famd xs H' own q := by
  unfold famd
  rw [← Int.card_Ico]
  refine card_le_card_of_injOn (fun η => sw xs q.1.1 q.1.2.1 η.2.1) (fun η hη => ?_)
    (fam_cell_injOn hx hH hown q)
  exact Finset.mem_coe.mpr (mem_Ico.mpr (fam_cell_mem hx hH hown q (Finset.mem_coe.mp hη)))

include hx hH hown in
/-- (a) A family spans at least twice its height. -/
theorem fam_long (q : Keys xs H' own) :
    famP xs H' own q + 2 * famd xs H' own q ≤ famU xs H' own q := by
  obtain ⟨η₀, hη₀, hP, hU⟩ := fam_span hx hH hown q
  have hup₀ := fam_up hx hH hη₀
  obtain ⟨ho1, ho2, ho3⟩ := fam_owner hx hH hown q
  have hw := isWalk_sw hx q.1.1 q.1.2.1
  have l1 := hw.lip (show famP xs H' own q ≤ q.1.2.2 by omega)
  have l2 := hw.lip (show q.1.2.2 ≤ famU xs H' own q by omega)
  have he : sw xs q.1.1 q.1.2.1 (famU xs H' own q) = sw xs q.1.1 q.1.2.1 (famP xs H' own q) := by
    rw [← hP, ← hU]; exact hup₀.2
  unfold famd
  have hnn : 0 ≤ sw xs q.1.1 q.1.2.1 q.1.2.2 - sw xs q.1.1 q.1.2.1 (famP xs H' own q) := by omega
  have := Int.toNat_of_nonneg hnn
  push_cast [Nat.cast_sub (show famP xs H' own q ≤ q.1.2.2 by omega),
    Nat.cast_sub (show q.1.2.2 ≤ famU xs H' own q by omega)] at l1 l2
  omega

theorem famDepth_pos (q : Keys xs H' own) : 1 ≤ famDepth xs H' own q :=
  card_pos.mpr ⟨q, mem_filter.mpr ⟨mem_univ _, rfl, rfl, le_rfl, le_rfl⟩⟩

include hx hH hown in
/-- (c) At owner-load at most `ℓ`, every family has depth at most `ℓ`: the families whose span
contains its span have distinct owners, all inside one time of its span. -/
theorem famDepth_le {ℓ : ℕ}
    (hload : ∀ (h : Fin k) (σ : Bool) (t : ℕ),
      ((H'.filter (fun η => η.1 = h ∧ side xs η = σ ∧ η.2.1 < t ∧ t < η.2.2)).image own).card ≤ ℓ)
    (q : Keys xs H' own) : famDepth xs H' own q ≤ ℓ := by
  have hPU := famP_lt_famU hx hH hown q
  calc famDepth xs H' own q
      ≤ ((H'.filter (fun η => η.1 = q.1.1 ∧ side xs η = q.1.2.1 ∧ η.2.1 < famP xs H' own q + 1 ∧
          famP xs H' own q + 1 < η.2.2)).image own).card := by
        refine card_le_card_of_injOn (fun q' => q'.1.2.2) (fun q' hq' => ?_)
          (fun q' hq' q'' hq'' he => ?_)
        · obtain ⟨-, h1, h2, h3, h4⟩ := mem_filter.mp (Finset.mem_coe.mp hq')
          obtain ⟨η, hη, hP, hU⟩ := fam_span hx hH hown q'
          obtain ⟨hηH, he1, he2, he3⟩ := mem_fam.mp hη
          exact Finset.mem_coe.mpr (mem_image.mpr ⟨η, mem_filter.mpr ⟨hηH, he1.trans h1,
            he2.trans h2, by omega, by omega⟩, he3⟩)
        · obtain ⟨-, h1, h2, -, -⟩ := mem_filter.mp (Finset.mem_coe.mp hq')
          obtain ⟨-, h1', h2', -, -⟩ := mem_filter.mp (Finset.mem_coe.mp hq'')
          exact Subtype.ext (Prod.ext (h1.trans h1'.symm) (Prod.ext (h2.trans h2'.symm) he))
    _ ≤ ℓ := hload _ _ _

include hx hH hown in
/-- (b) Distinct families of one head and side have distinct spans; indeed their spans start at
distinct times. -/
theorem famP_ne {q q' : Keys xs H' own} (hh : q.1.1 = q'.1.1) (hσ : q.1.2.1 = q'.1.2.1)
    (hne : q ≠ q') : famP xs H' own q ≠ famP xs H' own q' := by
  intro he
  obtain ⟨η₀, hη₀, hP₀, hU₀⟩ := fam_span hx hH hown q
  obtain ⟨η₀', hη₀', hP₀', hU₀'⟩ := fam_span hx hH hown q'
  have hop₀ := fam_hop hH hη₀
  have hop₀' := fam_hop hH hη₀'
  rw [← hh] at hop₀'
  have hu := hop_start_unique hop₀ (show IsHop (xs q.1.1) T η₀.2.1 η₀'.2.2 by
    rw [hP₀, he, ← hP₀']; exact hop₀')
  obtain ⟨-, k1, -, k3⟩ := mem_fam.mp hη₀
  obtain ⟨-, k1', -, k3'⟩ := mem_fam.mp hη₀'
  have heq : η₀ = η₀' := Prod.ext (k1.trans (hh.trans k1'.symm))
    (Prod.ext (by rw [hP₀, he, hP₀']) hu)
  apply hne
  apply Subtype.ext
  refine Prod.ext hh (Prod.ext hσ ?_)
  rw [← k3, ← k3', heq]

include hx hH hown in
/-- (b) The spans of the families of one head and side do not cross. -/
theorem fam_no_cross {q q' : Keys xs H' own} (hh : q.1.1 = q'.1.1) (hσ : q.1.2.1 = q'.1.2.1) :
    ¬ (famP xs H' own q < famP xs H' own q' ∧ famP xs H' own q' < famU xs H' own q ∧
      famU xs H' own q < famU xs H' own q') := by
  rintro ⟨h1, h2, h3⟩
  obtain ⟨η₀, hη₀, hP, hU⟩ := fam_span hx hH hown q
  obtain ⟨η₀', hη₀', hP', hU'⟩ := fam_span hx hH hown q'
  have u₀ := fam_up hx hH hη₀
  have u₀' := fam_up hx hH hη₀'
  rw [← hh, ← hσ] at u₀'
  have a1 := u₀.1 η₀'.2.1 (by omega) (by omega)
  have a2 := u₀'.1 η₀.2.2 (by omega) (by omega)
  have := u₀.2
  omega

/-- Distinct families of one head and side, of equal depth, with nested spans cannot exist:
the inner one would be deeper. -/
theorem famDepth_lt {q q' : Keys xs H' own} (hh : q.1.1 = q'.1.1) (hσ : q.1.2.1 = q'.1.2.1)
    (hP : famP xs H' own q < famP xs H' own q') (hU : famU xs H' own q' < famU xs H' own q) :
    famDepth xs H' own q < famDepth xs H' own q' := by
  unfold famDepth
  refine card_lt_card ⟨fun q'' hq'' => ?_, fun hsub => ?_⟩
  · obtain ⟨-, h1, h2, h3, h4⟩ := mem_filter.mp hq''
    exact mem_filter.mpr ⟨mem_univ _, h1.trans hh, h2.trans hσ, by omega, by omega⟩
  · have := mem_filter.mp (hsub (mem_filter.mpr ⟨mem_univ q', rfl, rfl, le_rfl, le_rfl⟩))
    omega

include hx hH hown in
/-- (d), one direction: if the span of `q` starts first, it ends before that of `q'` starts. -/
theorem disj_aux {q q' : Keys xs H' own} (hh : q.1.1 = q'.1.1) (hσ : q.1.2.1 = q'.1.2.1)
    (hd : famDepth xs H' own q = famDepth xs H' own q')
    (hlt : famP xs H' own q < famP xs H' own q') : famU xs H' own q ≤ famP xs H' own q' := by
  by_contra hgt
  push Not at hgt
  obtain ⟨η₀, hη₀, hP, hU⟩ := fam_span hx hH hown q
  obtain ⟨η₀', hη₀', hP', hU'⟩ := fam_span hx hH hown q'
  rcases lt_trichotomy (famU xs H' own q) (famU xs H' own q') with h | h | h
  · exact fam_no_cross hx hH hown hh hσ ⟨hlt, hgt, h⟩
  · have hop₀ := fam_hop hH hη₀
    have hop₀' := fam_hop hH hη₀'
    rw [← hh] at hop₀'
    have := hop_end_unique hop₀ (show IsHop (xs q.1.1) T η₀'.2.1 η₀.2.2 by
      rw [hU, h, ← hU']; exact hop₀')
    omega
  · have := famDepth_lt hh hσ hlt h
    omega

theorem vcode_lt {ℓ : ℕ} (q : Keys xs H' own) (hd : famDepth xs H' own q ≤ ℓ) :
    vcode xs H' own ℓ q < 2 * k * ℓ := by
  unfold vcode
  have h1 := famDepth_pos q
  have hb : (q.1.1 : ℕ) * 2 + (if q.1.2.1 then 1 else 0) + 1 ≤ 2 * k := by
    have := q.1.1.isLt
    split_ifs <;> omega
  have h2 := Nat.mul_le_mul_right ℓ hb
  rw [add_mul, one_mul] at h2
  omega

theorem code_inj {h h' : ℕ} {b b' : Bool}
    (e : h * 2 + (if b then 1 else 0) = h' * 2 + (if b' then 1 else 0)) : h = h' ∧ b = b' := by
  cases b <;> cases b' <;> simp at e ⊢ <;> omega

theorem vh_eq {ℓ : ℕ} {hℓ : 0 < ℓ} {q q' : Keys xs H' own} (hd : famDepth xs H' own q ≤ ℓ)
    (hd' : famDepth xs H' own q' ≤ ℓ)
    (hv : (famData xs H' own ℓ hℓ).vh q = (famData xs H' own ℓ hℓ).vh q') :
    q.1.1 = q'.1.1 ∧ q.1.2.1 = q'.1.2.1 ∧ famDepth xs H' own q = famDepth xs H' own q' := by
  have hv' : vcode xs H' own ℓ q = vcode xs H' own ℓ q' := by
    have := congrArg Fin.val hv
    simp only [famData] at this
    rwa [Nat.mod_eq_of_lt (vcode_lt q hd), Nat.mod_eq_of_lt (vcode_lt q' hd')] at this
  unfold vcode at hv'
  have hp := famDepth_pos q
  have hp' := famDepth_pos q'
  have hdiv := congrArg (· / ℓ) hv'
  have hmod := congrArg (· % ℓ) hv'
  rw [Nat.add_mul_div_right _ _ hℓ, Nat.add_mul_div_right _ _ hℓ,
    Nat.div_eq_of_lt (show famDepth xs H' own q - 1 < ℓ by omega),
    Nat.div_eq_of_lt (show famDepth xs H' own q' - 1 < ℓ by omega)] at hdiv
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (show famDepth xs H' own q - 1 < ℓ by omega),
    Nat.mod_eq_of_lt (show famDepth xs H' own q' - 1 < ℓ by omega)] at hmod
  rw [zero_add, zero_add] at hdiv
  obtain ⟨e1, e2⟩ := code_inj hdiv
  exact ⟨Fin.ext e1, e2, by omega⟩

include hx hH hown in
/-- (d) Two distinct families of one virtual head have disjoint spans. -/
theorem famData_disj {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hload : ∀ (h : Fin k) (σ : Bool) (t : ℕ),
      ((H'.filter (fun η => η.1 = h ∧ side xs η = σ ∧ η.2.1 < t ∧ t < η.2.2)).image own).card ≤ ℓ)
    {q q' : Keys xs H' own} (hne : q ≠ q')
    (hv : (famData xs H' own ℓ hℓ).vh q = (famData xs H' own ℓ hℓ).vh q') :
    famU xs H' own q ≤ famP xs H' own q' ∨ famU xs H' own q' ≤ famP xs H' own q := by
  obtain ⟨hh, hσ, hd⟩ := vh_eq (famDepth_le hx hH hown hload q) (famDepth_le hx hH hown hload q') hv
  have hP := famP_ne hx hH hown hh hσ hne
  rcases lt_or_gt_of_ne hP with h | h
  · exact Or.inl (disj_aux hx hH hown hh hσ hd h)
  · exact Or.inr (disj_aux hx hH hown hh.symm hσ.symm hd.symm h)

include hx hH hown in
/-- **Structure of families.** The family data satisfy the hypotheses of the family clock. -/
theorem famData_valid {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hload : ∀ (h : Fin k) (σ : Bool) (t : ℕ),
      ((H'.filter (fun η => η.1 = h ∧ side xs η = σ ∧ η.2.1 < t ∧ t < η.2.2)).image own).card ≤ ℓ) :
    (famData xs H' own ℓ hℓ).Valid T where
  hop_in := by
    intro x hx'
    obtain ⟨η, hη, h1, h2⟩ := mem_famData_H.mp hx'
    obtain ⟨hηH, -, -, ho⟩ := mem_fam.mp hη
    have hb := fam_bounds hη
    have hin := hown η hηH
    simp only [famData]
    rw [← h1, ← h2, ← ho]
    exact ⟨hb.1, hin.1, hin.2, hb.2⟩
  span_end := by
    intro x hx' hu
    obtain ⟨η, hη, h1, h2⟩ := mem_famData_H.mp hx'
    obtain ⟨η₀, hη₀, hP, hU⟩ := fam_span hx hH hown x.1
    simp only [famData] at hu ⊢
    have := hop_end_unique (fam_hop hH hη) (show IsHop (xs x.1.1.1) T η₀.2.1 η.2.2 by
      rw [h2, hu, ← hU]; exact fam_hop hH hη₀)
    omega
  disj := fun q q' hne hv => famData_disj hx hH hown hℓ hload hne hv
  card_le := by
    intro q
    calc ((famData xs H' own ℓ hℓ).H.filter (fun x => x.1 = q)).card
        ≤ ((fam xs H' own q.1).image (fun η => (q, η.2.1, η.2.2))).card := by
          refine card_le_card fun x hx' => ?_
          obtain ⟨hxH, hxq⟩ := mem_filter.mp hx'
          obtain ⟨η, hη, h1, h2⟩ := mem_famData_H.mp hxH
          rw [hxq] at hη
          exact mem_image.mpr ⟨η, hη, Prod.ext hxq.symm (Prod.ext h1 h2)⟩
      _ ≤ (fam xs H' own q.1).card := card_image_le
      _ ≤ famd xs H' own q := card_fam_le hx hH hown q
  d_pos := by
    intro q
    simp only [famData, famd]
    have := (fam_owner hx hH hown q).2.2
    omega
  long := fun q => fam_long hx hH hown q
  lt_T := by
    intro q
    obtain ⟨η₀, hη₀, -, hU⟩ := fam_span hx hH hown q
    simp only [famData]
    rw [← hU]
    exact (fam_hop hH hη₀).2.1

end Hyp

end Families

end BoundedNesting
