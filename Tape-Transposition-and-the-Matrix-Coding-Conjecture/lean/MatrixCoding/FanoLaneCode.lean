import MatrixCoding.FanoAttainment
import LeanMachine.DisjointSums
import Mathlib.Data.ZMod.Basic

/-!
# The three-lane code attaining the Fano bound

Each nonincident cell has one lane for each of its three mutual triangles.
The 28 checks have disjoint supports on the 147 scalar coordinates. Their
fibres therefore have size |A|^119 over any finite abelian group A, including
arbitrary prescribed triangle sums. Incident cells have three free lanes.
-/

namespace LeanBacklog.FanoLaneCode

open Finset FanoCertificate FanoFull FanoAttainment
open scoped BigOperators
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Every residual cell is in exactly three of the saved mutual triangles. -/
theorem through_card : ∀ v : Cell, Fintype.card {t : Fin 28 // v ∈ triangle t} = 3 := by
  decide

open scoped Classical
noncomputable section

abbrev Slot := Grid × Fin 3

/-- Choose a fixed labelling of the three triangles through each residual cell. -/
def laneEquiv (v : Cell) : {t : Fin 28 // v ∈ triangle t} ≃ Fin 3 :=
  Fintype.equivOfCardEq (by simpa using through_card v)

/-- The scalar coordinate assigned to one triangle at one of its cells. -/
def slot (t : Fin 28) (v : triangle t) : Slot :=
  (embed v, laneEquiv v ⟨t, v.property⟩)

theorem slot_injective (t : Fin 28) : Function.Injective (slot t) := by
  intro v u h
  exact Subtype.ext (embed_injective (congrArg Prod.fst h))

private theorem slot_eq_triangle {t s : Fin 28} {v : triangle t} {u : triangle s}
    (h : slot t v = slot s u) : t = s := by
  have hcell : (v : Cell) = (u : Cell) := embed_injective (congrArg Prod.fst h)
  rcases v with ⟨v, hv⟩
  rcases u with ⟨u, hu⟩
  dsimp only at hcell
  subst u
  exact congrArg Subtype.val ((laneEquiv v).injective (congrArg Prod.snd h))

/-- One nonempty, disjoint sum for each of the 28 mutual triangles. -/
def checks : LeanMachine.DisjointSums Slot (Fin 28) where
  support t := univ.image (slot t)
  nonempty t := by
    have ht : (triangle t).Nonempty := card_pos.mp (by rw [triangle_card]; decide)
    obtain ⟨v, hv⟩ := ht
    exact ⟨slot t ⟨v, hv⟩, mem_image.mpr ⟨⟨v, hv⟩, mem_univ _, rfl⟩⟩
  disjoint := by
    intro t s hts
    apply disjoint_left.mpr
    intro q hq hq'
    obtain ⟨v, _, hv⟩ := mem_image.mp hq
    obtain ⟨u, _, hu⟩ := mem_image.mp hq'
    exact hts (slot_eq_triangle (hv.trans hu.symm))

theorem support_card (t : Fin 28) : (checks.support t).card = 3 := by
  simp only [checks, card_image_of_injective _ (slot_injective t), card_univ,
    Fintype.card_coe, triangle_card]

/-- No lane of an incident cell occurs in a check. -/
theorem support_nonincident (t : Fin 28) {q : Slot} (hq : q ∈ checks.support t) :
    ¬ incident q.1.1 q.1.2 := by
  obtain ⟨v, _, rfl⟩ := mem_image.mp hq
  exact cells_nonincident v

/-- Every lane of every nonincident cell occurs in a check. -/
theorem support_covers {p : Grid} (hp : ¬ incident p.1 p.2) (l : Fin 3) :
    ∃ t, (p, l) ∈ checks.support t := by
  obtain ⟨v, hv₁, hv₂⟩ := cells_complete p.1 p.2 hp
  have hv : embed v = p := Prod.ext hv₁ hv₂
  let t := (laneEquiv v).symm l
  refine ⟨t.1, mem_image.mpr ⟨⟨v, t.2⟩, mem_univ _, ?_⟩⟩
  apply Prod.ext hv
  exact (laneEquiv v).apply_symm_apply l

/-- All other scalar coordinates in a check lie in helper rows of the target. -/
theorem support_mutual (t : Fin 28) {q z : Slot}
    (hq : q ∈ checks.support t) (hz : z ∈ checks.support t) (hne : z ≠ q) :
    incident z.1.1 q.1.2 := by
  obtain ⟨v, _, rfl⟩ := mem_image.mp hq
  obtain ⟨u, _, rfl⟩ := mem_image.mp hz
  have huv : (u : Cell) ≠ (v : Cell) := by
    intro h
    exact hne (congrArg (slot t) (Subtype.ext h))
  have h := triangle_mutual t v v.2 u u.2 huv
  change incident (row u) (column v)
  simpa only [nbhd_eq_incidence, mem_filter, mem_univ, true_and] using h

variable {A : Type*} [AddCommGroup A] [Fintype A]

omit [AddCommGroup A] in
theorem alphabet_card : Fintype.card (Fin 3 → A) = Fintype.card A ^ 3 := by
  simp

/-- Arrays with one prescribed sum per triangle. The zero syndrome is the
three-lane parity code of Theorem E. -/
def code (s : Fin 28 → A) : Finset (Grid → Fin 3 → A) :=
  (univ.filter fun x : Slot → A => checks.encode x = s).map
    (Equiv.curry Grid (Fin 3) A).toEmbedding

theorem mem_code_iff_encode (s : Fin 28 → A) (x : Grid → Fin 3 → A) :
    x ∈ code s ↔ checks.encode (Function.uncurry x) = s := by
  simp [code]

/-- Precisely the displayed triangle equations, with no additional restrictions. -/
theorem mem_code_iff (s : Fin 28 → A) (x : Grid → Fin 3 → A) :
    x ∈ code s ↔ ∀ t, ∑ v : triangle t, x (embed v) (laneEquiv v ⟨t, v.2⟩) = s t := by
  rw [mem_code_iff_encode, funext_iff]
  have he (t : Fin 28) : checks.encode (Function.uncurry x) t =
      ∑ v : triangle t, x (embed v) (laneEquiv v ⟨t, v.2⟩) := by
    rw [LeanMachine.DisjointSums.encode_apply]
    dsimp only [checks]
    rw [sum_image (slot_injective t).injOn]
    rfl
  simp only [he]

/-- All 147 lanes are present, with 28 independent checks: exactly 119 free
base-alphabet symbols. This reuses the disjoint-sums fibre count. -/
theorem code_card (s : Fin 28 → A) : (code s).card = Fintype.card A ^ 119 := by
  convert checks.fiber_card (A := A) s using 1
  · rw [code, card_map]
    congr 1
    ext x
    simp
  · norm_num [Slot, Grid]

/-- Every incident entry can be replaced by any three lane values. -/
theorem update_incident (s : Fin 28 → A) {x : Grid → Fin 3 → A}
    (hx : x ∈ code s) {p : Grid} (hp : incident p.1 p.2) (a : Fin 3 → A) :
    Function.update x p a ∈ code s := by
  rw [mem_code_iff_encode] at hx ⊢
  calc
    checks.encode (Function.uncurry (Function.update x p a)) =
        checks.encode (Function.uncurry x) := by
      ext t
      simp only [LeanMachine.DisjointSums.encode_apply]
      apply sum_congr rfl
      intro q hq
      have hne : q.1 ≠ p := by
        intro h
        exact support_nonincident t hq (h ▸ hp)
      simp [Function.uncurry, hne]
    _ = s := hx

/-- Whole-column recovery for the actual Fano helper map, over A cubed. -/
theorem isWholeRowCode (s : Fin 28 → A) :
    RowSpread.IsWholeRowCodeExcept rowRelation ∅ (code s) := by
  rw [RowSpread.wholeRowCode_iff]
  intro x hx z hz j _ hxz i
  by_cases hi : incident i j
  · exact hxz i (by simpa [rowRelation] using hi) j
  · funext l
    obtain ⟨t, ht⟩ := support_covers (p := (i, j)) hi l
    change Function.uncurry x ((i, j), l) = Function.uncurry z ((i, j), l)
    rw [checks.recover (Function.uncurry x) t ht, checks.recover (Function.uncurry z) t ht,
      (mem_code_iff_encode s x).mp hx, (mem_code_iff_encode s z).mp hz]
    congr 1
    apply sum_congr rfl
    intro q hq
    have hiq := support_mutual t ht (mem_erase.mp hq).2 (mem_erase.mp hq).1
    exact congrFun (hxz q.1.1 (by simpa [rowRelation] using hiq) q.1.2) q.2

/-- Exact attainment in the alphabet-normalized units of Theorem E. -/
theorem log_card (s : Fin 28 → A) :
    Real.log (code s).card = (119 / 3 : ℝ) * Real.log (Fintype.card (Fin 3 → A)) := by
  simp only [code_card, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow]
  ring

/-- The existing full Fano upper bound makes this code optimal among all
whole-row codes over the same cube alphabet, including nonlinear codes. -/
theorem optimal (s : Fin 28 → A) (C : Finset (Grid → Fin 3 → A))
    (hC : RowSpread.IsWholeRowCodeExcept rowRelation ∅ C) : C.card ≤ (code s).card := by
  rw [code_card]
  apply (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 3 ≠ 0)).mp
  have h := wholeRow_card_cube C hC
  simpa only [alphabet_card, ← pow_mul, Nat.reduceMul] using h

/-- Theorem E's existence clause for every positive integer alphabet size.
No field is needed: the base group is ZMod q. -/
theorem exists_code_for_cardinality (q : ℕ) (hq : 0 < q) :
    ∃ C : Finset (Grid → Fin 3 → ZMod q),
      RowSpread.IsWholeRowCodeExcept rowRelation ∅ C ∧ C.card = q ^ 119 := by
  have : NeZero q := ⟨Nat.ne_of_gt hq⟩
  refine ⟨code (0 : Fin 28 → ZMod q), isWholeRowCode _, ?_⟩
  simp only [code_card, ZMod.card]

end
end LeanBacklog.FanoLaneCode
