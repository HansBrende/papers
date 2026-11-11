import SwapRigidity.Line
import SharedDecoders.CapacityRetentionAlgebra

/-! # Deterministic shared line rules on linear and affine sources

The literal zero-padded view, truncated shift, and boundary view identity
are reused from `SwapRigidity.Line`. The coordinate-chain argument is
stated for its homogeneous constraint space, so its use does not require
a linear representative of the decoder.
-/

namespace SharedDecoders

open Module SwapRigidity

abbrev LineMatrix (n : ℕ) (F : Type*) := Matrix (Fin n) (Fin n) F

variable {F : Type*} [Field F] {n : ℕ} {κ : Type*}

/-- One arbitrary total function per class, on the actual infinite
zero-padded line view. The source itself may be any set. -/
def IsDeterministicLineCode (cls : Fin n → κ) (C : Set (LineMatrix n F)) : Prop :=
  ∃ dec : κ → (Fin n → ℤ → F) → (Fin n → F),
    ∀ X ∈ C, ∀ c : Fin n, X c = dec (cls c) (lineView (c.val : ℤ) X)

def lineFirstColumn : LineMatrix n F →ₗ[F] (Fin n → F) where
  toFun X i := X i ⟨0, i.pos⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Zero boundary and successive-row shift equations within each interval. -/
def lineChainSpace (S : Finset (Fin n)) : Submodule F (LineMatrix n F) where
  carrier := {X | lineFirstColumn X = 0 ∧ ∀ c c' : Fin n,
    c'.val = c.val + 1 → c' ∉ S → X c' = truncShift X c}
  zero_mem' := by
    constructor
    · rfl
    · intro c c' _ _
      rw [map_zero]
      rfl
  add_mem' := by
    intro X Y hX hY
    constructor
    · rw [map_add, hX.1, hY.1, add_zero]
    · intro c c' hcc' hc'
      change X c' + Y c' = (truncShift (X+Y)) c
      rw [map_add]
      exact congrArg₂ (· + ·) (hX.2 c c' hcc' hc') (hY.2 c c' hcc' hc')
  smul_mem' := by
    intro a X hX
    constructor
    · rw [map_smul, hX.1, smul_zero]
    · intro c c' hcc' hc'
      change a • X c' = (truncShift (a • X)) c
      rw [map_smul]
      exact congrArg (a • ·) (hX.2 c c' hcc' hc')

/-- Restriction to the surviving entries of interval-first rows is injective;
the zero boundary removes at least one coordinate for each matrix row. -/
theorem lineChainSpace_finrank_add_le (S : Finset (Fin n))
    (hS0 : ∀ c : Fin n, c.val = 0 → c ∈ S) :
    finrank F (lineChainSpace (F := F) S) + n ≤ n * S.card := by
  classical
  -- `Q`: the entries `(c, r)` of the first row `c` of a band whose anti-diagonal reaches
  -- column `0` inside the band
  let Q : Finset (Fin n × Fin n) := (S ×ˢ Finset.univ).filter fun p =>
    p.1.val + p.2.val < n ∧ ∀ k : Fin n, p.1 < k → k.val ≤ p.1.val + p.2.val → k ∉ S
  -- `P`: the remaining entries of the first rows of the bands
  let P : Finset (Fin n × Fin n) := (S ×ˢ Finset.univ) \ Q
  -- every row lies in exactly one band, so `Q` has at least `n` elements
  have hex : ∀ x : ℕ, ∀ hx : x < n,
      ∃ c ∈ S, c.val ≤ x ∧ ∀ k : Fin n, c < k → k.val ≤ x → k ∉ S := by
    intro x
    induction x with
    | zero =>
      intro hx
      refine ⟨⟨0, hx⟩, hS0 _ rfl, le_rfl, fun k hk hk' => ?_⟩
      rw [Fin.lt_def] at hk
      simp only at hk
      omega
    | succ x ih =>
      intro hx
      by_cases hmem : (⟨x + 1, hx⟩ : Fin n) ∈ S
      · refine ⟨⟨x + 1, hx⟩, hmem, le_rfl, fun k hk hk' => ?_⟩
        rw [Fin.lt_def] at hk
        simp only at hk
        omega
      · obtain ⟨c, hc, hcx, hck⟩ := ih (by omega)
        refine ⟨c, hc, by omega, fun k hk hk' => ?_⟩
        by_cases hkx : k.val ≤ x
        · exact hck k hk hkx
        · have hk1 : k = ⟨x + 1, hx⟩ := Fin.ext (by simp only; omega)
          rw [hk1]
          exact hmem
  have hQcard : n ≤ Q.card := by
    have hsurj : Set.SurjOn (fun p : Fin n × Fin n => p.1.val + p.2.val) Q
        (Finset.range n : Finset ℕ) := by
      intro x hx
      have hx : x < n := Finset.mem_range.mp hx
      obtain ⟨c, hc, hcx, hck⟩ := hex x hx
      have hsum : c.val + (x - c.val) = x := by omega
      refine ⟨(c, ⟨x - c.val, by omega⟩), ?_, hsum⟩
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hc, Finset.mem_univ _⟩, by simp only; omega,
        fun k hk hk' => hck k hk (by simp only at hk'; omega)⟩
    have hle := Finset.card_le_card_of_surjOn _ hsurj
    rwa [Finset.card_range] at hle
  have hPcard : P.card + n ≤ n * S.card := by
    have hsub : Q ⊆ S ×ˢ Finset.univ := Finset.filter_subset _ _
    have hadd : P.card + Q.card = (S ×ˢ (Finset.univ : Finset (Fin n))).card :=
      Finset.card_sdiff_add_card_eq_card hsub
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm] at hadd
    omega
  let Ψ : lineChainSpace (F := F) S →ₗ[F] (P → F) :=
    { toFun := fun X p => (X : LineMatrix n F) p.val.1 p.val.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro X hΨ
    have hcol : ∀ i j : Fin n, j.val = 0 → (X : LineMatrix n F) i j = 0 := by
      intro i j hj
      have h1 : (X : LineMatrix n F) i ⟨0, i.pos⟩ = 0 := congrFun X.property.1 i
      rwa [show (⟨0, i.pos⟩ : Fin n) = j from Fin.ext hj.symm] at h1
    have hP : ∀ p ∈ P, (X : LineMatrix n F) p.1 p.2 = 0 := fun p hp =>
      congrFun hΨ ⟨p, hp⟩
    have hA : ∀ c c' : Fin n, c'.val = c.val + 1 → c' ∉ S → ∀ r : Fin n,
        (X : LineMatrix n F) c' r =
          if hr : r.val + 1 < n then (X : LineMatrix n F) c ⟨r.val + 1, hr⟩ else 0 :=
      fun c c' hcc' hc' r => congrFun (X.property.2 c c' hcc' hc') r
    -- the entries in `Q` vanish: walk down the anti-diagonal to column `0`
    have hB : ∀ t : ℕ, ∀ c r : Fin n, r.val = t → c.val + t < n →
        (∀ k : Fin n, c < k → k.val ≤ c.val + t → k ∉ S) →
        (X : LineMatrix n F) c r = 0 := by
      intro t
      induction t with
      | zero => exact fun c r hr _ _ => hcol c r hr
      | succ t ih =>
        intro c r hr hlt hk
        have hc'lt : c.val + 1 < n := by omega
        have hc'S : (⟨c.val + 1, hc'lt⟩ : Fin n) ∉ S :=
          hk _ (by rw [Fin.lt_def]; simp only; omega) (by simp only; omega)
        have hrt : t < n := by omega
        have hstep := hA c ⟨c.val + 1, hc'lt⟩ rfl hc'S ⟨t, hrt⟩
        have ht1 : t + 1 < n := by omega
        rw [dite_eq_left ht1, show (⟨t + 1, ht1⟩ : Fin n) = r from Fin.ext hr.symm] at hstep
        rw [← hstep]
        refine ih ⟨c.val + 1, hc'lt⟩ ⟨t, hrt⟩ rfl (by simp only; omega) fun k hk1 hk2 => ?_
        rw [Fin.lt_def] at hk1
        simp only at hk1 hk2
        exact hk k (by rw [Fin.lt_def]; omega) (by omega)
    -- the first row of every band vanishes
    have hC : ∀ c ∈ S, ∀ r : Fin n, (X : LineMatrix n F) c r = 0 := by
      intro c hc r
      by_cases hq : (c, r) ∈ Q
      · obtain ⟨-, hlt, hk⟩ := Finset.mem_filter.mp hq
        exact hB r.val c r rfl hlt hk
      · exact hP (c, r) (Finset.mem_sdiff.mpr
          ⟨Finset.mem_product.mpr ⟨hc, Finset.mem_univ _⟩, hq⟩)
    -- every row vanishes
    have hD : ∀ t : ℕ, ∀ c : Fin n, c.val = t → (X : LineMatrix n F) c = 0 := by
      intro t
      induction t with
      | zero => exact fun c hc => funext (hC c (hS0 c hc))
      | succ t ih =>
        intro c hc
        by_cases hcS : c ∈ S
        · exact funext (hC c hcS)
        · have htn : t < n := by omega
          funext r
          rw [hA ⟨t, htn⟩ c hc hcS r]
          by_cases hr : r.val + 1 < n
          · rw [dite_eq_left hr, ih ⟨t, htn⟩ rfl]
            rfl
          · rw [dite_eq_right hr]
            rfl
    apply Subtype.ext
    funext c
    exact hD c.val c rfl
  have hdim : finrank F (lineChainSpace (F := F) S) ≤ P.card := by
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hle
  omega

/-- The actual threefold linear slice used by the line argument. -/
def lineOverlap (C : Submodule F (LineMatrix n F)) : Submodule F (LineMatrix n F) :=
  (C ⊓ C.comap truncShift) ⊓ LinearMap.ker lineFirstColumn

theorem lineOverlap_dimension (C : Submodule F (LineMatrix n F)) :
    2 * finrank F C ≤ n^2 + n + finrank F (lineOverlap C) := by
  let C' := C ⊓ C.comap truncShift
  have hpre : finrank F C ≤ finrank F (C.comap (truncShift (F := F))) :=
    SwapRigidity.finrank_le_finrank_comap C truncShift
  have hinter := SwapRigidity.finrank_add_finrank_le_add_finrank_inf C (C.comap truncShift)
  rw [Module.finrank_matrix, Fintype.card_fin, finrank_self, mul_one] at hinter
  have hboundary := finrank_map_add_inf_ker C' lineFirstColumn
  have hmap := Submodule.finrank_le (C'.map lineFirstColumn)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hmap
  change finrank F (C'.map lineFirstColumn) + finrank F (lineOverlap C) = finrank F C' at hboundary
  change finrank F C + finrank F (C.comap truncShift) ≤ n*n + finrank F C' at hinter
  rw [pow_two]
  omega

/-- Decoder equality on identical actual line views gives covariance; no
subtraction or linearity of the decoder is used. -/
theorem IsDeterministicLineCode.row_succ_eq {cls : Fin n → κ} {C : Set (LineMatrix n F)}
    (h : IsDeterministicLineCode cls C) {X : LineMatrix n F} (hX : X ∈ C)
    (hTX : truncShift X ∈ C) (h0 : ∀ i j : Fin n, j.val = 0 → X i j = 0)
    {c c' : Fin n} (hcc' : c'.val = c.val + 1) (hcls : cls c = cls c') :
    X c' = truncShift X c := by
  obtain ⟨dec, hdec⟩ := h
  calc X c' = dec (cls c') (lineView (c'.val : ℤ) X) := hdec X hX c'
    _ = dec (cls c) (lineView (c.val : ℤ) (truncShift X)) := by
        rw [lineView_truncShift h0, hcls, hcc']
    _ = truncShift X c := (hdec _ hTX c).symm

theorem IsDeterministicLineCode.overlap_le_chain {cls : Fin n → κ}
    {C : Submodule F (LineMatrix n F)} (h : IsDeterministicLineCode cls (C : Set (LineMatrix n F)))
    {S : Finset (Fin n)}
    (hS : ∀ c c' : Fin n, c'.val = c.val + 1 → c' ∉ S → cls c = cls c') :
    lineOverlap C ≤ lineChainSpace S := by
  intro X hX
  refine ⟨hX.2, ?_⟩
  intro c c' hcc' hc'
  apply h.row_succ_eq hX.1.1 hX.1.2 ?_ hcc' (hS c c' hcc' hc')
  intro i j hj
  have hh : X i ⟨0,i.pos⟩ = 0 := congrFun hX.2 i
  rwa [show (⟨0,i.pos⟩ : Fin n) = j from Fin.ext hj.symm] at hh

/-- Deterministic shared rules on a linear source satisfy the line TP bound.
`S` consists of interval starts; class labels may repeat across intervals. -/
theorem IsDeterministicLineCode.two_mul_finrank_le {cls : Fin n → κ}
    {C : Submodule F (LineMatrix n F)} (h : IsDeterministicLineCode cls (C : Set (LineMatrix n F)))
    {S : Finset (Fin n)} (hS0 : ∀ c : Fin n, c.val = 0 → c ∈ S)
    (hS : ∀ c c' : Fin n, c'.val = c.val + 1 → c' ∉ S → cls c = cls c') :
    2 * finrank F C ≤ n^2 + n*S.card := by
  have hlower := lineOverlap_dimension C
  have hupper := (Submodule.finrank_mono (h.overlap_le_chain hS))
  have hchain := lineChainSpace_finrank_add_le (F := F) S hS0
  omega

/-- An actual affine translate, specified by its basepoint and direction. -/
def lineAffineSource (a : LineMatrix n F) (V : Submodule F (LineMatrix n F)) :
    Set (LineMatrix n F) := {X | X-a ∈ V}

/-- Directions in the zero-boundary overlap satisfy the homogeneous chain
equations once an actual point of the affine threefold slice is supplied. -/
theorem IsDeterministicLineCode.affine_overlap_le_chain {cls : Fin n → κ}
    (a : LineMatrix n F) (V : Submodule F (LineMatrix n F))
    (h : IsDeterministicLineCode cls (lineAffineSource a V))
    (z : LineMatrix n F) (hz : z ∈ lineAffineSource a V)
    (hTz : truncShift z ∈ lineAffineSource a V) (hzero : lineFirstColumn z = 0)
    {S : Finset (Fin n)}
    (hS : ∀ c c' : Fin n, c'.val = c.val + 1 → c' ∉ S → cls c = cls c') :
    lineOverlap V ≤ lineChainSpace S := by
  intro v hv
  refine ⟨hv.2, ?_⟩
  have hzv : z+v ∈ lineAffineSource a V := by
    change z+v-a ∈ V
    have he : z+v-a = (z-a)+v := by abel
    rw [he]
    exact V.add_mem hz hv.1.1
  have hTzv : truncShift (z+v) ∈ lineAffineSource a V := by
    change truncShift (z+v)-a ∈ V
    rw [map_add]
    have he : truncShift z + truncShift v - a = (truncShift z-a)+truncShift v := by abel
    rw [he]
    exact V.add_mem hTz hv.1.2
  have hcol (X : LineMatrix n F) (hX : lineFirstColumn X = 0) :
      ∀ i j : Fin n, j.val = 0 → X i j = 0 := by
    intro i j hj
    have hh : X i ⟨0,i.pos⟩ = 0 := congrFun hX i
    rwa [show (⟨0,i.pos⟩ : Fin n) = j from Fin.ext hj.symm] at hh
  have hzvzero : lineFirstColumn (z+v) = 0 := by rw [map_add, hzero, hv.2, add_zero]
  intro c c' hcc' hc'
  have hbase := h.row_succ_eq hz hTz (hcol z hzero) hcc' (hS c c' hcc' hc')
  have hsum := h.row_succ_eq hzv hTzv (hcol (z+v) hzvzero) hcc' (hS c c' hcc' hc')
  rw [map_add] at hsum
  change z c' + v c' = truncShift z c + truncShift v c at hsum
  rw [hbase] at hsum
  exact add_left_cancel hsum

/-- Qualified affine line bound. Nonemptiness of `C ∩ T⁻¹C` alone is not
a premise here: the chosen point must also have zero first column. -/
theorem IsDeterministicLineCode.affine_two_mul_finrank_le {cls : Fin n → κ}
    (a : LineMatrix n F) (V : Submodule F (LineMatrix n F))
    (h : IsDeterministicLineCode cls (lineAffineSource a V))
    (hjoint : ∃ z, z ∈ lineAffineSource a V ∧ truncShift z ∈ lineAffineSource a V ∧
      lineFirstColumn z = 0)
    {S : Finset (Fin n)} (hS0 : ∀ c : Fin n, c.val = 0 → c ∈ S)
    (hS : ∀ c c' : Fin n, c'.val = c.val + 1 → c' ∉ S → cls c = cls c') :
    2 * finrank F V ≤ n^2 + n*S.card := by
  obtain ⟨z,hz,hTz,hzero⟩ := hjoint
  have hlower := lineOverlap_dimension V
  have hupper := Submodule.finrank_mono (h.affine_overlap_le_chain a V z hz hTz hzero hS)
  have hchain := lineChainSpace_finrank_add_le (F := F) S hS0
  omega

end SharedDecoders
