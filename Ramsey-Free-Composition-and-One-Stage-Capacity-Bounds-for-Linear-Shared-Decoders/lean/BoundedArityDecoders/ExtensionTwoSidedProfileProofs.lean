import BoundedArityDecoders.ExtensionTwoSidedProfile

/-!
# Proofs — Extension Result 3: Characteristic-Free Two-Sided Coarse–Fine Bound (`Problem 9.3`)

Complete kernel-verified proofs for all theorem specifications in
`BoundedArityDecoders.ExtensionTwoSidedProfile`:
* `extension_Theorem3_TwoSidedCoarseFine` (`Extension_Theorem3_TwoSidedCoarseFineSpec`)
* `extension_Theorem3_ConcreteWinOverTP` (`Extension_Theorem3_ConcreteWinOverTPSpec`)
* `swapCode_finrank_le_twoSidedCoarseFine`
* `swapCode_finrank_le_contiguousCoarseFine`
* `swapCode_oneSidedTP_le_contiguousCoarseFine`
-/

namespace BoundedArityDecoders

open Module Matrix
open scoped BigOperators

section Theorem3Proofs

private def zmodToFin {d : ℕ} [NeZero d] (x : ZMod d) : Fin d :=
  ⟨x.val, x.val_lt⟩

private def finToZMod {d : ℕ} (r : Fin d) : ZMod d :=
  (r.val : ZMod d)

private lemma zmodToFin_finToZMod {d : ℕ} [NeZero d] (r : Fin d) :
    zmodToFin (finToZMod r) = r :=
  Fin.ext (ZMod.val_cast_of_lt r.isLt)

private lemma finToZMod_zmodToFin {d : ℕ} [NeZero d] (x : ZMod d) :
    finToZMod (zmodToFin x) = x :=
  ZMod.natCast_zmod_val x

private def zmodEquivFin (d : ℕ) [NeZero d] : ZMod d ≃ Fin d where
  toFun := zmodToFin
  invFun := finToZMod
  left_inv := finToZMod_zmodToFin
  right_inv := zmodToFin_finToZMod

private lemma finToZMod_injective {d : ℕ} [NeZero d] :
    Function.Injective (finToZMod (d := d)) :=
  (zmodEquivFin d).symm.injective

private lemma mem_image_finToZMod {d : ℕ} [NeZero d] (S : Finset (Fin d)) (x : ZMod d) :
    x ∈ S.image finToZMod ↔ zmodToFin x ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨r, hr, rfl⟩
    rwa [zmodToFin_finToZMod]
  · intro hx
    exact ⟨zmodToFin x, hx, finToZMod_zmodToFin x⟩

private lemma zmodToFin_add_nat {d : ℕ} [NeZero d] (r : Fin d) (u : ℕ) :
    zmodToFin (finToZMod r + (u : ZMod d)) =
      ⟨(r.val + u) % d, Nat.mod_lt _ (NeZero.pos d)⟩ := by
  apply Fin.ext
  have hcast : finToZMod r + (u : ZMod d) = ((r.val + u : ℕ) : ZMod d) := by
    simp [finToZMod, Nat.cast_add]
  rw [hcast]
  exact ZMod.val_natCast (n := d) (r.val + u)

private lemma zmodToFin_add_one {d : ℕ} [NeZero d] (r : Fin d) :
    zmodToFin (finToZMod r + 1) =
      ⟨(r.val + 1) % d, Nat.mod_lt _ (NeZero.pos d)⟩ := by
  simpa using zmodToFin_add_nat r 1

private lemma card_endpoints_image_finToZMod {d : ℕ} [NeZero d] (S : Finset (Fin d)) :
    let S_Z := S.image finToZMod
    (S_Z.filter fun a : ZMod d => a + 1 ∉ S_Z).card = cyclicRunEndpointCount S := by
  intro S_Z
  have hfilter :
      (S_Z.filter fun a : ZMod d => a + 1 ∉ S_Z) =
        (S.filter fun r : Fin d =>
          (⟨(r.val + 1) % d, Nat.mod_lt _ (NeZero.pos d)⟩ : Fin d) ∉ S).image finToZMod := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_filter] at hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx.1
      rw [Finset.mem_image]
      refine ⟨r, Finset.mem_filter.mpr ⟨hr, ?_⟩, rfl⟩
      intro hsucc
      apply hx.2
      rw [← zmodToFin_add_one r] at hsucc
      exact (mem_image_finToZMod S (finToZMod r + 1)).mpr hsucc
    · intro hx
      obtain ⟨r, hr_filt, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hr, hnot⟩ := Finset.mem_filter.mp hr_filt
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image_of_mem finToZMod hr, ?_⟩
      intro hmem
      have hsucc : zmodToFin (finToZMod r + 1) ∈ S :=
        (mem_image_finToZMod S (finToZMod r + 1)).mp hmem
      rw [zmodToFin_add_one r] at hsucc
      exact hnot hsucc
  rw [hfilter, Finset.card_image_of_injective _ finToZMod_injective]
  rfl

private lemma cyclicRunEndpointCount_le_cyclicRunCount {d : ℕ} [NeZero d]
    (S : Finset (Fin d)) :
    cyclicRunEndpointCount S ≤ cyclicRunCount S := by
  dsimp only [cyclicRunCount]
  split_ifs with h
  · subst h
    simp [cyclicRunEndpointCount]
  · exact le_rfl

private lemma shift_val_eq_iff {d : ℕ} [NeZero d] (r c : ZMod d) (e : Fin d) :
    (zmodToFin c).val = ((zmodToFin r).val + e.val) % d ↔ c = r + finToZMod e := by
  constructor
  · intro hval
    have hval' : c.val = (r.val + e.val) % d := hval
    calc c = (c.val : ZMod d) := (ZMod.natCast_zmod_val c).symm
      _ = (((r.val + e.val) % d : ℕ) : ZMod d) := by rw [hval']
      _ = ((r.val + e.val : ℕ) : ZMod d) := ZMod.natCast_mod (r.val + e.val) d
      _ = (r.val : ZMod d) + (e.val : ZMod d) := Nat.cast_add r.val e.val
      _ = r + finToZMod e := by rw [ZMod.natCast_zmod_val]; rfl
  · rintro rfl
    show (r + finToZMod e).val = (r.val + e.val) % d
    rw [ZMod.val_add, show (finToZMod e).val = e.val from ZMod.val_cast_of_lt e.isLt]

/-- Unpack `HasCoarseFineIntervalDecomposition` into `ZMod d` coarse interval starts/lengths
together with diagonal shift-invariance along every interior step `u ↦ u + 1` (`u + 1 < len i`). -/
private lemma coarseFine_unpack {F : Type*} [Field F] {d : ℕ} [NeZero d] {α : Type*}
    {S : Finset (Fin d)} {c : ℕ} {M : α → Matrix (Fin d) (Fin d) F}
    (hM : HasCoarseFineIntervalDecomposition S c M) :
    let S_Z := S.image finToZMod
    ∃ (len : Fin c → ℕ) (start : Fin c → ZMod d),
      (∀ i : Fin c, 1 ≤ len i) ∧
      (∀ x : ZMod d, x ∉ S_Z →
        ∃ (i : Fin c) (u : ℕ), u < len i ∧ x = start i + (u : ZMod d)) ∧
      (∀ (i : Fin c) (u : ℕ), u < len i → start i + (u : ZMod d) ∉ S_Z) ∧
      (∀ (i : Fin c) (u : ℕ), u + 1 < len i →
        let a := start i + (u : ZMod d)
        ∀ (t : α) (a' : ZMod d),
          M t (zmodToFin (a + 1)) (zmodToFin (a' + 1)) =
            M t (zmodToFin a) (zmodToFin a')) := by
  intro S_Z
  obtain ⟨coarse, hInt, hDisj, hUnion, hSpan⟩ := hM
  let len : Fin c → ℕ := fun i => Classical.choose (hInt i)
  have hlen_spec : ∀ i : Fin c,
      1 ≤ len i ∧ len i ≤ d ∧ IsCyclicInterval (len i) (coarse i) :=
    fun i => Classical.choose_spec (hInt i)
  let startFin : Fin c → Fin d := fun i => Classical.choose (hlen_spec i).2.2
  have hstart_spec : ∀ i : Fin c,
      coarse i = (Finset.range (len i)).image (fun u =>
        ⟨((startFin i).val + u) % d, Nat.mod_lt _ (NeZero.pos d)⟩) :=
    fun i => Classical.choose_spec (hlen_spec i).2.2
  let start : Fin c → ZMod d := fun i => finToZMod (startFin i)
  have hmem_coarse : ∀ (i : Fin c) (u : ℕ), u < len i →
      zmodToFin (start i + (u : ZMod d)) ∈ coarse i := by
    intro i u hu
    rw [hstart_spec i, Finset.mem_image]
    exact ⟨u, Finset.mem_range.mpr hu, (zmodToFin_add_nat (startFin i) u).symm⟩
  have hcoarse_not_S : ∀ (i : Fin c) {r : Fin d}, r ∈ coarse i → r ∉ S := by
    intro i r hr
    have hbi : r ∈ Finset.univ.biUnion coarse :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hr⟩
    rw [hUnion, Finset.mem_sdiff] at hbi
    exact hbi.2
  refine ⟨len, start, fun i => (hlen_spec i).1, ?_, ?_, ?_⟩
  · intro x hx
    have hx_not_S : zmodToFin x ∉ S := fun h => hx ((mem_image_finToZMod S x).mpr h)
    have hx_sdiff : zmodToFin x ∈ Finset.univ \ S :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx_not_S⟩
    rw [← hUnion, Finset.mem_biUnion] at hx_sdiff
    obtain ⟨i, _, hxi⟩ := hx_sdiff
    rw [hstart_spec i, Finset.mem_image] at hxi
    obtain ⟨u, hu_range, hu_eq⟩ := hxi
    refine ⟨i, u, Finset.mem_range.mp hu_range, ?_⟩
    have hfin : zmodToFin (start i + (u : ZMod d)) = zmodToFin x := by
      rw [zmodToFin_add_nat (startFin i) u, hu_eq]
    calc x = finToZMod (zmodToFin x) := (finToZMod_zmodToFin x).symm
      _ = finToZMod (zmodToFin (start i + (u : ZMod d))) := by rw [← hfin]
      _ = start i + (u : ZMod d) := finToZMod_zmodToFin _
  · intro i u hu hx
    exact hcoarse_not_S i (hmem_coarse i u hu) ((mem_image_finToZMod S _).mp hx)
  · intro i u hu1 a t
    have ha_eq1 : a + 1 = start i + ((u + 1 : ℕ) : ZMod d) := by
      simp [a, Nat.cast_add, add_assoc]
    have ha_in : zmodToFin a ∈ coarse i := hmem_coarse i u (by omega)
    have ha1_in : zmodToFin (a + 1) ∈ coarse i := by
      rw [ha_eq1]
      exact hmem_coarse i (u + 1) hu1
    have ha_not_S : zmodToFin a ∉ S := hcoarse_not_S i ha_in
    have ha1_not_S : zmodToFin (a + 1) ∉ S := hcoarse_not_S i ha1_in
    let InvSub : Submodule F (Matrix (Fin d) (Fin d) F) :=
      { carrier := {W | ∀ a' : ZMod d,
          W (zmodToFin (a + 1)) (zmodToFin (a' + 1)) = W (zmodToFin a) (zmodToFin a')}
        add_mem' := fun {W₁ W₂} h₁ h₂ a' => by simp [h₁ a', h₂ a']
        zero_mem' := fun _ => rfl
        smul_mem' := fun c {W} hW a' => by simp [hW a'] }
    have hGen : ∀ (I : Finset (Fin d)) (e : Fin d),
        (zmodToFin (a + 1) ∈ I ↔ zmodToFin a ∈ I) →
        intervalMaskRotMatrix F I e ∈ InvSub := by
      intro I e hIiff a'
      simp only [intervalMaskRotMatrix, Matrix.of_apply, shift_val_eq_iff, hIiff]
      have hshift : (a' + 1 = a + 1 + finToZMod e) ↔ (a' = a + finToZMod e) := by
        rw [show a + 1 + finToZMod e = (a + finToZMod e) + 1 by abel]
        exact add_right_cancel_iff
      simp only [hshift]
    have hSpanLe :
        Submodule.span F
          ({X | ∃ (I : Finset (Fin d)) (_hI : I ⊆ S) (e : Fin d),
              X = intervalMaskRotMatrix F I e} ∪
           {X | ∃ (j : Fin c) (e : Fin d),
              X = intervalMaskRotMatrix F (coarse j) e} ∪
           {X | ∃ e : Fin d,
              X = intervalMaskRotMatrix F Finset.univ e}) ≤ InvSub := by
      rw [Submodule.span_le]
      rintro W ((⟨I, hIS, e, rfl⟩ | ⟨j, e, rfl⟩) | ⟨e, rfl⟩)
      · refine hGen I e ?_
        have h1 : zmodToFin (a + 1) ∉ I := fun h => ha1_not_S (hIS h)
        have h0 : zmodToFin a ∉ I := fun h => ha_not_S (hIS h)
        simp [h1, h0]
      · refine hGen (coarse j) e ?_
        by_cases hji : j = i
        · subst hji
          simp [ha1_in, ha_in]
        · have hdisj_ji : Disjoint (coarse j) (coarse i) := hDisj hji
          have h1 : zmodToFin (a + 1) ∉ coarse j :=
            Finset.disjoint_right.mp hdisj_ji ha1_in
          have h0 : zmodToFin a ∉ coarse j :=
            Finset.disjoint_right.mp hdisj_ji ha_in
          simp [h1, h0]
      · exact hGen Finset.univ e (by simp)
    exact hSpanLe (hSpan t)

private lemma two_mul_finrank_le_sup_add_inf_comap
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (W : Submodule F V) (f : V →ₗ[F] V) :
    2 * finrank F W ≤ finrank F ↥(W ⊔ W.comap f) + finrank F ↥(W ⊓ W.comap f) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (W.comap f)
  have h2 := SwapRigidity.finrank_le_finrank_comap W f
  omega

private lemma finrank_le_card_of_eq_zero_outside
    {F : Type*} [Field F] {d : ℕ} [NeZero d]
    (W : Submodule F (Matrix (ZMod d) (ZMod d) F))
    (supp : Finset (ZMod d × ZMod d))
    (hsupp : ∀ X ∈ W, ∀ b a : ZMod d, (b, a) ∉ supp → X b a = 0) :
    finrank F W ≤ supp.card := by
  let res : W →ₗ[F] (↥supp → F) :=
    { toFun := fun X p => X.1 p.1.1 p.1.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective res := by
    rw [injective_iff_map_eq_zero]
    intro X hX
    apply Subtype.ext
    ext b a
    by_cases hba : (b, a) ∈ supp
    · exact congrFun hX ⟨(b, a), hba⟩
    · exact hsupp X.1 X.2 b a hba
  calc finrank F W
      ≤ finrank F (↥supp → F) := LinearMap.finrank_le_finrank_of_injective hinj
    _ = Fintype.card ↥supp := Module.finrank_fintype_fun_eq_card F
    _ = supp.card := Fintype.card_coe supp

private lemma finrank_add_card_le_sq_of_eq_zero_on
    {F : Type*} [Field F] {d : ℕ} [NeZero d]
    (W : Submodule F (Matrix (ZMod d) (ZMod d) F))
    (zeroSet : Finset (ZMod d × ZMod d))
    (hzero : ∀ X ∈ W, ∀ b a : ZMod d, (b, a) ∈ zeroSet → X b a = 0) :
    finrank F W + zeroSet.card ≤ d ^ 2 := by
  have hle := finrank_le_card_of_eq_zero_outside W (Finset.univ \ zeroSet) (by
    intro X hX b a hnot
    apply hzero X hX b a
    by_contra hnz
    exact hnot (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnz⟩))
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ zeroSet)
  have huniv : (Finset.univ : Finset (ZMod d × ZMod d)).card = d ^ 2 := by
    rw [Finset.card_univ, Fintype.card_prod, ZMod.card, sq]
  omega

/-- Core unsymmetrized `4 * finrank` integer bound for `Theorem 3`. -/
private theorem four_mul_finrank_swapCode_le
    {F : Type*} [Field F] {d : ℕ} [NeZero d] {α : Type*} [Fintype α]
    {S_A S_B : Finset (Fin d)} {c_A c_B : ℕ}
    {A B : α → Matrix (Fin d) (Fin d) F}
    (hA : HasCoarseFineIntervalDecomposition S_A c_A A)
    (hB : HasCoarseFineIntervalDecomposition S_B c_B B) :
    let sA := S_A.card
    let sB := S_B.card
    let mA := cyclicRunEndpointCount S_A
    let mB := cyclicRunEndpointCount S_B
    4 * finrank F (SwapRigidity.swapCode A B) ≤
      2 * d ^ 2 + sB * (d - sA) + 2 * sA * sB +
        2 * c_B * d + c_A * sB + 2 * sB * mA + mB * (d - sA) := by
  intro sA sB mA mB
  let S_AZ : Finset (ZMod d) := S_A.image finToZMod
  let S_BZ : Finset (ZMod d) := S_B.image finToZMod
  have hsAZ : S_AZ.card = sA := Finset.card_image_of_injective S_A finToZMod_injective
  have hsBZ : S_BZ.card = sB := Finset.card_image_of_injective S_B finToZMod_injective
  have hmAZ : (S_AZ.filter fun a : ZMod d => a + 1 ∉ S_AZ).card = mA :=
    card_endpoints_image_finToZMod S_A
  have hmBZ : (S_BZ.filter fun b : ZMod d => b + 1 ∉ S_BZ).card = mB :=
    card_endpoints_image_finToZMod S_B
  obtain ⟨lenA, startA, _hlenA_pos, hcovA, hnotSA, hshiftA⟩ := coarseFine_unpack hA
  obtain ⟨lenB, startB, _hlenB_pos, hcovB, hnotSB, hshiftB⟩ := coarseFine_unpack hB
  -- Transfer `Matrix (Fin d) (Fin d) F` to `Matrix (ZMod d) (ZMod d) F`.
  let toZModMat : Matrix (Fin d) (Fin d) F ≃ₗ[F] Matrix (ZMod d) (ZMod d) F :=
    { toFun := fun X => Matrix.of fun b a => X (zmodToFin b) (zmodToFin a)
      invFun := fun Y => Matrix.of fun b a => Y (finToZMod b) (finToZMod a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun X => by ext b a; simp [zmodToFin_finToZMod]
      right_inv := fun Y => by ext b a; simp [finToZMod_zmodToFin] }
  let K_op : Matrix (ZMod d) (ZMod d) F →ₗ[F] Matrix (ZMod d) (ZMod d) F :=
    { toFun := fun X => Matrix.of fun b a =>
        ∑ t : α, ∑ a' : ZMod d, ∑ b' : ZMod d,
          A t (zmodToFin a) (zmodToFin a') * X a' b' * B t (zmodToFin b) (zmodToFin b')
      map_add' := fun X₁ X₂ => by
        ext b a
        simp only [Matrix.of_apply, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r X => by
        ext b a
        simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ =>
          Finset.sum_congr rfl fun a' _ =>
            Finset.sum_congr rfl fun b' _ => by ring }
  let K'_op : Matrix (ZMod d) (ZMod d) F →ₗ[F] Matrix (ZMod d) (ZMod d) F :=
    { toFun := fun X => Matrix.of fun b a =>
        if b ∈ S_BZ ∧ a ∈ S_AZ then 0 else K_op X b a
      map_add' := fun X₁ X₂ => by
        ext b a
        simp only [Matrix.of_apply, map_add, Matrix.add_apply]
        split_ifs <;> simp
      map_smul' := fun r X => by
        ext b a
        simp only [Matrix.of_apply, map_smul, Matrix.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
  let 𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) F) := LinearMap.ker (LinearMap.id - K_op)
  let Y : Submodule F (Matrix (ZMod d) (ZMod d) F) := LinearMap.ker (LinearMap.id - K'_op)
  have mem_𝒳_iff : ∀ X, X ∈ 𝒳 ↔ X = K_op X := by
    intro X
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have mem_Y_iff : ∀ X, X ∈ Y ↔ X = K'_op X := by
    intro X
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hY_zero : ∀ X ∈ Y, ∀ b a : ZMod d, b ∈ S_BZ → a ∈ S_AZ → X b a = 0 := by
    intro X hX b a hb ha
    have hEq := congrFun (congrFun ((mem_Y_iff X).mp hX) b) a
    simpa [K'_op, hb, ha] using hEq
  -- Identify `(swapCode A B).map toZModMat` with `𝒳`.
  have hSwapMap : (SwapRigidity.swapCode A B).map toZModMat.toLinearMap ≤ 𝒳 := by
    rintro _ ⟨X_fin, hX_fin, rfl⟩
    rw [mem_𝒳_iff]
    ext b a
    have hEntry := (SwapRigidity.mem_swapCode_iff_apply.mp hX_fin) (zmodToFin b) (zmodToFin a)
    show X_fin (zmodToFin b) (zmodToFin a) =
      ∑ t : α, ∑ a' : ZMod d, ∑ b' : ZMod d,
        A t (zmodToFin a) (zmodToFin a') * X_fin (zmodToFin a') (zmodToFin b') *
          B t (zmodToFin b) (zmodToFin b')
    rw [hEntry]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← (zmodEquivFin d).sum_comp]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← (zmodEquivFin d).sum_comp]
    rfl
  have hFinrankSwapLe : finrank F (SwapRigidity.swapCode A B) ≤ finrank F 𝒳 := by
    rw [← LinearEquiv.finrank_map_eq toZModMat (SwapRigidity.swapCode A B)]
    exact Submodule.finrank_mono hSwapMap
  -- Step 1: Restrict `𝒳` to `S_BZ × S_AZ`; kernel embeds into `Y`.
  have hStep1 : finrank F 𝒳 ≤ finrank F Y + sA * sB := by
    let resS : 𝒳 →ₗ[F] (↥S_BZ × ↥S_AZ → F) :=
      { toFun := fun X p => X.1 p.1.1 p.2.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let kerToY : LinearMap.ker resS →ₗ[F] Y :=
      { toFun := fun X => ⟨X.1.1, by
          rw [mem_Y_iff]
          have hXK : X.1.1 = K_op X.1.1 := (mem_𝒳_iff X.1.1).mp X.1.2
          ext b a
          simp only [K'_op, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
          by_cases hba : b ∈ S_BZ ∧ a ∈ S_AZ
          · rw [ite_eq_left hba]
            exact congrFun X.2 (⟨b, hba.1⟩, ⟨a, hba.2⟩)
          · rw [ite_eq_right hba]
            exact congrFun (congrFun hXK b) a⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hkerInj : Function.Injective kerToY := by
      rw [injective_iff_map_eq_zero]
      intro X hX
      have h0 : (kerToY X).1 = 0 := by rw [hX]; rfl
      exact Subtype.ext (Subtype.ext h0)
    have hkerLe : finrank F (LinearMap.ker resS) ≤ finrank F Y :=
      LinearMap.finrank_le_finrank_of_injective hkerInj
    have hranLe : finrank F (LinearMap.range resS) ≤ sA * sB := by
      calc finrank F (LinearMap.range resS)
          ≤ finrank F (↥S_BZ × ↥S_AZ → F) := Submodule.finrank_le _
        _ = Fintype.card (↥S_BZ × ↥S_AZ) := Module.finrank_fintype_fun_eq_card F
        _ = sA * sB := by
            rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, hsBZ, hsAZ, mul_comm]
    have hrn := LinearMap.finrank_range_add_finrank_ker resS
    omega
  -- Step 2: Column shift `σ_col` on `Y`.
  let σ_col : Matrix (ZMod d) (ZMod d) F →ₗ[F] Matrix (ZMod d) (ZMod d) F :=
    { toFun := fun X => Matrix.of fun r c => X r (c + 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Y_1 : Submodule F (Matrix (ZMod d) (ZMod d) F) := Y ⊓ Y.comap σ_col
  have hmA_le_sA : mA ≤ sA := by
    rw [← hmAZ, ← hsAZ]
    exact Finset.card_filter_le _ _
  have hStep2 : 2 * finrank F Y + sB * (sA - mA) ≤ d ^ 2 + finrank F Y_1 := by
    let I_AZ : Finset (ZMod d) := S_AZ.filter fun a => a - 1 ∈ S_AZ
    have hI_eq : I_AZ = (S_AZ.filter fun u => u + 1 ∈ S_AZ).image (· + 1) := by
      ext a
      simp only [I_AZ, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨ha, ha1⟩
        exact ⟨a - 1, ⟨ha1, by simpa using ha⟩, sub_add_cancel a 1⟩
      · rintro ⟨u, ⟨hu, hu1⟩, rfl⟩
        exact ⟨hu1, by simpa using hu⟩
    have hI_card : I_AZ.card = sA - mA := by
      have hsdiff_eq :
          (S_AZ.filter fun u : ZMod d => u + 1 ∈ S_AZ) =
            S_AZ \ (S_AZ.filter fun u : ZMod d => u + 1 ∉ S_AZ) := by
        ext u
        by_cases hu : u ∈ S_AZ <;> simp [hu]
      have hpart := Finset.card_sdiff_add_card_eq_card
        (Finset.filter_subset (fun u : ZMod d => u + 1 ∉ S_AZ) S_AZ)
      rw [← hsdiff_eq, hmAZ, hsAZ] at hpart
      rw [hI_eq, Finset.card_image_of_injective _ (add_left_injective (1 : ZMod d))]
      omega
    have hSupBound :
        finrank F ↥(Y ⊔ Y.comap σ_col) + (S_BZ ×ˢ I_AZ).card ≤ d ^ 2 := by
      refine finrank_add_card_le_sq_of_eq_zero_on (Y ⊔ Y.comap σ_col) (S_BZ ×ˢ I_AZ) ?_
      intro W hW b a hba
      rw [Finset.mem_product] at hba
      obtain ⟨hb, haI⟩ := hba
      rw [Finset.mem_filter] at haI
      obtain ⟨ha, ha_prev⟩ := haI
      obtain ⟨U, hU, V, hV, rfl⟩ := Submodule.mem_sup.mp hW
      have hU0 : U b a = 0 := hY_zero U hU b a hb ha
      have hV_in : σ_col V ∈ Y := hV
      have hV0 : V b a = 0 := by
        have h := hY_zero (σ_col V) hV_in b (a - 1) hb ha_prev
        change V b ((a - 1) + 1) = 0 at h
        rwa [sub_add_cancel] at h
      simp [hU0, hV0]
    rw [Finset.card_product, hsBZ, hI_card] at hSupBound
    have hSupInf := two_mul_finrank_le_sup_add_inf_comap Y σ_col
    change 2 * finrank F Y ≤ finrank F ↥(Y ⊔ Y.comap σ_col) + finrank F Y_1 at hSupInf
    omega
  -- Step 3: Diagonal invariance on `Y_1` along coarse intervals of `B`.
  have hY1_step : ∀ X ∈ Y_1, ∀ (j : Fin c_B) (v : ℕ), v + 1 < lenB j →
      let b := startB j + (v : ZMod d)
      ∀ a : ZMod d, X (b + 1) a = X b (a + 1) := by
    intro X hX j v hv1 b a
    obtain ⟨hXY, hXcolY⟩ := Submodule.mem_inf.mp hX
    have hb_not : b ∉ S_BZ := hnotSB j v (by omega)
    have hb1_not : b + 1 ∉ S_BZ := by
      have heq : b + 1 = startB j + ((v + 1 : ℕ) : ZMod d) := by
        simp [b, Nat.cast_add, add_assoc]
      rw [heq]
      exact hnotSB j (v + 1) hv1
    have hLHS : X (b + 1) a = K_op X (b + 1) a := by
      have h := congrFun (congrFun ((mem_Y_iff X).mp hXY) (b + 1)) a
      simpa [K'_op, hb1_not] using h
    have hRHS : X b (a + 1) = K_op (σ_col X) b a := by
      have h := congrFun (congrFun ((mem_Y_iff (σ_col X)).mp hXcolY) b) a
      have h' : σ_col X b a = K_op (σ_col X) b a := by
        simpa [K'_op, hb_not] using h
      exact h'
    rw [hLHS, hRHS]
    dsimp only [K_op, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, σ_col]
    refine Finset.sum_congr rfl fun t _ =>
      Finset.sum_congr rfl fun a' _ => ?_
    rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod d))]
    refine Finset.sum_congr rfl fun b' _ => ?_
    change A t (zmodToFin a) (zmodToFin a') * X a' (b' + 1) *
        B t (zmodToFin (b + 1)) (zmodToFin (b' + 1)) =
      A t (zmodToFin a) (zmodToFin a') * X a' (b' + 1) *
        B t (zmodToFin b) (zmodToFin b')
    rw [hshiftB j v hv1 t b']
  have hY1_walk : ∀ X ∈ Y_1, ∀ (j : Fin c_B) (v : ℕ), v < lenB j →
      ∀ a : ZMod d, X (startB j + (v : ZMod d)) a = X (startB j) (a + (v : ZMod d)) := by
    intro X hX j v
    induction v with
    | zero =>
      intro _ a
      simp
    | succ v ih =>
      intro hv1 a
      have hstep := hY1_step X hX j v hv1 a
      have heq1 : startB j + ((v + 1 : ℕ) : ZMod d) = (startB j + (v : ZMod d)) + 1 := by
        simp [Nat.cast_add, add_assoc]
      have heq2 : (a + 1) + (v : ZMod d) = a + ((v + 1 : ℕ) : ZMod d) := by
        simp [Nat.cast_add]
        abel
      rw [heq1, hstep, ih (by omega) (a + 1), heq2]
  let Z_0 : Submodule F (Matrix (ZMod d) (ZMod d) F) :=
    { carrier := {X | X ∈ Y_1 ∧ ∀ (j : Fin c_B) (a : ZMod d), X (startB j) a = 0}
      add_mem' := fun {X₁ X₂} h₁ h₂ =>
        ⟨Y_1.add_mem h₁.1 h₂.1, fun j a => by simp [h₁.2 j a, h₂.2 j a]⟩
      zero_mem' := ⟨Y_1.zero_mem, fun _ _ => rfl⟩
      smul_mem' := fun r {X} hX =>
        ⟨Y_1.smul_mem r hX.1, fun j a => by simp [hX.2 j a]⟩ }
  have hStep3 : finrank F Y_1 ≤ c_B * d + finrank F Z_0 := by
    let evalB : Y_1 →ₗ[F] (Fin c_B × ZMod d → F) :=
      { toFun := fun X p => X.1 (startB p.1) p.2
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let kerToZ0 : LinearMap.ker evalB →ₗ[F] Z_0 :=
      { toFun := fun X => ⟨X.1.1, X.1.2, fun j a => congrFun X.2 (j, a)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hkerInj : Function.Injective kerToZ0 := by
      rw [injective_iff_map_eq_zero]
      intro X hX
      have h0 : (kerToZ0 X).1 = 0 := by rw [hX]; rfl
      exact Subtype.ext (Subtype.ext h0)
    have hkerLe : finrank F (LinearMap.ker evalB) ≤ finrank F Z_0 :=
      LinearMap.finrank_le_finrank_of_injective hkerInj
    have hranLe : finrank F (LinearMap.range evalB) ≤ c_B * d := by
      calc finrank F (LinearMap.range evalB)
          ≤ finrank F (Fin c_B × ZMod d → F) := Submodule.finrank_le _
        _ = Fintype.card (Fin c_B × ZMod d) := Module.finrank_fintype_fun_eq_card F
        _ = c_B * d := by rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]
    have hrn := LinearMap.finrank_range_add_finrank_ker evalB
    omega
  have hZ0_support : ∀ X ∈ Z_0, ∀ b a : ZMod d,
      (b ∉ S_BZ ∨ a ∈ S_AZ) → X b a = 0 := by
    intro X ⟨hXY1, hXstart⟩ b a hcond
    rcases hcond with hb_not | ha_in
    · obtain ⟨j, v, hv, rfl⟩ := hcovB b hb_not
      rw [hY1_walk X hXY1 j v hv a]
      exact hXstart j (a + (v : ZMod d))
    · by_cases hb_in : b ∈ S_BZ
      · exact hY_zero X hXY1.1 b a hb_in ha_in
      · obtain ⟨j, v, hv, rfl⟩ := hcovB b hb_in
        rw [hY1_walk X hXY1 j v hv a]
        exact hXstart j (a + (v : ZMod d))
  -- Step 4: Row shift `σ_row` on `Z_0`.
  let σ_row : Matrix (ZMod d) (ZMod d) F →ₗ[F] Matrix (ZMod d) (ZMod d) F :=
    { toFun := fun X => Matrix.of fun r c => X (r + 1) c
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L_AZ : Finset (ZMod d) := Finset.univ \ S_AZ
  have hsA_le_d : sA ≤ d := by
    simpa [sA, Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ S_A
  have hLAZ_card : L_AZ.card = d - sA := by
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S_AZ)
    rw [Finset.card_univ, ZMod.card, hsAZ] at hcard
    change L_AZ.card + sA = d at hcard
    omega
  have hSupZ0 : finrank F ↥(Z_0 ⊔ Z_0.comap σ_row) ≤ (sB + mB) * (d - sA) := by
    let rowSupp : Finset (ZMod d) := S_BZ ∪ S_BZ.image (· + 1)
    have hrowSupp_sub :
        rowSupp ⊆ S_BZ ∪ (S_BZ.filter fun r : ZMod d => r + 1 ∉ S_BZ).image (· + 1) := by
      intro x hx
      rw [Finset.mem_union] at hx ⊢
      rcases hx with hxB | hxImg
      · exact Or.inl hxB
      · by_cases hxB : x ∈ S_BZ
        · exact Or.inl hxB
        · right
          rw [Finset.mem_image] at hxImg ⊢
          obtain ⟨r, hr, rfl⟩ := hxImg
          exact ⟨r, Finset.mem_filter.mpr ⟨hr, hxB⟩, rfl⟩
    have hrowSupp_card : rowSupp.card ≤ sB + mB := by
      calc rowSupp.card
          ≤ (S_BZ ∪ (S_BZ.filter fun r : ZMod d => r + 1 ∉ S_BZ).image (· + 1)).card :=
            Finset.card_mono hrowSupp_sub
        _ ≤ S_BZ.card + ((S_BZ.filter fun r : ZMod d => r + 1 ∉ S_BZ).image (· + 1)).card :=
            Finset.card_union_le _ _
        _ ≤ S_BZ.card + (S_BZ.filter fun r : ZMod d => r + 1 ∉ S_BZ).card :=
            Nat.add_le_add_left Finset.card_image_le _
        _ = sB + mB := by rw [hsBZ, hmBZ]
    have hle := finrank_le_card_of_eq_zero_outside (Z_0 ⊔ Z_0.comap σ_row)
      (rowSupp ×ˢ L_AZ) (by
        intro W hW b a hnot
        obtain ⟨U, hU, V, hV, rfl⟩ := Submodule.mem_sup.mp hW
        have hV_in : σ_row V ∈ Z_0 := hV
        by_cases haS : a ∈ S_AZ
        · have hU0 : U b a = 0 := hZ0_support U hU b a (Or.inr haS)
          have hV0 : V b a = 0 := by
            have h := hZ0_support (σ_row V) hV_in (b - 1) a (Or.inr haS)
            change V ((b - 1) + 1) a = 0 at h
            rwa [sub_add_cancel] at h
          simp [hU0, hV0]
        · have haL : a ∈ L_AZ := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haS⟩
          have hb_not_supp : b ∉ rowSupp := fun hb => hnot (Finset.mem_product.mpr ⟨hb, haL⟩)
          have hb_not_B : b ∉ S_BZ := fun hb => hb_not_supp (Finset.mem_union_left _ hb)
          have hbprev_not_B : b - 1 ∉ S_BZ := by
            intro hbp
            apply hb_not_supp
            refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨b - 1, hbp, sub_add_cancel b 1⟩
          have hU0 : U b a = 0 := hZ0_support U hU b a (Or.inl hb_not_B)
          have hV0 : V b a = 0 := by
            have h := hZ0_support (σ_row V) hV_in (b - 1) a (Or.inl hbprev_not_B)
            change V ((b - 1) + 1) a = 0 at h
            rwa [sub_add_cancel] at h
          simp [hU0, hV0])
    calc finrank F ↥(Z_0 ⊔ Z_0.comap σ_row)
        ≤ (rowSupp ×ˢ L_AZ).card := hle
      _ = rowSupp.card * (d - sA) := by rw [Finset.card_product, hLAZ_card]
      _ ≤ (sB + mB) * (d - sA) := Nat.mul_le_mul_right (d - sA) hrowSupp_card
  let Z_1 : Submodule F (Matrix (ZMod d) (ZMod d) F) := Z_0 ⊓ Z_0.comap σ_row
  have hZ1_step : ∀ X ∈ Z_1, ∀ (i : Fin c_A) (u : ℕ), u + 1 < lenA i →
      let a := startA i + (u : ZMod d)
      ∀ b : ZMod d, X b (a + 1) = X (b + 1) a := by
    intro X hX i u hu1 a b
    obtain ⟨hXZ0, hXrowZ0⟩ := Submodule.mem_inf.mp hX
    have hXY : X ∈ Y := hXZ0.1.1
    have hXrowY : σ_row X ∈ Y := hXrowZ0.1.1
    have ha_not : a ∉ S_AZ := hnotSA i u (by omega)
    have ha1_not : a + 1 ∉ S_AZ := by
      have heq : a + 1 = startA i + ((u + 1 : ℕ) : ZMod d) := by
        simp [a, Nat.cast_add, add_assoc]
      rw [heq]
      exact hnotSA i (u + 1) hu1
    have hLHS : X b (a + 1) = K_op X b (a + 1) := by
      have h := congrFun (congrFun ((mem_Y_iff X).mp hXY) b) (a + 1)
      simpa [K'_op, ha1_not] using h
    have hRHS : X (b + 1) a = K_op (σ_row X) b a := by
      have h := congrFun (congrFun ((mem_Y_iff (σ_row X)).mp hXrowY) b) a
      have h' : σ_row X b a = K_op (σ_row X) b a := by
        simpa [K'_op, ha_not] using h
      exact h'
    rw [hLHS, hRHS]
    dsimp only [K_op, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, σ_row]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod d))]
    refine Finset.sum_congr rfl fun a' _ =>
      Finset.sum_congr rfl fun b' _ => ?_
    change A t (zmodToFin (a + 1)) (zmodToFin (a' + 1)) * X (a' + 1) b' *
        B t (zmodToFin b) (zmodToFin b') =
      A t (zmodToFin a) (zmodToFin a') * X (a' + 1) b' *
        B t (zmodToFin b) (zmodToFin b')
    rw [hshiftA i u hu1 t a']
  have hZ1_walk : ∀ X ∈ Z_1, ∀ (i : Fin c_A) (u : ℕ), u < lenA i →
      ∀ b : ZMod d, X b (startA i + (u : ZMod d)) = X (b + (u : ZMod d)) (startA i) := by
    intro X hX i u
    induction u with
    | zero =>
      intro _ b
      simp
    | succ u ih =>
      intro hu1 b
      have hstep := hZ1_step X hX i u hu1 b
      have heq1 : startA i + ((u + 1 : ℕ) : ZMod d) = (startA i + (u : ZMod d)) + 1 := by
        simp [Nat.cast_add, add_assoc]
      have heq2 : (b + 1) + (u : ZMod d) = b + ((u + 1 : ℕ) : ZMod d) := by
        simp [Nat.cast_add]
        abel
      rw [heq1, hstep, ih (by omega) (b + 1), heq2]
  have hInfZ0 : finrank F Z_1 ≤ c_A * sB := by
    let evalA : Z_1 →ₗ[F] (Fin c_A × ↥S_BZ → F) :=
      { toFun := fun X p => X.1 p.2.1 (startA p.1)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective evalA := by
      rw [injective_iff_map_eq_zero]
      intro X hX
      apply Subtype.ext
      ext b a
      by_cases haS : a ∈ S_AZ
      · exact hZ0_support X.1 X.2.1 b a (Or.inr haS)
      · obtain ⟨i, u, hu, rfl⟩ := hcovA a haS
        rw [hZ1_walk X.1 X.2 i u hu b]
        by_cases hbu : b + (u : ZMod d) ∈ S_BZ
        · exact congrFun hX (i, ⟨b + (u : ZMod d), hbu⟩)
        · exact hZ0_support X.1 X.2.1 (b + (u : ZMod d)) (startA i) (Or.inl hbu)
    calc finrank F Z_1
        ≤ finrank F (Fin c_A × ↥S_BZ → F) := LinearMap.finrank_le_finrank_of_injective hinj
      _ = Fintype.card (Fin c_A × ↥S_BZ) := Module.finrank_fintype_fun_eq_card F
      _ = c_A * sB := by rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, hsBZ]
  have hStep4 : 2 * finrank F Z_0 ≤ sB * (d - sA) + mB * (d - sA) + c_A * sB := by
    have hSupInf := two_mul_finrank_le_sup_add_inf_comap Z_0 σ_row
    change 2 * finrank F Z_0 ≤ finrank F ↥(Z_0 ⊔ Z_0.comap σ_row) + finrank F Z_1 at hSupInf
    have hexpand : (sB + mB) * (d - sA) = sB * (d - sA) + mB * (d - sA) := Nat.add_mul _ _ _
    omega
  -- Combine Steps 1–4 in `ℕ`.
  have hsB_split : sB * (sA - mA) + sB * mA = sA * sB := by
    calc sB * (sA - mA) + sB * mA
        = sB * ((sA - mA) + mA) := (Nat.mul_add _ _ _).symm
      _ = sB * sA := by rw [Nat.sub_add_cancel hmA_le_sA]
      _ = sA * sB := mul_comm _ _
  have hAssoc1 : 2 * sA * sB = 2 * (sA * sB) := Nat.mul_assoc 2 sA sB
  have hAssoc2 : 2 * c_B * d = 2 * (c_B * d) := Nat.mul_assoc 2 c_B d
  have hAssoc3 : 2 * sB * mA = 2 * (sB * mA) := Nat.mul_assoc 2 sB mA
  omega

private theorem finrank_swapCode_le_unsymmetrized
    {F : Type*} [Field F] {d : ℕ} [NeZero d] {α : Type*} [Fintype α]
    {S_A S_B : Finset (Fin d)} {c_A c_B : ℕ}
    {A B : α → Matrix (Fin d) (Fin d) F}
    (hA : HasCoarseFineIntervalDecomposition S_A c_A A)
    (hB : HasCoarseFineIntervalDecomposition S_B c_B B) :
    (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
      theorem3UnsymmetrizedBound d S_A.card (cyclicRunEndpointCount S_A) c_A
        S_B.card (cyclicRunEndpointCount S_B) c_B := by
  have h4 := four_mul_finrank_swapCode_le hA hB
  have hsA_le : S_A.card ≤ d := by
    simpa [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ S_A
  have h4r : (4 : ℝ) * (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
      ((2 * d ^ 2 + S_B.card * (d - S_A.card) + 2 * S_A.card * S_B.card +
        2 * c_B * d + c_A * S_B.card + 2 * S_B.card * cyclicRunEndpointCount S_A +
        cyclicRunEndpointCount S_B * (d - S_A.card) : ℕ) : ℝ) := by
    exact_mod_cast h4
  push_cast [Nat.cast_sub hsA_le] at h4r
  dsimp only [theorem3UnsymmetrizedBound]
  linarith

private lemma theorem3UnsymmetrizedBound_mono_runs
    {d sA mA mA' cA sB mB mB' cB : ℕ}
    (hsA : sA ≤ d) (hmA : mA ≤ mA') (hmB : mB ≤ mB') :
    theorem3UnsymmetrizedBound d sA mA cA sB mB cB ≤
      theorem3UnsymmetrizedBound d sA mA' cA sB mB' cB := by
  have hsA_r : (sA : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr hsA
  have hsB_r : (0 : ℝ) ≤ (sB : ℝ) := Nat.cast_nonneg sB
  have hmA_r : (mA : ℝ) ≤ (mA' : ℝ) := Nat.cast_le.mpr hmA
  have hmB_r : (mB : ℝ) ≤ (mB' : ℝ) := Nat.cast_le.mpr hmB
  dsimp only [theorem3UnsymmetrizedBound]
  nlinarith

/-- Proof of `Extension_Theorem3_TwoSidedCoarseFineSpec` (`Theorem 3`). -/
theorem extension_Theorem3_TwoSidedCoarseFine : Extension_Theorem3_TwoSidedCoarseFineSpec := by
  intro F _ d _ α _ S_A S_B c_A c_B A B hA hB
  have hAB := finrank_swapCode_le_unsymmetrized hA hB
  have hBA := finrank_swapCode_le_unsymmetrized hB hA
  rw [← SwapRigidity.finrank_swapCode_swap A B] at hBA
  have hMinEnd :
      (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
        min
          (theorem3UnsymmetrizedBound d S_A.card (cyclicRunEndpointCount S_A) c_A
            S_B.card (cyclicRunEndpointCount S_B) c_B)
          (theorem3UnsymmetrizedBound d S_B.card (cyclicRunEndpointCount S_B) c_B
            S_A.card (cyclicRunEndpointCount S_A) c_A) :=
    le_min hAB hBA
  refine ⟨hMinEnd, le_min ?_ ?_⟩
  · have hsA : S_A.card ≤ d := by
      simpa [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ S_A
    exact le_trans hAB (theorem3UnsymmetrizedBound_mono_runs hsA
      (cyclicRunEndpointCount_le_cyclicRunCount S_A)
      (cyclicRunEndpointCount_le_cyclicRunCount S_B))
  · have hsB : S_B.card ≤ d := by
      simpa [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ S_B
    exact le_trans hBA (theorem3UnsymmetrizedBound_mono_runs hsB
      (cyclicRunEndpointCount_le_cyclicRunCount S_B)
      (cyclicRunEndpointCount_le_cyclicRunCount S_A))

/-- Direct unpacked universal theorem form of `Theorem 3`
(`Extension_Theorem3_TwoSidedCoarseFineSpec`). -/
theorem swapCode_finrank_le_twoSidedCoarseFine
    (F : Type*) [Field F] (d : ℕ) [NeZero d] (α : Type*) [Fintype α]
    (S_A S_B : Finset (Fin d)) (c_A c_B : ℕ)
    (A B : α → Matrix (Fin d) (Fin d) F)
    (hA : HasCoarseFineIntervalDecomposition S_A c_A A)
    (hB : HasCoarseFineIntervalDecomposition S_B c_B B) :
    let sA := S_A.card
    let sB := S_B.card
    (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
      min
        (theorem3UnsymmetrizedBound d sA (cyclicRunEndpointCount S_A) c_A
          sB (cyclicRunEndpointCount S_B) c_B)
        (theorem3UnsymmetrizedBound d sB (cyclicRunEndpointCount S_B) c_B
          sA (cyclicRunEndpointCount S_A) c_A) ∧
    (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
      min
        (theorem3UnsymmetrizedBound d sA (cyclicRunCount S_A) c_A
          sB (cyclicRunCount S_B) c_B)
        (theorem3UnsymmetrizedBound d sB (cyclicRunCount S_B) c_B
          sA (cyclicRunCount S_A) c_A) :=
  extension_Theorem3_TwoSidedCoarseFine F d α S_A S_B c_A c_B A B hA hB

/-! ### Concrete Contiguous Coarse–Fine Realization & Win Over One-Sided `Theorem TP` -/

private lemma mem_contiguousFineSet_iff {d s : ℕ} [NeZero d] (hs : s ≤ d) (r : Fin d) :
    r ∈ contiguousFineSet (d := d) s ↔ r.val < s := by
  simp only [contiguousFineSet, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨u, hu, rfl⟩
    show u % d < s
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hu hs)]
    exact hu
  · intro hr
    refine ⟨r.val, hr, Fin.ext ?_⟩
    exact Nat.mod_eq_of_lt r.isLt

private lemma card_contiguousFineSet {d s : ℕ} [NeZero d] (hs : s ≤ d) :
    (contiguousFineSet (d := d) s).card = s := by
  dsimp only [contiguousFineSet]
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range s
  · intro u hu v hv hEq
    have hu_lt : u < d := lt_of_lt_of_le (Finset.mem_range.mp hu) hs
    have hv_lt : v < d := lt_of_lt_of_le (Finset.mem_range.mp hv) hs
    have hval : u % d = v % d := congrArg Fin.val hEq
    rwa [Nat.mod_eq_of_lt hu_lt, Nat.mod_eq_of_lt hv_lt] at hval

private lemma cyclicRunEndpointCount_contiguousFineSet {d s : ℕ} [NeZero d]
    (hs1 : 1 ≤ s) (hsd : s < d) :
    cyclicRunEndpointCount (contiguousFineSet (d := d) s) = 1 := by
  let r₀ : Fin d := ⟨s - 1, by omega⟩
  have hfilter :
      ((contiguousFineSet (d := d) s).filter fun r : Fin d =>
        (⟨(r.val + 1) % d, Nat.mod_lt _ (NeZero.pos d)⟩ : Fin d) ∉
          contiguousFineSet (d := d) s) = {r₀} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_singleton,
      mem_contiguousFineSet_iff (le_of_lt hsd)]
    constructor
    · rintro ⟨hr_lt, hr_succ⟩
      have hmod : (r.val + 1) % d = r.val + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hmod] at hr_succ
      exact Fin.ext (by show r.val = s - 1; omega)
    · rintro rfl
      have hmod : ((s - 1) + 1) % d = s := by
        rw [show (s - 1) + 1 = s by omega]
        exact Nat.mod_eq_of_lt hsd
      exact ⟨by show s - 1 < s; omega, by show ¬ ((s - 1 + 1) % d < s); omega⟩
  dsimp only [cyclicRunEndpointCount]
  rw [hfilter, Finset.card_singleton]

private lemma cyclicRunCount_contiguousFineSet {d s : ℕ} [NeZero d]
    (hs1 : 1 ≤ s) (hsd : s < d) :
    cyclicRunCount (contiguousFineSet (d := d) s) = 1 := by
  dsimp only [cyclicRunCount]
  split_ifs
  · rfl
  · exact cyclicRunEndpointCount_contiguousFineSet hs1 hsd

private lemma contiguousCoarseComplement_isCyclicInterval {d s : ℕ} [NeZero d]
    (hsd : s < d) :
    IsCyclicInterval (d - s) (contiguousCoarseComplement (d := d) s) := by
  refine ⟨⟨s, hsd⟩, ?_⟩
  ext r
  simp only [contiguousCoarseComplement, Finset.mem_sdiff, Finset.mem_univ, true_and,
    mem_contiguousFineSet_iff (le_of_lt hsd), Finset.mem_image, Finset.mem_range]
  constructor
  · intro hr
    refine ⟨r.val - s, by have := r.isLt; omega, Fin.ext ?_⟩
    show (s + (r.val - s)) % d = r.val
    rw [show s + (r.val - s) = r.val by omega, Nat.mod_eq_of_lt r.isLt]
  · rintro ⟨u, hu, rfl⟩
    show ¬ ((s + u) % d < s)
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

private lemma hasCoarseFine_of_inContiguous
    {F : Type*} [Field F] {d s : ℕ} [NeZero d] {α : Type*}
    {M : α → Matrix (Fin d) (Fin d) F}
    (hs1 : 1 ≤ s) (hsd : s < d) (hM : InContiguousCoarseFineSpan s M) :
    HasCoarseFineIntervalDecomposition (contiguousFineSet (d := d) s) 1 M := by
  let coarse : Fin 1 → Finset (Fin d) := fun _ => contiguousCoarseComplement (d := d) s
  refine ⟨coarse, ?_, ?_, ?_, ?_⟩
  · intro _
    exact ⟨d - s, by omega, by omega, contiguousCoarseComplement_isCyclicInterval hsd⟩
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · ext r
    simp [coarse, contiguousCoarseComplement]
  · intro a
    refine Submodule.span_mono ?_ (hM a)
    rintro X ((⟨r, hr, e, rfl⟩ | ⟨e, rfl⟩) | ⟨e, rfl⟩)
    · exact Set.mem_union_left _ (Set.mem_union_left _
        ⟨{r}, Finset.singleton_subset_iff.mpr hr, e, rfl⟩)
    · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨0, e, rfl⟩)
    · exact Set.mem_union_right _ ⟨e, rfl⟩

/-- Proof of `Extension_Theorem3_ConcreteWinOverTPSpec`. -/
theorem extension_Theorem3_ConcreteWinOverTP : Extension_Theorem3_ConcreteWinOverTPSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro α β hα0 hα1 hβ0 hβ1
    rcases le_total α β with hle | hle
    · rw [min_eq_left hle]
      have hmin : min (β * (1 + α)) (α * (1 + β)) ≤ α * (1 + β) := min_le_right _ _
      nlinarith
    · rw [min_eq_right hle]
      have hmin : min (β * (1 + α)) (α * (1 + β)) ≤ β * (1 + α) := min_le_left _ _
      nlinarith
  · intro F _ d _ α _ s_A s_B hsA hsB A B hA hB
    have hDecompA := hasCoarseFine_of_inContiguous hsA.1 hsA.2 hA
    have hDecompB := hasCoarseFine_of_inContiguous hsB.1 hsB.2 hB
    have hCardA := card_contiguousFineSet (d := d) (le_of_lt hsA.2)
    have hCardB := card_contiguousFineSet (d := d) (le_of_lt hsB.2)
    have hRunA := cyclicRunCount_contiguousFineSet hsA.1 hsA.2
    have hEndA := cyclicRunEndpointCount_contiguousFineSet hsA.1 hsA.2
    have hEndB := cyclicRunEndpointCount_contiguousFineSet hsB.1 hsB.2
    refine ⟨hDecompA, hDecompB, hCardA, hRunA, ?_⟩
    have hMain := (extension_Theorem3_TwoSidedCoarseFine F d α
      (contiguousFineSet (d := d) s_A) (contiguousFineSet (d := d) s_B) 1 1 A B
      hDecompA hDecompB).1
    rw [hCardA, hCardB, hEndA, hEndB] at hMain
    set αr : ℝ := (s_A : ℝ) / (d : ℝ)
    set βr : ℝ := (s_B : ℝ) / (d : ℝ)
    have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
    have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
    have hsA_eq : (s_A : ℝ) = αr * (d : ℝ) := by
      dsimp [αr]
      exact (div_mul_cancel₀ (s_A : ℝ) hd_ne).symm
    have hsB_eq : (s_B : ℝ) = βr * (d : ℝ) := by
      dsimp [βr]
      exact (div_mul_cancel₀ (s_B : ℝ) hd_ne).symm
    have hsA_lt : (s_A : ℝ) < (d : ℝ) := Nat.cast_lt.mpr hsA.2
    have hsB_lt : (s_B : ℝ) < (d : ℝ) := Nat.cast_lt.mpr hsB.2
    have hsA_nn : (0 : ℝ) ≤ (s_A : ℝ) := Nat.cast_nonneg s_A
    have hsB_nn : (0 : ℝ) ≤ (s_B : ℝ) := Nat.cast_nonneg s_B
    rcases le_total s_B s_A with hle | hle
    · have hle_r : (s_B : ℝ) ≤ (s_A : ℝ) := Nat.cast_le.mpr hle
      have hβ_le_α : βr ≤ αr := div_le_div_of_nonneg_right hle_r hd_pos.le
      have hmin_eq : min (βr * (1 + αr)) (αr * (1 + βr)) = βr * (1 + αr) :=
        min_eq_left (by nlinarith)
      rw [hmin_eq]
      have hle_AB : min (theorem3UnsymmetrizedBound d s_A 1 1 s_B 1 1)
          (theorem3UnsymmetrizedBound d s_B 1 1 s_A 1 1) ≤
          theorem3UnsymmetrizedBound d s_A 1 1 s_B 1 1 := min_le_left _ _
      have hId :
          ((1 / 2 : ℝ) + (1 / 4 : ℝ) * (βr * (1 + αr))) * (d : ℝ) ^ 2 =
            (1 / 2 : ℝ) * (d : ℝ) ^ 2 + (1 / 4 : ℝ) * (s_B : ℝ) * (d : ℝ) +
              (1 / 4 : ℝ) * (s_A : ℝ) * (s_B : ℝ) := by
        rw [hsA_eq, hsB_eq]
        ring
      dsimp only [theorem3UnsymmetrizedBound] at hMain hle_AB
      linarith
    · have hle_r : (s_A : ℝ) ≤ (s_B : ℝ) := Nat.cast_le.mpr hle
      have hα_le_β : αr ≤ βr := div_le_div_of_nonneg_right hle_r hd_pos.le
      have hmin_eq : min (βr * (1 + αr)) (αr * (1 + βr)) = αr * (1 + βr) :=
        min_eq_right (by nlinarith)
      rw [hmin_eq]
      have hle_BA : min (theorem3UnsymmetrizedBound d s_A 1 1 s_B 1 1)
          (theorem3UnsymmetrizedBound d s_B 1 1 s_A 1 1) ≤
          theorem3UnsymmetrizedBound d s_B 1 1 s_A 1 1 := min_le_right _ _
      have hId :
          ((1 / 2 : ℝ) + (1 / 4 : ℝ) * (αr * (1 + βr))) * (d : ℝ) ^ 2 =
            (1 / 2 : ℝ) * (d : ℝ) ^ 2 + (1 / 4 : ℝ) * (s_A : ℝ) * (d : ℝ) +
              (1 / 4 : ℝ) * (s_B : ℝ) * (s_A : ℝ) := by
        rw [hsA_eq, hsB_eq]
        ring
      dsimp only [theorem3UnsymmetrizedBound] at hMain hle_BA
      linarith
  · refine ⟨by norm_num, ?_⟩
    intro k _
    let d := 2 * k
    have : NeZero d := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne k)⟩
    have hFormula :
        theorem3UnsymmetrizedBound d k 1 1 k 1 1 = (11 / 16 : ℝ) * (d : ℝ) ^ 2 + (d : ℝ) := by
      dsimp only [theorem3UnsymmetrizedBound, d]
      push_cast
      ring
    refine ⟨hFormula, ?_, ?_⟩
    · intro hk9
      have hd18 : (18 : ℝ) ≤ (d : ℝ) := by
        have h : 18 ≤ d := by dsimp [d]; omega
        exact_mod_cast h
      nlinarith
    · intro F _ α _ A B hA hB
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
      have hkd : k < d := by dsimp [d]; omega
      have hDecompA := hasCoarseFine_of_inContiguous hk1 hkd hA
      have hDecompB := hasCoarseFine_of_inContiguous hk1 hkd hB
      have hMain := (extension_Theorem3_TwoSidedCoarseFine F d α
        (contiguousFineSet (d := d) k) (contiguousFineSet (d := d) k) 1 1 A B
        hDecompA hDecompB).1
      rw [card_contiguousFineSet (d := d) (le_of_lt hkd),
          cyclicRunEndpointCount_contiguousFineSet hk1 hkd,
          min_self, hFormula] at hMain
      exact hMain

/-- Direct unpacked theorem form of the concrete contiguous coarse–fine swap-code bound
(`Extension_Theorem3_ConcreteWinOverTPSpec`, Part 2). -/
theorem swapCode_finrank_le_contiguousCoarseFine.{u, v}
    (F : Type u) [Field F] (d : ℕ) [NeZero d] (α : Type v) [Fintype α]
    (s_A s_B : ℕ) (hsA : 1 ≤ s_A ∧ s_A < d) (hsB : 1 ≤ s_B ∧ s_B < d)
    (A B : α → Matrix (Fin d) (Fin d) F)
    (hA : InContiguousCoarseFineSpan s_A A)
    (hB : InContiguousCoarseFineSpan s_B B) :
    let αr : ℝ := (s_A : ℝ) / (d : ℝ)
    let βr : ℝ := (s_B : ℝ) / (d : ℝ)
    HasCoarseFineIntervalDecomposition (contiguousFineSet (d := d) s_A) 1 A ∧
    HasCoarseFineIntervalDecomposition (contiguousFineSet (d := d) s_B) 1 B ∧
    (contiguousFineSet (d := d) s_A).card = s_A ∧
    cyclicRunCount (contiguousFineSet (d := d) s_A) = 1 ∧
    (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
      ((1 / 2 : ℝ) + (1 / 4 : ℝ) * min (βr * (1 + αr)) (αr * (1 + βr))) * (d : ℝ) ^ 2 +
        (5 / 4 : ℝ) * (d : ℝ) :=
  extension_Theorem3_ConcreteWinOverTP.{u, v, 0, 0}.2.1 F d α s_A s_B hsA hsB A B hA hB

private lemma shift_cond_eq_zmod {d : ℕ} [NeZero d] (r u : ZMod d) (e : Fin d) :
    ((zmodToFin (r + u)).val = ((zmodToFin r).val + e.val) % d) ↔ u = finToZMod e := by
  constructor
  · intro hmod
    have hcast : (((r + u).val : ℕ) : ZMod d) = (((r.val + e.val) % d : ℕ) : ZMod d) :=
      congrArg (fun n : ℕ => (n : ZMod d)) hmod
    rw [ZMod.natCast_zmod_val, ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val] at hcast
    exact add_left_cancel hcast
  · rintro rfl
    have hsum : r + finToZMod e = ((r.val + e.val : ℕ) : ZMod d) := by
      simp [finToZMod, Nat.cast_add]
    show (r + finToZMod e).val = (r.val + e.val) % d
    rw [hsum]
    exact ZMod.val_natCast (n := d) (r.val + e.val)

private lemma oneSidedTP_of_inContiguous
    {F : Type*} [Field F] {d : ℕ} [NeZero d] {α : Type*} [Fintype α]
    {s : ℕ} (hs : 1 ≤ s ∧ s < d)
    {A B : α → Matrix (Fin d) (Fin d) F}
    (hA : InContiguousCoarseFineSpan s A) :
    2 * finrank F (SwapRigidity.swapCode A B) ≤ d ^ 2 + (s + 1) * d := by
  classical
  let cls : ZMod d → Fin (s + 1) := fun r =>
    if hr : r.val < s then ⟨r.val, by omega⟩ else ⟨s, by omega⟩
  have hcls_iff : ∀ r₁ r₂ : ZMod d,
      cls r₁ = cls r₂ → (r₁.val < s ∧ zmodToFin r₁ = zmodToFin r₂) ∨ (s ≤ r₁.val ∧ s ≤ r₂.val) := by
    intro r₁ r₂ hEq
    have hval : (cls r₁).val = (cls r₂).val := congrArg Fin.val hEq
    by_cases hr₁ : r₁.val < s
    · by_cases hr₂ : r₂.val < s
      · simp only [cls, hr₁, hr₂, ↓reduceDIte] at hval
        exact Or.inl ⟨hr₁, Fin.ext hval⟩
      · simp only [cls, hr₁, hr₂, ↓reduceDIte] at hval
        omega
    · by_cases hr₂ : r₂.val < s
      · simp only [cls, hr₁, hr₂, ↓reduceDIte] at hval
        omega
      · exact Or.inr ⟨by omega, by omega⟩
  let PSub : Submodule F (Matrix (Fin d) (Fin d) F) :=
    { carrier := {M | ∀ r₁ r₂ u : ZMod d, cls r₁ = cls r₂ →
        M (zmodToFin r₁) (zmodToFin (r₁ + u)) = M (zmodToFin r₂) (zmodToFin (r₂ + u))}
      add_mem' := fun {M₁ M₂} h₁ h₂ r₁ r₂ u hcls => by
        simp [h₁ r₁ r₂ u hcls, h₂ r₁ r₂ u hcls]
      zero_mem' := fun _ _ _ _ => rfl
      smul_mem' := fun c {M} hM r₁ r₂ u hcls => by
        simp [hM r₁ r₂ u hcls] }
  have hSpanLe : Submodule.span F
      ({X | ∃ (r : Fin d) (_hr : r ∈ contiguousFineSet (d := d) s) (e : Fin d),
          X = intervalMaskRotMatrix F {r} e} ∪
       {X | ∃ e : Fin d,
          X = intervalMaskRotMatrix F (contiguousCoarseComplement (d := d) s) e} ∪
       {X | ∃ e : Fin d,
          X = intervalMaskRotMatrix F Finset.univ e}) ≤ PSub := by
    rw [Submodule.span_le]
    rintro M ((⟨r₀, hr₀, e, rfl⟩ | ⟨e, rfl⟩) | ⟨e, rfl⟩) r₁ r₂ u hcls
    · have hr₀_lt : r₀.val < s := (mem_contiguousFineSet_iff (le_of_lt hs.2) r₀).mp hr₀
      have heq_iff : (zmodToFin r₁ = r₀) ↔ (zmodToFin r₂ = r₀) := by
        rcases hcls_iff r₁ r₂ hcls with ⟨_, hEqFin⟩ | ⟨hge₁, hge₂⟩
        · rw [hEqFin]
        · constructor <;> intro hEq <;>
            { have := congrArg Fin.val hEq; dsimp [zmodToFin] at this; omega }
      simp [intervalMaskRotMatrix, shift_cond_eq_zmod, heq_iff]
    · have hle_iff : (s ≤ (zmodToFin r₁).val) ↔ (s ≤ (zmodToFin r₂).val) := by
        rcases hcls_iff r₁ r₂ hcls with ⟨_, hEqFin⟩ | ⟨hge₁, hge₂⟩
        · rw [hEqFin]
        · dsimp [zmodToFin]; omega
      simp [intervalMaskRotMatrix, contiguousCoarseComplement,
        mem_contiguousFineSet_iff (le_of_lt hs.2), shift_cond_eq_zmod, hle_iff]
    · simp [intervalMaskRotMatrix, shift_cond_eq_zmod]
  have hA_cls : ∀ a : α, A a ∈ PSub := fun a => hSpanLe (hA a)
  let coeffA : α → Fin (s + 1) → ZMod d → F := fun a k u =>
    if h : ∃ r₀ : ZMod d, cls r₀ = k then
      A a (zmodToFin (Classical.choose h)) (zmodToFin (Classical.choose h + u))
    else 0
  have hcoeffA : ∀ (a : α) (r u : ZMod d),
      A a (zmodToFin r) (zmodToFin (r + u)) = coeffA a (cls r) u := by
    intro a r u
    have hex : ∃ r₀ : ZMod d, cls r₀ = cls r := ⟨r, rfl⟩
    simp only [coeffA, dite_eq_left hex]
    exact hA_cls a r (Classical.choose hex) u (Classical.choose_spec hex).symm
  let toTransZMod : Matrix (Fin d) (Fin d) F ≃ₗ[F] Matrix (ZMod d) (ZMod d) F :=
    { toFun := fun X => Matrix.of fun r c => X (zmodToFin c) (zmodToFin r)
      invFun := fun Y => Matrix.of fun r c => Y (finToZMod c) (finToZMod r)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun X => by ext r c; simp [zmodToFin_finToZMod]
      right_inv := fun Y => by ext r c; simp [finToZMod_zmodToFin] }
  let 𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) F) :=
    (SwapRigidity.swapCode A B).map toTransZMod.toLinearMap
  have hClassUnif : SwapRigidity.IsClassUniformCode cls 𝒳 := by
    let dec : Fin (s + 1) → (Matrix (ZMod d) (ZMod d) F →ₗ[F] (ZMod d → F)) := fun k =>
      { toFun := fun Z c =>
          ∑ a : α, ∑ u : ZMod d, ∑ c' : ZMod d,
            coeffA a k u * Z c' u * B a (zmodToFin c) (zmodToFin c')
        map_add' := fun Z₁ Z₂ => by
          funext c
          simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]
        map_smul' := fun x Z => by
          funext c
          simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.smul_apply,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun u _ =>
              Finset.sum_congr rfl fun c' _ => by ring }
    refine ⟨dec, ?_⟩
    rintro _ ⟨X, hX, rfl⟩ r
    funext c
    have hEntry := (SwapRigidity.mem_swapCode_iff_apply.mp hX) (zmodToFin c) (zmodToFin r)
    show X (zmodToFin c) (zmodToFin r) =
      ∑ a : α, ∑ u : ZMod d, ∑ c' : ZMod d,
        coeffA a (cls r) u * X (zmodToFin (u + r)) (zmodToFin c') *
          B a (zmodToFin c) (zmodToFin c')
    rw [hEntry]
    refine Finset.sum_congr rfl fun a _ => ?_
    let shiftEquiv : ZMod d ≃ Fin d := (Equiv.addRight r).trans (zmodEquivFin d)
    rw [← shiftEquiv.sum_comp (fun a' : Fin d =>
          ∑ b' : Fin d, A a (zmodToFin r) a' * X a' b' * B a (zmodToFin c) b')]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← (zmodEquivFin d).sum_comp (fun b' : Fin d =>
          A a (zmodToFin r) (shiftEquiv u) * X (shiftEquiv u) b' * B a (zmodToFin c) b')]
    refine Finset.sum_congr rfl fun c' _ => ?_
    have hu' : shiftEquiv u = zmodToFin (u + r) := rfl
    rw [hu', show zmodEquivFin d c' = zmodToFin c' from rfl]
    congr 2
    rw [add_comm u r, hcoeffA a r u]
  let S : Finset (ZMod d) := (Finset.range (s + 1)).image (fun u : ℕ => (u : ZMod d))
  have hS_nonempty : S.Nonempty :=
    ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), Nat.cast_zero⟩⟩
  have hS_card : S.card ≤ s + 1 :=
    Finset.card_image_le.trans (by rw [Finset.card_range])
  have hS_cls : ∀ c ∉ S, cls (c - 1) = cls c := by
    intro c hcS
    have hc_ge : s + 1 ≤ c.val := by
      by_contra hlt
      exact hcS (Finset.mem_image.mpr
        ⟨c.val, Finset.mem_range.mpr (by omega), ZMod.natCast_zmod_val c⟩)
    have hc_lt : c.val < d := c.val_lt
    have hc_sub : c - 1 = ((c.val - 1 : ℕ) : ZMod d) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_zmod_val, Nat.cast_one]
    have hc1_val : (c - 1).val = c.val - 1 := by
      rw [hc_sub, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hnot1 : ¬ ((c - 1).val < s) := by omega
    have hnot2 : ¬ (c.val < s) := by omega
    simp [cls, hnot1, hnot2]
  have hTP := hClassUnif.two_mul_finrank_le hS_nonempty hS_cls
  have hfinrank_eq : finrank F 𝒳 = finrank F (SwapRigidity.swapCode A B) :=
    toTransZMod.finrank_map_eq (SwapRigidity.swapCode A B)
  rw [hfinrank_eq] at hTP
  calc 2 * finrank F (SwapRigidity.swapCode A B)
      ≤ d ^ 2 + d * S.card := hTP
    _ ≤ d ^ 2 + d * (s + 1) := Nat.add_le_add_left (Nat.mul_le_mul_left d hS_card) (d ^ 2)
    _ = d ^ 2 + (s + 1) * d := by ring

/-- **One-Sided `Theorem TP` Baseline on `InContiguousCoarseFineSpan`.**
Applying `SwapRigidity.IsClassUniformCode.two_mul_finrank_le` (`Theorem TP`, Paper 17 Theorem 6.4)
on each side of `InContiguousCoarseFineSpan` and symmetrizing via `SwapRigidity.finrank_swapCode_swap`
yields `2 * finrank F (SwapRigidity.swapCode A B) ≤ d^2 + (min s_A s_B + 1) * d`, i.e.,
`finrank F (SwapRigidity.swapCode A B) ≤ (1/2 + (1/2) * min α β) * d^2 + (1/2) * d`. -/
theorem swapCode_oneSidedTP_le_contiguousCoarseFine.{u, v}
    (F : Type u) [Field F] (d : ℕ) [NeZero d] (α : Type v) [Fintype α]
    (s_A s_B : ℕ) (hsA : 1 ≤ s_A ∧ s_A < d) (hsB : 1 ≤ s_B ∧ s_B < d)
    (A B : α → Matrix (Fin d) (Fin d) F)
    (hA : InContiguousCoarseFineSpan s_A A)
    (hB : InContiguousCoarseFineSpan s_B B) :
    let αr : ℝ := (s_A : ℝ) / (d : ℝ)
    let βr : ℝ := (s_B : ℝ) / (d : ℝ)
    2 * finrank F (SwapRigidity.swapCode A B) ≤ d ^ 2 + (min s_A s_B + 1) * d ∧
    (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
      ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min αr βr) * (d : ℝ) ^ 2 + (1 / 2 : ℝ) * (d : ℝ) := by
  intro αr βr
  have hTPA : 2 * finrank F (SwapRigidity.swapCode A B) ≤ d ^ 2 + (s_A + 1) * d :=
    oneSidedTP_of_inContiguous hsA hA
  have hTPB : 2 * finrank F (SwapRigidity.swapCode A B) ≤ d ^ 2 + (s_B + 1) * d := by
    rw [SwapRigidity.finrank_swapCode_swap A B]
    exact oneSidedTP_of_inContiguous hsB hB
  have hNat : 2 * finrank F (SwapRigidity.swapCode A B) ≤ d ^ 2 + (min s_A s_B + 1) * d := by
    rcases le_total s_A s_B with hle | hle
    · rw [min_eq_left hle]; exact hTPA
    · rw [min_eq_right hle]; exact hTPB
  refine ⟨hNat, ?_⟩
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  have hReal2 : (2 : ℝ) * (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
      (d : ℝ) ^ 2 + ((min s_A s_B : ℕ) + 1 : ℝ) * (d : ℝ) := by
    exact_mod_cast hNat
  have hmin_eq : ((min s_A s_B : ℕ) : ℝ) = min αr βr * (d : ℝ) := by
    rcases le_total s_A s_B with hle | hle
    · have hle_r : (s_A : ℝ) ≤ (s_B : ℝ) := Nat.cast_le.mpr hle
      have hα_le_β : αr ≤ βr := div_le_div_of_nonneg_right hle_r hd_pos.le
      rw [min_eq_left hle, min_eq_left hα_le_β]
      dsimp [αr]
      exact (div_mul_cancel₀ (s_A : ℝ) hd_ne).symm
    · have hle_r : (s_B : ℝ) ≤ (s_A : ℝ) := Nat.cast_le.mpr hle
      have hβ_le_α : βr ≤ αr := div_le_div_of_nonneg_right hle_r hd_pos.le
      rw [min_eq_right hle, min_eq_right hβ_le_α]
      dsimp [βr]
      exact (div_mul_cancel₀ (s_B : ℝ) hd_ne).symm
  rw [hmin_eq] at hReal2
  linarith

end Theorem3Proofs

end BoundedArityDecoders

