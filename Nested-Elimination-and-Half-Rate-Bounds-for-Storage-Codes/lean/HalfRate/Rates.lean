import HalfRate.IndexCoding

/-!
# The guessing number, the broadcast rate and fractional clique covers

On a triangle-free graph of maximum degree three:
* `guessingNumberAt_le`, `guessingNumberAt_sq`, `guessingNumber_eq`: `gn(G, q) ≤ ν*` for every
  `q ≥ 2`, with equality for perfect squares, so `gn(G) = sup_q gn(G, q) = ν*`;
* `broadcastBits_ge`, `broadcastBits_even`, `tendsto_broadcastBits`: the least number `β_t` of
  bits of an index code over `{0,1}^t` satisfies `(|V| − ν*) t ≤ β_t`, with equality for even
  `t`, so the broadcast rate `lim β_t / t` is `|V| − ν*`;
* `fracCliqueCoverNumber_eq` (every graph): covering the vertices fractionally by vertices and
  edges costs exactly `|V| − ν*`. In a triangle-free graph the cliques are the vertices and the
  edges, so this is the fractional clique cover number.
-/

namespace HalfRate

open Finset MotionDepthCodes Filter Topology

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

section Transport

variable {N : V → Finset V}

omit [DecidableEq V] in
/-- Storage codes transport along a bijection of alphabets. -/
theorem isStorageCode_map_equiv {α β : Type*} [DecidableEq β] {C : Finset (V → α)}
    (hC : IsStorageCode N C) (e : α ≃ β) :
    IsStorageCode N (C.image (fun x => e ∘ x)) := by
  intro x' hx' y' hy' v hxy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hx'
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hy'
  have := hC x hx y hy v fun u hu => e.injective (hxy u hu)
  simp [Function.comp, this]

omit [DecidableEq V] in
/-- Storage codes transport along an injection of alphabets. -/
theorem isStorageCode_map_injective {α β : Type*} [DecidableEq β] {C : Finset (V → α)}
    (hC : IsStorageCode N C) (e : α → β) (he : Function.Injective e) :
    IsStorageCode N (C.image (fun x => e ∘ x)) := by
  intro x' hx' y' hy' v hxy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hx'
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hy'
  have := hC x hx y hy v fun u hu => he (hxy u hu)
  simp [Function.comp, this]

/-- Index codes transport along an injection of message sets. -/
noncomputable def IndexCode.ofInjective {α M M' : Type*} (c : IndexCode N α M) [Nonempty M]
    (e : M → M') (he : Function.Injective e) : IndexCode N α M' where
  enc x := e (c.enc x)
  dec v m x := c.dec v (Function.invFun e m) x
  dec_local v m x x' h := c.dec_local v _ x x' h
  correct x v := by
    simp only [Function.leftInverse_invFun he (c.enc x)]
    exact c.correct x v

/-- Index codes restrict to a smaller alphabet that embeds with a retraction. -/
def IndexCode.restrict {α α' M : Type*} (c : IndexCode N α' M) (e : α → α') (r : α' → α)
    (hre : ∀ a, r (e a) = a) : IndexCode N α M where
  enc x := c.enc (e ∘ x)
  dec v m x := r (c.dec v m (e ∘ x))
  dec_local v m x x' h := by
    show r (c.dec v m (e ∘ x)) = r (c.dec v m (e ∘ x'))
    rw [c.dec_local v m (e ∘ x) (e ∘ x') fun u hu => by simp [Function.comp, h u hu]]
  correct x v := by
    show r (c.dec v (c.enc (e ∘ x)) (e ∘ x)) = x v
    rw [c.correct (e ∘ x) v]
    exact hre (x v)

end Transport

section Guessing

/-- The guessing number `gn(G, q)`: the largest `log_q |C|` over storage codes for `G` over an
alphabet of `q` symbols. -/
noncomputable def guessingNumberAt (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) : ℝ :=
  sSup {w | ∃ C : Finset (V → Fin q), IsStorageCode (nbhd G) C ∧ Real.logb q C.card = w}

/-- The guessing number `gn(G) = sup_{q ≥ 2} gn(G, q)`. -/
noncomputable def guessingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ⨆ q : {q : ℕ // 2 ≤ q}, guessingNumberAt G q

theorem fracMatchingNumber_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ fracMatchingNumber G := by
  obtain ⟨D, -, -, -, -, heq, -, -⟩ := fracMatchingNumber_spec G
  rw [heq]; positivity

theorem logb_card_le_fracMatchingNumber (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3)
    {q : ℕ} (hq : 2 ≤ q) {C : Finset (V → Fin q)} (hC : IsStorageCode (nbhd G) C) :
    Real.logb q C.card ≤ fracMatchingNumber G := by
  have : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have h := log_card_le_fracMatchingNumber hcf hdeg hC
  rw [Fintype.card_fin] at h
  rw [Real.logb, div_le_iff₀ hlq]
  exact h

theorem guessingNumberAt_bdd (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) {q : ℕ}
    (hq : 2 ≤ q) :
    BddAbove {w | ∃ C : Finset (V → Fin q), IsStorageCode (nbhd G) C ∧ Real.logb q C.card = w} :=
  ⟨fracMatchingNumber G, by
    rintro w ⟨C, hC, rfl⟩
    exact logb_card_le_fracMatchingNumber hcf hdeg hq hC⟩

/-- **`gn(G, q) ≤ ν*(G)`** for every `q ≥ 2`. -/
theorem guessingNumberAt_le (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) {q : ℕ}
    (hq : 2 ≤ q) : guessingNumberAt G q ≤ fracMatchingNumber G :=
  csSup_le ⟨_, ∅, fun _ h => absurd h (notMem_empty _), rfl⟩ (by
    rintro w ⟨C, hC, rfl⟩
    exact logb_card_le_fracMatchingNumber hcf hdeg hq hC)

/-- **`gn(G, r²) = ν*(G)`** for every `r ≥ 2`. -/
theorem guessingNumberAt_sq (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) {r : ℕ}
    (hr : 2 ≤ r) : guessingNumberAt G (r ^ 2) = fracMatchingNumber G := by
  have hr2 : 2 ≤ r ^ 2 := by nlinarith
  refine le_antisymm (guessingNumberAt_le hcf hdeg hr2) ?_
  have : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  obtain ⟨C, hC, hge⟩ := exists_code_fracMatchingNumber (G := G) (Fin r)
  let e : Fin r × Fin r ≃ Fin (r ^ 2) := finProdFinEquiv.trans (finCongr (sq r).symm)
  have hC' := isStorageCode_map_equiv hC e
  have hcard : (C.image (fun x => e ∘ x)).card = C.card :=
    card_image_of_injective _ fun x y hxy => by
      funext v
      exact e.injective (congrFun hxy v)
  have hmem : Real.logb ((r ^ 2 : ℕ) : ℝ) ((C.image (fun x => e ∘ x)).card : ℝ) ∈
      {w | ∃ C : Finset (V → Fin (r ^ 2)), IsStorageCode (nbhd G) C ∧
        Real.logb ((r ^ 2 : ℕ) : ℝ) C.card = w} := ⟨_, hC', rfl⟩
  have h1 := le_csSup (guessingNumberAt_bdd hcf hdeg hr2) hmem
  have hlq : 0 < Real.log ((r ^ 2 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hr2)
  have h2 : fracMatchingNumber G ≤ Real.logb ((r ^ 2 : ℕ) : ℝ)
      ((C.image (fun x => e ∘ x)).card : ℝ) := by
    rw [hcard, Real.logb, le_div_iff₀ hlq]
    have hcardr : Fintype.card (Fin r × Fin r) = r ^ 2 := by simp [sq]
    rw [hcardr] at hge
    exact hge
  exact h2.trans h1

/-- `gn(G, q) ≥ ν* · log(r²) / log q` whenever `r² ≤ q`: the code over `[r] × [r]` embeds in `[q]`. -/
theorem guessingNumberAt_ge (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) {q r : ℕ}
    (hr : 1 ≤ r) (hrq : r ^ 2 ≤ q) (hq : 2 ≤ q) :
    fracMatchingNumber G * (Real.log ((r : ℝ) ^ 2) / Real.log q) ≤ guessingNumberAt G q := by
  have : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  obtain ⟨C, hC, hge⟩ := exists_code_fracMatchingNumber (G := G) (Fin r)
  let e : Fin r × Fin r → Fin q := fun p => Fin.castLE ((pow_two r) ▸ hrq) (finProdFinEquiv p)
  have he : Function.Injective e := (Fin.castLE_injective _).comp finProdFinEquiv.injective
  have hC' := isStorageCode_map_injective hC e he
  have hcard : (C.image (fun x => e ∘ x)).card = C.card :=
    card_image_of_injective _ fun x y hxy => funext fun v => he (congrFun hxy v)
  have hmem : Real.logb (q : ℝ) ((C.image (fun x => e ∘ x)).card : ℝ) ∈
      {w | ∃ C : Finset (V → Fin q), IsStorageCode (nbhd G) C ∧ Real.logb q C.card = w} :=
    ⟨_, hC', rfl⟩
  have h1 := le_csSup (guessingNumberAt_bdd hcf hdeg hq) hmem
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  refine le_trans ?_ h1
  have hcardr : Fintype.card (Fin r × Fin r) = r ^ 2 := by simp [sq]
  rw [hcardr] at hge
  push_cast at hge
  rw [hcard, Real.logb, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hge hlq.le

/-- **`gn(G, q) → ν*(G)` as `q → ∞`**, so the supremum `gn(G)` is also the limit. -/
theorem tendsto_guessingNumberAt (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    Tendsto (fun q : ℕ => guessingNumberAt G q) atTop (𝓝 (fracMatchingNumber G)) := by
  have hν := fracMatchingNumber_nonneg G
  have hlo : ∀ᶠ q : ℕ in atTop,
      fracMatchingNumber G * (1 - Real.log 4 / Real.log q) ≤ guessingNumberAt G q := by
    filter_upwards [eventually_ge_atTop 4] with q hq
    have hr2 : 2 ≤ Nat.sqrt q := Nat.le_sqrt'.mpr (by norm_num; omega)
    have hrq : Nat.sqrt q ^ 2 ≤ q := Nat.sqrt_le' q
    have hq' : q < (Nat.sqrt q + 1) ^ 2 := Nat.lt_succ_sqrt' q
    have h4 : q ≤ 4 * Nat.sqrt q ^ 2 := by nlinarith
    have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
    have hlog : Real.log q - Real.log 4 ≤ Real.log ((Nat.sqrt q : ℝ) ^ 2) := by
      have h := Real.log_le_log (by exact_mod_cast (by omega : 0 < q))
        (show (q : ℝ) ≤ 4 * (Nat.sqrt q : ℝ) ^ 2 by exact_mod_cast h4)
      rw [Real.log_mul (by norm_num) (by positivity)] at h
      linarith
    have hfrac : 1 - Real.log 4 / Real.log q ≤ Real.log ((Nat.sqrt q : ℝ) ^ 2) / Real.log q := by
      rw [one_sub_div hlq.ne']
      exact div_le_div_of_nonneg_right hlog hlq.le
    exact (mul_le_mul_of_nonneg_left hfrac hν).trans
      (guessingNumberAt_ge hcf hdeg (by omega) hrq (by omega))
  have hhi : ∀ᶠ q : ℕ in atTop, guessingNumberAt G q ≤ fracMatchingNumber G := by
    filter_upwards [eventually_ge_atTop 2] with q hq
    exact guessingNumberAt_le hcf hdeg hq
  have hlim : Tendsto (fun q : ℕ => fracMatchingNumber G * (1 - Real.log 4 / Real.log q)) atTop
      (𝓝 (fracMatchingNumber G)) := by
    have hlog : Tendsto (fun q : ℕ => Real.log q) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun q : ℕ => Real.log 4 / Real.log q) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    simpa using (tendsto_const_nhds (x := fracMatchingNumber G)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub h0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlo hhi

/-- **The guessing number is the fractional matching number** on triangle-free graphs of maximum
degree three. -/
theorem guessingNumber_eq (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    guessingNumber G = fracMatchingNumber G := by
  have hbdd : BddAbove (Set.range fun q : {q : ℕ // 2 ≤ q} => guessingNumberAt G q) :=
    ⟨fracMatchingNumber G, by
      rintro _ ⟨q, rfl⟩
      exact guessingNumberAt_le hcf hdeg q.2⟩
  have : Nonempty {q : ℕ // 2 ≤ q} := ⟨⟨2, le_rfl⟩⟩
  refine le_antisymm (ciSup_le fun q => guessingNumberAt_le hcf hdeg q.2) ?_
  have h4 := le_ciSup hbdd ⟨2 ^ 2, by norm_num⟩
  rw [guessingNumberAt_sq hcf hdeg le_rfl] at h4
  exact h4

end Guessing

section Broadcast

/-- `β_t`: the least number of bits of an index code for `G` over the alphabet `{0,1}^t`. -/
noncomputable def broadcastBits (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) : ℕ :=
  sInf {n | Nonempty (IndexCode (nbhd G) (Fin t → Bool) (Fin n → Bool))}

theorem broadcastBits_nonempty (t : ℕ) :
    {n | Nonempty (IndexCode (nbhd G) (Fin t → Bool) (Fin n → Bool))}.Nonempty := by
  let c : IndexCode (nbhd G) (Fin t → Bool) (V → Fin t → Bool) :=
    { enc := id, dec := fun v m _ => m v, dec_local := fun _ _ _ _ _ => rfl,
      correct := fun _ _ => rfl }
  have hcard : Fintype.card (V → Fin t → Bool) = Fintype.card (Fin (t * Fintype.card V) → Bool) := by
    simp [Fintype.card_bool, Fintype.card_fin, ← pow_mul]
  have : Nonempty (V → Fin t → Bool) := ⟨fun _ _ => false⟩
  exact ⟨_, ⟨c.ofInjective (Fintype.equivOfCardEq hcard) (Fintype.equivOfCardEq hcard).injective⟩⟩

/-- **The converse.** `(|V| − ν*) t ≤ β_t`. -/
theorem broadcastBits_ge (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) (t : ℕ) :
    ((Fintype.card V : ℝ) - fracMatchingNumber G) * t ≤ broadcastBits G t := by
  obtain ⟨c⟩ := Nat.sInf_mem (broadcastBits_nonempty (G := G) t)
  have h := log_card_message_ge hcf hdeg c
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow] at h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold broadcastBits
  nlinarith

/-- `β_t ≤ β_{t+1}`: pad each symbol with one bit. -/
theorem broadcastBits_le_succ (t : ℕ) : broadcastBits G t ≤ broadcastBits G (t + 1) := by
  obtain ⟨c⟩ := Nat.sInf_mem (broadcastBits_nonempty (G := G) (t + 1))
  apply Nat.sInf_le
  refine ⟨c.restrict (fun a i => if h : i.val < t then a ⟨i, h⟩ else false)
    (fun b i => b i.castSucc) fun a => ?_⟩
  funext i
  simp

/-- The achievability for even `t`: `β_{2s} ≤ (|V| − ν*) 2s`, on every graph. -/
theorem broadcastBits_even_le (s : ℕ) :
    (broadcastBits G (2 * s) : ℝ) ≤ ((Fintype.card V : ℝ) - fracMatchingNumber G) * (2 * s) := by
  obtain ⟨T, c, hlog⟩ := exists_indexCode (G := G) (Fin s → ZMod 2)
  have hβ : Fintype.card (Fin s → ZMod 2) = 2 ^ s := by simp [ZMod.card]
  set n₀ := s * Fintype.card V + s * Fintype.card {v : V // v ∉ T}
  have hM : Fintype.card ((V → Fin s → ZMod 2) × ({v : V // v ∉ T} → Fin s → ZMod 2)) =
      Fintype.card (Fin n₀ → Bool) := by
    simp only [Fintype.card_prod, Fintype.card_fun, hβ, Fintype.card_bool, Fintype.card_fin, n₀,
      pow_add, ← pow_mul]
  have hA : Fintype.card (Fin (2 * s) → Bool) = Fintype.card ((Fin s → ZMod 2) × (Fin s → ZMod 2)) := by
    simp only [Fintype.card_prod, hβ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      ← pow_add, two_mul]
  have : Nonempty ((V → Fin s → ZMod 2) × ({v : V // v ∉ T} → Fin s → ZMod 2)) :=
    ⟨(fun _ _ => 0, fun _ _ => 0)⟩
  let eM := Fintype.equivOfCardEq hM
  let eA := Fintype.equivOfCardEq hA
  have hmem : n₀ ∈ {n | Nonempty (IndexCode (nbhd G) (Fin (2 * s) → Bool) (Fin n → Bool))} :=
    ⟨(c.ofInjective eM eM.injective).restrict eA eA.symm fun a => eA.symm_apply_apply a⟩
  have hle : broadcastBits G (2 * s) ≤ n₀ := Nat.sInf_le hmem
  have hn₀ : (n₀ : ℝ) = ((Fintype.card V : ℝ) - fracMatchingNumber G) * (2 * s) := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hM' : Fintype.card ((V → Fin s → ZMod 2) × ({v : V // v ∉ T} → Fin s → ZMod 2)) =
        2 ^ n₀ := by rw [hM]; simp
    have hB' : Fintype.card ((Fin s → ZMod 2) × (Fin s → ZMod 2)) = 2 ^ (2 * s) := by
      rw [← hA]; simp
    rw [hM', hB'] at hlog
    push_cast at hlog
    rw [Real.log_pow, Real.log_pow] at hlog
    have : (n₀ : ℝ) * Real.log 2 = ((Fintype.card V : ℝ) - fracMatchingNumber G) * (2 * s) *
        Real.log 2 := by
      rw [hlog]; push_cast; ring
    exact mul_right_cancel₀ hl2.ne' this
  calc (broadcastBits G (2 * s) : ℝ) ≤ n₀ := by exact_mod_cast hle
    _ = _ := hn₀

/-- **`β_{2s} = (|V| − ν*) 2s`** on triangle-free graphs of maximum degree three. -/
theorem broadcastBits_even (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) (s : ℕ) :
    (broadcastBits G (2 * s) : ℝ) = ((Fintype.card V : ℝ) - fracMatchingNumber G) * (2 * s) := by
  refine le_antisymm (broadcastBits_even_le s) ?_
  have := broadcastBits_ge hcf hdeg (2 * s)
  push_cast at this
  exact this

theorem fracMatchingNumber_le_card (G : SimpleGraph V) [DecidableRel G.Adj] :
    fracMatchingNumber G ≤ Fintype.card V := by
  obtain ⟨D, -, -, -, -, heq, -, -⟩ := fracMatchingNumber_spec G
  rw [heq]
  have : (D.card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ D
  linarith

/-- **The broadcast rate** `lim_t β_t / t` is `|V| − ν*` on triangle-free graphs of maximum degree
three. -/
theorem tendsto_broadcastBits (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    Tendsto (fun t => (broadcastBits G t : ℝ) / t) atTop
      (𝓝 ((Fintype.card V : ℝ) - fracMatchingNumber G)) := by
  have hb : 0 ≤ (Fintype.card V : ℝ) - fracMatchingNumber G := by
    have := fracMatchingNumber_le_card G
    have := fracMatchingNumber_nonneg G
    linarith
  have hupper : ∀ t : ℕ, (broadcastBits G t : ℝ) ≤
      ((Fintype.card V : ℝ) - fracMatchingNumber G) * (t + 1) := by
    intro t
    rcases Nat.even_or_odd t with ⟨s, hs⟩ | ⟨s, hs⟩
    · have ht : t = 2 * s := by omega
      subst ht
      rw [broadcastBits_even hcf hdeg s]
      push_cast
      nlinarith
    · have h1 := broadcastBits_le_succ (G := G) t
      have h2 := broadcastBits_even hcf hdeg (s + 1)
      have ht1 : 2 * (s + 1) = t + 1 := by omega
      rw [ht1] at h2
      have hcast : (2 * ((s + 1 : ℕ) : ℝ)) = (t : ℝ) + 1 := by exact_mod_cast ht1
      rw [hcast] at h2
      have h1' : (broadcastBits G t : ℝ) ≤ broadcastBits G (t + 1) := by exact_mod_cast h1
      rw [h2] at h1'
      exact h1'
  have hlo : ∀ᶠ t : ℕ in atTop, (Fintype.card V : ℝ) - fracMatchingNumber G ≤
      (broadcastBits G t : ℝ) / t := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    rw [le_div_iff₀ htR]
    exact broadcastBits_ge hcf hdeg t
  have hhi : ∀ᶠ t : ℕ in atTop, (broadcastBits G t : ℝ) / t ≤
      ((Fintype.card V : ℝ) - fracMatchingNumber G) * (1 + 1 / t) := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    rw [div_le_iff₀ htR]
    calc (broadcastBits G t : ℝ) ≤ ((Fintype.card V : ℝ) - fracMatchingNumber G) * (t + 1) :=
          hupper t
      _ = ((Fintype.card V : ℝ) - fracMatchingNumber G) * (1 + 1 / t) * t := by field_simp
  have hlim : Tendsto (fun t : ℕ => ((Fintype.card V : ℝ) - fracMatchingNumber G) *
      (1 + 1 / (t : ℝ))) atTop (𝓝 ((Fintype.card V : ℝ) - fracMatchingNumber G)) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := (Fintype.card V : ℝ) - fracMatchingNumber G)).mul this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hlo hhi

end Broadcast

section Covers

/-- A fractional cover of the vertices by vertices and edges: vertex weights `yv` and symmetric
edge weights `ye`, covering every vertex at least once. -/
structure IsFracCover (G : SimpleGraph V) (yv : V → ℝ) (ye : V → V → ℝ) : Prop where
  nonneg_v : ∀ v, 0 ≤ yv v
  nonneg_e : ∀ u v, 0 ≤ ye u v
  symm : ∀ u v, ye u v = ye v u
  adj : ∀ u v, ¬ G.Adj u v → ye u v = 0
  cover : ∀ v, 1 ≤ yv v + ∑ u, ye v u

/-- The weight of a cover, each edge counted once. -/
noncomputable def coverWeight (yv : V → ℝ) (ye : V → V → ℝ) : ℝ :=
  ∑ v, yv v + (∑ u, ∑ v, ye u v) / 2

/-- The fractional clique cover number of a triangle-free graph (its cliques are the vertices and
the edges). -/
noncomputable def fracCliqueCoverNumber (G : SimpleGraph V) : ℝ :=
  sInf {w | ∃ yv ye, IsFracCover G yv ye ∧ coverWeight yv ye = w}

/-- **Fractional covers by vertices and edges cost exactly `|V| − ν*`**, on every graph. -/
theorem fracCliqueCoverNumber_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    fracCliqueCoverNumber G = Fintype.card V - fracMatchingNumber G := by
  obtain ⟨D, -, S, -, -, heq, hS, hgreat⟩ := fracMatchingNumber_spec G
  have hdisj := disjoint_isolatedOut (G := G) S
  -- the dual solution read off the barrier set `S`
  let z : V → ℝ := fun v => if v ∈ isolatedOut G S then 1 else if v ∈ S then 0 else 1 / 2
  have hz0 : ∀ v, 0 ≤ z v := fun v => by simp only [z]; split_ifs <;> norm_num
  have hz1 : ∀ v, z v ≤ 1 := fun v => by simp only [z]; split_ifs <;> norm_num
  have hzadj : ∀ u v, G.Adj u v → z u + z v ≤ 1 := by
    intro u v huv
    have hiso : ∀ a b, G.Adj a b → a ∈ isolatedOut G S → b ∈ S := fun a b hab ha =>
      (mem_filter.mp ha).2.2 (by simpa [nbhd] using hab)
    simp only [z]
    by_cases hu : u ∈ isolatedOut G S
    · have hv : v ∈ S := hiso u v huv hu
      have hv' : v ∉ isolatedOut G S := fun h => Finset.disjoint_left.mp hdisj hv h
      simp [hu, hv, hv']
    · by_cases hv : v ∈ isolatedOut G S
      · have hu' : u ∈ S := hiso v u huv.symm hv
        simp [hu, hv, hu']
      · simp only [hu, hv, ↓reduceIte]
        split_ifs <;> norm_num
  have hzv : ∀ v, z v = (if v ∈ isolatedOut G S then (1 : ℝ) else 0) +
      1 / 2 * (if v ∈ univ \ (S ∪ isolatedOut G S) then (1 : ℝ) else 0) := by
    intro v
    have hd : v ∈ isolatedOut G S → v ∉ S := fun h hS' => Finset.disjoint_left.mp hdisj hS' h
    simp only [z]
    by_cases h1 : v ∈ isolatedOut G S
    · simp [h1, hd h1]
    · by_cases h2 : v ∈ S <;> simp [h1, h2]
  have hzsum : ∑ v, z v = Fintype.card V - fracMatchingNumber G := by
    simp only [hzv, sum_add_distrib, ← mul_sum, sum_boole, filter_mem_eq_inter, univ_inter]
    rw [card_sdiff_isolatedOut, heq]
    linarith
  have hdual : ∀ yv ye, IsFracCover G yv ye →
      Fintype.card V - fracMatchingNumber G ≤ coverWeight yv ye := by
    intro yv ye hc
    rw [← hzsum]
    have h1 : ∑ v, z v ≤ ∑ v, z v * (yv v + ∑ u, ye v u) :=
      sum_le_sum fun v _ => le_mul_of_one_le_right (hz0 v) (hc.cover v)
    have h2 : ∑ v, z v * yv v ≤ ∑ v, yv v :=
      sum_le_sum fun v _ => mul_le_of_le_one_left (hc.nonneg_v v) (hz1 v)
    have hswap : ∑ v, ∑ u, z v * ye v u = ∑ v, ∑ u, z u * ye v u := by
      rw [sum_comm]
      exact sum_congr rfl fun v _ => sum_congr rfl fun u _ => by rw [hc.symm u v]
    have h3 : 2 * ∑ v, ∑ u, z v * ye v u ≤ ∑ v, ∑ u, ye v u := by
      have h2s : 2 * ∑ v, ∑ u, z v * ye v u = ∑ v, ∑ u, (z v + z u) * ye v u := by
        rw [two_mul]
        nth_rewrite 2 [hswap]
        rw [← sum_add_distrib]
        exact sum_congr rfl fun v _ => by rw [← sum_add_distrib]; exact sum_congr rfl fun u _ => by ring
      rw [h2s]
      refine sum_le_sum fun v _ => sum_le_sum fun u _ => ?_
      by_cases hvu : G.Adj v u
      · exact mul_le_of_le_one_left (hc.nonneg_e v u) (hzadj v u hvu)
      · rw [hc.adj v u hvu]; simp
    have hexp : ∑ v, z v * (yv v + ∑ u, ye v u) = ∑ v, z v * yv v + ∑ v, ∑ u, z v * ye v u := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun v _ => by rw [mul_add, mul_sum]
    unfold coverWeight
    linarith
  obtain ⟨⟨y, hy, hyw⟩, -⟩ := hgreat
  have hmem : (Fintype.card V : ℝ) - fracMatchingNumber G ∈
      {w | ∃ yv ye, IsFracCover G yv ye ∧ coverWeight yv ye = w} := by
    refine ⟨fun v => 1 - ∑ u, y v u, y, ⟨fun v => by linarith [hy.le_one v], hy.nonneg, hy.symm,
      hy.adj, fun v => by linarith⟩, ?_⟩
    unfold coverWeight
    rw [← hyw]
    unfold fracWeight
    rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
    ring
  refine le_antisymm (csInf_le ⟨Fintype.card V - fracMatchingNumber G, ?_⟩ hmem) (le_csInf ⟨_, hmem⟩ ?_)
  · rintro w ⟨yv, ye, hc, rfl⟩
    exact hdual yv ye hc
  · rintro w ⟨yv, ye, hc, rfl⟩
    exact hdual yv ye hc

end Covers

end HalfRate
