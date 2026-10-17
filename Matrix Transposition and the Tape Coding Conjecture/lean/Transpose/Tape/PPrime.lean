import Transpose.Tape.PPrimeLocal
import Transpose.Tape.TheoremP

/-!
# Theorem P′ (data-dependent heads), also on a set of inputs (robust P′)

* `nodeBox`, `card_nodeBox_le` and `nodeCode_mem_nodeBox`: a node inside `[0, T)` has one of at
  most `structCount k T` node codes (by `abs_inPos_le`, `abs_workPos_le` and `outLen_le_self`,
  `Run.lean`).
* The Kraft count `kraft_group_on` over any set of inputs on which the machine is correct (at the end
  of its pass partition; no halting needed): within a class of inputs with equal codes, overwriting
  the unread comb bits (`overwrite`) is injective (`eq_of_overwrite_eq_on`). `kraft_group` is the
  case of all inputs.
* `theoremPprime_grouped_on` (robust P′_γ: correctness, the time bound and the pass partition only
  on a set `W` of co-entropy `≤ m`, each group paying `m` bits), from the Kraft count of each group,
  averaging over `W`, the per-run split `comb_split_le` and AM–GM (`pow_le_of_sum_pow_le`,
  `TheoremP.lean`); `theoremPprime_grouped_on_bits`. `theoremPprime_grouped` and
  `theoremPprime_grouped_bits` are their case `W` = all inputs, `m = 0`; then the corollaries
  (bits, per-`n`, power, the structure cost `γ` via `structBits_le`, greedy pass counts).
* Robust P′ on a set of co-entropy `m` (`2^L ≤ 2^m |W|`; correctness forces `W` to consist of matrix
  inputs): `theoremPprime_on` (`γ = 1`), `theoremPprime_on_bits`, `theoremPprime_on_div` and
  `theoremPprime_on_pow` (co-entropy `C n`), `theoremPprime_on_robust_gamma` and
  `theoremPprime_on_robust` (co-entropy `C n b`; if `(k+4)⌈log₂(2T+1)⌉ ≤ c′ b`, still
  `log_{k+1} n − O(log(C + c′))` passes: unlike Theorem P, the structure term is not `o(b)`, since
  `T ≥ L` makes it `≥ 2(k+4) log₂ n`), `theoremPprime_on_greedy`.
-/

namespace Transpose.Tape.Impl

open Transpose

variable {M : TM}

/-! ### Counting node codes -/

open Classical in
/-- The box of node codes of nodes inside `[0, T)`. -/
noncomputable def nodeBox (k T : ℕ) : Finset (NodeCode k) :=
  insert (none : NodeCode k) ((Finset.range T ×ˢ Finset.range T ×ˢ Finset.Icc (-(T : ℤ)) T ×ˢ
    Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(T : ℤ)) T) ×ˢ Finset.range T).map
      ⟨(some : ℕ × ℕ × ℤ × (Fin k → ℤ) × ℕ → NodeCode k), Option.some_injective _⟩)

theorem card_nodeBox_le (k T : ℕ) : (nodeBox k T).card ≤ structCount k T := by
  classical
  unfold nodeBox structCount
  refine le_trans (Finset.card_insert_le _ _) ?_
  rw [Finset.card_map]
  simp only [Finset.card_product, Finset.card_range, Int.card_Icc, Fintype.card_piFinset,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h : ((T : ℤ) + 1 - -(T : ℤ)).toNat = 2 * T + 1 := by omega
  rw [h]
  have hX : 1 ≤ (2 * T + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have h4 : T * T * T * (2 * T + 1) + 1 ≤ (2 * T + 1) ^ 4 := by
    have : (2 * T + 1) ^ 4 = 16 * (T * T * T * T) + 32 * (T * T * T) + 24 * (T * T) + 8 * T + 1 := by
      ring
    rw [this]
    nlinarith [Nat.zero_le (T * T * T * T), Nat.zero_le (T * T * T), Nat.zero_le (T * T)]
  calc T * (T * ((2 * T + 1) * ((2 * T + 1) ^ k * T))) + 1
      ≤ (T * T * T * (2 * T + 1) + 1) * (2 * T + 1) ^ k := by
        have : T * (T * ((2 * T + 1) * ((2 * T + 1) ^ k * T))) =
            T * T * T * (2 * T + 1) * (2 * T + 1) ^ k := by ring
        rw [this, add_mul, one_mul]
        omega
    _ ≤ (2 * T + 1) ^ 4 * (2 * T + 1) ^ k := Nat.mul_le_mul_right _ h4
    _ = (2 * T + 1) ^ (k + 4) := by ring

theorem nodeCode_mem_nodeBox {w : List Bool} {T : ℕ} {N : Finset ℕ} (hN : ∀ τ ∈ N, τ < T) :
    nodeCode M w N ∈ nodeBox M.k T := by
  classical
  unfold nodeCode nodeBox
  split_ifs with h
  · apply Finset.mem_insert_of_mem
    rw [Finset.mem_map]
    refine ⟨_, ?_, rfl⟩
    have ha := hN _ (N.min'_mem h)
    have he := hN _ (N.max'_mem h)
    have hi := abs_le.1 (abs_inPos_le (M := M) w (N.min' h))
    have hl := outLen_le_self (M := M) w (N.min' h)
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc, Fintype.mem_piFinset]
    refine ⟨ha, he, ⟨by omega, by omega⟩, fun t => ?_, by omega⟩
    have hw := abs_le.1 (abs_workPos_le (M := M) w (N.min' h) t)
    constructor <;> omega
  · exact Finset.mem_insert_self _ _

/-! ### The Kraft count -/

section Kraft

variable {n b : ℕ}

/-- Overwrite the positions of `F` in `v` by the indicator of `S`. -/
def overwrite {L : ℕ} (F : Finset ℕ) (v : Fin L → Bool) (S : Finset ℕ) : Fin L → Bool :=
  fun d => if d.val ∈ F then decide (d.val ∈ S) else v d

theorem overwrite_injOn {L : ℕ} {F : Finset ℕ} (hF : ∀ d ∈ F, d < L) (v : Fin L → Bool) :
    Set.InjOn (overwrite F v) (F.powerset : Set (Finset ℕ)) := by
  intro S hS S' hS' h
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hS hS'
  ext d
  constructor
  · intro hd
    have hdF := hS hd
    have := congrFun h ⟨d, hF d hdF⟩
    simp only [overwrite, hdF, ite_true, decide_eq_decide] at this
    exact this.1 hd
  · intro hd
    have hdF := hS' hd
    have := congrFun h ⟨d, hF d hdF⟩
    simp only [overwrite, hdF, ite_true, decide_eq_decide] at this
    exact this.2 hd

/-- The comb positions of `[o₁, o₂)` not read by the forest of `v`. -/
noncomputable def freeSet (M : TM) (r : ℕ) (pv : (Fin (n * n * b) → Bool) → ℕ → ℕ) (o₁ o₂ : ℕ)
    (v : Fin (n * n * b) → Bool) : Finset ℕ :=
  combSet n b o₁ o₂ \
    readSet (inTraj M (List.ofFn v)) (n * n * b) (forest M (List.ofFn v) (pv v) r o₁ o₂)

/-- The code of the forest of `[o₁, o₂)` on input `v`: the node and side codes at every
address. -/
noncomputable def groupCode (M : TM) (r : ℕ) (pv : (Fin (n * n * b) → Bool) → ℕ → ℕ) (o₁ o₂ : ℕ)
    (v : Fin (n * n * b) → Bool) :
    {α // α ∈ addresses M.k r} → NodeCode M.k × (Fin (M.q + 1) × (Fin M.k → Fin (M.g + 1))) :=
  fun α => (nodeCode M (List.ofFn v) (forestNode M (List.ofFn v) (pv v) o₁ o₂ α.1.1 α.1.2),
    sideCode M (List.ofFn v) (forestNode M (List.ofFn v) (pv v) o₁ o₂ α.1.1 α.1.2))

theorem freeSet_lt {r : ℕ} {pv : (Fin (n * n * b) → Bool) → ℕ → ℕ} {o₁ o₂ : ℕ}
    (v : Fin (n * n * b) → Bool) : ∀ d ∈ freeSet M r pv o₁ o₂ v, d < n * n * b := by
  intro d hd
  simp only [freeSet, combSet, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hd
  exact hd.1.1

/-- **Injectivity of overwriting within a code class**, for two inputs on which the machine is
correct. -/
theorem eq_of_overwrite_eq_on {r o₁ o₂ : ℕ}
    (Tv : (Fin (n * n * b) → Bool) → ℕ) (pv : (Fin (n * n * b) → Bool) → ℕ → ℕ)
    {v v' : Fin (n * n * b) → Bool}
    (hpv : PassPartition M (List.ofFn v) (Tv v) r (pv v))
    (hpv' : PassPartition M (List.ofFn v') (Tv v') r (pv v'))
    (hcv : ∃ A : Matrix, List.ofFn v = encode n b A ∧
      (run M (List.ofFn v) (Tv v)).outRev.reverse = encode n b (transpose A))
    (hcv' : ∃ A : Matrix, List.ofFn v' = encode n b A ∧
      (run M (List.ofFn v') (Tv v')).outRev.reverse = encode n b (transpose A))
    (hcode : groupCode M r pv o₁ o₂ v = groupCode M r pv o₁ o₂ v')
    {S S' : Finset ℕ}
    (h : overwrite (freeSet M r pv o₁ o₂ v) v S = overwrite (freeSet M r pv o₁ o₂ v') v' S') :
    v = v' := by
  classical
  have hout : ∀ d : Fin (n * n * b), d.val ∉ freeSet M r pv o₁ o₂ v →
      d.val ∉ freeSet M r pv o₁ o₂ v' → v d = v' d := by
    intro d hd hd'
    have := congrFun h d
    simp only [overwrite, hd, hd', ite_false] at this
    exact this
  have hcomb := forest_comb_agree_on hcv hcv' hpv hpv'
    (fun α hα => by
      have := congrFun hcode ⟨α, hα⟩
      simp only [groupCode, Prod.mk.injEq] at this
      exact this)
    (fun d hd hd' => by
      have hdL : d < n * n * b := Finset.mem_range.1 (Finset.mem_filter.1 hd).1
      rw [nth_ofFn v hdL, nth_ofFn v' hdL]
      congr 1
      apply hout ⟨d, hdL⟩
      · intro hF
        simp only [freeSet, Finset.mem_sdiff] at hF
        exact hF.2 hd
      · intro hF
        simp only [freeSet, Finset.mem_sdiff] at hF
        exact hF.2 hd')
  funext d
  by_cases hdc : d.val ∈ combSet n b o₁ o₂
  · have := hcomb d.val hdc
    rw [nth_ofFn v d.isLt, nth_ofFn v' d.isLt] at this
    exact Option.some.inj this
  · apply hout
    · intro hF
      simp only [freeSet, Finset.mem_sdiff] at hF
      exact hdc hF.1
    · intro hF
      simp only [freeSet, Finset.mem_sdiff] at hF
      exact hdc hF.1

/-- **The information count for data-dependent heads (Kraft form), on a set `V` of inputs** on which
the machine is correct: `Σ_{v ∈ V} 2^{|comb ∖ U(v)|} ≤ 2^L · ((2T+1)^{k+4} (q+1)(g+1)^k)^𝓗`. -/
theorem kraft_group_on {T r : ℕ} (V : Finset (Fin (n * n * b) → Bool))
    (Tv : (Fin (n * n * b) → Bool) → ℕ) (pv : (Fin (n * n * b) → Bool) → ℕ → ℕ)
    (hTv : ∀ v ∈ V, Tv v ≤ T)
    (hpv : ∀ v ∈ V, PassPartition M (List.ofFn v) (Tv v) r (pv v))
    (hcv : ∀ v ∈ V, ∃ A : Matrix, List.ofFn v = encode n b A ∧
      (run M (List.ofFn v) (Tv v)).outRev.reverse = encode n b (transpose A))
    {o₁ o₂ : ℕ} :
    ∑ v ∈ V, 2 ^ (combSet n b o₁ o₂ \ readSet (inTraj M (List.ofFn v)) (n * n * b)
        (forest M (List.ofFn v) (pv v) r o₁ o₂)).card ≤
      2 ^ (n * n * b) * (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ addrCount M.k r := by
  classical
  -- the box of codes
  let box : Finset ({α // α ∈ addresses M.k r} →
      NodeCode M.k × (Fin (M.q + 1) × (Fin M.k → Fin (M.g + 1)))) :=
    Fintype.piFinset (fun _ => nodeBox M.k T ×ˢ Finset.univ)
  have hbox : ∀ v ∈ V, groupCode M r pv o₁ o₂ v ∈ box := by
    intro v hv
    simp only [box, Fintype.mem_piFinset, Finset.mem_product, Finset.mem_univ, and_true]
    intro α
    apply nodeCode_mem_nodeBox
    intro τ hτ
    have hτF : τ ∈ forest M (List.ofFn v) (pv v) r o₁ o₂ := Finset.mem_biUnion.2 ⟨α.1, α.2, hτ⟩
    exact lt_of_lt_of_le (forest_subset (hpv v hv) o₁ o₂ τ hτF) (hTv v hv)
  have hcard_box : box.card ≤
      (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ addrCount M.k r := by
    simp only [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
      Fintype.card_coe, Finset.card_product, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
    have hc : (nodeBox M.k T).card * ((M.q + 1) * (M.g + 1) ^ M.k) ≤
        structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k) :=
      Nat.mul_le_mul_right _ (card_nodeBox_le M.k T)
    have hC : 1 ≤ structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k) :=
      Nat.one_le_iff_ne_zero.2 (by unfold structCount; positivity)
    calc _ ≤ (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ (addresses M.k r).card :=
          Nat.pow_le_pow_left hc _
      _ ≤ _ := Nat.pow_le_pow_right hC (card_addresses_le M.k r)
  -- each fiber contributes at most `2^L`
  have hfiber : ∀ c ∈ box, ∑ v ∈ V.filter (fun v => groupCode M r pv o₁ o₂ v = c),
      2 ^ (freeSet M r pv o₁ o₂ v).card ≤ 2 ^ (n * n * b) := by
    intro c _
    set Fib := V.filter (fun v => groupCode M r pv o₁ o₂ v = c) with hFib
    let N : (Fin (n * n * b) → Bool) → Finset (Fin (n * n * b) → Bool) := fun v =>
      (freeSet M r pv o₁ o₂ v).powerset.image (overwrite (freeSet M r pv o₁ o₂ v) v)
    have hN : ∀ v, (N v).card = 2 ^ (freeSet M r pv o₁ o₂ v).card := by
      intro v
      rw [Finset.card_image_of_injOn (overwrite_injOn (freeSet_lt v) v), Finset.card_powerset]
    have hdisj : (Fib : Set (Fin (n * n * b) → Bool)).PairwiseDisjoint N := by
      intro v hv v' hv' hne
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, hFib] at hv hv'
      rw [Function.onFun, Finset.disjoint_left]
      intro u hu hu'
      obtain ⟨S, -, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨S', -, hSS'⟩ := Finset.mem_image.1 hu'
      exact hne (eq_of_overwrite_eq_on Tv pv (hpv v hv.1)
        (hpv v' hv'.1) (hcv v hv.1) (hcv v' hv'.1) (hv.2.trans hv'.2.symm) hSS'.symm)
    calc ∑ v ∈ Fib, 2 ^ (freeSet M r pv o₁ o₂ v).card = ∑ v ∈ Fib, (N v).card :=
          Finset.sum_congr rfl (fun v _ => (hN v).symm)
      _ = (Fib.biUnion N).card := (Finset.card_biUnion hdisj).symm
      _ ≤ Fintype.card (Fin (n * n * b) → Bool) := Finset.card_le_univ _
      _ = 2 ^ (n * n * b) := by simp
  calc ∑ v ∈ V, 2 ^ (freeSet M r pv o₁ o₂ v).card
      = ∑ c ∈ box, ∑ v ∈ V.filter (fun v => groupCode M r pv o₁ o₂ v = c),
          2 ^ (freeSet M r pv o₁ o₂ v).card :=
        (Finset.sum_fiberwise_of_maps_to (fun v hv => hbox v hv) _).symm
    _ ≤ ∑ _c ∈ box, 2 ^ (n * n * b) := Finset.sum_le_sum hfiber
    _ = box.card * 2 ^ (n * n * b) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ addrCount M.k r * 2 ^ (n * n * b) :=
        Nat.mul_le_mul_right _ hcard_box
    _ = _ := Nat.mul_comm _ _

/-- **The information count for data-dependent heads (Kraft form).** -/
theorem kraft_group {T r : ℕ} (hcorr : Transposes M n b)
    (Tv : (Fin (n * n * b) → Bool) → ℕ) (pv : (Fin (n * n * b) → Bool) → ℕ → ℕ)
    (hTv : ∀ v, Tv v ≤ T) (hhalt : ∀ v, HaltsAt M (List.ofFn v) (Tv v))
    (hpv : ∀ v, PassPartition M (List.ofFn v) (Tv v) r (pv v)) {o₁ o₂ : ℕ} :
    ∑ v, 2 ^ (combSet n b o₁ o₂ \ readSet (inTraj M (List.ofFn v)) (n * n * b)
        (forest M (List.ofFn v) (pv v) r o₁ o₂)).card ≤
      2 ^ (n * n * b) * (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ addrCount M.k r :=
  kraft_group_on Finset.univ Tv pv (fun v _ => hTv v) (fun v _ => hpv v)
    (fun v _ => correct_of_transposes hcorr (ofFn_mem_matrixInputs v) (hhalt v))

end Kraft

/-! ### Theorem P′ -/

section PPrime

variable {n b T r : ℕ}

/-- **Theorem P′_γ on a set of co-entropy `≤ m`, log-free.** Every group pays `m` bits. -/
theorem theoremPprime_grouped_on {γ : ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    (hγ : 1 ≤ γ) {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    2 ^ (n * n * b) ≤
      2 ^ (numGroups n γ * m) * (2 ^ (addrCount M.k r * ((γ + 1) * n * b)) *
        (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ (numGroups n γ * addrCount M.k r)) := by
  classical
  have hW : W ⊆ matrixInputs n b := fun w hw => by
    obtain ⟨-, -, -, -, A, rfl, -⟩ := hrun w hw
    exact ⟨A, rfl⟩
  -- the inputs of `W` as vectors
  set V := (Finset.univ : Finset (Fin (n * n * b) → Bool)).filter (fun v => List.ofFn v ∈ W)
    with hV
  have hVcard : W.ncard = V.card := by
    rw [← ncard_ofFn_preimage hW, ← Set.ncard_coe_finset]
    congr 1
    ext v
    rw [Set.mem_ofPred_eq, Finset.mem_coe, hV, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩
  have hVne : V.Nonempty := by
    rw [← Finset.card_pos, ← hVcard]; exact ncard_pos_of_coentropy hco
  have hmem : ∀ v ∈ V, List.ofFn v ∈ W := fun v h => (Finset.mem_filter.1 h).2
  -- times, pass partitions and correctness on `W`
  have hrun' : ∀ v : Fin (n * n * b) → Bool, ∃ T' ≤ T, ∃ p : ℕ → ℕ, List.ofFn v ∈ W →
      PassPartition M (List.ofFn v) T' r p ∧
      ∃ A : Matrix, List.ofFn v = encode n b A ∧
        (run M (List.ofFn v) T').outRev.reverse = encode n b (transpose A) := by
    intro v
    by_cases hv : List.ofFn v ∈ W
    · obtain ⟨T', hT', p, h⟩ := hrun _ hv
      exact ⟨T', hT', p, fun _ => h⟩
    · exact ⟨0, Nat.zero_le _, fun _ => 0, fun h => absurd h hv⟩
  choose Tv hTv pv hv using hrun'
  set K := (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ addrCount M.k r with hK
  set G := numGroups n γ with hG
  -- the unread comb bits of group `s` on input `v`
  let mm : ℕ → (Fin (n * n * b) → Bool) → ℕ := fun s v =>
    (combSet n b (segLo n b γ s) (segHi n b γ s) \ readSet (inTraj M (List.ofFn v)) (n * n * b)
      (forest M (List.ofFn v) (pv v) r (segLo n b γ s) (segHi n b γ s))).card
  -- averaging the Kraft counts over `W`: some input of `W` has `Σ_s 2^{m_s} ≤ G K 2^m`
  have hsum : ∑ v ∈ V, ∑ s ∈ Finset.range G, 2 ^ mm s v ≤ ∑ _v ∈ V, G * (K * 2 ^ m) := by
    rw [Finset.sum_comm]
    calc ∑ s ∈ Finset.range G, ∑ v ∈ V, 2 ^ mm s v
        ≤ ∑ _s ∈ Finset.range G, 2 ^ (n * n * b) * K :=
          Finset.sum_le_sum (fun s _ => kraft_group_on V Tv pv (fun v _ => hTv v)
            (fun v h => (hv v (hmem v h)).1) (fun v h => (hv v (hmem v h)).2))
      _ = G * (2 ^ (n * n * b) * K) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ G * (2 ^ m * V.card * K) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (hVcard ▸ hco))
      _ = ∑ _v ∈ V, G * (K * 2 ^ m) := by rw [Finset.sum_const, smul_eq_mul]; ring
  obtain ⟨v₀, hv₀V, hv₀⟩ := Finset.exists_le_of_sum_le hVne hsum
  -- the comb split of `v₀`'s run and AM–GM
  calc _ ≤ _ := pow_le_of_sum_pow_le (fun s => mm s v₀)
        (comb_split_le (n := n) (b := b) (hv v₀ (hmem v₀ hv₀V)).1 hγ) hv₀
    _ = _ := by rw [mul_pow, hK, ← pow_mul, ← pow_mul]; ring

/-- **Theorem P′_γ, log-free**: the case `W` = all matrix inputs, `m = 0` of
`theoremPprime_grouped_on`. -/
theorem theoremPprime_grouped {γ : ℕ} (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p)
    (hγ : 1 ≤ γ) :
    2 ^ (n * n * b) ≤
      2 ^ (addrCount M.k r * ((γ + 1) * n * b)) *
        (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ (numGroups n γ * addrCount M.k r) := by
  have h := theoremPprime_grouped_on (m := 0) (W := matrixInputs n b)
    (fun w hw => by
      obtain ⟨T', hT', p, hh, hp⟩ := hrun w hw
      exact ⟨T', hT', p, hp, correct_of_transposes hcorr hw hh⟩) hγ
    (by rw [ncard_matrixInputs, pow_zero, one_mul])
  simpa using h

/-- `(2T+1)^{k+4} ≤ 2^{(k+4)⌈log₂(2T+1)⌉}`. -/
theorem structCount_le_pow (k T : ℕ) :
    structCount k T ≤ 2 ^ ((k + 4) * Nat.clog 2 (2 * T + 1)) := by
  unfold structCount
  calc (2 * T + 1) ^ (k + 4) ≤ (2 ^ Nat.clog 2 (2 * T + 1)) ^ (k + 4) :=
        Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _
    _ = _ := by rw [← pow_mul, Nat.mul_comm]

/-- **Theorem P′_γ on a set, bits form**:
`n² b ≤ ⌈n/γ⌉ m + 𝓗 ((γ+1) n b + ⌈n/γ⌉ (σ + (k+4)⌈log₂(2T+1)⌉))`. -/
theorem theoremPprime_grouped_on_bits {γ : ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    (hγ : 1 ≤ γ) {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    n * n * b ≤ numGroups n γ * m + addrCount M.k r * ((γ + 1) * n * b + numGroups n γ *
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1))) :=
  bits_of_logfree ((Nat.mul_le_mul (structCount_le_pow M.k T) (side_le_pow M)).trans_eq
    (by rw [← pow_add, Nat.add_comm])) (theoremPprime_grouped_on hrun hγ hco)

/-- **Theorem P′_γ, bits form**: the case `m = 0` of `theoremPprime_grouped_on_bits`. -/
theorem theoremPprime_grouped_bits {γ : ℕ} (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p)
    (hγ : 1 ≤ γ) :
    n * n * b ≤ addrCount M.k r * ((γ + 1) * n * b + numGroups n γ *
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1))) := by
  have h := theoremPprime_grouped_on_bits (m := 0) (W := matrixInputs n b)
    (fun w hw => by
      obtain ⟨T', hT', p, hh, hp⟩ := hrun w hw
      exact ⟨T', hT', p, hp, correct_of_transposes hcorr hw hh⟩) hγ
    (by rw [ncard_matrixInputs, pow_zero, one_mul])
  simpa using h

/-- **Theorem P′, log-free.** -/
theorem theoremPprime (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p) :
    2 ^ (n * n * b) ≤
      2 ^ (addrCount M.k r * (2 * n * b)) *
        (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ (n * addrCount M.k r) := by
  have := theoremPprime_grouped (γ := 1) hcorr hrun le_rfl
  simpa [numGroups_one] using this

/-- **Theorem P′, bits form.** -/
theorem theoremPprime_bits (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p) :
    n * n * b ≤ addrCount M.k r * (n * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1)))) := by
  have := theoremPprime_grouped_bits (γ := 1) hcorr hrun le_rfl
  rw [numGroups_one] at this
  calc n * n * b ≤ _ := this
    _ = _ := by ring

/-- **Theorem P′, per-`n` form.** -/
theorem theoremPprime_div (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p) :
    n * b ≤ addrCount M.k r * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1))) := by
  simpa using div_of_sq (X := 0) (by simpa using theoremPprime_bits hcorr hrun)

/-- The structure cost `(k+4)⌈log₂(2T+1)⌉` is at most
`γ = ⌈log₂ r⌉ + 2(k+2)⌈log₂(2T+3)⌉`. -/
theorem structBits_le (k T r : ℕ) :
    (k + 4) * Nat.clog 2 (2 * T + 1) ≤ Nat.clog 2 r + 2 * (k + 2) * Nat.clog 2 (2 * T + 3) := by
  have h1 : Nat.clog 2 (2 * T + 1) ≤ Nat.clog 2 (2 * T + 3) := Nat.clog_mono_right _ (by omega)
  have h2 : (k + 4) * Nat.clog 2 (2 * T + 1) ≤ 2 * (k + 2) * Nat.clog 2 (2 * T + 3) :=
    Nat.mul_le_mul (by omega) h1
  omega

/-- **Theorem P′ with the structure cost `γ = ⌈log₂ r⌉ + 2(k+2)⌈log₂(2T+3)⌉`.** -/
theorem theoremPprime_gamma (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p) :
    n * n * b ≤ addrCount M.k r * (n * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) +
        (Nat.clog 2 r + 2 * (M.k + 2) * Nat.clog 2 (2 * T + 3)))) + 1) :=
  (theoremPprime_bits hcorr hrun).trans (Nat.mul_le_mul_left _ (Nat.le_succ_of_le
    (Nat.mul_le_mul_left _ (by have := structBits_le M.k T r; omega))))

/-- **Theorem P′, power form.** -/
theorem theoremPprime_pow (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p) :
    M.k * (n * b) ≤ ((M.k + 1) ^ r - 1) * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1))) := by
  simpa using pow_of_div (X := 0) (by simpa using theoremPprime_div hcorr hrun)

/-- **Theorem P′ with greedy pass counts.** -/
theorem theoremPprime_greedy (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, HaltsAt M w T' ∧ greedyPasses M w T' ≤ r) :
    n * n * b ≤ addrCount M.k r * (n * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1)))) := by
  apply theoremPprime_bits hcorr
  intro w hw
  obtain ⟨T', hT', hh, hg⟩ := hrun w hw
  obtain ⟨p, hp⟩ := (passPartition_iff M w T' r).2 hg
  exact ⟨T', hT', p, hh, hp⟩

/-- **Theorem P′ covers Theorem P's machines.** -/
theorem theoremPprime_hyps_of_oblivious (hobl : ObliviousOn M (matrixInputs n b) T)
    {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) :
    ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p :=
  fun w hw => ⟨T, le_rfl, p, hobl.1 w hw, (passPartition_indep hobl hw₀ hw p).1 hp⟩

/-! ### Theorem P′ on a set of inputs (robust P′) -/

/-- **Theorem P′ on a set of co-entropy `≤ m`, log-free** (`γ = 1`). -/
theorem theoremPprime_on {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    2 ^ (n * n * b) ≤
      2 ^ (n * m) * (2 ^ (addrCount M.k r * (2 * n * b)) *
        (structCount M.k T * ((M.q + 1) * (M.g + 1) ^ M.k)) ^ (n * addrCount M.k r)) := by
  have := theoremPprime_grouped_on (γ := 1) hrun le_rfl hco
  simpa [numGroups_one] using this

/-- **Theorem P′ on a set, bits form**: `n² b ≤ n m + 𝓗 n (2b + σ + (k+4)⌈log₂(2T+1)⌉)`. -/
theorem theoremPprime_on_bits {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    n * n * b ≤ n * m + addrCount M.k r * (n * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1)))) := by
  have := theoremPprime_grouped_on_bits (γ := 1) hrun le_rfl hco
  rw [numGroups_one] at this
  calc n * n * b ≤ _ := this
    _ = _ := by ring

/-- **Theorem P′ on a set of co-entropy `≤ C n`, per-`n` form**:
`n b ≤ C n + 𝓗 (2b + σ + (k+4)⌈log₂(2T+1)⌉)`. -/
theorem theoremPprime_on_div {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {C : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * n) * W.ncard) :
    n * b ≤ C * n + addrCount M.k r * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1))) :=
  div_of_sq (theoremPprime_on_bits hrun hco)

/-- **Theorem P′ on a set of co-entropy `≤ C n`, power form**:
`k (n b) ≤ k C n + ((k+1)^r − 1)(2b + σ + (k+4)⌈log₂(2T+1)⌉)`. -/
theorem theoremPprime_on_pow {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {C : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * n) * W.ncard) :
    M.k * (n * b) ≤ M.k * (C * n) + ((M.k + 1) ^ r - 1) * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1))) :=
  pow_of_div (theoremPprime_on_div hrun hco)

/-- **Theorem P′ at the robust co-entropy level `C n b`, any grouping `γ`**:
`(γ − C) n² b ≤ γ C n b + 𝓗 (γ(γ+1) n b + (n + γ) σ′)`, `σ′ = σ + (k+4)⌈log₂(2T+1)⌉`. -/
theorem theoremPprime_on_robust_gamma {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {C γ : ℕ} (hγ : 1 ≤ γ) (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * (n * b)) * W.ncard) :
    (γ - C) * (n * n * b) ≤ γ * C * (n * b) + addrCount M.k r * (γ * (γ + 1) * (n * b) +
      (n + γ) * (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) +
        (M.k + 4) * Nat.clog 2 (2 * T + 1))) :=
  robust_arith_gamma (mul_numGroups_lt n hγ).le (theoremPprime_grouped_on_bits hrun hγ hco)

/-- **Theorem P′ at the robust co-entropy level `C n b`** (grouping `γ = 2C`):
`C n b ≤ 2C² b + 𝓗 (2C(2C+1) b + 2(σ + (k+4)⌈log₂(2T+1)⌉))`. -/
theorem theoremPprime_on_robust {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, PassPartition M w T' r p ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {C : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * (n * b)) * W.ncard) :
    C * (n * b) ≤ 2 * C * C * b + addrCount M.k r * (2 * C * (2 * C + 1) * b +
      2 * (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) +
        (M.k + 4) * Nat.clog 2 (2 * T + 1))) := by
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · simp
  exact robust_arith (mul_numGroups_lt n (by omega)).le
    (theoremPprime_grouped_on_bits (γ := 2 * C) hrun (by omega) hco)

/-- **Theorem P′ on a set, with greedy pass counts.** -/
theorem theoremPprime_on_greedy {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, greedyPasses M w T' ≤ r ∧
      ∃ A : Matrix, w = encode n b A ∧ (run M w T').outRev.reverse = encode n b (transpose A))
    {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    n * n * b ≤ n * m + addrCount M.k r * (n * (2 * b +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + (M.k + 4) * Nat.clog 2 (2 * T + 1)))) :=
  theoremPprime_on_bits (fun w hw => by
    obtain ⟨T', hT', hg, hc⟩ := hrun w hw
    obtain ⟨p, hp⟩ := (passPartition_iff M w T' r).2 hg
    exact ⟨T', hT', p, hp, hc⟩) hco

end PPrime

end Transpose.Tape.Impl
