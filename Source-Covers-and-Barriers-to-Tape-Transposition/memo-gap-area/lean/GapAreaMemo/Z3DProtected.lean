import GapAreaMemo.Z3DSteps

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: protected families and the hop tail

Every core family is the upper or lower family of a bank zigzag
(`core_bank_cases`) and has the height of that zigzag as its hop count
(`famA_card`, `famB_card`, `famC_card`). At most `16 · 2^ℓ - 6` core families
have `2^(n - 2ℓ - 2)` hops or more (`card_big_le`), so every hop ordering
places all of them among its first `R ≥ 16 · 2^ℓ` families: the bank-A and
bank-B families of level at most `ℓ` and the bank-C families of level at most
`ℓ + 1` are protected (`famA_protected`, `famB_protected`, `famC_protected`).
A selected prefix survives every admissible phase of a longer prefix
(`SortedCore.prefix_retained`). The bank-A upper families of the dyadic level
`⌊log₂ R⌋ + 2` leave a hop tail of at least `1 / (32 R)` beyond rank `R`
(`hop_tail_ge`), already before rank `64 R` (`hop_tail_ge_of_le`). The family at
rank `i` of a hop ordering has at most `512 L / (i + 1)²` hops (`hop_envelope`).
-/

namespace SourceCovers.SortedCore

open Finset

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K₀ : Finset (ActualFamily xs T)} (O : SortedCore K₀)

/-- A family whose competitors (all families with at least as many hops) lie in a set of fewer
than `R` families is among the first `R` families of every hop ordering. -/
theorem mem_selectedPrefix_of_card_lt {R : ℕ} {B : Finset (ActualFamily xs T)}
    (hB : B.card < R) {G : ActualFamily xs T} (hG : G ∈ K₀)
    (hsub : ∀ H ∈ K₀, G.hops.card ≤ H.hops.card → H ∈ B) : G ∈ O.selectedPrefix R := by
  obtain ⟨p, hp, hpG⟩ := List.mem_iff_getElem.mp (O.mem_families.mpr hG)
  by_contra hout
  have hRp : R ≤ p := by
    by_contra h
    exact hout (List.mem_toFinset.mpr (List.mem_take_iff_getElem.mpr ⟨p, by omega, hpG⟩))
  have hsubB : O.selectedPrefix (p + 1) ⊆ B := by
    intro H hH
    have hHK : H ∈ K₀ := O.selectedPrefix_subset _ hH
    obtain ⟨i, hi, hiH⟩ := List.mem_take_iff_getElem.mp (List.mem_toFinset.mp hH)
    have hiK : i < O.families.length := by omega
    apply hsub H hHK
    subst hiH hpG
    rcases Nat.lt_or_ge i p with hip | hip
    · exact O.hop_sorted.rel_get_of_lt (a := ⟨i, hiK⟩) (b := ⟨p, hp⟩) hip
    · obtain rfl : i = p := by omega
      exact le_rfl
  have hcard := card_le_card hsubB
  rw [O.selectedPrefix_card] at hcard
  have := O.length_eq_card
  omega

/-- The families of a shorter prefix survive every admissible phase of a longer prefix. -/
theorem prefix_retained {R J M ρ : ℕ} (hRJ : R ≤ J)
    (hρ : ρ ∈ admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M)
    {G : ActualFamily xs T} (hG : G ∈ O.selectedPrefix R) :
    G ∈ retainedCore (O.selectedPrefix J) M ρ := by
  have hq : (⟨G, O.selectedPrefix_mono hRJ hG⟩ : CoreFamily (O.selectedPrefix J)) ∈
      O.subprefix J R := by
    simp only [subprefix, mem_filter, mem_univ, true_and]
    exact hG
  unfold retainedCore
  exact mem_image.mpr ⟨_, protected_survives hρ hq, rfl⟩

end SourceCovers.SortedCore

namespace SourceCovers.Z3D.Index

open Finset StairFamilies

variable (P : Index)

/-! ### Hop counts -/

theorem famA_card {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ P.K) (up : Bool) :
    (P.famA k up).hops.card = P.a k := by
  obtain ⟨⟨_, hP⟩, ⟨_, hQ⟩⟩ := P.famA_sched h1 h2
  cases up
  · exact hQ.card
  · exact hP.card

theorem famB_card {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ P.K) (up : Bool) :
    (P.famB k up).hops.card = P.a k := by
  obtain ⟨⟨_, hP⟩, ⟨_, hQ⟩⟩ := P.famB_sched h1 h2
  cases up
  · exact hQ.card
  · exact hP.card

theorem famC_card {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ P.K) (up : Bool) :
    (P.famC k up).hops.card = P.cc k := by
  obtain ⟨⟨_, hP⟩, ⟨_, hQ⟩⟩ := P.famC_sched h1 h2
  have e : (P.segC (k - 1)).h = P.cc k := by
    show P.cc (k - 1 + 1) = P.cc k
    rw [Nat.sub_add_cancel h1]
  cases up
  · rw [hQ.card, e]
  · rw [hP.card, e]

/-! ### Every core family is a bank family -/

theorem stairX_upper_cases {j : ℕ} (hj : j < P.nX) :
    ∃ k, 1 ≤ k ∧ k ≤ P.K ∧ (P.stairX.upper j hj = P.famA k true ∨
      P.stairX.upper j hj = P.famB k true ∨ P.stairX.upper j hj = P.famC k true) := by
  have hj' : j < 3 * P.NX := hj
  have hK := P.K_eq_NX
  have hN := P.NX_pos
  rcases Nat.lt_or_ge j P.NX with h | h
  · refine ⟨2 * j + 1, by omega, by omega, Or.inr (Or.inr ?_)⟩
    unfold famC
    simp only [dite_eq_left (show 1 ≤ 2 * j + 1 ∧ 2 * j + 1 ≤ P.K by omega),
      dite_eq_left (show (2 * j + 1) % 2 = 1 by omega), ite_true]
    exact (P.stairX.upper_inj _ _).mpr (by omega)
  rcases Nat.lt_or_ge j (2 * P.NX) with h' | h'
  · refine ⟨P.K - 2 * (j - P.NX), by omega, by omega, Or.inr (Or.inl ?_)⟩
    unfold famB
    simp only [dite_eq_left (show 1 ≤ P.K - 2 * (j - P.NX) ∧ P.K - 2 * (j - P.NX) ≤ P.K by omega),
      dite_eq_left (show (P.K - 2 * (j - P.NX)) % 2 = 1 by omega), ite_true]
    exact (P.stairX.upper_inj _ _).mpr (by omega)
  · refine ⟨P.K - 2 * (j - 2 * P.NX), by omega, by omega, Or.inl ?_⟩
    unfold famA
    simp only [dite_eq_left (show 1 ≤ P.K - 2 * (j - 2 * P.NX) ∧
        P.K - 2 * (j - 2 * P.NX) ≤ P.K by omega),
      dite_eq_left (show (P.K - 2 * (j - 2 * P.NX)) % 2 = 1 by omega), ite_true]
    exact (P.stairX.upper_inj _ _).mpr (by omega)

theorem stairX_lower_cases {j : ℕ} (hj : j < P.nX) :
    ∃ k, 1 ≤ k ∧ k ≤ P.K ∧ (P.stairX.lower j hj = P.famA k false ∨
      P.stairX.lower j hj = P.famB k false ∨ P.stairX.lower j hj = P.famC k false) := by
  have hj' : j < 3 * P.NX := hj
  have hK := P.K_eq_NX
  have hN := P.NX_pos
  rcases Nat.lt_or_ge j P.NX with h | h
  · refine ⟨2 * j + 1, by omega, by omega, Or.inr (Or.inr ?_)⟩
    unfold famC
    simp only [dite_eq_left (show 1 ≤ 2 * j + 1 ∧ 2 * j + 1 ≤ P.K by omega),
      dite_eq_left (show (2 * j + 1) % 2 = 1 by omega), Bool.false_eq_true, ite_false]
    exact (P.stairX.lower_inj _ _).mpr (by omega)
  rcases Nat.lt_or_ge j (2 * P.NX) with h' | h'
  · refine ⟨P.K - 2 * (j - P.NX), by omega, by omega, Or.inr (Or.inl ?_)⟩
    unfold famB
    simp only [dite_eq_left (show 1 ≤ P.K - 2 * (j - P.NX) ∧ P.K - 2 * (j - P.NX) ≤ P.K by omega),
      dite_eq_left (show (P.K - 2 * (j - P.NX)) % 2 = 1 by omega), Bool.false_eq_true,
      ite_false]
    exact (P.stairX.lower_inj _ _).mpr (by omega)
  · refine ⟨P.K - 2 * (j - 2 * P.NX), by omega, by omega, Or.inl ?_⟩
    unfold famA
    simp only [dite_eq_left (show 1 ≤ P.K - 2 * (j - 2 * P.NX) ∧
        P.K - 2 * (j - 2 * P.NX) ≤ P.K by omega),
      dite_eq_left (show (P.K - 2 * (j - 2 * P.NX)) % 2 = 1 by omega), Bool.false_eq_true,
      ite_false]
    exact (P.stairX.lower_inj _ _).mpr (by omega)

theorem stairY_upper_cases {j : ℕ} (hj : j < P.nY) :
    ∃ k, 1 ≤ k ∧ k ≤ P.K ∧ (P.stairY.upper j hj = P.famA k true ∨
      P.stairY.upper j hj = P.famB k true ∨ P.stairY.upper j hj = P.famC k true) := by
  have hj' : j < 3 * P.NY := hj
  have hK := P.K_eq_NY
  have hN := P.NY_pos
  rcases Nat.lt_or_ge j P.NY with h | h
  · refine ⟨2 * j + 2, by omega, by omega, Or.inr (Or.inr ?_)⟩
    unfold famC
    simp only [dite_eq_left (show 1 ≤ 2 * j + 2 ∧ 2 * j + 2 ≤ P.K by omega),
      dite_eq_right (show ¬(2 * j + 2) % 2 = 1 by omega), ite_true]
    exact (P.stairY.upper_inj _ _).mpr (by omega)
  rcases Nat.lt_or_ge j (2 * P.NY) with h' | h'
  · refine ⟨P.K - 1 - 2 * (j - P.NY), by omega, by omega, Or.inr (Or.inl ?_)⟩
    unfold famB
    simp only [dite_eq_left (show 1 ≤ P.K - 1 - 2 * (j - P.NY) ∧
        P.K - 1 - 2 * (j - P.NY) ≤ P.K by omega),
      dite_eq_right (show ¬(P.K - 1 - 2 * (j - P.NY)) % 2 = 1 by omega), ite_true]
    exact (P.stairY.upper_inj _ _).mpr (by omega)
  · refine ⟨P.K - 1 - 2 * (j - 2 * P.NY), by omega, by omega, Or.inl ?_⟩
    unfold famA
    simp only [dite_eq_left (show 1 ≤ P.K - 1 - 2 * (j - 2 * P.NY) ∧
        P.K - 1 - 2 * (j - 2 * P.NY) ≤ P.K by omega),
      dite_eq_right (show ¬(P.K - 1 - 2 * (j - 2 * P.NY)) % 2 = 1 by omega), ite_true]
    exact (P.stairY.upper_inj _ _).mpr (by omega)

theorem stairY_lower_cases {j : ℕ} (hj : j < P.nY) :
    ∃ k, 1 ≤ k ∧ k ≤ P.K ∧ (P.stairY.lower j hj = P.famA k false ∨
      P.stairY.lower j hj = P.famB k false ∨ P.stairY.lower j hj = P.famC k false) := by
  have hj' : j < 3 * P.NY := hj
  have hK := P.K_eq_NY
  have hN := P.NY_pos
  rcases Nat.lt_or_ge j P.NY with h | h
  · refine ⟨2 * j + 2, by omega, by omega, Or.inr (Or.inr ?_)⟩
    unfold famC
    simp only [dite_eq_left (show 1 ≤ 2 * j + 2 ∧ 2 * j + 2 ≤ P.K by omega),
      dite_eq_right (show ¬(2 * j + 2) % 2 = 1 by omega), Bool.false_eq_true, ite_false]
    exact (P.stairY.lower_inj _ _).mpr (by omega)
  rcases Nat.lt_or_ge j (2 * P.NY) with h' | h'
  · refine ⟨P.K - 1 - 2 * (j - P.NY), by omega, by omega, Or.inr (Or.inl ?_)⟩
    unfold famB
    simp only [dite_eq_left (show 1 ≤ P.K - 1 - 2 * (j - P.NY) ∧
        P.K - 1 - 2 * (j - P.NY) ≤ P.K by omega),
      dite_eq_right (show ¬(P.K - 1 - 2 * (j - P.NY)) % 2 = 1 by omega), Bool.false_eq_true,
      ite_false]
    exact (P.stairY.lower_inj _ _).mpr (by omega)
  · refine ⟨P.K - 1 - 2 * (j - 2 * P.NY), by omega, by omega, Or.inl ?_⟩
    unfold famA
    simp only [dite_eq_left (show 1 ≤ P.K - 1 - 2 * (j - 2 * P.NY) ∧
        P.K - 1 - 2 * (j - 2 * P.NY) ≤ P.K by omega),
      dite_eq_right (show ¬(P.K - 1 - 2 * (j - 2 * P.NY)) % 2 = 1 by omega), Bool.false_eq_true,
      ite_false]
    exact (P.stairY.lower_inj _ _).mpr (by omega)

/-- **Every core family is a bank family**, with its bank index and side. -/
theorem core_bank_cases {G : ActualFamily P.heads P.T} (hG : G ∈ P.core) :
    ∃ k up, 1 ≤ k ∧ k ≤ P.K ∧ (G = P.famA k up ∨ G = P.famB k up ∨ G = P.famC k up) := by
  rcases P.core_cases hG with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · obtain ⟨k, h1, h2, h⟩ := P.stairX_upper_cases hj
    exact ⟨k, true, h1, h2, h⟩
  · obtain ⟨k, h1, h2, h⟩ := P.stairX_lower_cases hj
    exact ⟨k, false, h1, h2, h⟩
  · obtain ⟨k, h1, h2, h⟩ := P.stairY_upper_cases hj
    exact ⟨k, true, h1, h2, h⟩
  · obtain ⟨k, h1, h2, h⟩ := P.stairY_lower_cases hj
    exact ⟨k, false, h1, h2, h⟩

/-! ### Distinct bank-A families -/

theorem stairX_ne_stairY_upper {j j' : ℕ} (hj : j < P.nX) (hj' : j' < P.nY) :
    P.stairX.upper j hj ≠ P.stairY.upper j' hj' := by
  intro he
  have h0 : (P.stairX.upper j hj).1.1 = 0 := rfl
  have h1 : (P.stairY.upper j' hj').1.1 = 1 := rfl
  rw [he] at h0
  rw [h0] at h1
  exact absurd h1 (by decide)

theorem stairX_ne_stairY_lower {j j' : ℕ} (hj : j < P.nX) (hj' : j' < P.nY) :
    P.stairX.lower j hj ≠ P.stairY.lower j' hj' := by
  intro he
  have h0 : (P.stairX.lower j hj).1.1 = 0 := rfl
  have h1 : (P.stairY.lower j' hj').1.1 = 1 := rfl
  rw [he] at h0
  rw [h0] at h1
  exact absurd h1 (by decide)

/-- Bank-A families of one side and distinct indices are distinct. -/
theorem famA_inj {k k' : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ P.K) (h1' : 1 ≤ k') (h2' : k' ≤ P.K)
    {up : Bool} (he : P.famA k up = P.famA k' up) : k = k' := by
  have hK := P.K_odd
  unfold famA at he
  simp only [dite_eq_left (show 1 ≤ k ∧ k ≤ P.K from ⟨h1, h2⟩),
    dite_eq_left (show 1 ≤ k' ∧ k' ≤ P.K from ⟨h1', h2'⟩)] at he
  by_cases hp : k % 2 = 1 <;> by_cases hp' : k' % 2 = 1
  · simp only [dite_eq_left hp, dite_eq_left hp'] at he
    cases up
    · simp only [Bool.false_eq_true, ite_false] at he
      have := (P.stairX.lower_inj _ _).mp he
      omega
    · simp only [ite_true] at he
      have := (P.stairX.upper_inj _ _).mp he
      omega
  · simp only [dite_eq_left hp, dite_eq_right hp'] at he
    cases up
    · simp only [Bool.false_eq_true, ite_false] at he
      exact absurd he (P.stairX_ne_stairY_lower _ _)
    · simp only [ite_true] at he
      exact absurd he (P.stairX_ne_stairY_upper _ _)
  · simp only [dite_eq_right hp, dite_eq_left hp'] at he
    cases up
    · simp only [Bool.false_eq_true, ite_false] at he
      exact absurd he.symm (P.stairX_ne_stairY_lower _ _)
    · simp only [ite_true] at he
      exact absurd he.symm (P.stairX_ne_stairY_upper _ _)
  · simp only [dite_eq_right hp, dite_eq_right hp'] at he
    cases up
    · simp only [Bool.false_eq_true, ite_false] at he
      have := (P.stairY.lower_inj _ _).mp he
      omega
    · simp only [ite_true] at he
      have := (P.stairY.upper_inj _ _).mp he
      omega

/-! ### Counting the big families -/

theorem lev_le_of_a {k ℓ : ℕ} (h2 : k ≤ P.K) (hc : 2 ^ (P.n - 2 * ℓ - 2) ≤ P.a k) :
    lev k ≤ ℓ := by
  have he := P.exponent_ok h2
  unfold a at hc
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hc
  omega

theorem lev_le_of_cc {k ℓ : ℕ} (h2 : k ≤ P.K) (hc : 2 ^ (P.n - 2 * ℓ - 2) ≤ P.cc k) :
    lev k ≤ ℓ + 1 := by
  have he := P.exponent_ok h2
  unfold cc a at hc
  rw [show 8 * 2 ^ (P.n - 2 * lev k - 2) = 2 ^ (P.n - 2 * lev k - 2 + 3) by
    rw [pow_add]; ring] at hc
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hc
  omega

theorem lt_two_pow_of_lev_le {k ℓ : ℕ} (hl : lev k ≤ ℓ) : k < 2 ^ (ℓ + 1) :=
  lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) k)
    (Nat.pow_le_pow_right (by norm_num) (by unfold lev at hl; omega))

theorem card_image_Icc_le (f : ℕ × Bool → ActualFamily P.heads P.T) (N : ℕ) :
    ((Icc 1 N ×ˢ (univ : Finset Bool)).image f).card ≤ 2 * N := by
  refine card_image_le.trans ?_
  rw [card_product, Nat.card_Icc, card_univ, Fintype.card_bool]
  omega

/-- **At most `16 · 2^ℓ - 6` core families have `2^(n - 2ℓ - 2)` hops or more.** -/
theorem card_big_le (ℓ : ℕ) :
    (P.core.filter (fun G => 2 ^ (P.n - 2 * ℓ - 2) ≤ G.hops.card)).card ≤ 16 * 2 ^ ℓ - 6 := by
  have hsub : P.core.filter (fun G => 2 ^ (P.n - 2 * ℓ - 2) ≤ G.hops.card) ⊆
      ((Icc 1 (2 ^ (ℓ + 1) - 1) ×ˢ (univ : Finset Bool)).image (fun p => P.famA p.1 p.2) ∪
        (Icc 1 (2 ^ (ℓ + 1) - 1) ×ˢ (univ : Finset Bool)).image (fun p => P.famB p.1 p.2)) ∪
      (Icc 1 (2 ^ (ℓ + 2) - 1) ×ˢ (univ : Finset Bool)).image (fun p => P.famC p.1 p.2) := by
    intro G hG
    rw [mem_filter] at hG
    obtain ⟨k, up, h1, h2, hk⟩ := P.core_bank_cases hG.1
    rcases hk with rfl | rfl | rfl
    · have hc := hG.2
      rw [P.famA_card h1 h2 up] at hc
      have := lt_two_pow_of_lev_le (P.lev_le_of_a h2 hc)
      refine mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨(k, up), ?_, rfl⟩))
      simp only [mem_product, mem_Icc, mem_univ, and_true]
      omega
    · have hc := hG.2
      rw [P.famB_card h1 h2 up] at hc
      have := lt_two_pow_of_lev_le (P.lev_le_of_a h2 hc)
      refine mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨(k, up), ?_, rfl⟩))
      simp only [mem_product, mem_Icc, mem_univ, and_true]
      omega
    · have hc := hG.2
      rw [P.famC_card h1 h2 up] at hc
      have : k < 2 ^ (ℓ + 2) := lt_two_pow_of_lev_le (P.lev_le_of_cc h2 hc)
      refine mem_union_right _ (mem_image.mpr ⟨(k, up), ?_, rfl⟩)
      simp only [mem_product, mem_Icc, mem_univ, and_true]
      omega
  have e1 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have e2 : 2 ^ (ℓ + 2) = 4 * 2 ^ ℓ := by rw [pow_add]; ring
  have h0 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ 2 * (2 ^ (ℓ + 1) - 1) + 2 * (2 ^ (ℓ + 1) - 1) + 2 * (2 ^ (ℓ + 2) - 1) :=
        Nat.add_le_add (Nat.add_le_add (P.card_image_Icc_le _ _) (P.card_image_Icc_le _ _))
          (P.card_image_Icc_le _ _)
    _ = 16 * 2 ^ ℓ - 6 := by omega

theorem card_big_lt (ℓ : ℕ) :
    (P.core.filter (fun G => 2 ^ (P.n - 2 * ℓ - 2) ≤ G.hops.card)).card < 16 * 2 ^ ℓ := by
  have := P.card_big_le ℓ
  have : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  omega

/-! ### Protected families -/

/-- **Bank-A families of level at most `ℓ` are protected** by every prefix of length
`R ≥ 16 · 2^ℓ`. -/
theorem famA_protected {ℓ R : ℕ} (hR : 16 * 2 ^ ℓ ≤ R) (O : SortedCore P.core) {k : ℕ}
    (h1 : 1 ≤ k) (h2 : k ≤ P.K) (up : Bool) (hl : lev k ≤ ℓ) :
    P.famA k up ∈ O.selectedPrefix R := by
  refine O.mem_selectedPrefix_of_card_lt
    (B := P.core.filter (fun G => 2 ^ (P.n - 2 * ℓ - 2) ≤ G.hops.card)) ?_
    (P.famA_mem h1 h2 up) ?_
  · exact lt_of_lt_of_le (P.card_big_lt ℓ) hR
  · intro H hH hle
    refine mem_filter.mpr ⟨hH, le_trans ?_ hle⟩
    rw [P.famA_card h1 h2]
    unfold a
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Bank-B families of level at most `ℓ` are protected** by every prefix of length
`R ≥ 16 · 2^ℓ`. -/
theorem famB_protected {ℓ R : ℕ} (hR : 16 * 2 ^ ℓ ≤ R) (O : SortedCore P.core) {k : ℕ}
    (h1 : 1 ≤ k) (h2 : k ≤ P.K) (up : Bool) (hl : lev k ≤ ℓ) :
    P.famB k up ∈ O.selectedPrefix R := by
  refine O.mem_selectedPrefix_of_card_lt
    (B := P.core.filter (fun G => 2 ^ (P.n - 2 * ℓ - 2) ≤ G.hops.card)) ?_
    (P.famB_mem h1 h2 up) ?_
  · exact lt_of_lt_of_le (P.card_big_lt ℓ) hR
  · intro H hH hle
    refine mem_filter.mpr ⟨hH, le_trans ?_ hle⟩
    rw [P.famB_card h1 h2]
    unfold a
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Bank-C families of level at most `ℓ + 1` are protected** by every prefix of length
`R ≥ 16 · 2^ℓ`. -/
theorem famC_protected {ℓ R : ℕ} (hR : 16 * 2 ^ ℓ ≤ R) (O : SortedCore P.core) {k : ℕ}
    (h1 : 1 ≤ k) (h2 : k ≤ P.K) (up : Bool) (hl : lev k ≤ ℓ + 1) :
    P.famC k up ∈ O.selectedPrefix R := by
  refine O.mem_selectedPrefix_of_card_lt
    (B := P.core.filter (fun G => 2 ^ (P.n - 2 * ℓ - 2) ≤ G.hops.card)) ?_
    (P.famC_mem h1 h2 up) ?_
  · exact lt_of_lt_of_le (P.card_big_lt ℓ) hR
  · intro H hH hle
    refine mem_filter.mpr ⟨hH, le_trans ?_ hle⟩
    rw [P.famC_card h1 h2]
    unfold cc a
    rw [show 8 * 2 ^ (P.n - 2 * lev k - 2) = 2 ^ (P.n - 2 * lev k - 2 + 3) by
      rw [pow_add]; ring]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### The hop tail -/

/-- The hop tail between ranks `R` and `J` is at least `1 / (32 R)` in every hop ordering of the
core whose prefix of length `J` contains the bank-A upper families of level `⌊log₂ R⌋ + 2`, for
`1 ≤ R ≤ 2^ν / 4`. -/
theorem hop_tail_ge_of_mem {R : ℕ} (hR1 : 1 ≤ R) (hR : 4 * R ≤ 2 ^ P.ν) (O : SortedCore P.core)
    {J : ℕ} (hRJ : R ≤ J)
    (hmem : ∀ k, 1 ≤ k → k ≤ P.K → lev k = Nat.log 2 R + 2 →
      P.famA k true ∈ O.selectedPrefix J) :
    (1 : ℝ) / (32 * R) ≤ ∑ i ∈ Ico R J, O.hopProfile P.L i := by
  -- the dyadic scale `X = 2^(r+2)`, with `2R < X ≤ 4R`
  have hr1 : 2 ^ Nat.log 2 R ≤ R := Nat.pow_log_le_self 2 (by omega)
  have hr2 : R < 2 ^ (Nat.log 2 R + 1) := Nat.lt_pow_succ_log_self (by norm_num) R
  generalize Nat.log 2 R = r at hr1 hr2 hmem
  obtain ⟨X, hX⟩ : ∃ X, X = 2 ^ (r + 2) := ⟨_, rfl⟩
  have e1 : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ]; ring
  have e2 : X = 4 * 2 ^ r := by rw [hX, pow_add]; ring
  have e3 : 2 ^ (r + 2 + 1) = 2 * X := by rw [hX, pow_succ]; ring
  have hXR1 : X ≤ 4 * R := by omega
  have hXR2 : 2 * R < X := by omega
  have hrν : r + 2 ≤ P.ν := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by omega)
  have hK : 2 * X - 1 ≤ P.K := by
    have : 2 ^ (r + 2 + 1) ≤ 2 ^ (P.ν + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold K
    omega
  -- the bank-A upper families of level `r + 2`, all of height `α`
  obtain ⟨α, hα⟩ : ∃ α, α = 2 ^ (P.n - 2 * (r + 2) - 2) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; exact pow_pos (by norm_num) _
  have hrange : ∀ k ∈ Ico X (2 * X), 1 ≤ k ∧ k ≤ P.K := by
    intro k hk
    rw [mem_Ico] at hk
    omega
  have hlev : ∀ k ∈ Ico X (2 * X), lev k = r + 2 := by
    intro k hk
    rw [mem_Ico] at hk
    exact Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  have ha : ∀ k ∈ Ico X (2 * X), P.a k = α := by
    intro k hk
    unfold a
    rw [hlev k hk, hα]
  obtain ⟨Small, hSmall⟩ : ∃ S : Finset (ActualFamily P.heads P.T),
      S = (Ico X (2 * X)).image (fun k => P.famA k true) := ⟨_, rfl⟩
  have hSmall_card : Small.card = X := by
    rw [hSmall, card_image_of_injOn, Nat.card_Ico]
    · omega
    · intro k hk k' hk' he
      have h := hrange k (mem_coe.mp hk)
      have h' := hrange k' (mem_coe.mp hk')
      exact P.famA_inj h.1 h.2 h'.1 h'.2 he
  have hSmall_hops : ∀ G ∈ Small, G.hops.card = α := by
    intro G hG
    rw [hSmall] at hG
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hG
    rw [P.famA_card (hrange k hk).1 (hrange k hk).2, ha k hk]
  -- they lie in the prefix of length `J`
  have hSmallJ : Small ⊆ O.selectedPrefix J := by
    intro G hG
    rw [hSmall] at hG
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hG
    exact hmem k (hrange k hk).1 (hrange k hk).2 (hlev k hk)
  -- the hop mass beyond rank `R`
  have hmass : (X - R) * α ≤ ∑ G ∈ O.selectedPrefix J \ O.selectedPrefix R, G.hops.card := by
    have hsub : Small \ O.selectedPrefix R ⊆ O.selectedPrefix J \ O.selectedPrefix R :=
      sdiff_subset_sdiff hSmallJ (Subset.refl _)
    have hc1 := le_card_sdiff (O.selectedPrefix R) Small
    have hc2 := O.selectedPrefix_card R
    calc (X - R) * α ≤ (Small \ O.selectedPrefix R).card * α :=
          Nat.mul_le_mul_right _ (by omega)
      _ = ∑ G ∈ Small \ O.selectedPrefix R, G.hops.card := by
          rw [sum_congr rfl (fun G hG => hSmall_hops G (mem_sdiff.mp hG).1), sum_const,
            smul_eq_mul]
      _ ≤ _ := sum_le_sum_of_subset hsub
  -- `L = 4 X² α`
  have hL : P.L = 4 * X * X * α := by
    have hn : 2 * (r + 2) + 2 ≤ P.n := by have := P.m_ge; unfold n; omega
    unfold L
    rw [hX, hα, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  -- the tail is the hop mass beyond rank `R`, divided by `L`
  have htail : ∑ i ∈ Ico R J, O.hopProfile P.L i =
      ((∑ G ∈ O.selectedPrefix J \ O.selectedPrefix R, G.hops.card : ℕ) : ℝ) / P.L := by
    simp only [SortedCore.hopProfile]
    rw [O.sum_profile_Ico _ _ hRJ, Nat.cast_sum]
  rw [htail, hL]
  generalize (∑ G ∈ O.selectedPrefix J \ O.selectedPrefix R, G.hops.card) = M at hmass ⊢
  have hXpos : 0 < X := by omega
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR1
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hαR : (0 : ℝ) < α := by exact_mod_cast hα0
  have hX1' : (X : ℝ) ≤ 4 * R := by exact_mod_cast hXR1
  have hX2' : 2 * (R : ℝ) ≤ X := by exact_mod_cast hXR2.le
  have hmassR : ((X : ℝ) - R) * α ≤ M := by
    have h := (Nat.cast_le (α := ℝ)).mpr hmass
    rw [Nat.cast_mul, Nat.cast_sub (by omega : R ≤ X)] at h
    exact h
  have hLpos : (0 : ℝ) < ((4 * X * X * α : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hXpos) hXpos) hα0
  rw [div_le_div_iff₀ (by positivity) hLpos]
  push_cast
  nlinarith [mul_nonneg hR0.le (sub_nonneg.mpr hmassR),
    mul_nonneg hαR.le (mul_nonneg (sub_nonneg.mpr hX1') (sub_nonneg.mpr hX2')),
    mul_nonneg (mul_nonneg hαR.le hR0.le) hX0.le]

/-- **The hop tail beyond rank `R` is at least `1 / (32 R)`** in every hop ordering of the
core, for `1 ≤ R ≤ 2^ν / 4`. -/
theorem hop_tail_ge {R : ℕ} (hR1 : 1 ≤ R) (hR : 4 * R ≤ 2 ^ P.ν) (O : SortedCore P.core)
    {J : ℕ} (hJ : P.core.card ≤ J) (hRJ : R ≤ J) :
    (1 : ℝ) / (32 * R) ≤ ∑ i ∈ Ico R J, O.hopProfile P.L i := by
  -- the prefix of length `J` is the whole core
  have hJc : O.selectedPrefix J = P.core :=
    eq_of_subset_of_card_le (O.selectedPrefix_subset J) (by rw [O.selectedPrefix_card]; omega)
  refine P.hop_tail_ge_of_mem hR1 hR O hRJ fun k h1 h2 _ => ?_
  rw [hJc]
  exact P.famA_mem h1 h2 true

/-- **The hop tail between ranks `R` and `J ≥ 64 R` is at least `1 / (32 R)`** in every hop
ordering of the core, for `1 ≤ R ≤ 2^ν / 4`: the bank-A upper families of level
`⌊log₂ R⌋ + 2` are protected by the prefix of length `J`. -/
theorem hop_tail_ge_of_le {R : ℕ} (hR1 : 1 ≤ R) (hR : 4 * R ≤ 2 ^ P.ν) (O : SortedCore P.core)
    {J : ℕ} (hJ : 64 * R ≤ J) :
    (1 : ℝ) / (32 * R) ≤ ∑ i ∈ Ico R J, O.hopProfile P.L i := by
  have hr : 2 ^ Nat.log 2 R ≤ R := Nat.pow_log_le_self 2 (by omega)
  have e : 2 ^ (Nat.log 2 R + 2) = 4 * 2 ^ Nat.log 2 R := by rw [pow_add]; ring
  have hX : 16 * 2 ^ (Nat.log 2 R + 2) ≤ J := by omega
  exact P.hop_tail_ge_of_mem hR1 hR O (by omega) fun k h1 h2 hl =>
    P.famA_protected hX O h1 h2 true hl.le

/-! ### The hop envelope -/

/-- Every core family has between `1` and `2 L` hops. -/
theorem core_hops_bounds {G : ActualFamily P.heads P.T} (hG : G ∈ P.core) :
    1 ≤ G.hops.card ∧ G.hops.card ≤ 2 * P.L := by
  obtain ⟨k, up, h1, h2, hk⟩ := P.core_bank_cases hG
  have ha : P.a k ≤ P.a 1 := by
    unfold a lev
    rw [Nat.log_one_right]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hL := P.a_one
  have hpos := P.a_pos k
  rcases hk with rfl | rfl | rfl
  · rw [P.famA_card h1 h2 up]; omega
  · rw [P.famB_card h1 h2 up]; omega
  · rw [P.famC_card h1 h2 up]; unfold cc; omega

/-- The families at ranks `0, …, i` of a hop ordering are `i + 1` core families with at least
`v` hops, for every `v` at most the hop count at rank `i`. -/
theorem succ_le_card_filter (O : SortedCore P.core) {i : ℕ} (hi : i < O.families.length)
    {v : ℕ} (hv : v ≤ O.families[i].hops.card) :
    i + 1 ≤ (P.core.filter (fun G => v ≤ G.hops.card)).card := by
  have hsub : O.selectedPrefix (i + 1) ⊆ P.core.filter (fun G => v ≤ G.hops.card) := by
    intro H hH
    refine mem_filter.mpr ⟨O.selectedPrefix_subset _ hH, le_trans hv ?_⟩
    obtain ⟨j, hj, hjH⟩ := List.mem_take_iff_getElem.mp (List.mem_toFinset.mp hH)
    subst hjH
    rcases Nat.lt_or_ge j i with hji | hji
    · exact O.hop_sorted.rel_get_of_lt (a := ⟨j, by omega⟩) (b := ⟨i, hi⟩) hji
    · obtain rfl : j = i := by omega
      exact le_rfl
  have hcard := card_le_card hsub
  rw [O.selectedPrefix_card] at hcard
  have := O.length_eq_card
  omega

/-- **The inverse-square hop envelope**: the family at rank `i` of every hop ordering of the
core has at most `512 L / (i + 1)²` hops. -/
theorem hop_envelope_nat (O : SortedCore P.core) (i : ℕ) (hi : i < O.families.length) :
    O.families[i].hops.card * (i + 1) ^ 2 ≤ 512 * P.L := by
  obtain ⟨hb1, hb2⟩ := P.core_hops_bounds (O.mem_families.mp (List.getElem_mem hi))
  have hcount : ∀ ℓ, 2 ^ (P.n - 2 * ℓ - 2) ≤ O.families[i].hops.card → i + 1 < 16 * 2 ^ ℓ :=
    fun ℓ hℓ => lt_of_le_of_lt (P.succ_le_card_filter O hi hℓ) (P.card_big_lt ℓ)
  have he1 : 2 ^ Nat.log 2 O.families[i].hops.card ≤ O.families[i].hops.card :=
    Nat.pow_log_le_self 2 (by omega)
  have he2 : O.families[i].hops.card < 2 ^ (Nat.log 2 O.families[i].hops.card + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  generalize O.families[i].hops.card = h at hb2 hcount he1 he2 ⊢
  generalize Nat.log 2 h = e at he1 he2
  -- the scale `ℓ = ⌊(n - 1 - e) / 2⌋`, so that `n - 2ℓ - 2 ≤ e` and `e + 1 + 2ℓ ≤ n` if `e < n`
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = (P.n - 1 - e) / 2 := ⟨_, rfl⟩
  have hc := hcount ℓ (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) he1)
  have hscale : h * 2 ^ (2 * ℓ) ≤ 2 * P.L := by
    rcases Nat.lt_or_ge e P.n with he | he
    · calc h * 2 ^ (2 * ℓ) ≤ 2 ^ (e + 1) * 2 ^ (2 * ℓ) := Nat.mul_le_mul_right _ he2.le
        _ = 2 ^ (e + 1 + 2 * ℓ) := (pow_add _ _ _).symm
        _ ≤ 2 ^ P.n := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 2 * P.L := by unfold L; omega
    · rw [show ℓ = 0 by omega, mul_zero, pow_zero, mul_one]
      exact hb2
  calc h * (i + 1) ^ 2 ≤ h * (16 * 2 ^ ℓ) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc.le 2)
    _ = 256 * (h * 2 ^ (2 * ℓ)) := by rw [pow_mul']; ring
    _ ≤ 512 * P.L := by omega

/-- **The inverse-square hop envelope**, in real form: the family at rank `i` of every hop
ordering of the core has at most `512 L / (i + 1)²` hops. -/
theorem hop_envelope (O : SortedCore P.core) (i : ℕ) (hi : i < O.families.length) :
    (O.families[i].hops.card : ℝ) * ((i : ℝ) + 1) ^ 2 ≤ 512 * P.L := by
  exact_mod_cast P.hop_envelope_nat O i hi

end SourceCovers.Z3D.Index
