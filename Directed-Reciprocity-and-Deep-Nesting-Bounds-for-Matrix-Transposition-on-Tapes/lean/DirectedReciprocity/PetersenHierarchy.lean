import DirectedReciprocity.PositionalNest
import MotionDepthCodes.Petersen
import HalfRate.Blocks

/-!
# Non-monotone record-count hierarchy on generalized Petersen graphs (`Proposition GP`)

For `m_gp ≥ 5`, let `GP(m_gp, 2)` (`gpGraph m_gp`) be the cubic generalized Petersen graph on
`2 * m_gp` vertices (`0, …, m_gp - 1` along the outer cycle with step `±1`, `m_gp, …, 2 * m_gp - 1`
along the inner star polygon with step `±2`, and spokes `i ↔ m_gp + i`).

We first prove the global equivalence `elimCert_of_pieceCert_univ` / `pieceCert_univ_of_elimCert`:
for any recovery relation `N` on a finite vertex set `V`, `V` admits a global `m`-record piece
certificate (`PieceCert N ∅ univ` with `c.m = m`) if and only if `N` admits an `m`-record global
elimination certificate (`ElimCert N m`).

We then establish the non-monotone record-count hierarchy across `GP(5, 2)`, `GP(7, 2)`, and
`GP(9, 2)`:
1. **`GP(5, 2)` (the Petersen graph, `n = 10`)**: `gpGraph 5` coincides vertex-for-vertex with
   `MotionDepthCodes.petersenGraph`, and admits **no** global `PieceCert` or `ElimCert` for **any**
   number of records `m : ℕ` (`gp52_no_elimCert`, `petersen_no_pieceCert_univ`), even though it
   satisfies `RateBound (nbhd petersenGraph) (1 / 2)` (`rateBound_petersenGraph`) and decomposes into
   certified pieces (`rateBound_n3`).
2. **`GP(7, 2)` (`n = 14`)**: admits **no** global `PieceCert` or `ElimCert` with `m ≤ 3` records
   (`gp72_no_elimCert_le3`, `gp72_no_pieceCert_univ_le3`), **strictly separating `m = 3` from
   `m = 4`**, as it admits an explicit `4`-record global elimination certificate (`gp72_elimCert4`,
   `gp72_pieceCert_univ_4`).
3. **`GP(9, 2)` (`n = 18`)**: drops back from `4` records to an explicit `3`-record global
   elimination certificate (`gp92_elimCert3`, `gp92_pieceCert_univ_3`).
-/

namespace DirectedReciprocity

open Finset HalfRate MotionDepthCodes

section GlobalEquiv

variable {V : Type*} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem exists_first_not_mem {l : List V} {S : Finset V}
    (hex : ∃ x ∈ l, x ∉ S) :
    ∃ (j : ℕ) (hj : j < l.length), l[j] ∉ S ∧ ∀ i (hi : i < j), l[i]'(lt_trans hi hj) ∈ S := by
  induction l with
  | nil => obtain ⟨_, h, _⟩ := hex; cases h
  | cons hd tl ih =>
    by_cases hhd : hd ∈ S
    · have hex' : ∃ x ∈ tl, x ∉ S := by
        obtain ⟨x, hx, hxS⟩ := hex
        rcases List.mem_cons.mp hx with rfl | htl
        · exact absurd hhd hxS
        · exact ⟨x, htl, hxS⟩
      obtain ⟨j, hj, hnot, hprev⟩ := ih hex'
      refine ⟨j + 1, Nat.succ_lt_succ hj, by simpa using hnot, ?_⟩
      intro i hi
      rcases i with _ | i
      · simpa using hhd
      · exact hprev i (Nat.lt_of_succ_lt_succ hi)
    · exact ⟨0, Nat.zero_lt_succ _, by simpa using hhd, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

/-- Every global piece certificate `PieceCert N ∅ univ` induces an order-free global elimination
certificate `ElimCert N c.m` with the same record count `c.m`. -/
def elimCert_of_pieceCert_univ {N : V → Finset V} (c : PieceCert N ∅ univ) :
    ElimCert N c.m where
  P := c.P
  disj := c.disj
  cover v := by
    have hv : v ∈ (univ : Finset (Fin c.m)).biUnion c.P := by rw [c.cover]; exact mem_univ v
    obtain ⟨i, -, hi⟩ := mem_biUnion.mp hv
    exact ⟨i, hi⟩
  a := c.a
  b := c.b
  own v := c.own v (List.mem_toFinset.mp (c.hl.symm ▸ mem_univ v))
  ab v := c.ab v (List.mem_toFinset.mp (c.hl.symm ▸ mem_univ v))
  elim S hS := by
    have hnest := (relCharged_iff_nested N ∅ c.P c.b c.par (univ \ (∅ ∪ univ)) c.l).mp c.charged
    obtain ⟨x₀, hx₀S⟩ : ∃ x, x ∉ S := by
      by_contra hall
      push Not at hall
      exact hS (eq_univ_of_forall hall)
    have hx₀l : x₀ ∈ c.l := List.mem_toFinset.mp (c.hl.symm ▸ mem_univ x₀)
    obtain ⟨j, hj, hjS, hprev⟩ := exists_first_not_mem ⟨x₀, hx₀l, hx₀S⟩
    refine ⟨c.l[j], hjS, ?_⟩
    have hrev_sub : rev ∅ c.l j ⊆ S := by
      intro y hy
      simp only [rev, empty_union, List.mem_toFinset] at hy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      have hij : i < j := by simp at hi; omega
      rw [List.getElem_take]
      exact hprev i hij
    cases hp : c.par c.l[j] with
    | none =>
      have hcov := hnest.1 j hj hp
      simp only [empty_union] at hcov
      exact hcov.trans (union_subset_union hrev_sub (subset_refl _))
    | some w =>
      exfalso
      have hw := (hnest.2.1 j hj w hp).1
      simp at hw

/-- Conversely, every `m`-record `ElimCert` induces a global `PieceCert N ∅ univ` with `m` records. -/
theorem pieceCert_univ_of_elimCert {N : V → Finset V} {m : ℕ} (c : ElimCert N m) :
    ∃ p : PieceCert N ∅ univ, p.m = m := by
  have hcov : (univ : Finset (Fin m)).biUnion c.P = univ := by
    ext v; simp only [mem_biUnion, mem_univ, true_and, iff_true]; exact c.cover v
  obtain ⟨l, hl1, hl2, hl3⟩ := exists_relCharged N ∅ univ (univ \ (∅ ∪ univ)) c.P c.b
    (fun _ => none) (fun _ _ _ _ _ h _ => by cases h)
    (fun S _ hS => by
      obtain ⟨v, hvS, hN⟩ := c.elim S hS
      exact ⟨v, mem_univ v, hvS, fun _ => by simpa using hN, fun _ h => by cases h⟩)
    _ ∅ (empty_subset _) rfl (fun _ => ∅) (fun _ _ _ h => by cases h)
  refine ⟨{
    m := m
    P := c.P
    disj := c.disj
    cover := hcov
    l := l
    hl := by simpa using hl1
    a := c.a
    b := c.b
    par := fun _ => none
    own := fun v _ => c.own v
    ab := fun v _ => c.ab v
    charged := hl3 }, rfl⟩

/-- Global piece certificates of size `m` are equivalent to `ElimCert N m`. -/
theorem nonempty_elimCert_iff_pieceCert_univ {N : V → Finset V} (m : ℕ) :
    Nonempty (ElimCert N m) ↔ ∃ p : PieceCert N ∅ univ, p.m = m :=
  ⟨fun ⟨c⟩ => pieceCert_univ_of_elimCert c, fun ⟨p, hm⟩ => hm ▸ ⟨elimCert_of_pieceCert_univ p⟩⟩

/-- In any `ElimCert` on a simple graph `G`, adjacent vertices lie in distinct own-records. -/
theorem elimCert_adj_ne {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ}
    (c : ElimCert (nbhd G) m) {u v : V} (hadj : G.Adj u v) :
    c.a u ≠ c.a v := by
  have huv : u ≠ v := hadj.ne
  let S : Finset V := (univ.erase u).erase v
  have huS : u ∉ S := by simp [S, huv]
  have hvS : v ∉ S := by simp [S]
  have hSu : S ≠ univ := fun he => huS (he ▸ mem_univ u)
  obtain ⟨x, hxS, hNx⟩ := c.elim S hSu
  have hxu_or_xv : x = u ∨ x = v := by
    by_contra hneither
    push Not at hneither
    exact hxS (by simp [S, hneither.1, hneither.2])
  rcases hxu_or_xv with hxu | hxv
  · rw [hxu] at hNx
    have hmem : v ∈ S ∪ c.P (c.b u) := hNx (by simpa [nbhd] using hadj)
    have hvP : v ∈ c.P (c.b u) := (mem_union.mp hmem).resolve_left hvS
    have heq : c.a v = c.b u := by
      by_contra hne
      exact Finset.disjoint_left.mp (c.disj _ _ hne) (c.own v) hvP
    exact fun h => c.ab u (h.trans heq)
  · rw [hxv] at hNx
    have hmem : u ∈ S ∪ c.P (c.b v) := hNx (by simpa [nbhd] using hadj.symm)
    have huP : u ∈ c.P (c.b v) := (mem_union.mp hmem).resolve_left huS
    have heq : c.a u = c.b v := by
      by_contra hne
      exact Finset.disjoint_left.mp (c.disj _ _ hne) (c.own u) huP
    exact fun h => c.ab v (h.symm.trans heq)

end GlobalEquiv

section GPDef

/-- Adjacency list of the generalized Petersen graph `GP(m_gp, 2)` on `Fin (2 * m_gp)`. -/
def gpAdjList (m_gp : ℕ) (hm : 5 ≤ m_gp) (v : Fin (2 * m_gp)) : List (Fin (2 * m_gp)) :=
  if hv : v.val < m_gp then
    [ ⟨(v.val + m_gp - 1) % m_gp, by have := Nat.mod_lt (v.val + m_gp - 1) (by omega : 0 < m_gp); omega⟩,
      ⟨(v.val + 1) % m_gp, by have := Nat.mod_lt (v.val + 1) (by omega : 0 < m_gp); omega⟩,
      ⟨m_gp + v.val, by omega⟩ ]
  else
    let i := v.val - m_gp
    [ ⟨i, by omega⟩,
      ⟨m_gp + (i + m_gp - 2) % m_gp, by have := Nat.mod_lt (i + m_gp - 2) (by omega : 0 < m_gp); omega⟩,
      ⟨m_gp + (i + 2) % m_gp, by have := Nat.mod_lt (i + 2) (by omega : 0 < m_gp); omega⟩ ]

theorem gpAdjList_symm (m_gp : ℕ) (hm : 5 ≤ m_gp) {u v : Fin (2 * m_gp)}
    (h : v ∈ gpAdjList m_gp hm u) : u ∈ gpAdjList m_gp hm v := by
  have hu := u.isLt
  unfold gpAdjList at h ⊢
  split_ifs at h with hu_lt
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · have hv_lt : (u.val + m_gp - 1) % m_gp < m_gp := Nat.mod_lt _ (by omega)
      simp only [hv_lt, ↓reduceDIte, List.mem_cons]
      right; left
      apply Fin.ext; simp only
      rcases eq_or_lt_of_le (Nat.zero_le u.val) with hu0 | hu_pos
      · rw [← hu0]; simp [Nat.mod_eq_of_lt (show m_gp - 1 < m_gp by omega),
          show m_gp - 1 + 1 = m_gp by omega]
      · rw [show u.val + m_gp - 1 = m_gp + (u.val - 1) by omega, Nat.add_mod_left,
          Nat.mod_eq_of_lt (show u.val - 1 < m_gp by omega),
          show u.val - 1 + 1 = u.val by omega, Nat.mod_eq_of_lt hu_lt]
    · have hv_lt : (u.val + 1) % m_gp < m_gp := Nat.mod_lt _ (by omega)
      simp only [hv_lt, ↓reduceDIte, List.mem_cons]
      left
      apply Fin.ext; simp only
      rcases Nat.lt_or_ge (u.val + 1) m_gp with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt, show u.val + 1 + m_gp - 1 = m_gp + u.val by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt hu_lt]
      · have heq : u.val + 1 = m_gp := by omega
        rw [heq, Nat.mod_self, show 0 + m_gp - 1 = u.val by omega, Nat.mod_eq_of_lt hu_lt]
    · have hv_nlt : ¬ (m_gp + u.val < m_gp) := by omega
      simp only [hv_nlt, ↓reduceDIte, List.mem_cons]
      left; apply Fin.ext; simp
  · dsimp only at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have hi_lt : u.val - m_gp < m_gp := by omega
    rcases h with rfl | rfl | rfl
    · simp only [hi_lt, ↓reduceDIte, List.mem_cons]
      right; right; left
      apply Fin.ext; simp only; omega
    · have hv_nlt : ¬ (m_gp + (u.val - m_gp + m_gp - 2) % m_gp < m_gp) := by omega
      simp only [hv_nlt, ↓reduceDIte, List.mem_cons]
      right; right; left
      apply Fin.ext; simp only [Nat.add_sub_cancel_left]
      rcases Nat.lt_or_ge (u.val - m_gp) 2 with hi2 | hi2
      · have hmod1 : (u.val - m_gp + m_gp - 2) % m_gp = u.val - m_gp + m_gp - 2 :=
          Nat.mod_eq_of_lt (by omega)
        rw [hmod1, show u.val - m_gp + m_gp - 2 + 2 = m_gp + (u.val - m_gp) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt hi_lt]
        omega
      · rw [show u.val - m_gp + m_gp - 2 = m_gp + (u.val - m_gp - 2) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (show u.val - m_gp - 2 < m_gp by omega),
          show u.val - m_gp - 2 + 2 = u.val - m_gp by omega, Nat.mod_eq_of_lt hi_lt]
        omega
    · have hv_nlt : ¬ (m_gp + (u.val - m_gp + 2) % m_gp < m_gp) := by omega
      simp only [hv_nlt, ↓reduceDIte, List.mem_cons]
      right; left
      apply Fin.ext; simp only [Nat.add_sub_cancel_left]
      rcases Nat.lt_or_ge (u.val - m_gp + 2) m_gp with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt,
          show u.val - m_gp + 2 + m_gp - 2 = m_gp + (u.val - m_gp) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt hi_lt]
        omega
      · rw [show u.val - m_gp + 2 = m_gp + (u.val - m_gp + 2 - m_gp) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (show u.val - m_gp + 2 - m_gp < m_gp by omega),
          show u.val - m_gp + 2 - m_gp + m_gp - 2 = u.val - m_gp by omega,
          Nat.mod_eq_of_lt hi_lt]
        omega

theorem gpAdjList_irrefl (m_gp : ℕ) (hm : 5 ≤ m_gp) (u : Fin (2 * m_gp)) :
    u ∉ gpAdjList m_gp hm u := by
  have hu := u.isLt
  unfold gpAdjList
  split_ifs with hu_lt
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
    rintro (h | h | h)
    · rcases eq_or_lt_of_le (Nat.zero_le u.val) with hu0 | hu_pos
      · rw [← hu0, Nat.mod_eq_of_lt (by omega)] at h; omega
      · rw [show u.val + m_gp - 1 = m_gp + (u.val - 1) by omega, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by omega)] at h; omega
    · rcases Nat.lt_or_ge (u.val + 1) m_gp with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h; omega
      · rw [show u.val + 1 = m_gp by omega, Nat.mod_self] at h; omega
    · omega
  · dsimp only
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
    have hi_lt : u.val - m_gp < m_gp := by omega
    rintro (h | h | h)
    · omega
    · rcases Nat.lt_or_ge (u.val - m_gp) 2 with hi2 | hi2
      · rw [Nat.mod_eq_of_lt (show u.val - m_gp + m_gp - 2 < m_gp by omega)] at h; omega
      · rw [show u.val - m_gp + m_gp - 2 = m_gp + (u.val - m_gp - 2) by omega, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by omega)] at h; omega
    · rcases Nat.lt_or_ge (u.val - m_gp + 2) m_gp with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h; omega
      · rw [show u.val - m_gp + 2 = m_gp + (u.val - m_gp + 2 - m_gp) by omega, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by omega)] at h; omega

/-- Generalized Petersen graph `GP(m_gp, 2)` on `Fin (2 * m_gp)` for `m_gp ≥ 5`. -/
def gpGraph (m_gp : ℕ) (hm : 5 ≤ m_gp) : SimpleGraph (Fin (2 * m_gp)) where
  Adj u v := v ∈ gpAdjList m_gp hm u
  symm := ⟨fun _ _ h => gpAdjList_symm m_gp hm h⟩
  loopless := ⟨gpAdjList_irrefl m_gp hm⟩

instance (m_gp : ℕ) (hm : 5 ≤ m_gp) : DecidableRel (gpGraph m_gp hm).Adj :=
  fun u v => inferInstanceAs (Decidable (v ∈ gpAdjList m_gp hm u))

/-- `GP(5, 2)` coincides vertex-for-vertex with `MotionDepthCodes.petersenGraph`. -/
theorem gp52_eq_petersenGraph : gpGraph 5 (by decide) = petersenGraph := by
  ext u v
  revert u v
  decide

abbrev gpAdj5 : Fin 10 → List (Fin 10) := gpAdjList 5 (by decide)
abbrev gpAdj7 : Fin 14 → List (Fin 14) := gpAdjList 7 (by decide)
abbrev gp52 : SimpleGraph (Fin 10) := gpGraph 5 (by decide)
abbrev gp72 : SimpleGraph (Fin 14) := gpGraph 7 (by decide)
abbrev gp92 : SimpleGraph (Fin 18) := gpGraph 9 (by decide)

end GPDef

section PeelRefuter

/-- Pure `Bool` check: vertex `v` can be peeled at `rev` under coloring `col` if `v ∉ rev` and all
unrevealed neighbours of `v` share a single `col`-value. -/
def canPeelAt {n k : ℕ} (adj : Fin n → List (Fin n)) (col : Fin n → Fin k)
    (rev : List (Fin n)) (v : Fin n) : Bool :=
  !rev.contains v &&
    (adj v).all fun x =>
      rev.contains x ||
        (adj v).all fun y =>
          rev.contains y || (col x == col y)

def findPeelable {n k : ℕ} (adj : Fin n → List (Fin n)) (col : Fin n → Fin k)
    (rev : List (Fin n)) : List (Fin n) → Option (Fin n)
  | [] => none
  | v :: vs => if canPeelAt adj col rev v then some v else findPeelable adj col rev vs

theorem findPeelable_none {n k : ℕ} {adj : Fin n → List (Fin n)} {col : Fin n → Fin k}
    {rev : List (Fin n)} :
    ∀ {l : List (Fin n)}, findPeelable adj col rev l = none →
      ∀ v ∈ l, canPeelAt adj col rev v = false
  | [], _, _, hv => nomatch hv
  | w :: ws, h, v, hv => by
    unfold findPeelable at h
    split_ifs at h with hcw
    rcases List.mem_cons.mp hv with rfl | hvs
    · exact Bool.eq_false_iff.mpr hcw
    · exact findPeelable_none h v hvs

/-- Runs greedy monochromatic-unrevealed-neighbourhood peeling; returns `true` if a proper subset
`rev` of `Fin n` is reached from which no vertex can be peeled. -/
def peelFailsAux {n k : ℕ} (adj : Fin n → List (Fin n)) (col : Fin n → Fin k) :
    ℕ → List (Fin n) → Bool
  | 0, _ => false
  | fuel + 1, rev =>
    match findPeelable adj col rev (List.finRange n) with
    | none => rev.length < n
    | some v => peelFailsAux adj col fuel (v :: rev)

theorem peelFailsAux_sound {n k : ℕ} {adj : Fin n → List (Fin n)} {col : Fin n → Fin k} :
    ∀ (fuel : ℕ) (rev : List (Fin n)), peelFailsAux adj col fuel rev = true →
      ∃ S : Finset (Fin n), S ≠ univ ∧
        ∀ v ∉ S, ∃ x ∈ adj v, ∃ y ∈ adj v, x ∉ S ∧ y ∉ S ∧ col x ≠ col y
  | 0, _, h => by simp [peelFailsAux] at h
  | fuel + 1, rev, h => by
    unfold peelFailsAux at h
    cases hfp : findPeelable adj col rev (List.finRange n) with
    | some v =>
      rw [hfp] at h
      exact peelFailsAux_sound fuel (v :: rev) h
    | none =>
      rw [hfp] at h
      have hlen : rev.length < n := of_decide_eq_true h
      let S : Finset (Fin n) := rev.toFinset
      refine ⟨S, ?_, ?_⟩
      · intro heq
        have hc : S.card = n := by rw [heq, card_univ, Fintype.card_fin]
        have hle : S.card ≤ rev.length := List.toFinset_card_le rev
        omega
      · intro v hvS
        have hv_nmem : v ∉ rev := fun hm => hvS (List.mem_toFinset.mpr hm)
        have hfalse := findPeelable_none hfp v (List.mem_finRange v)
        have hall_false : ¬ (∀ x ∈ adj v, ∀ y ∈ adj v, x ∉ rev → y ∉ rev → col x = col y) := by
          intro hall
          have htrue : canPeelAt adj col rev v = true := by
            unfold canPeelAt
            rw [Bool.and_eq_true]
            refine ⟨by simp [hv_nmem], ?_⟩
            rw [List.all_eq_true]
            intro x hx
            by_cases hxr : x ∈ rev
            · simp [hxr]
            · have hxr_c : rev.contains x = false := by simp [hxr]
              rw [hxr_c, Bool.false_or, List.all_eq_true]
              intro y hy
              by_cases hyr : y ∈ rev
              · simp [hyr]
              · simp [hyr, hall x hx y hy hxr hyr]
          rw [hfalse] at htrue
          cases htrue
        push Not at hall_false
        obtain ⟨x, hx, y, hy, hxr, hyr, hne⟩ := hall_false
        exact ⟨x, hx, y, hy, fun hS => hxr (List.mem_toFinset.mp hS),
          fun hS => hyr (List.mem_toFinset.mp hS), hne⟩

/-- Exhaustive pure-`Bool` DFS over canonical RGS independent-set partitions `col : Fin n → Fin n`
(`col i ≤ i`, `col (col i) = col i`, proper coloring of `adj`). -/
def checkAllCanonicalPartitions {n : ℕ} (hn : 0 < n) (adj : Fin n → List (Fin n)) :
    ℕ → List (Fin n) → Bool
  | 0, acc =>
    let col : Fin n → Fin n := fun i => acc.getD i.val ⟨0, hn⟩
    peelFailsAux adj col n []
  | rem + 1, acc =>
    if hpos : acc.length < n then
      let vpos : Fin n := ⟨acc.length, hpos⟩
      (List.finRange n).all fun c =>
        let valid : Bool :=
          decide (c.val ≤ acc.length) &&
          (decide (c.val = acc.length) || (acc.getD c.val ⟨0, hn⟩ == c)) &&
          (adj vpos).all fun u => !(decide (u.val < acc.length)) || !(acc.getD u.val ⟨0, hn⟩ == c)
        !valid || checkAllCanonicalPartitions hn adj rem (acc ++ [c])
    else true

private theorem getD_prefix_eq {α : Type*} (d : α) (f : ℕ → α) :
    ∀ (m i : ℕ), i < m → ((List.range m).map f).getD i d = f i := by
  intro m i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
  simp

theorem checkAllCanonicalPartitions_sound {n : ℕ} (hn : 0 < n) (adj : Fin n → List (Fin n))
    (hchk : checkAllCanonicalPartitions hn adj n [] = true)
    (col : Fin n → Fin n)
    (hle : ∀ i : Fin n, (col i).val ≤ i.val)
    (hidem : ∀ i : Fin n, col (col i) = col i)
    (hprop : ∀ i : Fin n, ∀ u ∈ adj i, col u ≠ col i) :
    ∃ S : Finset (Fin n), S ≠ univ ∧
      ∀ v ∉ S, ∃ x ∈ adj v, ∃ y ∈ adj v, x ∉ S ∧ y ∉ S ∧ col x ≠ col y := by
  let f : ℕ → Fin n := fun j => if hj : j < n then col ⟨j, hj⟩ else ⟨0, hn⟩
  have step : ∀ (rem : ℕ) (hrem : rem ≤ n),
      checkAllCanonicalPartitions hn adj rem ((List.range (n - rem)).map f) = true →
      checkAllCanonicalPartitions hn adj 0 ((List.range n).map f) = true := by
    intro rem
    induction rem with
    | zero => intro _ h; simpa using h
    | succ rem ih =>
      intro hrem h
      set pos := n - (rem + 1)
      have hpos : pos < n := by omega
      unfold checkAllCanonicalPartitions at h
      have hlen : ((List.range pos).map f).length = pos := by simp
      split_ifs at h with hpos'
      · have hvpos : (⟨((List.range pos).map f).length, hpos'⟩ : Fin n) = ⟨pos, hpos⟩ :=
          Fin.ext hlen
        rw [List.all_eq_true] at h
        have hc := h (col ⟨pos, hpos⟩) (List.mem_finRange _)
        dsimp only at hc
        rw [hvpos, hlen] at hc
        have hvalid :
            (decide ((col ⟨pos, hpos⟩).val ≤ pos) &&
              (decide ((col ⟨pos, hpos⟩).val = pos) ||
                (((List.range pos).map f).getD (col ⟨pos, hpos⟩).val ⟨0, hn⟩ == col ⟨pos, hpos⟩)) &&
              (adj ⟨pos, hpos⟩).all fun u =>
                !(decide (u.val < pos)) ||
                  !(((List.range pos).map f).getD u.val ⟨0, hn⟩ == col ⟨pos, hpos⟩)) = true := by
          have hc1 : decide ((col ⟨pos, hpos⟩).val ≤ pos) = true :=
            decide_eq_true (hle ⟨pos, hpos⟩)
          have hc2 : (decide ((col ⟨pos, hpos⟩).val = pos) ||
              (((List.range pos).map f).getD (col ⟨pos, hpos⟩).val ⟨0, hn⟩ == col ⟨pos, hpos⟩)) = true := by
            rcases eq_or_lt_of_le (hle ⟨pos, hpos⟩) with heq | hlt
            · simp [heq]
            · rw [getD_prefix_eq _ f pos _ hlt]
              simp [f, lt_trans hlt hpos, hidem ⟨pos, hpos⟩]
          have hc3 : ((adj ⟨pos, hpos⟩).all fun u =>
              !(decide (u.val < pos)) ||
                !(((List.range pos).map f).getD u.val ⟨0, hn⟩ == col ⟨pos, hpos⟩)) = true := by
            rw [List.all_eq_true]
            intro u hu
            by_cases hult : u.val < pos
            · rw [getD_prefix_eq _ f pos _ hult]
              simp [f, hult, lt_trans hult hpos, hprop ⟨pos, hpos⟩ u hu]
            · simp [hult]
          rw [hc1, hc2, hc3]; rfl
        rw [hvalid] at hc
        simp only [Bool.not_true, Bool.false_or] at hc
        have happ : (List.range pos).map f ++ [col ⟨pos, hpos⟩] =
            (List.range (n - rem)).map f := by
          have hnr : n - rem = pos + 1 := by omega
          rw [hnr, List.range_succ, List.map_append, List.map_singleton]
          simp [f, hpos]
        rw [happ] at hc
        exact ih (by omega) hc
      · rw [hlen] at hpos'
        exact absurd hpos hpos'
  have hleaf := step n le_rfl (by simpa using hchk)
  unfold checkAllCanonicalPartitions at hleaf
  have hcol_eq : (fun i : Fin n => ((List.range n).map f).getD i.val ⟨0, hn⟩) = col := by
    funext i
    rw [getD_prefix_eq _ f n i.val i.isLt]
    simp [f, i.isLt]
  rw [hcol_eq] at hleaf
  exact peelFailsAux_sound n [] hleaf

/-- Exhaustive pure-`Bool` DFS over proper `Fin 3`-colorings `col : Fin n → Fin 3` with `col 0 = 0`. -/
def checkAllProper3Colorings {n : ℕ} (adj : Fin n → List (Fin n)) :
    ℕ → List (Fin 3) → Bool
  | 0, acc =>
    let col : Fin n → Fin 3 := fun i => acc.getD i.val 0
    peelFailsAux adj col n []
  | rem + 1, acc =>
    if hpos : acc.length < n then
      let vpos : Fin n := ⟨acc.length, hpos⟩
      (List.finRange 3).all fun c =>
        let valid : Bool :=
          (!(decide (acc.length = 0)) || (c == 0)) &&
          (adj vpos).all fun u => !(decide (u.val < acc.length)) || !(acc.getD u.val 0 == c)
        !valid || checkAllProper3Colorings adj rem (acc ++ [c])
    else true

theorem checkAllProper3Colorings_sound {n : ℕ} (hn : 0 < n) (adj : Fin n → List (Fin n))
    (hchk : checkAllProper3Colorings adj n [] = true)
    (col : Fin n → Fin 3) (h0 : col ⟨0, hn⟩ = 0)
    (hprop : ∀ i : Fin n, ∀ u ∈ adj i, col u ≠ col i) :
    ∃ S : Finset (Fin n), S ≠ univ ∧
      ∀ v ∉ S, ∃ x ∈ adj v, ∃ y ∈ adj v, x ∉ S ∧ y ∉ S ∧ col x ≠ col y := by
  let f : ℕ → Fin 3 := fun j => if hj : j < n then col ⟨j, hj⟩ else 0
  have step : ∀ (rem : ℕ) (hrem : rem ≤ n),
      checkAllProper3Colorings adj rem ((List.range (n - rem)).map f) = true →
      checkAllProper3Colorings adj 0 ((List.range n).map f) = true := by
    intro rem
    induction rem with
    | zero => intro _ h; simpa using h
    | succ rem ih =>
      intro hrem h
      set pos := n - (rem + 1)
      have hpos : pos < n := by omega
      unfold checkAllProper3Colorings at h
      have hlen : ((List.range pos).map f).length = pos := by simp
      split_ifs at h with hpos'
      · have hvpos : (⟨((List.range pos).map f).length, hpos'⟩ : Fin n) = ⟨pos, hpos⟩ :=
          Fin.ext hlen
        rw [List.all_eq_true] at h
        have hc := h (col ⟨pos, hpos⟩) (List.mem_finRange _)
        dsimp only at hc
        rw [hvpos, hlen] at hc
        have hvalid :
            ((!(decide (pos = 0)) || (col ⟨pos, hpos⟩ == 0)) &&
              (adj ⟨pos, hpos⟩).all fun u =>
                !(decide (u.val < pos)) ||
                  !(((List.range pos).map f).getD u.val 0 == col ⟨pos, hpos⟩)) = true := by
          have hc1 : (!(decide (pos = 0)) || (col ⟨pos, hpos⟩ == 0)) = true := by
            by_cases hp0 : pos = 0
            · have hf0 : (⟨pos, hpos⟩ : Fin n) = ⟨0, hn⟩ := Fin.ext hp0
              rw [hf0, h0]
              simp
            · simp [hp0]
          have hc2 : ((adj ⟨pos, hpos⟩).all fun u =>
              !(decide (u.val < pos)) ||
                !(((List.range pos).map f).getD u.val 0 == col ⟨pos, hpos⟩)) = true := by
            rw [List.all_eq_true]
            intro u hu
            by_cases hult : u.val < pos
            · rw [getD_prefix_eq _ f pos _ hult]
              simp [f, hult, lt_trans hult hpos, hprop ⟨pos, hpos⟩ u hu]
            · simp [hult]
          rw [hc1, hc2]; rfl
        rw [hvalid] at hc
        simp only [Bool.not_true, Bool.false_or] at hc
        have happ : (List.range pos).map f ++ [col ⟨pos, hpos⟩] =
            (List.range (n - rem)).map f := by
          have hnr : n - rem = pos + 1 := by omega
          rw [hnr, List.range_succ, List.map_append, List.map_singleton]
          simp [f, hpos]
        rw [happ] at hc
        exact ih (by omega) hc
      · rw [hlen] at hpos'
        exact absurd hpos hpos'
  have hleaf := step n le_rfl (by simpa using hchk)
  unfold checkAllProper3Colorings at hleaf
  have hcol_eq : (fun i : Fin n => ((List.range n).map f).getD i.val 0) = col := by
    funext i
    rw [getD_prefix_eq _ f n i.val i.isLt]
    simp [f, i.isLt]
  rw [hcol_eq] at hleaf
  exact peelFailsAux_sound n [] hleaf

end PeelRefuter

section ExplicitBuilder

/-- Builds an `ElimCert (nbhd G) m` from a record assignment `a`, supplying assignment `b`,
and bijective peeling order `ord : Fin n → Fin n` checked at the `n` indices `0, …, n - 1`. -/
def mkElimCertOfOrder {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n → Fin m) (ord : Fin n → Fin n)
    (hab : ∀ v, a v ≠ b v)
    (hbij : Function.Bijective ord)
    (hstep : ∀ j : Fin n, ∀ u ∈ nbhd G (ord j),
      (∃ i : Fin n, i < j ∧ ord i = u) ∨ a u = b (ord j)) :
    ElimCert (nbhd G) m where
  P r := univ.filter (fun v => a v = r)
  disj r₁ r₂ hne := by
    rw [disjoint_left]
    intro v h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    exact hne (h1.symm.trans h2)
  cover v := ⟨a v, by simp⟩
  a := a
  b := b
  own v := by simp
  ab := hab
  elim S hS := by
    have hex : (univ.filter (fun j : Fin n => ord j ∉ S)).Nonempty := by
      by_contra hempty
      rw [not_nonempty_iff_eq_empty] at hempty
      apply hS; apply eq_univ_of_forall; intro x
      obtain ⟨j, rfl⟩ := hbij.2 x
      by_contra hjS
      have hm : j ∈ univ.filter (fun j : Fin n => ord j ∉ S) := mem_filter.mpr ⟨mem_univ j, hjS⟩
      rw [hempty] at hm; exact nomatch hm
    let j₀ := (univ.filter (fun j : Fin n => ord j ∉ S)).min' hex
    have hj₀ : ord j₀ ∉ S := (mem_filter.mp (min'_mem _ hex)).2
    refine ⟨ord j₀, hj₀, ?_⟩
    intro u hu
    rcases hstep j₀ u hu with ⟨i, hij, rfl⟩ | hau
    · apply mem_union_left
      by_contra hiS
      have hle := min'_le (univ.filter (fun j : Fin n => ord j ∉ S)) i
        (mem_filter.mpr ⟨mem_univ i, hiS⟩)
      exact not_lt_of_ge hle hij
    · exact mem_union_right _ (by simp [hau])

end ExplicitBuilder

section HierarchyResults

private theorem gp52_canonical_chk :
    checkAllCanonicalPartitions (by decide) gpAdj5 10 [] = true := by
  decide +kernel

private theorem gp72_3col_chk :
    checkAllProper3Colorings gpAdj7 14 [] = true := by
  decide +kernel

/-- **Part 1 of Proposition GP (`GP(5, 2)` / Petersen graph)**: `GP(5, 2)` admits **no** global
elimination certificate `ElimCert` over **any** number of records `m : ℕ`. -/
theorem gp52_no_elimCert (m : ℕ) : ¬ Nonempty (ElimCert (nbhd gp52) m) := by
  rintro ⟨c⟩
  let col : Fin 10 → Fin 10 := fun u =>
    (univ.filter (fun i : Fin 10 => c.a i = c.a u)).min' ⟨u, mem_filter.mpr ⟨mem_univ u, rfl⟩⟩
  have hcol_a : ∀ u : Fin 10, c.a (col u) = c.a u := fun u =>
    (mem_filter.mp (min'_mem (univ.filter (fun i : Fin 10 => c.a i = c.a u))
      ⟨u, mem_filter.mpr ⟨mem_univ u, rfl⟩⟩)).2
  have hcol_iff : ∀ u v : Fin 10, col u = col v ↔ c.a u = c.a v := by
    intro u v
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← hcol_a u, h, hcol_a v]
    · simp only [col, h]
  have hle : ∀ i : Fin 10, (col i).val ≤ i.val := fun i =>
    min'_le (univ.filter (fun k : Fin 10 => c.a k = c.a i)) i (mem_filter.mpr ⟨mem_univ i, rfl⟩)
  have hidem : ∀ i : Fin 10, col (col i) = col i := fun i => (hcol_iff _ _).mpr (hcol_a i)
  have hprop : ∀ i : Fin 10, ∀ u ∈ gpAdj5 i, col u ≠ col i := by
    intro i u hu heq
    exact elimCert_adj_ne c hu ((hcol_iff u i).mp heq).symm
  obtain ⟨S, hSu, hstuck⟩ := checkAllCanonicalPartitions_sound (by decide)
    gpAdj5 gp52_canonical_chk col hle hidem hprop
  obtain ⟨v, hvS, hNv⟩ := c.elim S hSu
  obtain ⟨x, hx, y, hy, hxS, hyS, hne⟩ := hstuck v hvS
  have hx' : x ∈ nbhd gp52 v := mem_filter.mpr ⟨mem_univ x, hx⟩
  have hy' : y ∈ nbhd gp52 v := mem_filter.mpr ⟨mem_univ y, hy⟩
  have hxP : x ∈ c.P (c.b v) := (mem_union.mp (hNv hx')).resolve_left hxS
  have hyP : y ∈ c.P (c.b v) := (mem_union.mp (hNv hy')).resolve_left hyS
  have hax : c.a x = c.b v := by
    by_contra h1; exact Finset.disjoint_left.mp (c.disj _ _ h1) (c.own x) hxP
  have hay : c.a y = c.b v := by
    by_contra h1; exact Finset.disjoint_left.mp (c.disj _ _ h1) (c.own y) hyP
  exact hne ((hcol_iff x y).mpr (hax.trans hay.symm))

/-- Equivalent `PieceCert` form for `petersenGraph` (`GP(5, 2)`): no global `PieceCert` exists for
any record count `m`. -/
theorem petersen_no_pieceCert_univ : ¬ Nonempty (PieceCert (nbhd petersenGraph) ∅ univ) := by
  have hnb : nbhd petersenGraph = nbhd gp52 := by
    ext v u
    revert v u
    decide
  rw [hnb]
  rintro ⟨p⟩
  exact gp52_no_elimCert p.m ⟨elimCert_of_pieceCert_univ p⟩

/-- **Part 2a of Proposition GP (`GP(7, 2)` 3-record impossibility)**: `GP(7, 2)` (`n = 14`) admits
**no** global elimination certificate with `m ≤ 3` records. -/
theorem gp72_no_elimCert_le3 {m : ℕ} (hm : m ≤ 3) : ¬ Nonempty (ElimCert (nbhd gp72) m) := by
  rintro ⟨c⟩
  have hm0 : 0 < m := Fin.pos (c.a 0)
  let emb : Fin m → Fin 3 := fun r => ⟨r.val, by omega⟩
  have hemb_inj : Function.Injective emb :=
    fun r₁ r₂ h => Fin.ext (by simpa [emb] using congrArg Fin.val h)
  have hswap_gen : ∀ c0 x y : Fin 3,
      (if x = c0 then 0 else if x = 0 then c0 else x) =
      (if y = c0 then 0 else if y = 0 then c0 else y) → x = y := by decide
  let c0 : Fin 3 := emb (c.a 0)
  let swap0 : Fin 3 → Fin 3 := fun x => if x = c0 then 0 else if x = 0 then c0 else x
  have hswap_inj : Function.Injective swap0 := fun x y h => hswap_gen c0 x y h
  let col : Fin 14 → Fin 3 := fun u => swap0 (emb (c.a u))
  have hcol_iff : ∀ u v : Fin 14, col u = col v ↔ c.a u = c.a v :=
    fun u v => ⟨fun h => hemb_inj (hswap_inj h), fun h => by simp [col, h]⟩
  have h0 : col ⟨0, by decide⟩ = 0 := by simp [col, swap0, c0]
  have hprop : ∀ i : Fin 14, ∀ u ∈ gpAdj7 i, col u ≠ col i := by
    intro i u hu heq
    exact elimCert_adj_ne c hu ((hcol_iff u i).mp heq).symm
  obtain ⟨S, hSu, hstuck⟩ := checkAllProper3Colorings_sound (by decide)
    gpAdj7 gp72_3col_chk col h0 hprop
  obtain ⟨v, hvS, hNv⟩ := c.elim S hSu
  obtain ⟨x, hx, y, hy, hxS, hyS, hne⟩ := hstuck v hvS
  have hx' : x ∈ nbhd gp72 v := mem_filter.mpr ⟨mem_univ x, hx⟩
  have hy' : y ∈ nbhd gp72 v := mem_filter.mpr ⟨mem_univ y, hy⟩
  have hxP : x ∈ c.P (c.b v) := (mem_union.mp (hNv hx')).resolve_left hxS
  have hyP : y ∈ c.P (c.b v) := (mem_union.mp (hNv hy')).resolve_left hyS
  have hax : c.a x = c.b v := by
    by_contra h1; exact Finset.disjoint_left.mp (c.disj _ _ h1) (c.own x) hxP
  have hay : c.a y = c.b v := by
    by_contra h1; exact Finset.disjoint_left.mp (c.disj _ _ h1) (c.own y) hyP
  exact hne ((hcol_iff x y).mpr (hax.trans hay.symm))

theorem gp72_no_pieceCert_univ_le3 :
    ¬ ∃ p : PieceCert (nbhd gp72) ∅ univ, p.m ≤ 3 := by
  rintro ⟨p, hp⟩
  exact gp72_no_elimCert_le3 hp ⟨elimCert_of_pieceCert_univ p⟩

def gp72_a : Fin 14 → Fin 4 := ![0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 0, 1, 2, 3]
def gp72_b : Fin 14 → Fin 4 := ![1, 0, 3, 0, 1, 2, 0, 3, 1, 0, 2, 3, 1, 2]
def gp72_ord : Fin 14 → Fin 14 := ![3, 4, 5, 10, 11, 12, 13, 6, 0, 7, 8, 1, 2, 9]

/-- **Part 2b of Proposition GP (`GP(7, 2)` explicit 4-record global certificate)**: `GP(7, 2)`
admits an explicit `4`-record global elimination certificate (`strictly separating m = 3 from m = 4`). -/
def gp72_elimCert4 : ElimCert (nbhd gp72) 4 :=
  mkElimCertOfOrder gp72 gp72_a gp72_b gp72_ord (by decide) (by decide) (by decide)

theorem gp72_pieceCert_univ_4 : ∃ p : PieceCert (nbhd gp72) ∅ univ, p.m = 4 :=
  pieceCert_univ_of_elimCert gp72_elimCert4

def gp92_a : Fin 18 → Fin 3 := ![0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 2, 0, 1, 2, 2, 0, 0]
def gp92_b : Fin 18 → Fin 3 := ![1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 1, 0, 2, 2, 0, 0, 1, 2]
def gp92_ord : Fin 18 → Fin 18 := ![3, 4, 12, 13, 15, 6, 5, 14, 16, 7, 8, 17, 10, 1, 0, 9, 11, 2]

/-- **Part 3 of Proposition GP (`GP(9, 2)` explicit 3-record global certificate)**: `GP(9, 2)`
(`n = 18`) drops back from `4` records to an explicit `3`-record global elimination certificate. -/
def gp92_elimCert3 : ElimCert (nbhd gp92) 3 :=
  mkElimCertOfOrder gp92 gp92_a gp92_b gp92_ord (by decide) (by decide) (by decide)

theorem gp92_pieceCert_univ_3 : ∃ p : PieceCert (nbhd gp92) ∅ univ, p.m = 3 :=
  pieceCert_univ_of_elimCert gp92_elimCert3

/-- **Proposition GP (combined non-monotone record-count hierarchy across `GP(5,2), GP(7,2), GP(9,2)`).** -/
theorem generalizedPetersen_hierarchy :
    (∀ m, ¬ Nonempty (ElimCert (nbhd gp52) m)) ∧
    (∀ m ≤ 3, ¬ Nonempty (ElimCert (nbhd gp72) m)) ∧
    Nonempty (ElimCert (nbhd gp72) 4) ∧
    Nonempty (ElimCert (nbhd gp92) 3) :=
  ⟨gp52_no_elimCert, fun _ hm => gp72_no_elimCert_le3 hm, ⟨gp72_elimCert4⟩, ⟨gp92_elimCert3⟩⟩

end HierarchyResults

end DirectedReciprocity
