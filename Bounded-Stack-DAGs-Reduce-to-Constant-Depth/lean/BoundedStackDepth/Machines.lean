import BoundedStackDepth.Main
import MergeDepth.LinearCrux
import MergeDepth.FieldMachine

/-!
# Corollaries O and HV: depth reduction for oblivious machines and for their codes

The machine-level consequences of Theorem T, in the frozen machine model of the first paper, through
the eleventh paper's library (`MergeDepth`): its traces, dependency DAGs (`DepStep`, `IsDepPath`),
genies (`LinNet.GFree`), index codes (`IsIndexCode`) and linear data paths (`LinDataPath`).

* `genie`, `genie_cost`: **the genie.** For `k` walks, pauses allowed, the heads of the edges of
  Theorem T's cut at `ε/(4βC)` and the steps `≡ R - 1 (mod R)`, `R = ⌈4βC/ε⌉`, form a genie of cost
  `β |Γ| ≤ ε L` (for `T ≤ C (L + 1)`) under which every path of the dependency DAG has at most
  `genieDepth k β C ε = K^P ⌈4βC/ε⌉` vertices, `K` and `P` the parameters of Theorem T at
  `ε/(4βC)`. This is the eleventh paper's cold genie with Theorem T in place of Theorem F, so no step
  is excluded.
* `genie_of_trace`, `DepthTCP`, `depthTCP`: **(a) of Corollary O.** Every trace of every machine has
  such a genie; in particular `depth-TCP(k, C, β, ε, D)` (the fourth paper's Definition 4.7) holds.
* `depCone`, `coneSystem`, `SCone`, `CruxOn`, `Crux`: the cone systems `I_Γ`, the class
  `S_{k,C,β,D}` and the crux `Crux(S_{k,C,β,D}, ρ)` (the fourth paper's Definition 4.8).
* `exists_indexCode`: for an oblivious transposer, the revealed values of any set `Γ` of steps form
  an index code with `β |Γ|` bits for its cone system: the eleventh paper's `field_isIndexCode` for
  the full pruning, whose field cones project into the cones of the dependency DAG
  (`coneI_subset_depCone`).
* `crux_excludes`: **(b).** If `Crux(S_{k,C,β,D}, ρ)` holds for some `ρ > ε`, then at all large
  sizes `d` no machine with `k` work tapes and value width at most `β` is oblivious at length
  `L = d² b(d)`, halts within `C (L + 1)` steps and transposes.
* `ballSystem_minrank`, `linCrux_excludes`: **(c).** The same for machines with an `F`-linear data
  path, under the linear crux `LinCrux_F(S_ball_{k,C,β,D}, ρ)` (the eighth paper's Definition 7.4, as
  formalized in the eleventh paper's library): the rigidity step bounds the minrank of the ball system
  of radius `genieDepth k β C ε` by `εL`.
* `coneSystem_subset_ballSystem`, `ballSystem_indexCode`: **Corollary HV.** The cones of the genie lie
  in the balls `B^D(ℓ)` of the eleventh paper (`MergeDepth.ballSystem`), so the ball system of radius
  `genieDepth k β C ε` of an oblivious transposer has an index code with at most `εL` bits.
* `ConjHVStar`, `ConjHVStarLin`, `hvStar`, `hvStar_linear`: the eleventh paper's Conjecture HV*
  (code-level depth reduction, its Conjecture 3.22) holds, in both its forms.
-/

namespace BoundedStackDepth

open Finset BoundedNesting MergeDepth Transpose Transpose.Tape

/-! ### The genie -/

open Classical in
/-- **The genie.** The heads of the edges of Theorem T's cut at `ε` and the steps `≡ R - 1 (mod R)`
form a set `Γ` of at most `εT + T/R` steps under which every path of the dependency DAG has at most
`K^P · R` vertices: a path avoids the cut, so it has fewer than `K^P` hop steps, and its runs of
state steps have fewer than `R` steps. -/
theorem genie (k : ℕ) {ε : ℝ} (hε : 0 < ε) {R : ℕ} (hR : 1 ≤ R) (xs : Fin k → ℕ → ℤ)
    (hx : ∀ h, IsWalk (xs h)) (T : ℕ) :
    ∃ Γ : Finset ℕ, (R * Γ.card : ℝ) ≤ R * ε * T + T ∧
      ∀ π, IsDepPath xs T π → LinNet.GFree Γ π → π.length ≤ parK k ε ^ parP k ε * R := by
  obtain ⟨cutS, cutH, -, -, hcard, hF⟩ := tcpAt_direct k hε T xs hx
  set Γ := cutS.image (· - 1) ∪ cutH.image Prod.fst ∪ periodic T R
  refine ⟨Γ, ?_, ?_⟩
  · have h1 : Γ.card ≤ cutS.card + cutH.card + (periodic T R).card :=
      (card_union_le _ _).trans (Nat.add_le_add_right
        ((card_union_le _ _).trans (Nat.add_le_add card_image_le card_image_le)) _)
    have h2 := card_periodic_le T R hR
    have h1' : (Γ.card : ℝ) ≤ cutS.card + cutH.card + (periodic T R).card := by exact_mod_cast h1
    have h2' : (R * (periodic T R).card : ℝ) ≤ T := by exact_mod_cast h2
    have hcard' : ((cutS.card : ℝ) + cutH.card) ≤ ε * T := by exact_mod_cast hcard
    have hP' : (0 : ℝ) ≤ R := by positivity
    nlinarith
  · intro π hp hfree
    rcases π with _ | ⟨t, ρ⟩
    · simp
    set π := t :: ρ with hπ
    set f : ℕ → ℕ := fun i => π.getD i 0
    have hnotΓ : ∀ i, i + 1 < π.length → f (i + 1) ∉ Γ := fun i hi =>
      hfree _ (getD_mem_tail π i hi)
    -- the steps of `π` avoid Theorem T's cut
    have hsteps : AvoidPath T (hopPairs (allHops xs T)) cutH cutS f (π.length - 1) := by
      intro i hi
      have hi' : i + 1 < π.length := by omega
      have hs := depStep_getD xs T π hp i hi'
      have hΓ := hnotΓ i hi'
      by_cases hst : f (i + 1) + 1 = f i
      · left
        rcases hs with ⟨-, hT⟩ | hhop
        · refine ⟨hst, by omega, hT, fun hS => hΓ ?_⟩
          exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨_, hS, by
            show f i - 1 = f (i + 1)
            omega⟩))
        · obtain ⟨η, hη, he⟩ := mem_image.mp hhop
          have := (mem_allHops.mp hη)
          simp only [Prod.mk.injEq] at he
          exfalso
          have := this.1
          simp only [f] at hst
          omega
      · right
        rcases hs with ⟨hb, -⟩ | hhop
        · exact absurd hb hst
        · exact ⟨hhop, fun hc =>
            hΓ (mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨_, hc, rfl⟩)))⟩
    have hFcount : ((range (π.length - 1)).filter
        fun i => (f (i + 1), f i) ∈ hopPairs (allHops xs T)).card ≤ parK k ε ^ parP k ε - 1 :=
      hF f (π.length - 1) hsteps
    have hK : 1 ≤ parK k ε ^ parP k ε := Nat.one_le_pow _ _ (by unfold parK; omega)
    -- so the path has fewer than `K^P` hop steps
    have hhops : hopCount π < parK k ε ^ parP k ε := by
      rw [hopCount_eq]
      refine lt_of_le_of_lt (card_le_card fun i hi => ?_) (lt_of_le_of_lt hFcount (by omega))
      obtain ⟨hi, hne⟩ := mem_filter.mp hi
      refine mem_filter.mpr ⟨hi, ?_⟩
      rcases hsteps i (mem_range.mp hi) with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hne
      · exact h
    -- runs of state steps have fewer than `R` steps
    have hlen := length_le_hops_aux xs T hR ρ t 0 hp (fun v hv hvP =>
        hfree v (by simpa [hπ] using hv) (mem_union_right _ hvP))
      (fun ρ' hρ' hρc hρf => by simpa using state_run_le xs T hR ρ' t hρ' hρc hρf)
    rw [zero_add] at hlen
    calc π.length ≤ (hopCount π + 1) * R := hlen
      _ ≤ parK k ε ^ parP k ε * R := Nat.mul_le_mul_right _ hhops

/-- **The depth of the genie**: `D = D₁ ⌈4βC/ε⌉` with `D₁ = K^P` at `ε/(4βC)`, the parameters of
Theorem T (`parK`, `parP`). -/
noncomputable def genieDepth (k β : ℕ) (C ε : ℝ) : ℕ :=
  parK k (ε / (4 * β * C)) ^ parP k (ε / (4 * β * C)) * ⌈4 * β * C / ε⌉₊

/-- **The genie with its cost.** For `C ≥ 1`, `β ≥ 1`, `ε > 0`, `L ≥ 1` and `T ≤ C (L + 1)`, the
genie of `genie` at `ε/(4βC)` with `R = ⌈4βC/ε⌉` has cost `β |Γ| ≤ ε L`, and every path of the
dependency DAG that avoids it has at most `genieDepth k β C ε` vertices. -/
theorem genie_cost {k β L T : ℕ} (hβ : 1 ≤ β) (hL : 1 ≤ L) {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε)
    (hT : (T : ℝ) ≤ C * (L + 1)) (xs : Fin k → ℕ → ℤ) (hx : ∀ h, IsWalk (xs h)) :
    ∃ Γ : Finset ℕ, (β * Γ.card : ℝ) ≤ ε * L ∧
      ∀ π, IsDepPath xs T π → LinNet.GFree Γ π → π.length ≤ genieDepth k β C ε := by
  have hC0 : (0 : ℝ) < C := by linarith
  have hβ' : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have hβC : (0 : ℝ) < 4 * β * C := by positivity
  set R := ⌈4 * β * C / ε⌉₊
  have hR : 1 ≤ R := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  obtain ⟨Γ, hcard, hpath⟩ := genie k (div_pos hε hβC) hR xs hx T
  refine ⟨Γ, ?_, hpath⟩
  -- `β |Γ| ≤ β (ε/(4βC)) T + β T / R ≤ ε T / (2C) ≤ ε (L + 1)/2 ≤ ε L`
  have hPge : 4 * β * C / ε ≤ (R : ℝ) := Nat.le_ceil _
  have hPpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : (Γ.card : ℝ) ≤ ε / (4 * β * C) * T + T / R := by
    have : (R : ℝ) * Γ.card ≤ R * (ε / (4 * β * C)) * T + T := hcard
    calc (Γ.card : ℝ) = (R * Γ.card) / R := by field_simp
      _ ≤ (R * (ε / (4 * β * C)) * T + T) / R := by gcongr
      _ = ε / (4 * β * C) * T + T / R := by field_simp
  have h2 : (T : ℝ) / R ≤ ε / (4 * β * C) * T := by
    rw [div_le_iff₀ hPpos]
    have : ε / (4 * β * C) * R ≥ 1 := by
      rw [ge_iff_le, ← div_le_iff₀' (div_pos hε hβC), one_div_div]
      exact hPge
    have hT0 : (0 : ℝ) ≤ T := by positivity
    nlinarith
  have h3 : (β : ℝ) * Γ.card ≤ ε * T / (2 * C) := by
    have : (β : ℝ) * Γ.card ≤ β * (2 * (ε / (4 * β * C) * T)) := by
      gcongr
      linarith
    calc (β : ℝ) * Γ.card ≤ β * (2 * (ε / (4 * β * C) * T)) := this
      _ = ε * T / (2 * C) := by field_simp; ring
  calc (β : ℝ) * Γ.card ≤ ε * T / (2 * C) := h3
    _ ≤ ε * (C * (L + 1)) / (2 * C) := by gcongr
    _ = ε * (L + 1) / 2 := by field_simp
    _ ≤ ε * L := by nlinarith

/-- **(a) of Corollary O.** For every machine `M`, every input `w`, `L ≥ 1`, `β ≥ 1` and every horizon
`T ≤ C (L + 1)`, the dependency DAG of the work-head walks of the trace of `w` has a genie of cost
`β |Γ| ≤ ε L` under which every path has at most `genieDepth M.k β C ε` vertices. -/
theorem genie_of_trace (M : TM) (w : List Bool) {β L T : ℕ} (hβ : 1 ≤ β) (hL : 1 ≤ L) {C ε : ℝ}
    (hC : 1 ≤ C) (hε : 0 < ε) (hT : (T : ℝ) ≤ C * (L + 1)) :
    ∃ Γ : Finset ℕ, (β * Γ.card : ℝ) ≤ ε * L ∧
      ∀ π, IsDepPath (trace M w).work T π → LinNet.GFree Γ π → π.length ≤ genieDepth M.k β C ε :=
  genie_cost hβ hL hC hε hT _ (trace M w).work_isWalk

/-- The value width of a machine is at least `2`. -/
theorem two_le_valueWidth (M : TM) : 2 ≤ valueWidth M := by
  unfold valueWidth
  omega

/-- **`depth-TCP(k, C, β, ε, D)`** (the fourth paper's Definition 4.7), in the frozen model: every
machine with `k` work tapes and value width at most `β` has, at every large size `d` at which it is
oblivious at length `L = d² b(d)` with halting time `T ≤ C (L + 1)`, a genie of cost `β |Γ| ≤ ε L`
whose avoiding paths have at most `D` edges (full depth at most `D`). -/
def DepthTCP (k : ℕ) (C : ℝ) (β : ℕ) (ε : ℝ) (D : ℕ) : Prop :=
  ∀ M : TM, M.k = k → valueWidth M ≤ β → ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ T : ℕ,
    ObliviousOn M (inputsOfLength (d * d * entryBits d)) T →
    (T : ℝ) ≤ C * ((d * d * entryBits d : ℕ) + 1) →
    ∃ Γ : Finset ℕ, (β * Γ.card : ℝ) ≤ ε * (d * d * entryBits d : ℕ) ∧
      ∀ π, IsDepPath (traceAt M (d * d * entryBits d)).work T π → LinNet.GFree Γ π →
        π.length ≤ D + 1

/-- **(a) of Corollary O, as depth-TCP**: `depth-TCP(k, C, β, ε, genieDepth k β C ε)` holds for
every `C ≥ 1` and `ε > 0`, with threshold `d₀ = 1`. -/
theorem depthTCP {k β : ℕ} {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) :
    DepthTCP k C β ε (genieDepth k β C ε) := by
  intro M hk hβ
  refine ⟨1, fun d hd T _ hT => ?_⟩
  have hL : 1 ≤ d * d * entryBits d := Nat.mul_pos (Nat.mul_pos hd hd) (one_le_entryBits d)
  obtain ⟨Γ, hc, hp⟩ := genie_of_trace M (List.ofFn fun _ : Fin (d * d * entryBits d) => false)
    ((two_le_valueWidth M).trans' (by omega) |>.trans hβ) hL hC hε hT
  subst hk
  exact ⟨Γ, hc, fun π h1 h2 => (hp π h1 h2).trans (Nat.le_succ _)⟩

/-! ### Cone systems and the crux -/

section Crux

variable {k : ℕ}

open Classical in
/-- **The cone set** `I_Γ(t)` of a step `t` of the dependency DAG of the walks `xs` before `T`: the
positions read (`rdStep`) at the ends of the `Γ`-free dependency paths from `t`. -/
noncomputable def depCone {L : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ) (rdStep : ℕ → Option (Fin L))
    (Γ : Finset ℕ) (t : ℕ) : Finset (Fin L) :=
  univ.filter fun j => ∃ π : List ℕ, IsDepPath xs T (t :: π) ∧ LinNet.GFree Γ (t :: π) ∧
    rdStep ((t :: π).getLastD t) = some j

/-- **The cone system** `(I_Γ(ℓ))_ℓ` of a trace: the cone set of the append step of every output
position `ℓ`, the positions being those read by the input head (`readPos`). -/
noncomputable def coneSystem (τ₀ : Trace k) (T : ℕ) (Γ : Finset ℕ) (d b : ℕ) :
    Fin (d * d * b) → Finset (Fin (d * d * b)) :=
  fun ℓ => depCone τ₀.work T (readPos τ₀ (d * d * b)) Γ (appendTime τ₀ T ℓ)

end Crux

/-- **The class `S_{k,C,β,D}`** (the fourth paper's Definition 4.8), at size `(d, b)` and length
`L = d² b`: the cone systems `I_Γ` of the machines `M` with `k` work tapes and value width at most
`β` that are oblivious at length `L` (frozen `ObliviousOn`) with halting time `T ≤ C (L + 1)` and
append exactly `L` bits, for the sets `Γ` of steps whose avoiding dependency paths have at most `D`
edges. -/
def SCone (k : ℕ) (C : ℝ) (β D d b : ℕ) : Set (Fin (d * d * b) → Finset (Fin (d * d * b))) :=
  {I | ∃ (M : TM) (T : ℕ) (Γ : Finset ℕ), M.k = k ∧ valueWidth M ≤ β ∧
    ObliviousOn M (inputsOfLength (d * d * b)) T ∧ (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1) ∧
    (appendList (traceAt M (d * d * b)) T).length = d * d * b ∧
    (∀ π, IsDepPath (traceAt M (d * d * b)).work T π → LinNet.GFree Γ π → π.length ≤ D + 1) ∧
    I = coneSystem (traceAt M (d * d * b)) T Γ d b}

/-- **The crux `Crux(S_{k,C,β,D}, ρ)`** (the fourth paper's Definition 4.8), at the sizes `(d, b)`
with `B d b`: for every `η > 0` there is `d₀` such that every index code for every system of
`S_{k,C,β,D}` at a size `d ≥ d₀` has at least `(ρ - η) L` bits. -/
def CruxOn (B : ℕ → ℕ → Prop) (k : ℕ) (C : ℝ) (β D : ℕ) (ρ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, B d b → ∀ I ∈ SCone k C β D d b,
    ∀ (m : ℕ) (E : (Fin (d * d * b) → Bool) → (Fin m → Bool)), IsIndexCode E I (tposOf d b) →
      (ρ - η) * (d * d * b : ℕ) ≤ m

/-- **The crux at the lengths of the paper**, `L = d² b(d)` (`entryBits`). -/
abbrev Crux (k : ℕ) (C : ℝ) (β D : ℕ) (ρ : ℝ) : Prop :=
  CruxOn (fun d b => b = entryBits d) k C β D ρ

/-- An index code for a system is one for every larger system. -/
theorem IsIndexCode.mono {L : ℕ} {α : Type*} {E : (Fin L → Bool) → α}
    {I J : Fin L → Finset (Fin L)} {tpos : Fin L → Fin L} (h : IsIndexCode E I tpos)
    (hIJ : ∀ ℓ, I ℓ ⊆ J ℓ) : IsIndexCode E J tpos :=
  fun ℓ w w' hE hJ => h ℓ w w' hE fun j hj => hJ j (hIJ ℓ hj)

/-- **Index codes with `m` bits.** An index code with at most `2^m` code words gives one with values
in `{0,1}^m`. -/
theorem IsIndexCode.bits {L m : ℕ} {α : Type*} {inst : DecidableEq α} {E : (Fin L → Bool) → α}
    {I : Fin L → Finset (Fin L)} {tpos : Fin L → Fin L} (h : IsIndexCode E I tpos)
    (hcard : (@Finset.image _ _ inst E univ).card ≤ 2 ^ m) :
    ∃ E' : (Fin L → Bool) → (Fin m → Bool), IsIndexCode E' I tpos := by
  have hc : Fintype.card (@Finset.image _ _ inst E univ) ≤ Fintype.card (Fin m → Bool) := by
    simpa using hcard
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun w => ι ⟨E w, mem_image_of_mem _ (mem_univ w)⟩, fun ℓ w w' hE hI => h ℓ w w' ?_ hI⟩
  exact congrArg Subtype.val (ι.injective hE)

/-- The last vertex of a path, after mapping its vertices. -/
theorem getLastD_cons_map (g : ℕ → ℕ) : ∀ (ρ : List ℕ) (u : ℕ),
    (g u :: ρ.map g).getLastD (g u) = g ((u :: ρ).getLastD u)
  | [], _ => rfl
  | v :: ρ, u => by
    rw [List.map_cons, LinNet.getLastD_cons_cons, LinNet.getLastD_cons_cons]
    exact getLastD_cons_map g ρ v

open Classical in
/-- **Field cones lie in dependency cones.** In the field DAG of a pruning, with the fields of the
steps of `Γ` revealed, the cone set of a field node of step `t` lies in the cone set `I_Γ(t)` of the
dependency DAG: a field path projects to a dependency path (`isDepPath_map`, `toFunDag_edge`) that
avoids `Γ`, and reads the position read at its last step (`toFunDag_rd`). -/
theorem coneI_subset_depCone {M : TM} {L T : ℕ} {τ₀ : Trace M.k} (Pr : Pruning M L τ₀ T)
    (Γ : Finset ℕ) (u : ℕ) :
    coneI Pr.toFunDag.net (Γ.biUnion (fieldNodesAt M.k)) u ⊆
      depCone τ₀.work T (readPos τ₀ L) Γ (u / (M.k + 2)) := by
  intro j hj
  simp only [coneI, mem_filter, mem_univ, true_and] at hj
  obtain ⟨π, hπ, hfree, hrd⟩ := hj
  obtain ⟨ρ, rfl⟩ := Pr.toFunDag.net.mem_paths_head hπ
  have hdep := isDepPath_map Pr.toFunDag (· / (M.k + 2)) τ₀.work T
    (fun u v hv => Pr.toFunDag_edge u v hv) (u :: ρ) u hπ
  simp only [depCone, mem_filter, mem_univ, true_and]
  refine ⟨ρ.map (· / (M.k + 2)), by simpa using hdep, fun v hv hvΓ => ?_, ?_⟩
  · simp only [List.tail_cons, List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact hfree w (by simpa using hw) (mem_biUnion.mpr ⟨_, hvΓ, mem_fieldNodesAt.mpr rfl⟩)
  · rw [getLastD_cons_map (· / (M.k + 2)) ρ u]
    exact Pr.toFunDag_rd _ j hrd

open Classical in
/-- **The index code of a genie** (the fourth paper's cone lemma and Theorem D at one size). For an
oblivious transposer and any set `Γ` of steps, with `β ≥ β(M)`, the values of the steps of `Γ`
determine an index code with `β |Γ|` bits for the cone system `I_Γ`. -/
theorem exists_indexCode {M : TM} {d b T : ℕ} {τ₀ : Trace M.k}
    (hM : ObliviousTransposer M d b τ₀ T) {β : ℕ} (hβ : valueWidth M ≤ β) (Γ : Finset ℕ) :
    ∃ E : (Fin (d * d * b) → Bool) → (Fin (β * Γ.card) → Bool),
      IsIndexCode E (coneSystem τ₀ T Γ d b) (tposOf d b) := by
  obtain ⟨hcode, hcard⟩ := Pruning.field_isIndexCode hM (Pruning.full hM.follows) hβ Γ ∅ ∅
  refine IsIndexCode.bits (IsIndexCode.mono hcode fun ℓ => ?_) (by simpa using hcard)
  split_ifs with h
  · exact empty_subset _
  · have := coneI_subset_depCone (Pruning.full hM.follows) Γ (outputNodeOf τ₀ T ℓ)
    simpa [union_empty, outputNodeOf_div, coneSystem] using this

/-- **(b) of Corollary O: the crux alone excludes oblivious linear-time transposers.** Let `C ≥ 1`
and `ε > 0`. If `Crux(S_{k,C,β,D}, ρ)` holds for some `ρ > ε`, with `D = genieDepth k β C ε`, then
there is `d₀` such that for no `d ≥ d₀` is any machine with `k` work tapes and value width at most
`β` oblivious at length `L = d² b(d)` with halting time at most `C (L + 1)` and a transposer of all
`d × d` matrices with `b(d)`-bit entries. -/
theorem crux_excludes {k β : ℕ} {C ε ρ : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) (hερ : ε < ρ)
    (hcrux : Crux k C β (genieDepth k β C ε) ρ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ M : TM, M.k = k → valueWidth M ≤ β → ∀ T : ℕ,
      ¬ ObliviousLinTime M d (entryBits d) C T := by
  obtain ⟨d₁, hd₁⟩ := hcrux ((ρ - ε) / 2) (by linarith)
  refine ⟨max d₁ 1, fun d hd M hk hβ T ⟨hobl, hT, htr⟩ => ?_⟩
  have hd1 : 1 ≤ d := (le_max_right _ _).trans hd
  have hL : 1 ≤ d * d * entryBits d := Nat.mul_pos (Nat.mul_pos hd1 hd1) (one_le_entryBits d)
  obtain ⟨hM, hlen⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
  have hβ1 : 1 ≤ β := (two_le_valueWidth M).trans' (by omega) |>.trans hβ
  obtain ⟨Γ, hcost, hpath⟩ := genie_of_trace M (List.ofFn fun _ : Fin (d * d * entryBits d) => false)
    hβ1 hL hC hε hT
  obtain ⟨E, hE⟩ := exists_indexCode hM hβ Γ
  subst hk
  have hmem : coneSystem (traceAt M (d * d * entryBits d)) T Γ d (entryBits d) ∈
      SCone M.k C β (genieDepth M.k β C ε) d (entryBits d) :=
    ⟨M, T, Γ, rfl, hβ, hobl, hT, hlen, fun π h1 h2 => (hpath π h1 h2).trans (Nat.le_succ _), rfl⟩
  have hbits := hd₁ d ((le_max_left _ _).trans hd) (entryBits d) rfl _ hmem _ E hE
  have hL' : (1 : ℝ) ≤ (d * d * entryBits d : ℕ) := by exact_mod_cast hL
  push_cast at hbits hcost hL'
  nlinarith

/-- **The ball systems of linear oblivious transposers have small minrank** (the rigidity step of
(c)). For a machine with `k` work tapes and value width at most `β` that is oblivious at length
`L = d² b(d)` with halting time `T ≤ C (L + 1)`, transposes, and has an `F`-linear data path, the
minrank over `F` of its ball system of radius `genieDepth k β C ε` is at most `εL`. -/
theorem ballSystem_minrank (F : Type*) [Field F] {k β : ℕ} {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε)
    {d : ℕ} (hd : 1 ≤ d) (M : TM) (hk : M.k = k) (hβ : valueWidth M ≤ β) {T m : ℕ}
    (hM : ObliviousLinTime M d (entryBits d) C T)
    (P : LinDataPath F M (d * d * entryBits d) (traceAt M (d * d * entryBits d)) T m) :
    (LinNet.minrank F (tposOf d (entryBits d))
        (ballSystem (traceAt M (d * d * entryBits d)) T (genieDepth k β C ε) d (entryBits d)) : ℝ) ≤
      ε * (d * d * entryBits d : ℕ) := by
  classical
  obtain ⟨hobl, hT, htr⟩ := hM
  have hL : 1 ≤ d * d * entryBits d := Nat.mul_pos (Nat.mul_pos hd hd) (one_le_entryBits d)
  obtain ⟨hO, -⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
  have hβ1 : 1 ≤ β := (two_le_valueWidth M).trans' (by omega) |>.trans hβ
  obtain ⟨Γ, hcost, hpath⟩ := genie_of_trace M (List.ofFn fun _ : Fin (d * d * entryBits d) => false)
    hβ1 hL hC hε hT
  subst hk
  -- full depth bounds linear depth: outside the reach, the path sums are empty
  have hdepth : ∀ ℓ j : Fin (d * d * entryBits d),
      j ∉ P.net.reach Γ (genieDepth M.k β C ε) (appendTime (traceAt M (d * d * entryBits d)) T ℓ) →
      P.φ ℓ ⬝ᵥ P.net.C Γ (appendTime (traceAt M (d * d * entryBits d)) T ℓ) j = 0 := by
    intro ℓ j hj
    have hC0 : P.net.C Γ (appendTime (traceAt M (d * d * entryBits d)) T ℓ) j = 0 := by
      unfold LinNet.C
      refine sum_eq_zero fun π hπ => absurd ?_ hj
      obtain ⟨hπp, hfree, hrd⟩ := mem_filter.mp hπ
      simp only [LinNet.reach, mem_filter, mem_univ, true_and]
      exact ⟨π, hπp, hfree, (hpath π (isDepPath_of_paths P.net_depStep π _ hπp) hfree).trans
        (Nat.le_succ _), hrd⟩
    rw [hC0, dotProduct_zero]
  obtain ⟨-, hrank⟩ := P.rigidity_machine hO hβ Γ _ hdepth
  have hrank' : (LinNet.minrank F (tposOf d (entryBits d))
      (ballSystem (traceAt M (d * d * entryBits d)) T (genieDepth M.k β C ε) d (entryBits d)) : ℝ) ≤
      β * Γ.card := by exact_mod_cast hrank
  linarith

/-- **(c) of Corollary O: the linear crux alone excludes oblivious linear-time transposers with a
linear data path.** Let `C ≥ 1` and `ε > 0`. If `LinCrux_F(S_ball_{k,C,β,D}, ρ)` holds for some
`ρ > ε`, with `D = genieDepth k β C ε`, then there is `d₀` such that for no `d ≥ d₀` is any machine
with `k` work tapes and value width at most `β` oblivious at length `L = d² b(d)` with halting time
at most `C (L + 1)`, a transposer, and equipped with an `F`-linear data path. -/
theorem linCrux_excludes (F : Type*) [Field F] {k β : ℕ} {C ε ρ : ℝ} (hC : 1 ≤ C) (hε : 0 < ε)
    (hερ : ε < ρ) (hcrux : LinCrux F k C β (genieDepth k β C ε) ρ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ M : TM, M.k = k → valueWidth M ≤ β → ∀ T : ℕ,
      ¬ (ObliviousLinTime M d (entryBits d) C T ∧
        ∃ m, Nonempty (LinDataPath F M (d * d * entryBits d) (traceAt M (d * d * entryBits d)) T m)) := by
  obtain ⟨d₁, hd₁⟩ := hcrux ((ρ - ε) / 2) (by linarith)
  refine ⟨max d₁ 1, fun d hd M hk hβ T ⟨hM, m, ⟨P⟩⟩ => ?_⟩
  have hd1 : 1 ≤ d := (le_max_right _ _).trans hd
  have hL : 1 ≤ d * d * entryBits d := Nat.mul_pos (Nat.mul_pos hd1 hd1) (one_le_entryBits d)
  have hrank := ballSystem_minrank F hC hε hd1 M hk hβ hM P
  obtain ⟨hobl, hT, htr⟩ := hM
  obtain ⟨-, hlen⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
  subst hk
  have hcr := hd₁ d ((le_max_left _ _).trans hd) (entryBits d) rfl _
    ⟨M, T, rfl, hβ, hobl, hT, hlen, rfl⟩
  have hL' : (1 : ℝ) ≤ (d * d * entryBits d : ℕ) := by exact_mod_cast hL
  nlinarith

/-! ### Corollary HV: code-level depth reduction -/

/-- **The cones of a genie lie in the balls.** If every `Γ`-free path of the dependency DAG has at
most `D` vertices, the cone set of every output position lies in its ball `B^D(ℓ)` of the eleventh
paper: the input positions read at the ends of dependency paths of at most `D` edges from its append
step. -/
theorem coneSystem_subset_ballSystem {k : ℕ} {τ₀ : Trace k} {T : ℕ} {Γ : Finset ℕ} {D : ℕ}
    (hpath : ∀ π, IsDepPath τ₀.work T π → LinNet.GFree Γ π → π.length ≤ D) (d b : ℕ)
    (ℓ : Fin (d * d * b)) : coneSystem τ₀ T Γ d b ℓ ⊆ ballSystem τ₀ T D d b ℓ := by
  intro j hj
  simp only [coneSystem, depCone, ballSystem, stepBall, mem_filter, mem_univ, true_and] at hj ⊢
  obtain ⟨π, hπ, hfree, hrd⟩ := hj
  have hlen := hpath _ hπ hfree
  simp only [List.length_cons] at hlen
  exact ⟨π, hπ, by omega, hrd⟩

/-- **Corollary HV: the ball systems of oblivious transposers have short index codes.** For a
machine with `k` work tapes and value width at most `β` that is oblivious at length `L = d² b(d)`
with halting time `T ≤ C (L + 1)` and transposes, and for `C ≥ 1` and `ε > 0`, the ball system of
radius `genieDepth k β C ε` of its trace has an index code with at most `εL` bits: the code of the
genie of (a), for the larger side information. -/
theorem ballSystem_indexCode {k β : ℕ} {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) {d : ℕ} (hd : 1 ≤ d)
    (M : TM) (hk : M.k = k) (hβ : valueWidth M ≤ β) {T : ℕ}
    (hM : ObliviousLinTime M d (entryBits d) C T) :
    ∃ m : ℕ, (m : ℝ) ≤ ε * (d * d * entryBits d : ℕ) ∧
      ∃ E : (Fin (d * d * entryBits d) → Bool) → (Fin m → Bool),
        IsIndexCode E (ballSystem (traceAt M (d * d * entryBits d)) T (genieDepth k β C ε) d
          (entryBits d)) (tposOf d (entryBits d)) := by
  obtain ⟨hobl, hT, htr⟩ := hM
  have hL : 1 ≤ d * d * entryBits d := Nat.mul_pos (Nat.mul_pos hd hd) (one_le_entryBits d)
  obtain ⟨hO, -⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
  have hβ1 : 1 ≤ β := (two_le_valueWidth M).trans' (by omega) |>.trans hβ
  obtain ⟨Γ, hcost, hpath⟩ := genie_of_trace M (List.ofFn fun _ : Fin (d * d * entryBits d) => false)
    hβ1 hL hC hε hT
  obtain ⟨E, hE⟩ := exists_indexCode hO hβ Γ
  subst hk
  exact ⟨β * Γ.card, by exact_mod_cast hcost, E,
    IsIndexCode.mono hE fun ℓ => coneSystem_subset_ballSystem hpath d (entryBits d) ℓ⟩

/-- **Conjecture HV\* of the eleventh paper** (code-level depth reduction, its Conjecture 3.22),
all-code form, in the frozen machine model at the lengths `L = d² b(d)`: there is `c > 0` such that
for every `τ ≥ 1` there is a radius `r` with the following property. For every `η > 0` there is `d₀`
such that, for every `d ≥ d₀`, every machine with `k` work tapes and value width at most `β` that is
oblivious at length `L` with halting time `T ≤ C (L + 1)` and transposes all `d × d` matrices
(`ObliviousLinTime`) has an index code with at most `εL + c N_R / τ + ηL` bits for its ball system
of radius `r` (`MergeDepth.ballSystem`), where `N_R` counts the deep hops at `V` of its trace
(`MergeDepth.deepHops`). The conjecture assumes `k, V ≥ 1`, `β ≥ 2`, `C ≥ 1` and `0 < ε ≤ 1`; here
`C` is real, and the eleventh paper's integer `C` is a special case. -/
def ConjHVStar (k V β : ℕ) (C ε : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ τ : ℕ, 1 ≤ τ → ∃ r : ℕ, ∀ η : ℝ, 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ (M : TM) (T : ℕ), M.k = k → valueWidth M ≤ β → ObliviousLinTime M d (entryBits d) C T →
      ∃ m : ℕ, (m : ℝ) ≤ ε * (d * d * entryBits d : ℕ) +
          c * ((deepHops (traceAt M (d * d * entryBits d)).work T V).card : ℝ) / τ +
          η * (d * d * entryBits d : ℕ) ∧
        ∃ E : (Fin (d * d * entryBits d) → Bool) → (Fin m → Bool),
          IsIndexCode E (ballSystem (traceAt M (d * d * entryBits d)) T r d (entryBits d))
            (tposOf d (entryBits d))

/-- **Conjecture HV\* of the eleventh paper, linear form**: for a field `F` and a width `m` (the
constant `c` may depend on both), the same holds for the machines that moreover have an `F`-linear
data path of width at most `m` at length `L`, with the minrank over `F` of the ball system in place
of the length of an index code. -/
def ConjHVStarLin (F : Type*) [Field F] (k V β : ℕ) (C ε : ℝ) (m : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ τ : ℕ, 1 ≤ τ → ∃ r : ℕ, ∀ η : ℝ, 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ (M : TM) (T : ℕ), M.k = k → valueWidth M ≤ β → ObliviousLinTime M d (entryBits d) C T →
      ∀ m' ≤ m, Nonempty (LinDataPath F M (d * d * entryBits d) (traceAt M (d * d * entryBits d))
          T m') →
        (LinNet.minrank F (tposOf d (entryBits d))
            (ballSystem (traceAt M (d * d * entryBits d)) T r d (entryBits d)) : ℝ) ≤
          ε * (d * d * entryBits d : ℕ) +
            c * ((deepHops (traceAt M (d * d * entryBits d)).work T V).card : ℝ) / τ +
            η * (d * d * entryBits d : ℕ)

/-- **Corollary HV: Conjecture HV\* holds**, for all `k, V, β`, every `C ≥ 1` and every `ε > 0`,
with `c = 1`, the radius `genieDepth k β C ε` for every `τ`, and `d₀ = 1`. -/
theorem hvStar {k V β : ℕ} {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) : ConjHVStar k V β C ε := by
  refine ⟨1, one_pos, fun τ _ => ⟨genieDepth k β C ε, fun η hη => ⟨1, fun d hd M T hk hβ hM => ?_⟩⟩⟩
  obtain ⟨m, hm, E, hE⟩ := ballSystem_indexCode hC hε hd M hk hβ hM
  refine ⟨m, ?_, E, hE⟩
  have h1 : (0 : ℝ) ≤ 1 * ((deepHops (traceAt M (d * d * entryBits d)).work T V).card : ℝ) / τ := by
    positivity
  have h2 : (0 : ℝ) ≤ η * (d * d * entryBits d : ℕ) := by positivity
  linarith

/-- **Corollary HV, linear form: Conjecture HV\* holds in its linear form**, for every field `F`
and every width `m`, with the same `c`, radius and `d₀`. -/
theorem hvStar_linear (F : Type*) [Field F] {k V β : ℕ} {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε)
    (m : ℕ) : ConjHVStarLin F k V β C ε m := by
  refine ⟨1, one_pos, fun τ _ => ⟨genieDepth k β C ε, fun η hη =>
    ⟨1, fun d hd M T hk hβ hM m' _ ⟨P⟩ => ?_⟩⟩⟩
  have hrank := ballSystem_minrank F hC hε hd M hk hβ hM P
  have h1 : (0 : ℝ) ≤ 1 * ((deepHops (traceAt M (d * d * entryBits d)).work T V).card : ℝ) / τ := by
    positivity
  have h2 : (0 : ℝ) ≤ η * (d * d * entryBits d : ℕ) := by positivity
  linarith

end BoundedStackDepth
