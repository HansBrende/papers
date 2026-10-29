import SourceCovers.SerialTimes

set_option autoImplicit false

/-! Actual family hops and exact shadows for the serial continuation.
The last sparse return is clipped only in the ordinary shadow orbit. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset BoundedNesting
noncomputable section

variable (P : Parameters)

theorem bank_reflection_hop (c : Fin 2) (j : Fin P.bankCount) {a : ℕ}
    (ha : 0 < a) (hah : a ≤ P.width) :
    (Fin.castAdd 4 (P.bankHeadIndex c j),
      P.bankBase c + j.val * P.width + (P.width - a),
      P.bankBase c + (j.val + 1) * P.width + a) ∈ (P.bankFamily c j).hops := by
  rw [P.bankFamily_hops]
  let i : Fin P.width := ⟨a - 1, by omega⟩
  refine mem_image.mpr ⟨i, mem_univ _, Prod.ext rfl (Prod.ext ?_ ?_)⟩
  · dsimp only [i]
    have he : P.bankBase c + (j.val + 1) * P.width =
        P.bankBase c + j.val * P.width + P.width := by ring
    rw [he]
    omega
  · dsimp only [i]
    omega

theorem bank_reflection_shadow (c : Fin 2) (j : Fin P.bankCount) {a : ℕ}
    (ha : 0 < a) (hah : a < P.width) :
    (P.bankFamily c j).shadow (P.bankBase c + (j.val + 1) * P.width + a) =
      P.bankBase c + j.val * P.width + (P.width - a) := by
  have hh := P.bank_reflection_hop c j ha hah.le
  apply (P.bankFamily c j).shadow_exact P.heads_isWalk hh
  rw [P.bankFamily_start]
  dsimp only
  omega

theorem newer_serial_hop (k : Fin (P.m - 1)) :
    (4, P.bridgeReturn k, P.lateTime k) ∈ P.newerFamily.hops := by
  have hb := P.bridgeReturn_bounds k
  have hv := P.lateTime_bounds k
  have he : P.lateTime k + P.bridgeReturn k = 19 * P.length := by
    rw [bridgeReturn, ← P.lateWindow_eq k]
    dsimp only [lateTime] at hv ⊢
    omega
  let i : Fin P.length := ⟨P.bridgeReturn k - 7 * P.length, by omega⟩
  have hd : P.newer.depart i = P.bridgeReturn k := by
    rw [newer_depart]
    dsimp only [i]
    omega
  have hu : P.newer.arrive i = P.lateTime k := by
    rw [newer_arrive]
    dsimp only [i]
    omega
  rw [← hd, ← hu]
  exact NativeExcursion.mem_family (xs := P.heads) (T := P.horizon)
    P.newer 4 P.heads_newer (P.newer_before_horizon 0) i

theorem newer_serial_shadow (k : Fin (P.m - 1)) :
    P.newerFamily.shadow (P.lateTime k) = P.bridgeReturn k := by
  apply P.newerFamily.shadow_exact P.heads_isWalk (P.newer_serial_hop k)
  rw [newerFamily_start]
  exact (P.bridgeReturn_bounds k).1.ne'

theorem bridge_serial_hop (k : Fin (P.m - 1)) :
    (7, P.bridgeExit k, P.bridgeReturn k) ∈ P.bridgeFamily.hops := by
  let i : Fin P.length := ⟨P.laneHeight k, (P.laneHeight_bounds k).2.trans P.m_lt_length⟩
  have hd : P.bridge.depart i = P.bridgeExit k := rfl
  have hu : P.bridge.arrive i = P.bridgeReturn k :=
    P.bridgeArrival_delayed (by have := k.isLt; omega)
  rw [← hd, ← hu]
  exact NativeExcursion.mem_family (xs := P.heads) (T := P.horizon)
    P.bridge 7 P.heads_bridge (P.bridge_before_horizon 0) i

theorem bridge_serial_shadow (k : Fin (P.m - 1)) :
    P.bridgeFamily.shadow (P.bridgeReturn k) = P.bridgeExit k := by
  apply P.bridgeFamily.shadow_exact P.heads_isWalk (P.bridge_serial_hop k)
  rw [bridgeFamily_start]
  exact (P.bridgeExit_bounds k).1.ne'

theorem older_serial_hop (i : Fin P.targets) :
    (6, P.sparseDeparture i, P.sparseArrival i) ∈ P.olderFamily.hops :=
  NativeExcursion.mem_family (T := P.horizon) P.older 6 P.heads_older (P.older_before_horizon 0) i

theorem older_serial_shadow (i : Fin P.targets) :
    P.olderFamily.shadow (P.sparseArrival i) = P.coverSeed i := by
  have hs := NativeExcursion.family_shadow_arrive (T := P.horizon)
    P.older 6 P.heads_older (P.older_before_horizon 0) i
  change P.olderFamily.shadow (P.sparseArrival i) =
    max (P.sparseDeparture 0 + 1) (P.sparseDeparture i) at hs
  rw [hs, P.sparseDeparture_zero]
  by_cases hi : i = 0
  · subst i
    simp [coverSeed, sparseDeparture_zero]
  · have hl := P.gridFloor_large hi
    simp only [coverSeed, ite_eq_right hi, sparseDeparture]
    omega

theorem early_serial_hop (i : Fin P.targets) :
    (5, P.coverTarget i, P.coverSeed i) ∈ P.earlyFamily.hops := by
  let a : Fin P.length := ⟨P.coverTarget i, (P.coverTarget_bounds i).2⟩
  have hd : P.early.depart a = P.coverTarget i := P.early_depart a
  have hu : P.early.arrive a = P.coverSeed i := by
    rw [P.early_arrive]
    change 3 * P.length - P.coverTarget i = P.coverSeed i
    have hb := P.coverSeed_bounds i
    have he := P.early_shadow_coverSeed 5 P.heads_early
      (show P.early.arrive 0 < P.horizon from by
        rw [P.early_arrive]
        dsimp only [horizon]
        omega) i
    rw [P.early_shadow_return 5 P.heads_early _ hb.1 hb.2.le] at he
    omega
  rw [← hd, ← hu]
  exact NativeExcursion.mem_family (xs := P.heads) (T := P.horizon)
    P.early 5 P.heads_early _ a

theorem early_serial_shadow (i : Fin P.targets) :
    P.earlyFamily.shadow (P.coverSeed i) = P.coverTarget i :=
  P.early_shadow_coverSeed 5 P.heads_early _ i

end
end SourceCovers.SerialGeometry.Parameters
