import TransposeFollowup.RationalPageOpcode
import TransposeFollowup.RecordMotion

/-! Materialized page records and their exact head-walk semantics. Neither
list lengths nor this semantic refinement assert a native generation cost. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

def rationalOpcodeTable {c : ℕ} (F : Fin c → RationalMobius) (n : ℕ) :
    List.Vector (List.Vector PageOpcode (rationalPageCount F)) (2 * n) :=
  List.Vector.ofFn (fun u => List.Vector.ofFn (rationalPageOpcode F u))

theorem rationalOpcodeTable_get {c n : ℕ} (F : Fin c → RationalMobius)
    (u : Fin (2 * n)) (p : Fin (rationalPageCount F)) :
    ((rationalOpcodeTable F n).get u).get p = rationalPageOpcode F u p := by
  simp [rationalOpcodeTable]

def rationalOpcodeTape {c : ℕ} (F : Fin c → RationalMobius) (n : ℕ) : List PageOpcode :=
  ((rationalOpcodeTable F n).toList.map List.Vector.toList).flatten

theorem rationalOpcodeTape_length {c : ℕ} (F : Fin c → RationalMobius) (n : ℕ) :
    (rationalOpcodeTape F n).length = (2 * n) * rationalPageCount F := by
  rw [rationalOpcodeTape, List.length_flatten, List.map_map]
  have hf : (List.length ∘ (List.Vector.toList : List.Vector PageOpcode (rationalPageCount F) → _)) =
      Function.const _ (rationalPageCount F) := by
    funext row
    exact row.property
  rw [hf, List.map_const, List.sum_replicate]
  rw [List.Vector.toList_length, smul_eq_mul]

def rationalOpcodeWalk {c : ℕ} (F : Fin c → RationalMobius) (n R offset : ℕ)
    (p : Fin (rationalPageCount F)) (t : ℕ) : ℤ :=
  opcodeRampWalk R offset (fun u p => ((rationalOpcodeTable F n).get u).get p) p t

theorem rationalOpcodeWalk_eq {c n : ℕ} (F : Fin c → RationalMobius)
    (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K)
    (p : Fin (rationalPageCount F)) (t : ℕ) :
    rationalOpcodeWalk F n (K * r) offset p t =
      (overlapPages (rationalFamilyMaps F) n).walk r K offset hr hK p t := by
  classical
  rw [NestedMatchingPages.walk_eq_opcodeRampWalk]
  simp only [rationalOpcodeWalk, rationalOpcodeTable_get, rationalPageOpcode_eq]

theorem rationalOpcodeWalk_record_delta {c n : ℕ} (F : Fin c → RationalMobius)
    (R offset : ℕ) (u : Fin (2 * n)) (p : Fin (rationalPageCount F))
    (s : ℕ) (hs : s ≤ 7 * R) :
    rationalOpcodeWalk F n R offset p (offset + 7 * R * u.val + s) -
      rationalOpcodeWalk F n R offset p (offset + 7 * R * u.val) =
      (rationalPageOpcode F u p).direction * cappedRamp (4 * R) R s := by
  simpa only [rationalOpcodeWalk, rationalOpcodeTable_get] using
    opcodeRampWalk_record_delta R offset
      (fun u p => ((rationalOpcodeTable F n).get u).get p) p u s hs

theorem rationalOpcodeWalk_reset {c n : ℕ} (F : Fin c → RationalMobius)
    (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K)
    (p : Fin (rationalPageCount F)) {t : ℕ}
    (ht : NestedMatchingPages.horizon (v := 2 * n) r K offset ≤ t) :
    rationalOpcodeWalk F n (K * r) offset p t = 0 := by
  classical
  rw [rationalOpcodeWalk_eq F r K offset hr hK]
  exact (overlapPages (rationalFamilyMaps F) n).walk_reset r K offset hr hK p ht

theorem rationalOpcodeWalk_recordRun {c n : ℕ} (F : Fin c → RationalMobius)
    (R offset : ℕ) (u : Fin (2 * n)) (p : Fin (rationalPageCount F))
    (s : ℕ) (hs : s ≤ 7 * R) :
    recordRun R (rationalPageOpcode F u p)
      (rationalOpcodeWalk F n R offset p (offset + 7 * R * u.val)) s =
      rationalOpcodeWalk F n R offset p (offset + 7 * R * u.val + s) := by
  simpa only [rationalOpcodeWalk, rationalOpcodeTable_get] using
    opcodeRampWalk_recordRun R offset
      (fun u p => ((rationalOpcodeTable F n).get u).get p) p u s hs

end TransposeFollowup
