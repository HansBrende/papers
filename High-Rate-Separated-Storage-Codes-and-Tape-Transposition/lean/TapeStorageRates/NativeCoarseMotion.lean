import TapeStorageRates.NativeCoarsePhases

namespace TapeStorageRates.Native

open Transpose MergeDepth

private theorem ofFn_last {α : Type*} {n : ℕ} (hn : 0<n) (a b : α) :
    (List.ofFn fun i : Fin n => if i.val+1<n then a else b) =
      List.replicate (n-1) a ++ [b] := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    simp only [List.getElem_ofFn]
    by_cases h : i<n-1
    · rw [List.getElem_append_left (by simpa using h)]
      simp [show i+1<n by omega]
    · rw [List.getElem_append_right (by simp; omega)]
      have eq : i=n-1 := by
        have hi' : i<n := by simpa only [List.length_ofFn] using hi
        omega
      simp [eq,show ¬n-1+1<n by omega]

def scalarMoves (s : ℕ) (e : Fin 3) : List ℤ :=
  List.replicate s (-1) ++ List.replicate (3*s-1) 1 ++ List.replicate 1 0 ++ List.replicate 1 0 ++
  List.replicate (3*s-1) (-1) ++ List.replicate 1 0 ++ List.replicate s 1 ++
  List.replicate s (moveInt (direction e)) ++ List.replicate s 0

theorem core_work_moves {k s : ℕ} (hs : 0<s) (a : Descriptor k) (h : Fin k) :
    (coreMoves s a).map (fun m => moveInt (m.2.1 h)) = scalarMoves s (a.1.2 h) := by
  simp only [coreMoves,List.map_append,List.map_replicate,List.map_ofFn,
    List.map_cons,List.map_nil,Function.comp_def,straight]
  simp only [apply_ite]
  simp only [moveInt]
  rw [ofFn_last (by omega : 0<3*s),ofFn_last (by omega : 0<3*s)]
  simp [scalarMoves,List.append_assoc,moveInt]

theorem core_input_moves {k s : ℕ} (hs : 0<s) (a : Descriptor k) :
    (coreMoves s a).map (fun m => moveInt m.1) = scalarMoves s a.1.1 := by
  simp only [coreMoves,List.map_append,List.map_replicate,List.map_ofFn,
    List.map_cons,List.map_nil,Function.comp_def,straight]
  simp only [apply_ite]
  simp only [moveInt]
  rw [ofFn_last (by omega : 0<3*s),ofFn_last (by omega : 0<3*s)]
  simp [scalarMoves,List.append_assoc,moveInt]

theorem scalarMoves_prefix {s : ℕ} (hs : 0<s) (e : Fin 3) (i : ℕ)
    (hi : i≤10*s+1) : ((scalarMoves s e).take i).sum = fineOffset s e i := by
  simp only [scalarMoves,List.take_append,List.length_append,List.length_replicate,
    List.take_replicate,List.sum_append,List.sum_replicate]
  fin_cases e <;> simp [direction,moveInt,fineOffset] <;> split_ifs <;> omega

end TapeStorageRates.Native
