import TransposeFollowup.TernaryBufferedRule

/-! Exact coordinates of the buffered F3 prefix/difference. Buffer positions
are independent lanes: the output at group i, lane j uses only lane j of
preceding groups. Width may be an entire matrix row or one b-trit entry. -/
namespace TransposeFollowup.TernaryBank
open FixedTapeCompiler
open CopyMachine (Sym)
set_option autoImplicit false

theorem bufferOutput_getI (sub : Bool) (xs ys : List (Sym Bool)) (j : ℕ)
    (hx : j<xs.length) (hy : j<ys.length) :
    (bufferOutput sub xs ys).getI j=encode (digit sub (decode (xs.getI j)) (decode (ys.getI j))) := by
  rw [List.getI_eq_getElem _ (by simp only [bufferOutput,List.length_zipWith]; omega)]
  simp only [bufferOutput,List.getElem_zipWith]
  rw [List.getI_eq_getElem xs hx,List.getI_eq_getElem ys hy]

theorem bufferSaved_decode_getI (sub : Bool) (xs ys : List (Sym Bool)) (j : ℕ)
    (hx : j<xs.length) (hy : j<ys.length) :
    decode ((bufferSaved sub xs ys).getI j)=stored sub (decode (xs.getI j)) (decode (ys.getI j)) := by
  cases sub with
  | false =>
    change decode ((bufferOutput false xs ys).getI j)=digit false (decode (xs.getI j)) (decode (ys.getI j))
    rw [bufferOutput_getI false xs ys j hx hy,decode_encode]
  | true =>
    change decode ((xs.map (fun a => encode (decode a))).getI j)=decode (xs.getI j)
    rw [List.getI_eq_getElem _ (by simpa using hx),List.getElem_map,decode_encode,
      List.getI_eq_getElem xs hx]

theorem rows_coordinate (sub : Bool) (W : ℕ) (rows : List (List (Sym Bool)))
    (hw : ∀ xs ∈ rows, xs.length=W) (ys : List (Sym Bool)) (hy : ys.length=W)
    (i j : ℕ) (hi : i<rows.length) (hj : j<W) :
    (BufferedRows.rowsResult (bufferRule sub) rows ys).1.getI (i*W+j)=
      encode ((rowResult sub (decode (ys.getI j)) (rows.map (fun xs => decode (xs.getI j)))).getI i) := by
  induction rows generalizing ys i with
  | nil => simp at hi
  | cons xs rows ih =>
    have hx := hw xs List.mem_cons_self
    have hxy : xs.length=ys.length := hx.trans hy.symm
    have ho : (bufferOutput sub xs ys).length=W :=
      (BufferedRows.output_length (bufferRule sub) xs ys hxy).trans hx
    have hs : (bufferSaved sub xs ys).length=W :=
      (BufferedRows.saved_length (bufferRule sub) xs ys hxy).trans hx
    have htail : ∀ zs ∈ rows, zs.length=W := fun zs hz => hw zs (List.mem_cons_of_mem _ hz)
    change (bufferOutput sub xs ys++(BufferedRows.rowsResult (bufferRule sub) rows (bufferSaved sub xs ys)).1).getI
      (i*W+j)=encode ((rowResult sub (decode (ys.getI j))
        (decode (xs.getI j)::rows.map (fun xs => decode (xs.getI j)))).getI i)
    rw [rowResult_cons]
    cases i with
    | zero =>
      simp only [Nat.zero_mul,zero_add,List.getI_cons_zero]
      rw [List.getI_append _ _ j (by omega)]
      exact bufferOutput_getI sub xs ys j (by omega) (by omega)
    | succ i =>
      rw [List.getI_cons_succ,show (i+1)*W+j=W+(i*W+j) by ring,
        List.getI_append_right _ _ _ (by omega),ho,Nat.add_sub_cancel_left]
      rw [ih htail (bufferSaved sub xs ys) hs i (by simpa using hi)]
      rw [bufferSaved_decode_getI sub xs ys j (by omega) (by omega)]

theorem bank_coordinate (sub : Bool) (W r : ℕ) (x : ℕ → Sym Bool)
    (i j : ℕ) (hi : i<r) (hj : j<W) :
    BufferedRows.bankValue (bufferRule sub) W r x (i*W+j)=
      encode ((rowResult sub 0 (List.ofFn (fun a : Fin r => decode (x (a*W+j))))).getI i) := by
  have h := rows_coordinate sub W (TapeWindow.rows W r x) (TapeWindow.row_lengths W r x)
    (List.replicate W .blank) (by simp) i j (by simpa [TapeWindow.rows_length] using hi) hj
  have hz : decode ((List.replicate W (Sym.blank : Sym Bool)).getI j)=0 := by
    rw [List.getI_eq_getElem _ (by simpa using hj),List.getElem_replicate]
    rfl
  have hc : (TapeWindow.rows W r x).map (fun xs => decode (xs.getI j))=
      List.ofFn (fun a : Fin r => decode (x (a*W+j))) := by
    simp only [TapeWindow.rows,List.map_ofFn]
    congr 1
    funext a
    dsimp only [Function.comp_apply]
    rw [List.getI_eq_getElem _ (by simpa using hj),List.getElem_ofFn]
  simpa only [BufferedRows.bankValue,BufferedRows.bankOutput,hz,hc] using h

theorem vertical_entry (sub : Bool) (b d : ℕ) (x : ℕ → Sym Bool)
    (i j l : ℕ) (hi : i<d) (hj : j<d) (hl : l<b) :
    BufferedRows.bankValue (bufferRule sub) (d*b) d x (i*(d*b)+j*b+l)=
      encode ((rowResult sub 0
        (List.ofFn (fun a : Fin d => decode (x (a*(d*b)+j*b+l))))).getI i) := by
  simpa only [Nat.add_assoc] using bank_coordinate sub (d*b) d x i (j*b+l) hi (by nlinarith)

end TransposeFollowup.TernaryBank
