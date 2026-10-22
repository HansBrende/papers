from pathlib import Path
import json,hashlib,re
P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition')
A=Path('/Users/hansbrende/Documents/Codex/2026-10-09/a/research/10-linear-decision/archive/r1912-build-speed')
sources=json.loads((A/'baseline-sources.json').read_text())
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
items=[('NativePaddedFieldMachine','NativePaddedField','tail_trace','open FixedTapeCompiler CopyMachine\nopen NativeFieldCopy (targetBinding allBinding)','C source field pos'),('CountedFillBody','CountedFill','emit_step','open FixedTapeCompiler\nopen CopyMachine (Tape Sym symbols)','m bit i hi fuel acc origin')]
proofs=[];records=[]
for file,ns,n,opens,args in items:
 path='lean/TransposeFollowup/'+file+'.lean';source=sources[path]
 start=source.index('theorem '+n+' ');end=source.index(' := by\n',start)
 header=source[start:end];newname='R1912_original_header_'+n
 renamed=header.replace('theorem '+n+' ','theorem '+newname+' ',1)
 code=f'namespace TransposeFollowup.{ns}\n{opens}\nset_option autoImplicit false\n\n'+renamed+f' := by\n  exact {n} {args}\n\nend TransposeFollowup.{ns}\n'
 proofs.append(code)
 records.append({'name':f'TransposeFollowup.{ns}.{n}','auditor_declaration':f'TransposeFollowup.{ns}.{newname}','baseline_source':path,'baseline_source_sha256':sha(source),'original_header':header,'original_header_sha256':sha(header),'renamed_header':renamed,'source_check_text':code,'source_check_text_sha256':sha(code),'change':'Only theorem identifier renamed; archived full binders/premises/conclusion preserved exactly. Proof is direct application of current original-named theorem.'})
old=Path('/private/tmp/r1912-kernel-type-checker.lean').read_text();old=old[:old.index('\nrun_cmd R1912TypeConversionAudit.runChunk ')]
old=old.replace('open Lean Elab Command\nnamespace R1912TypeConversionAudit', '\n'.join(proofs)+'\nopen Lean Elab Command\nnamespace R1912TypeConversionAudit',1)
start=old.index('  -- Sharing changes only object representation')
end=old.index('\n  pure (Json.mkObj [',start)
replacement='''  let current := Expr.const name (levels.toList.map Level.param)
  let headerAuditor : Option Name :=
    if nameText == "TransposeFollowup.NativePaddedField.tail_trace" then
      some ``TransposeFollowup.NativePaddedField.R1912_original_header_tail_trace
    else if nameText == "TransposeFollowup.CountedFill.emit_step" then
      some ``TransposeFollowup.CountedFill.R1912_original_header_emit_step
    else none
  let checkedType ← match headerAuditor with
    | none => pure oldType
    | some auditor => do
      let some headerInfo := env.find? auditor | throwError "Missing kernel-checked original header: {nameText}"
      unless headerInfo.levelParams == levels.toList do throwError "Header universe parameters differ: {nameText}"
      pure headerInfo.type
  -- The two exceptional records use the exact archived source-header statement,
  -- because their old Expr references contain retired generated proof constants.
  -- They are never reported as exact old-Expr conversions.
  let checkedType := ShareCommon.shareCommon checkedType
  if headerAuditor.isNone then
    unless reprStr checkedType == baselineRepr do throwError "Sharing changed Expr repr: {nameText}"
  let application := Expr.app (Expr.lam `r1912_original_type checkedType (.bvar 0) .default) current
  match Kernel.check env {} application with
  | .error ex => throwError "Preserved statement kernel check failed for {nameText}: {ex.toMessageData (← getOptions)}"
  | .ok _ => pure ()'''
old=old[:start]+replacement+old[end:]
old=old.replace('("kernel_identity_application_checked", toJson true),','''("validation_route", toJson (if headerAuditor.isNone then "original_expr_kernel" else "archived_source_header_kernel")),
    ("kernel_identity_application_checked", toJson headerAuditor.isNone),
    ("original_source_header_kernel_checked", toJson headerAuditor.isSome),
    ("auditor_declaration", toJson (headerAuditor.map Name.toString)),''')
commands=[]
outdir=Path('/private/tmp/r1912-kernel-type-conversion-v2');outdir.mkdir(exist_ok=True)
for p in sorted(Path('/private/tmp/r1912-original-types-ast-chunks').glob('[0-9][0-9][0-9].json')):
 output=outdir/f'r1912-kernel-type-conversion-{p.stem}.json'
 commands.append('\nrun_cmd R1912TypeConversionAudit.runChunk '+json.dumps(str(p))+' '+json.dumps(str(output))+'\n')
checker=Path('/private/tmp/r1912-kernel-type-checker-v2.lean');checker.write_text(old+''.join(commands))
record={'format':'r1912-exact-archived-source-header-checks-v1','baseline_inventory':str(A/'baseline-sources.json'),'baseline_inventory_sha256':hashlib.sha256((A/'baseline-sources.json').read_bytes()).hexdigest(),'checker':str(checker),'checker_sha256':hashlib.sha256(checker.read_bytes()).hexdigest(),'declarations':records,'count':2}
Path('/private/tmp/r1912-source-header-checks.json').write_text(json.dumps(record,indent=2)+'\n')
print(checker);print('/private/tmp/r1912-source-header-checks.json')
