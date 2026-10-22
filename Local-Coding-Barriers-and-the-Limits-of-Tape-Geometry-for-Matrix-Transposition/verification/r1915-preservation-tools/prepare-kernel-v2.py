#!/usr/bin/env python3
"""Prepare one explicitly distinguished archived-header check; never run Lean.
Preserve v1 unchanged. The other three raw differences retain original-Expr
kernel conversion, and every row retains exact old/current repr/universe checks.
"""
from pathlib import Path
import copy,hashlib,json
P=Path('.');V=P/'verification'
C=Path('external/temporary/r1915-preservation/capture');D=C/'kernel-v2';D.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(s):return hashlib.sha256(s.encode()).hexdigest()
def rec(p):
 p=Path(p);return {'path':str(p.resolve()),'bytes':p.stat().st_size,'sha256':sha(p)}
def write(p,x):
 with Path(p).open('x')as out:json.dump(x,out,indent=2);out.write('\n')
oldplan=json.loads((C/'kernel/plan.json').read_text());oldchecker=Path(oldplan['checker'])
assert sha(oldchecker)==oldplan['checker_sha256']
sources=json.loads((C/'baseline-sources.json').read_text());path='lean/TransposeFollowup/SpectralGapInterface.lean';source=sources[path]
short='expansion_of_restrictedL2Gap';name='TransposeFollowup.RationalUnitMobius.'+short
newshort='R1915_original_header_'+short;auditor='TransposeFollowup.RationalUnitMobius.'+newshort
start=source.index('theorem '+short+' ');end=source.index(' :=\n',start);header=source[start:end]
renamed=header.replace('theorem '+short+' ','theorem '+newshort+' ',1)
context='namespace TransposeFollowup\nopen Classical Set MeasureTheory\nopen scoped BigOperators\nset_option autoImplicit false\n\nnamespace RationalUnitMobius\n\n'
code=context+renamed+' := by\n  exact expansion_of_restrictedL2Gap F hc hK hnear he hdet hgap\n\nend RationalUnitMobius\nend TransposeFollowup\n'
text=oldchecker.read_text();marker='open Lean Elab Command\nnamespace R1915TypeConversionAudit';assert text.count(marker)==1
text=text.replace(marker,code+'\n'+marker,1)
start=text.index('  let current := Expr.const name (levels.toList.map Level.param)')
end=text.index('\n  pure (Json.mkObj [',start)
replacement='''  let current := Expr.const name (levels.toList.map Level.param)
  let headerAuditor : Option Name :=
    if nameText == "TransposeFollowup.RationalUnitMobius.expansion_of_restrictedL2Gap" then
      some ``TransposeFollowup.RationalUnitMobius.R1915_original_header_expansion_of_restrictedL2Gap
    else none
  let checkedType ← match headerAuditor with
    | none => pure oldType
    | some auditor => do
      let some headerInfo := env.find? auditor | throwError "Missing kernel-checked original header: {nameText}"
      unless headerInfo.levelParams == levels.toList do throwError "Header universe parameters differ: {nameText}"
      pure headerInfo.type
  -- Only the named exception uses the exact archived source-header statement.
  -- Its old Expr contains a retired generated proof constant, so this route
  -- is never reported as a successful original-Expr conversion.
  let checkedType := ShareCommon.shareCommon checkedType
  if headerAuditor.isNone then
    unless reprStr checkedType == baselineRepr do throwError "Sharing changed original Expr: {nameText}"
  let application := Expr.app (Expr.lam `r1915_original_type checkedType (.bvar 0) .default) current
  match Kernel.check env {} application with
  | .error ex => throwError "Preserved statement kernel check failed for {nameText}: {ex.toMessageData (← getOptions)}"
  | .ok _ => pure ()'''
text=text[:start]+replacement+text[end:]
old='''    ("validation_route", toJson "original_expr_kernel"),
    ("kernel_identity_application_checked", toJson true),
    ("original_source_header_kernel_checked", toJson false),
    ("auditor_declaration", toJson (none : Option String)),'''
new='''    ("validation_route", toJson (if headerAuditor.isNone then "original_expr_kernel" else "archived_source_header_kernel")),
    ("kernel_identity_application_checked", toJson headerAuditor.isNone),
    ("original_source_header_kernel_checked", toJson headerAuditor.isSome),
    ("auditor_declaration", toJson (headerAuditor.map Name.toString)),'''
assert text.count(old)==1;text=text.replace(old,new)
text=text[:text.index('\nrun_cmd R1915TypeConversionAudit.runChunk ')]
plan=copy.deepcopy(oldplan);plan['version']=2
for row in plan['chunks']:
 assert sha(row['input'])==row['input_sha256']
 row['output']=str(D/Path(row['output']).name)
 text+='\nrun_cmd R1915TypeConversionAudit.runChunk '+json.dumps(row['input'])+' '+json.dumps(row['output'])+'\n'
checker=D/'check.lean';checker.write_text(text)
plan['checker']=str(checker);plan['checker_sha256']=sha(checker)
plan['original_expr_kernel_targets']=3;plan['archived_source_header_targets']=[name]
plan['prior_attempt']={'status':'failed_preserved','reason':'Original Expr references retired generated proof constant expansion_of_restrictedL2Gap._proof_1; no conversion failure was relabeled as success.',
 'checker':rec(oldchecker),'plan':rec(C/'kernel/plan.json'),'inputs':[rec(row['input'])for row in oldplan['chunks']],
 'outputs':[rec(row['output'])for row in oldplan['chunks']if Path(row['output']).exists()],
 'execution':rec(V/'r1915-type-kernel-conversions-timing.json'),'log':rec(V/'r1915-type-kernel-conversions.log')}
assert json.loads(Path(plan['prior_attempt']['execution']['path']).read_text())['exit_code']!=0
headers={'format':'r1915-exact-archived-source-header-checks-v1','baseline_inventory':str(C/'baseline-sources.json'),'baseline_inventory_sha256':sha(C/'baseline-sources.json'),
 'checker':str(checker),'checker_sha256':sha(checker),'count':1,'declarations':[{
 'name':name,'auditor_declaration':auditor,'baseline_source':path,'baseline_source_sha256':digest(source),
 'original_header':header,'original_header_sha256':digest(header),'renamed_header':renamed,
 'source_check_text':code,'source_check_text_sha256':digest(code),
 'change':'Only theorem identifier renamed. Complete archived binders/premises/conclusion and original namespace/opens/scoped notation/options are preserved. Proof directly applies the current theorem; this is a separate source-contract check, not old-Expr conversion.'}]}
write(D/'source-headers.json',headers);plan['source_headers']=rec(D/'source-headers.json');write(D/'plan.json',plan)
print(json.dumps({'checker':str(checker),'plan':str(D/'plan.json'),'source_headers':str(D/'source-headers.json'),'original_expr_targets':3,'source_header_targets':1,'v1_modified':False,'Lean_executed':False}))
