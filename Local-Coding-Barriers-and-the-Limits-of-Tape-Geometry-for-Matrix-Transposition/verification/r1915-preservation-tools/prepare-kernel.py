#!/usr/bin/env python3
"""Prepare exact-AST/native-kernel checks ONLY for actual raw differences.
No Lean execution. Reuses the reviewed R1912 parser/checker implementations.
Unknown constructors, missing old constants or different universe parameters
fail closed; no aliases, normalization or automatic source-header exceptions.
"""
from pathlib import Path
import argparse,hashlib,json,importlib.util,re
P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition');V=P/'verification'
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--capture',type=Path,default=Path('/private/tmp/r1915-preservation/capture'));a=p.parse_args();C=a.capture
P=Path(json.loads((C/'names.json').read_text())['project']);V=P/'verification'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
comparison=read(C/'comparison.json');different=read(C/'differences.json')['differences'];assert comparison['status']=='differences_require_review' and len(different)==comparison['raw_different']>0
assert sha(C/'differences.json')==comparison['differences']['sha256']
parserpath=V/'r1912-decode-expr-repr.py';spec=importlib.util.spec_from_file_location('r1912_preserved_parser',parserpath);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
D=C/'kernel';D.mkdir(exist_ok=False);records=[]
for r in different:
 n=r['name'];b=r['baseline'];f=r['final'];ast=parser.Parser(b['type']).all_expr()
 records.append({'name':n,'nameAST':parser.flat_name(n),'levelParams':b['levelParams'],'levelParamsAST':[parser.flat_name(x) for x in b['levelParams']],'baselineRepr':b['type'],'baselineReprSHA256':hashlib.sha256(b['type'].encode()).hexdigest(),'baselineTypeAST':ast,'baselineChunk':r['chunk'],'currentRepr':f['type'],'currentReprSHA256':hashlib.sha256(f['type'].encode()).hexdigest(),'currentLevelParams':f['levelParams'],'currentChunk':r['chunk']})
oldpath=V/'r1912-kernel-type-checker-v2.lean';old=oldpath.read_text();start=old.index('open Lean Elab Command\nnamespace R1912TypeConversionAudit');end=old.index('\nend R1912TypeConversionAudit',start)+len('\nend R1912TypeConversionAudit');body=old[start:end]
start=body.index('  let headerAuditor : Option Name :=');end=body.index('\n  pure (Json.mkObj [',start)
body=body[:start]+'''  let oldType := ShareCommon.shareCommon oldType
  unless reprStr oldType == baselineRepr do throwError "Sharing changed old Expr: {nameText}"
  let application := Expr.app (Expr.lam `r1915_original_type oldType (.bvar 0) .default) current
  match Kernel.check env {} application with
  | .error ex => throwError "Original Expr kernel conversion failed for {nameText}: {ex.toMessageData (← getOptions)}"
  | .ok _ => pure ()'''+body[end:]
body=body.replace('toJson (if headerAuditor.isNone then "original_expr_kernel" else "archived_source_header_kernel")','toJson "original_expr_kernel"').replace('toJson headerAuditor.isNone','toJson true').replace('toJson headerAuditor.isSome','toJson false').replace('toJson (headerAuditor.map Name.toString)','toJson (none : Option String)').replace('R1912','R1915').replace('r1912','r1915')
assert 'headerAuditor' not in body
imports=re.findall(r'^import (\S+)\s*$',(P/'lean/SupportAxioms.lean').read_text(),re.M);code='import Lean\n'+''.join('import '+m+'\n' for m in imports)+body+'\n';chunks=[]
for i in range(0,len(records),8):
 rows=records[i:i+8];path=D/f'input-{i//8:03d}.json';out=D/f'output-{i//8:03d}.json';obj={'format':'r1915-preserved-expr-ast-v1','expectedDeclarations':len(rows),'comparisonSHA256':sha(C/'comparison.json'),'decoderSHA256':sha(parserpath),'declarations':rows};path.write_text(json.dumps(obj,ensure_ascii=False,separators=(',',':'))+'\n')
 chunks.append({'input':str(path),'input_sha256':sha(path),'output':str(out),'names':[r['name'] for r in rows]})
 code+='\nrun_cmd R1915TypeConversionAudit.runChunk '+json.dumps(str(path))+' '+json.dumps(str(out))+'\n'
script=D/'check.lean';script.write_text(code)
manifest={'format':'r1915-kernel-preservation-plan-v1','status':'prepared_not_executed','original_declarations':6306,'raw_identical':comparison['raw_identical'],'kernel_targets':len(records),'names':[r['name'] for r in records],'comparison_sha256':sha(C/'comparison.json'),'checker':str(script),'checker_sha256':sha(script),'reused_parser':str(parserpath),'reused_parser_sha256':sha(parserpath),'reused_checker':str(oldpath),'reused_checker_sha256':sha(oldpath),'chunks':chunks,'required':'Every original/current repr roundtrip and ordered universe identity must pass before native Kernel.check. Preserve failures; missing generated proof names require separate explicit original-source-header evidence, never automatic success.'}
(D/'plan.json').write_text(json.dumps(manifest,indent=2)+'\n');print(script)
