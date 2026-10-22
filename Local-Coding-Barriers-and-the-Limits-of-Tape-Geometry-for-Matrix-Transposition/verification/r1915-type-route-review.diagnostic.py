#!/usr/bin/env python3
"""Diagnostic structural diff only; never certifies mathematical equivalence."""
from pathlib import Path
import json,hashlib,importlib.util
P=Path('.');C=Path('external/temporary/r1915-preservation/capture')
parserpath=P/'verification/r1912-decode-expr-repr.py';spec=importlib.util.spec_from_file_location('expr_parser',parserpath);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
name='TransposeFollowup.RationalUnitMobius.expansion_of_restrictedL2Gap'
rows=json.loads((C/'kernel/input-000.json').read_text())['declarations'];row=next(x for x in rows if x['name']==name)
old=row['baselineTypeAST'];new=parser.Parser(row['currentRepr']).all_expr();changes=[]
def flat(n):
 if n[0]=='anonymous':return ''
 return (flat(n[1])+'.'if flat(n[1])else'')+str(n[2])
def difference(kind,path,a,b):
 changes.append({'kind':kind,'path':path,'old':a,'new':b})
def walk(a,b,path):
 if a==b:return
 if not isinstance(a,list)or not isinstance(b,list)or len(a)!=len(b)or a[0]!=b[0]:difference('constructor_or_shape',path,a,b);return
 tag=a[0]
 if tag in ['lam','forallE','letE']:
  if a[1]!=b[1]:difference('binder_name',path+[1],a[1],b[1])
  for i in range(2,len(a)-1):walk(a[i],b[i],path+[i])
  if a[-1]!=b[-1]:difference('binder_info_or_let_flag',path+[len(a)-1],a[-1],b[-1])
 elif tag=='app':walk(a[1],b[1],path+[1]);walk(a[2],b[2],path+[2])
 elif tag=='const':
  if a[1]!=b[1]:difference('constant_name',path+[1],a[1],b[1])
  if a[2]!=b[2]:difference('constant_universe_levels',path+[2],a[2],b[2])
 elif tag=='proj':
  for i in [1,2]:
   if a[i]!=b[i]:difference('projection_field',path+[i],a[i],b[i])
  walk(a[3],b[3],path+[3])
 else:difference('other_expression_field',path,a,b)
walk(old,new,[])
for r in changes:
 if r['kind']in ['binder_name','constant_name']:r['old_name']=flat(r['old']);r['new_name']=flat(r['new'])
count={k:sum(r['kind']==k for r in changes)for k in sorted({r['kind']for r in changes})}
expected_old=name+'._proof_1';expected_new='TransposeFollowup.RationalUnitMobius.expansion_of_restrictedCorrelationGap._proof_1'
only_expected=all((r['kind']=='binder_name'and'_hyg'in r['old_name']and'_hyg'in r['new_name'])or(r['kind']=='constant_name'and r['old_name']==expected_old and r['new_name']==expected_new)for r in changes)
out={'status':'diagnostic_complete','declaration':name,'baseline_repr_sha256':hashlib.sha256(row['baselineRepr'].encode()).hexdigest(),'current_repr_sha256':hashlib.sha256(row['currentRepr'].encode()).hexdigest(),'baseline_ast_matches_reparse':old==parser.Parser(row['baselineRepr']).all_expr(),'counts':count,'only_hygienic_binder_names_and_expected_generated_helper_differ':only_expected,'changes':changes,'scope':'Structural diagnostic only, not an equality certificate or an acceptance normalization. Source-header and native-kernel verification routes remain separate.'}
Path('external/temporary/r1915-header-expression-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='changes'},indent=2));print(json.dumps([{k:v for k,v in r.items()if k not in ['old','new']}for r in changes],indent=2))
