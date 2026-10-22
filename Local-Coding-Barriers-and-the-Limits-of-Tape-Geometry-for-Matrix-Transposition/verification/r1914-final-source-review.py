#!/usr/bin/env python3
"""Replay approved R1914 source organization and audit final restored sources.

READ ONLY for the project. Do not execute until root confirms that sources are
final/restored and authorizes this lightweight review. Does not invoke Lean/Lake. A pass
is a source-preservation result, not a substitute for root's kernel/axiom audit.
"""
from __future__ import annotations
import argparse
from collections import Counter
import datetime as dt
import hashlib
import json
from pathlib import Path
import re

P=Path('.')
A=Path('external/research-workspace/research/10-linear-decision/archive/r1914-analytic-build-speed')
NAMES=[
 'TransposeFollowup.MobiusNearIdentity','TransposeFollowup.MobiusPairwiseComparison',
 'TransposeFollowup.MobiusActionContinuity','TransposeFollowup.MobiusGroupAverage',
 'TransposeFollowup.MobiusGroupSmoothing']
IM=re.compile(r'^import ([A-Za-z_][A-Za-z0-9_.]*)\n',re.M)


def require(test,msg):
    if not test:raise ValueError(msg)


def unique(pairs):
    d={}
    for k,v in pairs:
        require(k not in d,f'duplicate JSON key: {k!r}');d[k]=v
    return d


def read(p):
    with Path(p).open(encoding='utf-8')as f:return json.load(f,object_pairs_hook=unique)


def sha(s):return hashlib.sha256(s.encode()).hexdigest()

def record(p):
    b=Path(p).read_bytes();return {'path':str(Path(p).resolve()),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}

def rel(m):return 'lean/'+m.replace('.','/')+'.lean'

def module(r):return r.removeprefix('lean/').removesuffix('.lean').replace('/','.')

def imports(s):return IM.findall(s)

def body(s):return IM.sub('',s)

def localpath(path):
    p=Path(path)
    if p.is_absolute():p=p.relative_to(P)
    r=str(p)
    require(r=='lean/SupportAxioms.lean'or r.startswith(('lean/TransposeFollowup/','lean/FixedTapeCompiler/')),f'out-of-scope source: {r}')
    require(p.suffix=='.lean'and'..'not in p.parts,f'invalid source path: {r}')
    return r


def apply_receipt(before,receipt):
    changes=receipt['changes'];require(isinstance(changes,list)and changes,'empty/malformed mutation receipt')
    paths=[localpath(c['path'])for c in changes];require(len(paths)==len(set(paths)),'duplicate source path in mutation receipt')
    after=dict(before)
    for c,r in zip(changes,paths):
        old,new=c['old_text'],c['new_text']
        require(old is None or isinstance(old,str),f'{r}: invalid old text')
        require(new is None or isinstance(new,str),f'{r}: invalid new text')
        require(old!=new,f'{r}: receipt records a no-op')
        require(before.get(r)==old,f'{r}: receipt old text differs from preceding reconstructed stage')
        require(c['old_sha256']==(None if old is None else sha(old)),f'{r}: old source digest mismatch')
        require(c['new_sha256']==(None if new is None else sha(new)),f'{r}: new source digest mismatch')
        if new is None:del after[r]
        else:after[r]=new
    return after,paths


def expected_imports(before):
    after=dict(before)
    edits=[('RealMobiusAverage','import TransposeFollowup.RationalMobiusAction\n','import TransposeFollowup.RealMobiusL2\n'),
      ('SpectralGapInterface','import TransposeFollowup.RealMobiusAverage\n','import TransposeFollowup.RealMobiusAverage\nimport TransposeFollowup.RationalMobiusAction\n')]
    for name,old,new in edits:
        r=rel('TransposeFollowup.'+name);require(before[r].startswith(old),f'import-stage old header mismatch: {name}')
        after[r]=new+before[r][len(old):]
    return after


def expected_geometry(before,proposal):
    require(len(proposal['relocations'])==8,'expected exactly8 relocated declarations')
    after,paths=apply_receipt(before,proposal)
    core=rel(proposal['new_module']);require(before.get(core)is None,'geometry core already existed at baseline stage')
    names=[];relocation_records=[]
    for moved in proposal['relocations']:
        n=moved['declaration'];text=moved['source_text'];oldpath=rel(moved['old_module'])
        require(sha(text)==moved['source_sha256'],f'moved source digest mismatch: {n}')
        require(before[oldpath].count(text)==1 and after[core].count(text)==1,f'declaration was not moved byte-exactly once: {n}')
        require(text not in after[oldpath],f'moved declaration duplicated in old owner: {n}')
        require(moved['new_module']==proposal['new_module'],f'wrong destination for relocation: {n}')
        require(text.startswith(moved['kind']+' '+n.rsplit('.',1)[1]+' '),f'relocation identity/header mismatch: {n}')
        old_line=before[oldpath][:before[oldpath].index(text)].count('\n')+1
        new_line=after[core][:after[core].index(text)].count('\n')+1
        require(moved['old_start_line']==old_line and moved['new_start_line']==new_line,f'relocation line metadata mismatch: {n}')
        relocation_records.append({'declaration':n,'kind':moved['kind'],'old_module':moved['old_module'],
            'new_module':proposal['new_module'],'old_source':oldpath,'new_source':core,
            'old_start_line':old_line,'new_start_line':new_line,'source_lines':text.count('\n'),
            'source_bytes':len(text.encode()),'source_sha256':sha(text)})
        names.append(n)
    core_header=''.join('import '+m+'\n'for m in ['TransposeFollowup.RealMobiusAlgebra',
        'Mathlib.Tactic.FinCases','Mathlib.Tactic.Linarith','Mathlib.Tactic.NormNum','Mathlib.Tactic.Ring'])+'''\n/-! Elementary entry bounds and identity neighborhoods of the existing real
Mobius matrix group. These definitions and proofs are shared by trace geometry
and the Haar/walk developments. -/
namespace TransposeFollowup.RealMobius
open Classical Set
set_option autoImplicit false

'''
    require(after[core]==core_header+''.join(m['source_text']for m in proposal['relocations'])+'end TransposeFollowup.RealMobius\n',
        'geometry core contains unexpected text beyond exact eight declarations and approved namespace/import context')
    require(len(set(names))==8,'duplicated relocation name')
    expected_names={'mobiusIdentityDistanceSq','mobiusIdentityBall','mobiusIdentityBall_entry_bounds','matrixEntryBox','one_mem_matrixEntryBox','matrixEntryBox_inv','matrixEntryBox_mul','mobiusIdentityBall_subset_entryBox_two'}
    require({n.rsplit('.',1)[1]for n in names}==expected_names,'unexpected geometry relocation set')
    for name in ['MobiusHaarKernel','MobiusHaarEntryBox','MobiusWalkEntrySupport']:
        r=rel('TransposeFollowup.'+name);residue=before[r]
        for moved in proposal['relocations']:
            if rel(moved['old_module'])==r:residue=residue.replace(moved['source_text'],'',1)
        require(after[r]=='import '+proposal['new_module']+'\n'+residue,f'owner has unapproved changes beyond exact relocation/import: {r}')
    r=rel('TransposeFollowup.SL2SpanningTrace')
    require(after[r]==before[r].replace('import TransposeFollowup.MobiusWalkEntrySupport\n','import '+proposal['new_module']+'\n',1),'SL2SpanningTrace changed beyond import')
    require('instance instGroupLocallyCompactSpace' in after[rel('TransposeFollowup.MobiusHaarKernel')],'global instance moved/deleted')
    require(not re.search(r'^\s*instance\b',clean(after[core]),re.M),'core introduces/moves a global instance')
    require(set(paths)=={core,rel('TransposeFollowup.SL2SpanningTrace'),*[rel('TransposeFollowup.'+n)for n in ['MobiusHaarKernel','MobiusHaarEntryBox','MobiusWalkEntrySupport']]},'geometry changed extra files')
    return after,names,relocation_records


def expected_merge(before,destination):
    require(destination in NAMES,'merge destination must be one of the five approved modules')
    for m in NAMES:require(rel(m)in before,f'missing merge member: {m}')
    mapping={m:destination for m in NAMES};removed={rel(m)for m in NAMES if m!=destination}
    after={}
    for r,s in before.items():
        if r in removed:continue
        imps=list(dict.fromkeys(mapping.get(m,m)for m in imports(s)))
        after[r]=''.join('import '+m+'\n'for m in imps)+body(s)
    external=list(dict.fromkeys(mapping.get(i,i)for m in NAMES for i in imports(before[rel(m)])if i not in NAMES))
    require(destination not in external,'merge creates self import')
    after[rel(destination)]=''.join('import '+m+'\n'for m in external)+'\n'.join(body(before[rel(m)])for m in NAMES)
    return after,{'members':NAMES,'destination':destination,'removed':sorted(removed),'external_imports':external,'body_sha256':{m:sha(body(before[rel(m)]))for m in NAMES}}


def clean(s):
    out=list(s);i=0;depth=0;string=False;line=False
    while i<len(s):
        if line:
            if s[i]=='\n':line=False
            else:out[i]=' '
            i+=1;continue
        if depth:
            if s.startswith('/-',i):out[i:i+2]=[' ',' '];depth+=1;i+=2;continue
            if s.startswith('-/',i):out[i:i+2]=[' ',' '];depth-=1;i+=2;continue
            if s[i]!='\n':out[i]=' '
            i+=1;continue
        if string:
            if s[i]=='\\'and i+1<len(s):out[i:i+2]=[' ',' '];i+=2;continue
            if s[i]=='"':string=False
            if s[i]!='\n':out[i]=' '
            i+=1;continue
        if s.startswith('--',i):out[i:i+2]=[' ',' '];line=True;i+=2;continue
        if s.startswith('/-',i):out[i:i+2]=[' ',' '];depth=1;i+=2;continue
        if s[i]=='"':out[i]=' ';string=True
        i+=1
    require(depth==0 and not string,'unterminated Lean comment/string')
    return ''.join(out)


def current_sources():
    actual={str(p.relative_to(P)):p.read_text()for root in [P/'lean/TransposeFollowup',P/'lean/FixedTapeCompiler']for p in root.rglob('*.lean')}
    actual['lean/SupportAxioms.lean']=(P/'lean/SupportAxioms.lean').read_text()
    return actual


def same_sources(expected,actual,label):
    diff=[r for r in sorted(set(expected)|set(actual))if expected.get(r)!=actual.get(r)]
    require(not diff,f'{label}: {diff[:20]}')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--baseline',type=Path,default=A/'baseline-sources.json')
    p.add_argument('--baseline-receipt',type=Path,help='Optional frozen source_sha256 receipt; source inventory itself is always hashed in output')
    p.add_argument('--geometry-proposal',type=Path,default=A/'source-review/geometry-proposal.json')
    p.add_argument('--stage',action='append',required=True,metavar='KIND:PATH',help='Ordered source mutation receipts: imports, geometry, merge, import-repair, approved-repair')
    p.add_argument('--merge-destination',default='TransposeFollowup.MobiusGroupSmoothing')
    p.add_argument('--approved-repair',type=Path,action='append',default=[],help='Explicit independently reviewed full-text repair receipt; each approved-repair stage must byte-match one listed receipt')
    p.add_argument('--benchmark-receipt',type=Path,action='append',default=[],help='Restored benchmark edit receipt(s); a restored/restored flag is required')
    p.add_argument('--expected-original-names',type=int,default=6306)
    p.add_argument('--output',type=Path,default=Path('external/temporary/r1914-final-source-review.json'))
    args=p.parse_args()
    baseline=read(args.baseline);expected=dict(baseline)
    require('lean/SupportAxioms.lean'in baseline,'baseline audit source missing')
    for r,s in baseline.items():require(localpath(r)==r and isinstance(s,str),f'bad baseline source: {r}')
    if args.baseline_receipt:
        receipt=read(args.baseline_receipt)
        require(receipt['source_sha256']=={r:sha(s)for r,s in baseline.items()},'frozen source digest receipt differs from baseline')
    approved=[read(path)for path in args.approved_repair]
    stages=[];seen=set();relocations=[];relocation_records=[];merge_info=None
    for item in args.stage:
        kind,text=item.split(':',1);path=Path(text);r=read(path)
        require(kind in ['imports','geometry','merge','import-repair','approved-repair'],f'unknown source stage {kind}')
        if kind in ['imports','geometry','merge']:
            require(kind not in seen,f'duplicate structural stage {kind}');seen.add(kind)
        after,paths=apply_receipt(expected,r)
        if kind=='imports':same_sources(expected_imports(expected),after,'import stage differs from approved two edits')
        elif kind=='geometry':
            planned,relocations,relocation_records=expected_geometry(expected,read(args.geometry_proposal));same_sources(planned,after,'geometry stage differs from exact proposal')
        elif kind=='merge':
            planned,merge_info=expected_merge(expected,args.merge_destination);same_sources(planned,after,'merge differs from exact ordered proof-body concatenation/import remapping')
        elif kind=='import-repair':
            require(set(expected)==set(after),'import repair adds/deletes a source file')
            for name in paths:require(body(expected[name])==body(after[name]),f'import repair changes proof text: {name}')
        elif kind=='approved-repair':require(any(r['changes']==x['changes']for x in approved),'repair stage is not independently listed as approved full-text change')
        expected=after;stages.append({'kind':kind,'receipt':record(path),'changed_sources':paths})
    require({'imports','geometry'}.issubset(seen),'missing required import/geometry structural stages')
    actual=current_sources();same_sources(expected,actual,'actual final sources differ from replayed approved stages')
    original_names=re.findall(r'^\s*#print axioms (\S+)\s*$',clean(baseline['lean/SupportAxioms.lean']),re.M)
    final_names=re.findall(r'^\s*#print axioms (\S+)\s*$',clean(actual['lean/SupportAxioms.lean']),re.M)
    require(len(original_names)==len(set(original_names))==args.expected_original_names,'baseline declaration audit cardinality mismatch')
    require(final_names==original_names,'original audit declarations/order changed')
    forbidden=set('sorry sorryAx admit axiom unsafe native_decide implemented_by extern trustLevel addDecl addAndCompile mkAxiom mkSorry setEnv run_meta elab_rules initialize syntax macro_rules elab run_tac run_cmd'.split())
    opts=Counter()
    for r,s in actual.items():
        t=clean(s);hits=set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',t))&forbidden
        require(not hits,f'forbidden trust-changing token in {r}: {sorted(hits)}')
        for option in re.findall(r'^\s*set_option\s+(.+)$',t,re.M):
            require(option.strip()=='autoImplicit false',f'unapproved option/limit in {r}: {option}');opts[option.strip()]+=1
        require(not re.search(r'#(?:eval|compile|extern)\b',t),f'unapproved executable command in {r}')
    G={module(r):imports(clean(s))for r,s in actual.items()if r!='lean/SupportAxioms.lean'}
    colors={}
    def visit(m,trail):
        require(colors.get(m)!=1,f'local dependency cycle: {trail+[m]}')
        if colors.get(m)==2:return
        colors[m]=1
        for dep in G[m]:
            if dep in G:visit(dep,trail+[m])
            else:require(not dep.startswith(('TransposeFollowup.','FixedTapeCompiler.')),f'missing local import {m}->{dep}')
        colors[m]=2
    for m in G:visit(m,[])
    for dep in imports(clean(actual['lean/SupportAxioms.lean'])):require(dep in G or not dep.startswith(('TransposeFollowup.','FixedTapeCompiler.')),f'missing audit-root import: {dep}')
    benchmarks=[]
    for path in args.benchmark_receipt:
        b=read(path);require(b.get('restored')is True or b.get('restore_completed')is True,f'benchmark edit not restored: {path}');benchmarks.append(record(path))
    same_sources(actual,current_sources(),'sources changed during final audit')
    change_inventory=[]
    for r in sorted(set(baseline)|set(actual)):
        old,new=baseline.get(r),actual.get(r)
        if old==new:continue
        kind='added' if old is None else 'removed' if new is None else 'changed'
        change_inventory.append({'path':r,'kind':kind,'old_sha256':None if old is None else sha(old),
            'new_sha256':None if new is None else sha(new),
            'non_import_body_changed':None if old is None or new is None else body(old)!=body(new)})
    change_counts=dict(Counter(c['kind']for c in change_inventory))
    for kind in ['added','changed','removed']:change_counts.setdefault(kind,0)
    out={'format':'r1914-independent-source-review-v1','status':'passed','finished_at_utc':dt.datetime.now(dt.timezone.utc).isoformat(),
         'scope':'Source replay, exact structural body preservation and trust/import hygiene only. Kernel/type/axiom verification and protected-original/config guards remain separate root-owned audits.',
         'baseline':record(args.baseline),'baseline_receipt':None if args.baseline_receipt is None else record(args.baseline_receipt),
         'geometry_proposal':record(args.geometry_proposal),'source_change_counts':change_counts,'source_changes':change_inventory,
         'baseline_sources':len(baseline),'final_sources':len(actual),'mathematical_modules':len(G),
         'original_audit_names_preserved':len(original_names),'original_audit_order_exact':True,'stages':stages,'geometry_relocations':relocations,
         'geometry_relocation_records':relocation_records,'geometry_proof_headers_and_bodies_exact':True,'global_geometry_instance_moved':False,'optional_merge':merge_info,
         'explicit_approved_repairs':[record(path)for path in args.approved_repair], 'benchmark_receipts':benchmarks,
         'forbidden_tokens':[],'set_options':dict(opts),'local_imports_acyclic':True,'missing_local_imports':[],
         'final_source_sha256':{r:sha(s)for r,s in sorted(actual.items())},'reviewer':record(__file__),
         'no_Lean_Lake_executed':True,'no_repository_sources_modified':True}
    args.output.write_text(json.dumps(out,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k not in ['final_source_sha256','geometry_relocations','geometry_relocation_records','source_changes','optional_merge']},indent=2))


if __name__=='__main__':main()
