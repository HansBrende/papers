#!/usr/bin/env python3
"""Read-only mathematical source review after the R1915 merge and edit restoration.
Does not invoke Lean/Lake. Run only when root confirms the mathematical source
snapshot is final. Writes the requested JSON report, never mathematical sources.
"""
from __future__ import annotations
import argparse
from collections import Counter
import datetime as dt
import hashlib
import json
from pathlib import Path
import re

P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition')
A=Path('/Users/hansbrende/Documents/Codex/2026-10-09/a/research/10-linear-decision/archive/r1915-spectral-build-speed')
MEMBERS=['TransposeFollowup.'+m for m in ['ConditionalSpectralExpansion','RationalMobiusAction','SpectralGapInterface','RationalRestrictedGap','RationalContinuousExpander','UnconditionalPaidPadding']]
DEST=MEMBERS[-1]
EXTERNAL=['TransposeFollowup.'+m for m in ['NormalizedCellCorrelation','RealMobiusL2','RealMobiusAverage','InitialWalkDensityCap','RestrictedGapFromAutocorrelation','RationalNearIdentityFamily','ContinuousNativePadding']]
IM=re.compile(r'^import ([A-Za-z_][A-Za-z0-9_.]*)\n',re.M)


def require(ok,msg):
    if not ok:raise ValueError(msg)


def unique(pairs):
    d={}
    for k,v in pairs:require(k not in d,f'duplicate JSON key: {k!r}');d[k]=v
    return d


def read(p):return json.loads(Path(p).read_bytes().decode('utf-8'),object_pairs_hook=unique)
def sha(s):return hashlib.sha256(s.encode('utf-8')).hexdigest()
def record(p):
    p=Path(p);b=p.read_bytes();return {'path':str(p.resolve()),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def rel(m):return 'lean/'+m.replace('.','/')+'.lean'
def module(r):return r.removeprefix('lean/').removesuffix('.lean').replace('/','.')
def body(s):return IM.sub('',s)
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


def sources():
    d={str(p.relative_to(P)):p.read_bytes().decode('utf-8')for root in [P/'lean/TransposeFollowup',P/'lean/FixedTapeCompiler']for p in root.rglob('*.lean')}
    d['lean/SupportAxioms.lean']=(P/'lean/SupportAxioms.lean').read_bytes().decode('utf-8');return d


def scope_record(m,s):
    t=clean(s);stack=[];commands=[]
    for match in re.finditer(r'^[ \t]*(namespace|section|end)(?:[ \t]+([A-Za-z0-9_.]+))?[ \t]*$',t,re.M):
        kind,name=match.groups();name=name or ''
        if kind in ['namespace','section']:stack.append((kind,name))
        else:
            require(bool(stack),f'unmatched closing scope in {m}')
            _,opened=stack.pop();require(not name or name==opened,f'mismatched closing scope in {m}: {name} vs {opened}')
        commands.append({'kind':kind,'name':name,'line':s[:match.start()].count('\n')+1})
    require(not stack,f'open namespace/section at EOF: {m}')
    instances=re.findall(r'^[ \t]*(?:(?:noncomputable|local|scoped)\s+)*instance\b.*$',t,re.M)
    require(not instances,f'moved instance declaration needs separate review: {m}')
    require(not re.search(r'^[ \t]*(?:private\b|local\s+(?:attribute|instance)|attribute\s+\[local)',t,re.M),f'private/local attribute scope needs separate review: {m}')
    options=[x.strip()for x in re.findall(r'^\s*set_option\s+(.+)$',t,re.M)]
    require(options==['autoImplicit false'],f'unexpected merged source options: {m}')
    return {'module':m,'body_sha256':sha(body(s)),'scope_commands':commands,'namespace_sections_balanced':True,
            'global_instance_declarations':instances,'variable_command_lines':[i for i,line in enumerate(t.splitlines(),1)if re.match(r'^[ \t]*variable\b',line)],'set_options':options}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--baseline',type=Path,default=A/'baseline-sources.json')
    p.add_argument('--baseline-receipt',type=Path,default=A/'before-receipt.json')
    p.add_argument('--proposal',type=Path,default=Path('/private/tmp/r1915-terminal-merge/one/proposal.json'))
    p.add_argument('--application',type=Path,default=P/'verification/r1915-merge-application.json')
    p.add_argument('--benchmark-receipt',type=Path,action='append',default=[])
    p.add_argument('--output',type=Path,default=Path('/private/tmp/r1915-final-source-review.json'))
    a=p.parse_args();B=read(a.baseline);frozen=read(a.baseline_receipt);Q=read(a.proposal);application=read(a.application)
    require('lean/SupportAxioms.lean'in B,'baseline audit root missing')
    require({r:sha(s)for r,s in B.items()}==frozen['source_sha256'],'frozen source snapshot differs from pre-round receipt')
    require(Q['all_input_source_sha256']==frozen['source_sha256'],'reviewed proposal not bound to frozen source snapshot')
    for r,s in B.items():
        require((r=='lean/SupportAxioms.lean'or r.startswith(('lean/TransposeFollowup/','lean/FixedTapeCompiler/')))and r.endswith('.lean')and'..'not in Path(r).parts,f'out-of-scope baseline source: {r}')
        require(isinstance(s,str)and'\r'not in s,f'noncanonical baseline text: {r}')
    require(application['format']=='r1915-six-module-merge-application-v1'and application['status'].startswith('APPLIED;'),'application is not an applied six-module merge')
    for key,path in [('reviewed_proposal',a.proposal),('frozen_baseline',a.baseline)]:
        actual_record=record(path);require(all(application[key][k]==actual_record[k]for k in ['bytes','sha256']),f'application provenance mismatch: {key}')
    require(application['members']==MEMBERS and application['destination']==DEST,'wrong applied member order/destination')
    require(application['changes']==Q['changes'],'applied fulltext changes differ from reviewed proposal')
    external=list(dict.fromkeys(i for m in MEMBERS for i in IM.findall(B[rel(m)])if i not in MEMBERS))
    require(external==EXTERNAL==application['external_imports'],'external imports differ from reviewed seven-import union')
    require(Q['groups'][0]['members']==MEMBERS and Q['groups'][0]['destination']==DEST and len(Q['groups'])==1,'proposal is not the approved single group')
    scopes=[scope_record(m,B[rel(m)])for m in MEMBERS]
    removed={rel(m)for m in MEMBERS[:-1]};expected={}
    for r,s in B.items():
        if r in removed:continue
        imps=list(dict.fromkeys(DEST if i in MEMBERS else i for i in IM.findall(s)))
        expected[r]=''.join('import '+i+'\n'for i in imps)+body(s)
    expected[rel(DEST)]=''.join('import '+i+'\n'for i in EXTERNAL)+'\n'.join(body(B[rel(m)])for m in MEMBERS)
    replay=dict(B);paths=[]
    for c in application['changes']:
        r=c['path'];require(r not in paths and r in B,f'duplicate/new change path: {r}');paths.append(r)
        require(c['old_text']==B[r]and c['old_sha256']==sha(B[r]),f'old text/digest differs from frozen source: {r}')
        new=c['new_text'];require(c['new_sha256']==(None if new is None else sha(new)),f'new text/digest mismatch: {r}')
        require(new!=B[r],f'no-op mutation receipt: {r}')
        if new is None:del replay[r]
        else:replay[r]=new
    require(replay==expected,'applied changes differ from independent exact-body concatenation/import remap')
    require(set(paths)=={rel(m)for m in MEMBERS}|{'lean/SupportAxioms.lean'},'unexpected changed source outside seven approved paths')
    require(application['body_sha256']=={m:sha(body(B[rel(m)]))for m in MEMBERS},'applied original body hashes mismatch')
    require(application['final_source_sha256']=={r:sha(s)for r,s in expected.items()},'application final inventory differs from replay')
    current=sources();require(current==expected,'current sources differ from exact applied/restored merge')
    names=lambda s:re.findall(r'^\s*#print axioms (\S+)\s*$',clean(s),re.M)
    oldnames,newnames=names(B['lean/SupportAxioms.lean']),names(current['lean/SupportAxioms.lean'])
    require(oldnames==newnames and len(oldnames)==len(set(oldnames))==6306,'original audit names/order changed')
    forbidden=set('sorry sorryAx admit axiom unsafe native_decide implemented_by extern trustLevel addDecl addAndCompile mkAxiom mkSorry setEnv run_meta elab_rules initialize syntax macro_rules elab run_tac run_cmd'.split())
    options=Counter();old_options=Counter()
    for r,s in current.items():
        require('\r'not in s,f'noncanonical current source newline: {r}')
        t=clean(s);hits=set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',t))&forbidden;require(not hits,f'forbidden trust token in {r}: {sorted(hits)}')
        for option in re.findall(r'^\s*set_option\s+(.+)$',t,re.M):
            option=option.strip();require(option=='autoImplicit false',f'unapproved option/limit: {r}: {option}');options[option]+=1
        require(not re.search(r'#(?:eval|compile|extern)\b',t),f'unapproved executable command in {r}')
    for s in B.values():old_options.update(x.strip()for x in re.findall(r'^\s*set_option\s+(.+)$',clean(s),re.M))
    require(options==old_options,'source option inventory changed')
    G={module(r):IM.findall(clean(s))for r,s in current.items()if r!='lean/SupportAxioms.lean'};colors={}
    def visit(m,trail):
        require(colors.get(m)!=1,f'local dependency cycle: {trail+[m]}')
        if colors.get(m)==2:return
        colors[m]=1
        for dep in G[m]:
            if dep in G:visit(dep,trail+[m])
            else:require(not dep.startswith(('TransposeFollowup.','FixedTapeCompiler.')),f'missing local import: {m}->{dep}')
        colors[m]=2
    for m in G:visit(m,[])
    for dep in IM.findall(clean(current['lean/SupportAxioms.lean'])):require(dep in G or not dep.startswith(('TransposeFollowup.','FixedTapeCompiler.')),f'missing audit import: {dep}')
    benchmarks=[]
    for path in a.benchmark_receipt:
        b=read(path);require(b['restored']is True,f'benchmark edit not restored: {path}')
        if 'variants'in b:
            require(isinstance(b['variants'],dict)and b['variants'],'empty benchmark variant record')
            for variant,row in b['variants'].items():
                require(row['restored']is True,f'benchmark variant not restored: {variant}')
                source_map=B if variant=='baseline'else current
                require(row['source']in source_map and sha(source_map[row['source']])==row['original_sha256'],f'benchmark original source digest mismatch: {variant}')
        else:
            r=b.get('source');h=b.get('original_sha256')
            require(isinstance(r,str)and r in current and isinstance(h,str)and sha(current[r])==h,f'benchmark source digest not restored: {r}')
        benchmarks.append(record(path))
    changes=[]
    for r in sorted(set(B)|set(current)):
        old,new=B.get(r),current.get(r)
        if old==new:continue
        kind='added'if old is None else'removed'if new is None else'changed'
        changes.append({'path':r,'kind':kind,'old_sha256':None if old is None else sha(old),'new_sha256':None if new is None else sha(new),'non_import_body_changed':None if old is None or new is None else body(old)!=body(new)})
    counts={kind:sum(c['kind']==kind for c in changes)for kind in ['changed','removed','added']}
    require(counts=={'changed':2,'removed':5,'added':0},'unexpected final source change counts')
    require(sources()==current,'mathematical sources changed during review')
    out={'format':'r1915-independent-source-review-v1','status':'passed','finished_at_utc':dt.datetime.now(dt.timezone.utc).isoformat(),
        'scope':'Exact source replay, declaration-body/scope preservation and trust/import hygiene. Kernel/type/axiom verification and protected-original/config guards are separate. Earlier visibility of imported instances is not certified equivalent by source review.',
        'baseline':record(a.baseline),'baseline_receipt':record(a.baseline_receipt),'proposal':record(a.proposal),'application':record(a.application),
        'baseline_sources':len(B),'final_sources':len(current),'mathematical_modules':len(G),'source_change_counts':counts,'source_changes':changes,
        'stages':[{'kind':'merge','receipt':record(a.application),'changed_sources':paths}],
        'merge':{'members':MEMBERS,'destination':DEST,'external_imports':EXTERNAL,'removed':sorted(removed),'body_sha256':{m:sha(body(B[rel(m)]))for m in MEMBERS},'scope_records':scopes},
        'all_merged_nonimport_bodies_exact':True,'global_instances_moved':0,'explicit_approved_repairs':[],
        'original_audit_names_preserved':6306,'original_audit_order_exact':True,'benchmark_receipts':benchmarks,
        'forbidden_tokens':[],'set_options':dict(options),'local_imports_acyclic':True,'missing_local_imports':[],
        'final_source_sha256':{r:sha(s)for r,s in sorted(current.items())},'reviewer':record(__file__),
        'no_Lean_Lake_executed':True,'no_repository_mathematical_sources_modified':True}
    a.output.write_text(json.dumps(out,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k not in ['final_source_sha256','merge','source_changes']},indent=2))

if __name__=='__main__':main()
