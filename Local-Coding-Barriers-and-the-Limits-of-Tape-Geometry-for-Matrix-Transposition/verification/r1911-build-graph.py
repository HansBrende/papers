from pathlib import Path
import re,json,statistics,functools
P=Path('lean')
f={'.'.join(x.relative_to(P).with_suffix('').parts):x for d in ['TransposeFollowup','FixedTapeCompiler'] for x in (P/d).glob('*.lean')};text={m:p.read_text() for m,p in f.items()};deps={m:set(re.findall(r'^import ([A-Za-z0-9_.]+)',t,re.M))&f.keys() for m,t in text.items()}
rev={m:set() for m in f}
for m,d in deps.items():
 for a in d:rev[a].add(m)
log=Path('external/temporary/r1911-full-build.log').read_text();tim={m:float(t) for m,t in re.findall(r'Built ((?:TransposeFollowup|FixedTapeCompiler)\.[A-Za-z0-9_]+) \(([0-9.]+)s\)',log)}
@functools.cache
def path(m):
 p=max((path(x) for x in deps[m]),key=lambda a:a[0],default=(0,[]));return (p[0]+tim.get(m,14),p[1]+[m])
@functools.cache
def closure(m):
 return {m}|set().union(*(closure(x) for x in deps[m]))
@functools.cache
def descendants(m):
 return {m}|set().union(*(descendants(x) for x in rev[m]))
ends=sorted(f,key=lambda m:path(m)[0],reverse=True)
best=ends[0];out=dict(modules=len(f),recorded_builds=len(tim),recorded_seconds=sum(tim.values()),median_seconds=statistics.median(tim.values()),longest_assuming14s_for_unbuilt=dict(endpoint=best,seconds=path(best)[0],path=[dict(module=m,lines=len(text[m].splitlines()),seconds=tim.get(m),direct_imports=sorted(deps[m]),direct_consumers=len(rev[m]))for m in path(best)[1]]),biggest_fanin=[dict(module=m,closure=len(closure(m)),lines=len(text[m].splitlines()),descendants=len(descendants(m))) for m in sorted(f,key=lambda m:len(closure(m)),reverse=True)[:10]])
Path('external/temporary/r1911-build-graph.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='longest_assuming14s_for_unbuilt'},indent=2))
print('PATH',len(path(best)[1]),path(best)[0]);
for x in out['longest_assuming14s_for_unbuilt']['path']: print(x['module'].split('.')[-1],x['lines'],x['seconds'],x['direct_consumers'])
