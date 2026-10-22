from pathlib import Path
import re,json,functools,statistics,hashlib
P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition');V=P/'verification';L=P/'lean'
g=json.loads((V/'r1912-final-graph.json').read_text())['after'];D=g['direct_local_imports']
weights={}
for m,x,u in re.findall(r'Built ([A-Za-z0-9_.]+) \(([\d.]+)(ms|s)\)',(V/'r1912-build.log').read_text()):weights[m]=float(x)/(1000 if u=='ms' else 1)
R={m:set() for m in D}
for m,ds in D.items():
 for d in ds:R[d].add(m)
@functools.cache
def chain(m):
 score,p=max((chain(d) for d in D[m]),default=(0,[]),key=lambda x:x[0])
 return score+weights.get(m,0),p+[m]
@functools.cache
def desc(m):return {m}|set().union(*(desc(x) for x in R[m]))
score,path=max((chain(m) for m in D),key=lambda x:x[0])
print('built',len(weights),'total job durations',sum(weights.values()),'weighted path',score,'graph count',len(path),'builtpath count',sum(m in weights for m in path))
rows=[]
for m in path:
 p=L/Path(*m.split('.')).with_suffix('.lean');s=p.read_text();imps=re.findall(r'^import\s+(\S+)',s,re.M)
 row={'module':m,'seconds':weights.get(m,0),'lines':len(s.splitlines()),'direct_imports':imps,'direct_consumers':sorted(R[m]),'transitive_consumers':len(desc(m))}
 rows.append(row)
 print(f"{row['seconds']:4.1f} {row['lines']:4} {m.split('.')[-1]} <- {[x.split('.')[-1] for x in imps]}")
out={'weighted_path_seconds':score,'weighted_path':rows,'built_modules':len(weights),'durations':weights,'summed_job_seconds':sum(weights.values()),'unweighted_path_length':g['longest_path_length'],'unweighted_path_weight':sum(weights.get(m,0)for m in g['longest_path']),'source_graph_stale_modules':[m for m,h in g['source_sha256'].items() if hashlib.sha256((L/Path(*m.split('.')).with_suffix('.lean')).read_bytes()).hexdigest()!=h]}
Path('/private/tmp/r1913-import-bottleneck-analysis.json').write_text(json.dumps(out,indent=2)+'\n')
