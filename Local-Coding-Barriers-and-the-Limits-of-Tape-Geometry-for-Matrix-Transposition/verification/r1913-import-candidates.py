from pathlib import Path
import json,re,functools,copy
P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition');L=P/'lean'
old=json.loads(Path('/private/tmp/r1912-import-graph.json').read_text());G=old['graph'];local={'.'.join(p.relative_to(L).with_suffix('').parts):p for folder in ['TransposeFollowup','FixedTapeCompiler'] for p in (L/folder).rglob('*.lean')}
G={m:ds for m,ds in G.items() if not m.startswith(('TransposeFollowup.','FixedTapeCompiler.'))}
for m,p in local.items():G[m]=re.findall(r'^(?:(?:public|meta)\s+)*import\s+(\S+)',p.read_text(),re.M)
weights=json.loads(Path('/private/tmp/r1913-import-bottleneck-analysis.json').read_text())['durations']
def result(g):
 @functools.cache
 def anc(m):return {m}|set().union(*(anc(x) for x in g.get(m,[])))
 @functools.cache
 def path(m):
  score,p=max((path(d) for d in g.get(m,[]) if d in local),default=(0,[]),key=lambda x:x[0]);return score+weights.get(m,0),p+[m]
 score,p=max((path(m) for m in local),key=lambda x:x[0])
 full={m for m in local if 'Mathlib' in anc(m)}
 targets={m:{'fullMathlib':'Mathlib' in anc('TransposeFollowup.'+m),'mathlibVertices':sum(x=='Mathlib' or x.startswith('Mathlib.') for x in anc('TransposeFollowup.'+m)),'localVertices':len(anc('TransposeFollowup.'+m)&local.keys())} for m in ['RealMobiusL2','RealMobiusAverage','ComplexifiedL2Operator','MobiusSchwartzDerivative','MobiusHaarKernel','NormalizedCentralizerChart','UnconditionalPaidPadding']}
 return {'same_weight_path_seconds':score,'same_weight_path':p,'fullMathlibCount':len(full),'fullMathlibModules':sorted(full),'targets':targets}
base=result(G)
S=copy.deepcopy(G);S['TransposeFollowup.RealMobiusAverage']=['TransposeFollowup.RealMobiusL2'];S['TransposeFollowup.SpectralGapInterface'].append('TransposeFollowup.RationalMobiusAction')
a=result(S)
T=copy.deepcopy(S);T['TransposeFollowup.ComplexifiedL2Operator']=['TransposeFollowup.ComplexL2Parts','TransposeFollowup.RealMobiusAverage']
for m in ['GridHighFrequency','GridDyadicTail','RetainedCorrelationLimit','GridSmoothHighFrequency']:
 T['TransposeFollowup.'+m].append('TransposeFollowup.ContractionCorrelation')
b=result(T)
for tag,d in [('baseline',base),('realAverageCut',a),('plusCorrelationCut',b)]:
 print(tag,'path',d['same_weight_path_seconds'],'fullMathlib',d['fullMathlibCount'],'lost',len(set(base['fullMathlibModules'])-set(d['fullMathlibModules'])))
 print(d['targets'])
print('fullheavy realAverage descendants eliminated', sorted(set(base['fullMathlibModules'])-set(a['fullMathlibModules']))[:30])
Path('/private/tmp/r1913-import-candidates.json').write_text(json.dumps({'baseline':base,'realAverageCut':a,'plusCorrelationCut':b,'warning':'Static graph thought experiments only; no compilation, new durations, or claim all transitive consumer imports identified.'},indent=2)+'\n')
