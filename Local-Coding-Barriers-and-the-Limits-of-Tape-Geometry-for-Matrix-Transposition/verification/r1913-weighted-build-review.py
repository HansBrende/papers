from pathlib import Path
import json,re,hashlib,functools,statistics,datetime,collections
P=Path('.');V=P/'verification';L=P/'lean'
graph_path=Path('external/temporary/r1912-final-graph.json');graph=json.loads(graph_path.read_text());G=graph['after']['direct_local_imports']
text={n:(L/Path(*n.split('.')).with_suffix('.lean')).read_text()for n in G}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert all(hashlib.sha256(text[n].encode()).hexdigest()==graph['after']['source_sha256'][n]for n in G)
R={n:set()for n in G}
for n,ds in G.items():
 for d in ds:R[d].add(n)
log_path=V/'r1912-build.log';log=log_path.read_text();timing=json.loads((V/'r1912-build-timing.json').read_text());assert timing['exit_code']==0
pat=re.compile(r'^[^\n]*?\[(\d+)/(\d+)\] Built (\S+) \(([^)]+)\)$',re.M)
# Exact inversion of pinned Lake Build/Run.lean153-156, including its no-carry tenths behavior.
def fmt(ms):
 if ms>10000:return f'{ms//1000}s'
 if ms>1000:return f'{ms//1000}.{((ms+50)//100)%10}s'
 return f'{ms}ms'
small=collections.defaultdict(list)
for ms in range(1,10001):small[fmt(ms)].append(ms)
def interval(s):
 if s in small:return min(small[s])/1000,max(small[s])/1000
 assert re.fullmatch(r'\d+s',s),s
 sec=int(s[:-1]);assert sec>=10
 return max(10001,sec*1000)/1000,((sec+1)*1000-1)/1000
rows=[]
for index,total,name,display in pat.findall(log):
 lo,hi=interval(display);value=float(display[:-2])/1000 if display.endswith('ms')else float(display[:-1])
 rows.append(dict(module=name,job_index=int(index),display=display,displayed_seconds=value,lower_seconds=lo,upper_seconds=hi,source_lines=len(text[name].splitlines())))
assert len(rows)==347 and len({r['module']for r in rows})==347 and all(r['module']in G for r in rows)
by={r['module']:r for r in rows};weights={r['module']:r['displayed_seconds']for r in rows};lower={r['module']:r['lower_seconds']for r in rows};upper={r['module']:r['upper_seconds']for r in rows}
def best_path(weights,graph=G):
 @functools.cache
 def path(n):
  prefix=max((path(d)for d in graph[n]),key=lambda p:(p[0],len(p[1]),p[1]),default=(0,()))
  return prefix[0]+weights.get(n,0),prefix[1]+(n,)
 paths={n:path(n)for n in graph};return max(paths.values(),key=lambda p:(p[0],len(p[1]),p[1])),paths
cp,paths=best_path(weights);cp_low,_=best_path(lower);cp_high,_=best_path(upper)
@functools.cache
def ancestors(n):return {n}|set().union(*(ancestors(d)for d in G[n]))
@functools.cache
def descendants(n):return {n}|set().union(*(descendants(d)for d in R[n]))
def quotient(group):
 group=set(group);mapping={n:('@group'if n in group else n)for n in G};q={mapping[n]:set()for n in G}
 for n,ds in G.items():q[mapping[n]].update(mapping[d]for d in ds if mapping[d]!=mapping[n])
 active=set();done=set()
 def visit(n):
  if n in active:return False
  if n in done:return True
  active.add(n)
  if not all(visit(d)for d in q[n]):return False
  active.remove(n);done.add(n);return True
 acyclic=all(visit(n)for n in q)
 return q,acyclic
prefix='TransposeFollowup.'
candidates=[
 ('small_expansion_energy_pilot','Five adjacent error/energy lemmas, with no internal fan-out.','SmallExpansionSymmDiff IndicatorPullbackError WeightedIndicatorError WeightedEnergyTransfer UnitBoundaryError'),
 ('small_expansion_to_spectral_input','Same error/energy chain through almost-invariance and conditional spectral expansion; broader second batch.','SmallExpansionSymmDiff IndicatorPullbackError WeightedIndicatorError WeightedEnergyTransfer UnitBoundaryError CellCenteredAlmostInvariant CellCenteredRelativeError ExpansionParameters NormalizedCellCorrelation ConditionalSpectralExpansion'),
 ('mobius_continuity_averaging','One near-identity/continuity/averaging subroutine.','MobiusNearIdentity MobiusPairwiseComparison MobiusActionContinuity MobiusGroupAverage MobiusGroupSmoothing'),
 ('centralizer_sampling_packing','One centralizer chart/selection/sample/packing subroutine; imports need closer semantic audit.','NormalizedCentralizerChart CentralizerClusterSelection LocalizedCentralizerSample LocalizedCentralizerPacking ActualCentralizerPacking'),
 ('graph_to_rational_family','Combinatorial overlap expansion through rational family construction.','MonotoneOverlapGraph BipartiteExpansionCount BipartiteVertexExpansion OverlapExpansion SymmetricOverlap RationalFamilyGraph'),
 ('haar_entry_support','Haar kernel/column/entry support, with several external consumers remapped.','MobiusHaarKernel MobiusColumnHaar MobiusHaarEntryBox MobiusWalkEntrySupport'),
]
cs=[]
for label,reason,short in candidates:
 group=[prefix+n for n in short.split()];S=set(group);q,acyclic=quotient(group)
 hull=(set().union(*(ancestors(n)for n in S)) & set().union(*(descendants(n)for n in S)))-S
 assert acyclic == (not bool(hull))
 zero={n:(0 if n in S else weights.get(n,0))for n in G};zero_cp,_=best_path(zero)
 item=dict(id=label,reason=reason,modules=group,lines=sum(len(text[n].splitlines())for n in group),module_count=len(group),removed_boundaries=len(group)-1,displayed_action_sum_seconds=sum(weights.get(n,0)for n in group),all_rebuilt=all(n in by for n in group),all_on_selected_weighted_path=S<=set(cp[1]),direct_external_prerequisites=sorted(set().union(*(set(G[n])for n in group))-S),direct_external_consumers=sorted(set().union(*(R[n]for n in group))-S),quotient_acyclic=acyclic,extra_modules_required_for_convexity=sorted(hull),ideal_fixed_weight_zero_cost_path_seconds=zero_cp[0],ideal_fixed_weight_critical_path_reduction_ceiling_seconds=cp[0]-zero_cp[0],private_or_local_attribute_lines=[{'module':n,'line':i,'text':line.strip()}for n in group for i,line in enumerate(text[n].splitlines(),1)if re.match(r'\s*(private\b|local\s+(attribute|instance)|attribute\s+\[local)',line)])
 if acyclic:
  # Optimistic fixed-work model only; zero merged cost still brings external prerequisites forward.
  qw={n:weights.get(n,0)for n in q};qw['@group']=0
  qcp,_=best_path(qw,q);item['zero_cost_quotient_path_seconds']=qcp[0];item['zero_cost_quotient_path_reduction_ceiling_seconds']=cp[0]-qcp[0]
 cs.append(item)
# Log order is completion-report order, not execution intervals; no occupancy inferred.
quintiles=[]
for i in range(5):
 chunk=rows[i*len(rows)//5:(i+1)*len(rows)//5]
 quintiles.append(dict(completion_order_fifth=i+1,count=len(chunk),first_job=chunk[0]['job_index'],last_job=chunk[-1]['job_index'],median_seconds=statistics.median(r['displayed_seconds']for r in chunk),min_seconds=min(r['displayed_seconds']for r in chunk),max_seconds=max(r['displayed_seconds']for r in chunk)))
def percentile(values,p):
 vals=sorted(values);idx=(len(vals)-1)*p;lo=int(idx);hi=min(len(vals)-1,lo+1);return vals[lo]+(vals[hi]-vals[lo])*(idx-lo)
values=list(weights.values());fullpath=graph['after']['longest_path'];cp_rows=[dict(module=n,displayed_seconds=weights.get(n,0),lower_seconds=lower.get(n,0),upper_seconds=upper.get(n,0),rebuilt=n in by,source_lines=len(text[n].splitlines()))for n in cp[1]]
first_path=V/'r1912-consolidated-full-build.log';firstlog=first_path.read_text();first={n:float(t[:-1])for _,_,n,t in pat.findall(firstlog)};common=set(first)&set(weights)
firsttiming=json.loads((V/'r1912-consolidated-full-build-timing.json').read_text())
res=dict(created_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='Read-only timing/dependency review; no Lean/Lake execution or source/receipt modification.',inputs={str(p):sha(p)for p in [graph_path,log_path,V/'r1912-build-timing.json',first_path,V/'r1912-consolidated-full-build-timing.json']},final_build_wall_seconds=timing['wall_seconds'],total_lake_jobs_including_cached=10071,rebuilt_modules=len(rows),local_math_modules=len(G),summed_displayed_action_seconds=sum(values),summed_action_interval_seconds=[sum(lower.values()),sum(upper.values())],distribution=dict(min=min(values),p10=percentile(values,.1),p25=percentile(values,.25),median=statistics.median(values),p75=percentile(values,.75),p90=percentile(values,.9),max=max(values)),completion_order_fifths=quintiles,weighted_path=dict(displayed_seconds=cp[0],lower_bound_seconds=cp_low[0],upper_bound_from_display_intervals_seconds=cp_high[0],lower_bound_fraction_of_observed_wall=cp_low[0]/timing['wall_seconds'],total_nodes=len(cp[1]),rebuilt_nodes=sum(n in by for n in cp[1]),cached_nodes=sum(n not in by for n in cp[1]),rebuilt_source_lines=sum(len(text[n].splitlines())for n in cp[1]if n in by),nodes=cp_rows),unweighted_longest_path=dict(nodes=len(fullpath),rebuilt_nodes=sum(n in by for n in fullpath),displayed_action_sum_seconds=sum(weights.get(n,0)for n in fullpath),different_rebuilt_nodes_vs_selected_weighted_path=sorted(set(fullpath)^set(cp[1]))),largest_actions=sorted(rows,key=lambda r:(-r['displayed_seconds'],r['module']))[:30],candidate_group_pilots=cs,first_failed_attempt_context=dict(receipt=firsttiming,rebuilt_successful_modules=len(first),common_rebuilt_modules=len(common),final_only_rebuilt=len(set(weights)-set(first)),first_only_rebuilt=len(set(first)-set(weights)),common_median_first_seconds=statistics.median(first[n]for n in common),common_median_final_seconds=statistics.median(weights[n]for n in common),comparison_is_matched=False,caution='First attempt failed, had a different rebuilt set and pre-repair sources/import graph. Its wall time is not a baseline for a speed ratio. Common-name duration changes do not isolate concurrency, cache or source effects.'),modules=rows,method=['Use the current exact source-hash-matched local import DAG; all cached/unreported nodes have weight0.','Longest prerequisite path uses displayed build-action durations; ties prefer longer full local paths.','Invert pinned Lake formatTime to bound actual millisecond durations. All72 selected rebuilt-path durations exceed10s and are floored, so their1281s displayed sum is a lower bound.','Reported action durations exclude dependency waiting and inherited registered dependency times (JobState.renew). They include compilation and artifact work, and can include interference from concurrent work.','Summed concurrent actions are job-seconds, not wall seconds, CPU seconds or an achievable serial build duration.','There are no start timestamps; completion order does not identify overlapping processes, concurrency level or the hardware cause of long actions.','Candidate zero-cost models are fixed-duration best cases that cannot predict measured improvement; grouping can alter imports, invalidate more proofs per edit and change action durations.'],pinned_lake_evidence=[dict(file='Lake/Build/Module.lean',lines='981-990;1005-1010',claim='buildLean wraps own compile/artifact work in buildAction; recBuildLean waits for presetupJob before calling fetchCore.'),dict(file='Lake/Build/Common.lean',lines='318-331',claim='monoMsNow starts inside buildAction and accumulates only that action elapsed.'),dict(file='Lake/Build/Job/Register.lean',lines='20-21;28-32;38-44',claim='Registering returns job.renew, whose state retains trace and resets buildTime; dependency elapsed is not inherited.'),dict(file='Lake/Build/Run.lean',lines='123-138;153-156',claim='Monitor displays buildTime. >10000ms is integer division by1000; smaller displays use unusual tenths with no carry, so exact inverse intervals are used.'),dict(file='Lake/Build/Job/Monad.lean',lines='196-205',claim='mapM continuation executes after its input task has completed.')],benchmarks=['First: same five-body SmallExpansionSymmDiff-through-UnitBoundaryError scratch comparison on validated current cached prerequisites, split versus concatenated, two alternating pairs; no proof modifications or cache-forcing tricks. Include import-only probe to measure how much of isolated elapsed is common loading/artifact cost.','If pilot helps, stage the ten-body expansion-to-spectral-input group (1266 lines) after namespace/private/instance and quotient-DAG checks; use a normal targeted rebuild and exact source/type/axiom audit.','In parallel preparation, benchmark Mobius near-identity/continuity/averaging (5 modules) and centralizer chart/sample/packing only if its convexity report passes; do not expand into large heterogeneous files merely to shorten the path.','Use one explicit bounded set of affected modules for an end-to-end A/B baseline before the next source changes. Measure the same target set and source edit/restoration protocol on both sides; final validation remains separate.','A separate four-module pool1-vs-pool2 experiment with child Lean threads fixed can test contention. Treat it as secondary: a72-action dependency chain already accounts for at least1281s of the1321s run, although reducing contention can shorten those actions.'])
Path('external/temporary/r1913-weighted-build-review.json').write_text(json.dumps(res,indent=2)+'\n')
lines=['R1913 READ-ONLY WEIGHTED BUILD REVIEW','',f'Final ordinary build: {timing["wall_seconds"]:.3f}s. Lake reports10071 jobs, but only347 local modules rebuilt.',f'Summed displayed build actions: {sum(values):.1f} job-seconds, NOT elapsed build time.',f'Distribution: min {min(values):.1f}s; quartiles {percentile(values,.25):.1f}/{statistics.median(values):.1f}/{percentile(values,.75):.1f}s; max {max(values):.1f}s.','',f'The weighted dependency path contains {len(cp[1])} local nodes:72 rebuilt and9 cached.',f'Its displayed action sum is1281s; because all72 are floored integer-second displays,',f'1281s is a lower bound ({100*cp_low[0]/timing["wall_seconds"]:.2f}% of the observed1321.040s wall time).',f'The display-derived upper bound is {cp_high[0]:.3f}s and may exceed actual build wall time because every', 'node is independently rounded down. Do not identify the40.040s residual as scheduler overhead.',f'The prior unweighted81-node path has72 rebuilt nodes and1278s displayed work.', 'The weighted variant takes TraceSquareTwoStageSample and TraceSquareSampleApplication', 'instead of TraceSquarePairedEnlargement and TraceSquareActualWordGrowth. Cached prefixes', 'may tie; counting only rebuilt modules is essential.','', 'This is a mostly serial critical chain, from overlap expansion through analytic transport,', 'Haar/centralizer estimates and trace-square sampling to UnconditionalPaidPadding.', 'The natural next target is reducing repeated compiler/import/artifact cost on that chain.', 'Parallelism alone cannot shorten dependencies; reducing interference may still shorten actions.','', 'Timing semantics verified against pinned Lean4.34.1:', '  Module.lean981-990 and1005-1010: own compile/artifact action runs after presetup.', '  Common.lean318-331: action timer starts after prerequisite handling.', '  Job/Register.lean20-21,28-32,38-44: downstream state reset removes dependency buildTime.', '  Run.lean123-138,153-156: displayed buildTime; >10s floor, smaller format inverted exactly.', 'Thus dependent action durations may be added without double-counting dependency waits.','', 'Candidate groups (static candidates, no implementation or benchmark performed):']
for c in cs:lines.append(f'  {c["id"]}: {c["module_count"]} modules/{c["lines"]} lines/{c["displayed_action_sum_seconds"]:.0f}s observed action sum; quotient acyclic={c["quotient_acyclic"]}; zero-cost fixed-weight path reduction ceiling {c.get("zero_cost_quotient_path_reduction_ceiling_seconds",c["ideal_fixed_weight_critical_path_reduction_ceiling_seconds"]):.0f}s.')
lines+=['','Recommend first pilot: five error/energy modules (653 lines,84s in this run).', 'Compare the same five bodies split versus concatenated with two alternating pairs', 'and a cached-import-only probe, then ordinary targeted Lake validation. If useful,', 'expand to ten coherent modules (1266 lines); do not promise the84s disappears.', '', 'The largest single actions32s are not automatically best targets: many sit off the', 'selected critical chain, while most chain modules are small15-19s files. Pilot', 'cumulative repeated-loading costs on a critical chain before optimizing isolated tactics.', '', 'A future fixed workload end-to-end A/B is required before claiming a whole-project', 'speedup. The earlier1380.436s run failed and rebuilt553 modules; it is not a matched', 'baseline for the successful1321.040s run. Its common-module timings are context only.', '', 'No start timestamps exist, so this review cannot recover concurrency or blame RAM,', 'CPU, disk or paging. Zero-cost model ceilings hold other node durations fixed; they', 'are not promised wall-time savings. No Lean/Lake execution, sources, receipts or', 'configuration changed. Full path, timing bounds, quotient checks, consumers and', 'per-module data are in r1913-weighted-build-review.json.']
Path('external/temporary/r1913-weighted-build-review.txt').write_text('\n'.join(lines)+'\n')
print(json.dumps({k:res[k]for k in ['rebuilt_modules','summed_displayed_action_seconds','summed_action_interval_seconds','distribution']},indent=2));print('CP',cp[0],len(cp[1]),cp_low[0],cp_high[0]);print('GROUPS',[(c['id'],c['lines'],c['quotient_acyclic'],c.get('zero_cost_quotient_path_reduction_ceiling_seconds'))for c in cs])
