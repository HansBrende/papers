"""Prepare only a scratch Lean contract-inspection command. Never executes Lean."""
from pathlib import Path
import json,re,argparse
A=Path('/Users/hansbrende/Documents/Codex/2026-10-09/a/research/10-linear-decision/archive/r1912-build-speed')
p=argparse.ArgumentParser();p.add_argument('--label',default='baseline');p.add_argument('--source',type=Path,default=Path('/private/tmp/r1912-type-manifest.lean'));a=p.parse_args()
s=json.loads((A/'baseline-sources.json').read_text())['lean/SupportAxioms.lean'];r=json.loads((A/'before-receipt.json').read_text())
imports=re.findall(r'^import (\S+)\s*$',s,re.M)
# Use the active audit's imports after consolidation, preserving the same names.
P=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition')
imports=re.findall(r'^import (\S+)\s*$',(P/'lean/SupportAxioms.lean').read_text(),re.M)
names=r['verified_declarations'];assert len(names)==6297
path='/private/tmp/r1912-'+a.label+'-types.json'
code='import Lean\n'+''.join('import '+m+'\n' for m in imports)
for i in range(0,len(names),80):
 output='/private/tmp/r1912-'+a.label+'-types-'+str(i//80).zfill(3)+'.json'
 code+='\nopen Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n  let names : Array Name := #[\n'+',\n'.join('    ``'+n for n in names[i:i+80])+'\n  ]\n  let rows ← names.mapM fun n => do\n    let some info := env.find? n | throwError "missing declaration {n}"\n    pure (n.toString, Json.mkObj [("type", toJson (reprStr info.type)),\n      ("levelParams", toJson (info.levelParams.map Name.toString))])\n  liftIO <| IO.FS.writeFile '+json.dumps(output)+' (Json.mkObj rows.toList).compress\n'
a.source.write_text(code);print(a.source);print('Output: bounded chunks of 80 declarations; no increased limits')
