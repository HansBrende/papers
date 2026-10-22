#!/usr/bin/env python3
"""Prepare, never execute, bounded Lean type captures for the frozen6306 names.
Use reuse-baseline.py to bind the already verified R1914 final capture as baseline.
Final capture keeps those exact names but reads the then-current audit imports.
No aggregate type manifest is generated.
"""
from pathlib import Path
import argparse,hashlib,json,re
DEFAULT=Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition')
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write_new(p,j):
 with p.open('x') as f:json.dump(j,f,ensure_ascii=False,indent=2);f.write('\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('side',choices=['final']);ap.add_argument('--project',type=Path,default=DEFAULT);ap.add_argument('--capture',type=Path,default=Path('/private/tmp/r1915-preservation/capture'));a=ap.parse_args()
 P=a.project.resolve();C=a.capture.resolve();C.mkdir(parents=True,exist_ok=True);side=C/a.side;side.mkdir(exist_ok=False)
 audit=P/'lean/SupportAxioms.lean';audit_text=audit.read_text()
 names=re.findall(r'^#print axioms (\S+)\s*$',audit_text,re.M);assert len(names)==len(set(names)) and len(names)>=6306
 frozen=read(C/'names.json');assert frozen['count']==6306 and frozen['names']==names
 imports=re.findall(r'^import (\S+)\s*$',audit_text,re.M);assert imports and len(imports)==len(set(imports))
 code='import Lean\n'+''.join('import '+m+'\n' for m in imports)
 chunks=[]
 for i in range(0,len(names),80):
  target=side/f'{i//80:03d}.json';chunk=names[i:i+80]
  code+='\nopen Lean Elab Command in\nrun_cmd do\n  let output := '+json.dumps(str(target))+'\n  if ← liftIO (System.FilePath.pathExists output) then\n    throwError "Refusing to overwrite existing capture {output}"\n  let env ← getEnv\n  let names : Array Name := #[\n'+',\n'.join('    ``'+n for n in chunk)+'\n  ]\n  let rows ← names.mapM fun n => do\n    let some info := env.find? n | throwError "Missing declaration {n}"\n    pure (n.toString, Json.mkObj [("type", toJson (reprStr info.type)),\n      ("levelParams", toJson (info.levelParams.map Name.toString))])\n  liftIO <| IO.FS.writeFile output (Json.mkObj rows.toList).compress\n'
  chunks.append({'index':i//80,'path':str(target),'names':chunk})
 script=C/f'{a.side}-inspect.lean';script.write_text(code)
 descriptor={'format':'r1915-bounded-type-capture-v1','side':a.side,'declarations':6306,'chunk_size':80,'chunks':chunks,'frozen_names':str(C/'names.json'),'frozen_names_sha256':sha(C/'names.json'),'inspection_script':str(script),'inspection_script_sha256':sha(script),'audit_imports':imports,'active_audit_sha256':sha(audit),'no_aggregate':True}
 write_new(C/f'{a.side}-capture.json',descriptor)
 print(json.dumps({'script':str(script),'descriptor':str(C/f'{a.side}-capture.json'),'chunks':len(chunks),'declarations':len(names),'executed_Lean':False}))
if __name__=='__main__':main()
