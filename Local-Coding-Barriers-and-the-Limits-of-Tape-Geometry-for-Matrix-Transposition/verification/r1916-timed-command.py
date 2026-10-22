from pathlib import Path
import datetime,json,os,platform,subprocess,sys,time
P=Path(__file__).resolve().parents[1];V=P/'verification'
label=sys.argv[1];args=sys.argv[2:];assert args
assert not json.loads((V/'r1916-in-progress.json').read_text())['live_handles']
start=time.perf_counter();began=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (V/f'r1916-{label}.log').open('w') as out:
 child=subprocess.Popen(args,cwd=P/'lean',stdout=out,stderr=subprocess.STDOUT)
 pid,status,usage=os.wait4(child.pid,0);assert pid==child.pid
 child.returncode=os.waitstatus_to_exitcode(status)
row=dict(label=label,command=args,started_at=began,finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),wall_seconds=time.perf_counter()-start,exit_code=child.returncode,user_seconds=usage.ru_utime,system_seconds=usage.ru_stime,max_rss_bytes=usage.ru_maxrss if platform.system()=='Darwin' else usage.ru_maxrss*1024)
(V/f'r1916-{label}-timing.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row),flush=True);sys.exit(child.returncode)
