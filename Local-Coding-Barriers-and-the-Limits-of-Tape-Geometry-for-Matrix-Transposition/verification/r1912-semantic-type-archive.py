#!/usr/bin/env python3
"""Archive immutable raw type differences plus verified kernel conversions.

Run only after the separately executed Lean checker and receipt assembler pass.
This utility does NOT invoke Lean, edit proof sources, alter comparison receipts,
or normalize types. It repeats the exact raw comparisons, verifies semantic
coverage/provenance, archives the complete evidence, and compares every
archived member byte-for-byte with its original before optional bulk cleanup.
"""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import tarfile
import tempfile

P=Path('.')
V=P/'verification'
A=Path('external/research-workspace/research/10-linear-decision/archive/r1912-build-speed')
BLOCK=1024*1024
COUNT=6297
RAW_SAME=6028
RAW_DIFFERENT=269
KERNEL_COUNT=267
HEADER_COUNT=2
HEADER_NAMES={'TransposeFollowup.NativePaddedField.tail_trace',
              'TransposeFollowup.CountedFill.emit_step'}


def require(condition,message):
    if not condition: raise ValueError(message)


def unique(pairs):
    result={}
    for k,v in pairs:
        require(k not in result,f'duplicate JSON key: {k!r}')
        result[k]=v
    return result


def read(path):
    with Path(path).open(encoding='utf-8') as stream:
        return json.load(stream,object_pairs_hook=unique)


def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(BLOCK),b''): h.update(block)
    return h.hexdigest()


def stat_key(path):
    s=Path(path).stat()
    return s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns


def record(path):
    path=Path(path).resolve();before=stat_key(path)
    r={'path':str(path),'bytes':before[2],'sha256':sha(path)}
    require(stat_key(path)==before,f'file changed while reading: {path}')
    return r


def check_record(r,path=None):
    p=Path(r['path'] if path is None else path).resolve()
    require(p==Path(r['path']).resolve(),f'provenance path mismatch: {p}')
    actual=record(p)
    require(actual['bytes']==r['bytes'] and actual['sha256']==r['sha256'],f'provenance mismatch: {p}')
    return actual


def write_json(path,obj):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    fd,tmp=tempfile.mkstemp(prefix=path.name+'.',suffix='.tmp',dir=path.parent)
    try:
        with os.fdopen(fd,'w',encoding='utf-8') as stream:
            json.dump(obj,stream,ensure_ascii=False,sort_keys=True,indent=2);stream.write('\n')
        os.replace(tmp,path)
    finally:
        if os.path.exists(tmp):os.unlink(tmp)


def prepare(args):
    raw_record=record(args.comparison);raw=read(args.comparison)
    semantic_record=record(args.semantic);semantic=read(args.semantic)
    require(raw['status']=='failed' and raw['different_declarations']==RAW_DIFFERENT,'raw mismatch report must remain failed with269 differences')
    require(raw['archive'] is None,'raw receipt must remain unchanged with archive:null')
    require(all(raw[k]==COUNT for k in ['expected_original_declarations','baseline_declarations','final_declarations']),'raw declaration count mismatch')
    require(raw['chunk_pairs']==79,'expected79 raw chunk pairs')
    names=[r['name'] for r in raw['mismatches']]
    require(len(names)==len(set(names))==RAW_DIFFERENT,'raw mismatch-name set invalid')
    require(all(r['type_equal'] is False and r['levelParams_equal'] is True for r in raw['mismatches']),'unexpected raw difference class')
    require(semantic['format']=='r1912-kernel-type-conversion-v1' and semantic['status']=='passed','kernel conversion report not passed')
    require(semantic['archive'] is None,'semantic receipt must remain unchanged with archive:null')
    for key,val in [('original_declarations',COUNT),('raw_identical_declarations',RAW_SAME),('raw_different_declarations',RAW_DIFFERENT),('kernel_converted_declarations',KERNEL_COUNT),('source_header_checked_declarations',HEADER_COUNT)]:
        require(semantic[key]==val,f'semantic count mismatch: {key}')
    require(semantic['declarations']==names and set(semantic['checks'])==set(names),'semantic coverage differs from raw mismatch set')
    check_record(semantic['raw_comparison'],args.comparison)
    require(semantic['raw_comparison']['sha256']==raw_record['sha256'],'raw receipt provenance mismatch')
    require(record(args.raw_comparator)['sha256']==raw['comparator']['sha256'],'raw comparator is not the originally recorded code')
    # Reuse the preserved raw comparator's name extraction and exact record
    # equality. Its source hash is checked above before loading it.
    spec=importlib.util.spec_from_file_location('r1912_preserved_raw_comparator',args.raw_comparator)
    helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
    source_record=record(args.baseline_source_inventory)
    require(source_record['sha256']==raw['source_inventory_sha256'],'baseline source inventory changed')
    original_names=helper.expected_names(args.baseline_source_inventory)
    original_set=set(original_names)
    compact={side:read(Path(raw['compact_outputs'][side])) for side in ['baseline','final']}
    name_receipt=read(Path(raw['compact_outputs']['original_names']))
    require(name_receipt['names']==original_names and name_receipt['count']==COUNT,'compact original name list mismatch')
    require(name_receipt['source_inventory_sha256']==source_record['sha256'],'name inventory provenance mismatch')
    for side in compact:
        require(compact[side]['declarations']==COUNT and set(compact[side]['types'])==original_set,f'{side} compact manifest coverage mismatch')

    # Two retired generated proof names prevent old-Expr kernel conversion.
    # These use separate ordinary proofs of the exact archived source headers;
    # do not mislabel them as original-Expr conversion checks.
    check_record(semantic['exact_source_headers'])
    headers=read(semantic['exact_source_headers']['path'])
    require(headers['format']=='r1912-exact-archived-source-header-checks-v1' and headers['count']==HEADER_COUNT,'source-header receipt format/count mismatch')
    require(headers['baseline_inventory_sha256']==source_record['sha256'],'source-header baseline provenance mismatch')
    require(headers['checker_sha256']==semantic['checker']['sha256'],'source-header checker provenance mismatch')
    header_rows={r['name']:r for r in headers['declarations']}
    require(len(header_rows)==len(headers['declarations'])==HEADER_COUNT and set(header_rows)==HEADER_NAMES,'wrong source-header fallback declarations')
    source_inventory=read(args.baseline_source_inventory)
    checker_text=Path(semantic['checker']['path']).read_text()
    for n,h in header_rows.items():
        source=source_inventory[h['baseline_source']]
        require(hashlib.sha256(source.encode()).hexdigest()==h['baseline_source_sha256'],'source-header archived source digest mismatch')
        original=h['original_header'];renamed=h['renamed_header'];text=h['source_check_text']
        require(hashlib.sha256(original.encode()).hexdigest()==h['original_header_sha256'],'source-header text digest mismatch')
        require(source.count(original)==1,'source-header not uniquely present in original source')
        short=n.rsplit('.',1)[1];auditor=h['auditor_declaration'].rsplit('.',1)[1]
        require(original.startswith('theorem '+short+' '),'unexpected original theorem header')
        require(renamed==original.replace('theorem '+short+' ','theorem '+auditor+' ',1),'source-header changed beyond declaration identifier')
        require(renamed+' := by\n' in text,'renamed source-header not used as ordinary theorem statement')
        require(hashlib.sha256(text.encode()).hexdigest()==h['source_check_text_sha256'],'source-check text digest mismatch')
        require(checker_text.count(text)==1,'exact source-header check not uniquely in executed checker')

    # Bind successful kernel outputs to exact immutable AST inputs and code.
    for field in ['checker','input_inventory','lean_log','execution_record']:
        check_record(semantic[field])
    execution=read(semantic['execution_record']['path'])
    require(execution['exit_code']==0,'kernel checker process was not successful')
    log=Path(semantic['lean_log']['path']).read_text()
    require(not re.search(r'(^|\n)(?:.*: )?(?:error:|warning:)',log),'kernel log has an error/warning')
    require(sum('R1912 kernel conversion chunk passed:' in line for line in log.splitlines())==34,'kernel log must report34 successful chunks')
    inventory=read(semantic['input_inventory']['path'])
    require(inventory['declarations']==RAW_DIFFERENT and len(inventory['chunks'])==34,'AST chunk inventory count mismatch')
    ast_path=Path(inventory['source']);ast_record=record(ast_path)
    require(ast_record['sha256']==inventory['sourceSHA256'],'AST aggregate provenance mismatch')
    ast=read(ast_path)
    require(ast['expectedDeclarations']==RAW_DIFFERENT and ast['comparisonSHA256']==raw_record['sha256'],'AST aggregate provenance/coverage mismatch')
    require(record(args.decoder)['sha256']==ast['decoderSHA256'],'decoder source differs from recorded AST provenance')
    ast_rows={r['name']:r for r in ast['declarations']}
    require(len(ast_rows)==len(ast['declarations'])==RAW_DIFFERENT and set(ast_rows)==set(names),'AST aggregate names mismatch')
    require(len(semantic['input_chunks'])==len(semantic['output_chunks'])==34,'semantic chunk provenance count mismatch')
    seen=set()
    records=[]
    def add(path,member,bulky=False,expected=None):
        r=record(path)
        if expected is not None:
            require(r['bytes']==expected['bytes'] and r['sha256']==expected['sha256'],f'changed archived input: {path}')
        records.append(r|{'member':member,'bulky':bulky})
    for i,entry in enumerate(inventory['chunks']):
        require(entry['index']==i,'AST inventory order mismatch')
        inp=check_record(entry)
        require(inp==check_record(semantic['input_chunks'][i]),'semantic input provenance mismatch')
        out=check_record(semantic['output_chunks'][i])
        transport=read(inp['path']);result=read(out['path']);rows=transport['declarations']
        require(transport['comparisonSHA256']==raw_record['sha256'] and transport['decoderSHA256']==ast['decoderSHA256'],'AST chunk provenance mismatch')
        require(transport['expectedDeclarations']==len(rows) and 0<len(rows)<=8,'AST chunk size invalid')
        require([r['name'] for r in rows]==entry['declarations'],'AST chunk names mismatch')
        require(result['format']=='r1912-kernel-type-conversion-chunk-v1' and result['status']=='passed','kernel chunk not passed')
        require(result['checked_declarations']==len(rows) and Path(result['input']).resolve()==Path(inp['path']),'kernel chunk input/count mismatch')
        require(result['kernel_positive_and_negative_controls'] is True,'kernel controls not passed')
        require(result['comparisonSHA256']==raw_record['sha256'] and result['decoderSHA256']==ast['decoderSHA256'],'kernel chunk provenance mismatch')
        require([r['name'] for r in result['results']]==entry['declarations'],'kernel output name order mismatch')
        for row,check in zip(rows,result['results']):
            n=row['name'];require(n in ast_rows and n not in seen,'duplicate/unexpected kernel target')
            require(row==ast_rows[n],'AST chunk differs from aggregate record')
            require(check==semantic['checks'][n],'combined semantic receipt differs from chunk output')
            for flag in ['original_repr_roundtrip_exact','current_repr_matches_final_capture','ordered_universe_parameters_exact']:
                require(check[flag] is True,f'failed kernel/reconstruction check: {n}:{flag}')
            if n in HEADER_NAMES:
                require(check['validation_route']=='archived_source_header_kernel','source-header route missing')
                require(check['kernel_identity_application_checked'] is False and check['original_source_header_kernel_checked'] is True,'source-header check mislabeled as original Expr conversion')
                require(check['auditor_declaration']==header_rows[n]['auditor_declaration'],'source-header auditor declaration mismatch')
            else:
                require(check['validation_route']=='original_expr_kernel','unexpected kernel conversion route')
                require(check['kernel_identity_application_checked'] is True and check['original_source_header_kernel_checked'] is False,'original Expr conversion not passed')
            require(row['levelParams']==row['currentLevelParams']==check['levelParams'],f'universe parameter mismatch: {n}')
            for side,textfield,prefix in [('baseline','baselineRepr','baseline'),('final','currentRepr','current')]:
                text=row[textfield];encoded=text.encode('utf-8');h=hashlib.sha256(encoded).hexdigest()
                c=compact[side]['types'][n]
                require(h==row[prefix+'ReprSHA256']==check[prefix+'ReprSHA256']==c['type_sha256'],f'repr provenance mismatch: {n}:{side}')
                require(len(encoded)==c['type_utf8_bytes'] and len(text)==c['type_characters'] and c['levelParams']==row['levelParams'],f'compact type metadata mismatch: {n}:{side}')
            seen.add(n)
        add(inp['path'],f'semantic/input/{i:03d}.json',expected=inp)
        add(out['path'],f'semantic/output/{i:03d}.json',expected=out)
    require(seen==set(names),'kernel conversion target set incomplete')

    # Re-run every literal comparison, not a hash-only shortcut. Also bind the
    #269 original/current full strings directly to reconstructed AST inputs.
    chunk_records={(r['side'],r['index']):r for r in raw['input_chunks']}
    require(len(chunk_records)==len(raw['input_chunks'])==158,'raw chunk provenance coverage invalid')
    require(set(chunk_records)=={(s,i) for s in ('baseline','final') for i in range(79)},'raw chunks not79 complete pairs')
    seen_all=set();actual_different=[];identical=0
    for i in range(79):
        values={}
        for side in ('baseline','final'):
            r=chunk_records[side,i];check_record(r)
            values[side]=read(r['path'])
            add(r['path'],f'{side}/chunks/{i:03d}.json',bulky=True,expected=r)
        old,new=values['baseline'],values['final']
        require(set(old)==set(new),'raw chunk name partitions changed')
        require(not seen_all.intersection(old) and set(old).issubset(original_set),'raw chunk names duplicate/unexpected')
        for n in old:
            difference=helper.compare_record(n,old[n],new[n])
            if difference is None:identical+=1
            else:
                actual_different.append(difference)
                require(n in ast_rows,'literal mismatch lacks kernel conversion')
                row=ast_rows[n]
                require(old[n]['type']==row['baselineRepr'] and new[n]['type']==row['currentRepr'],f'AST repr differs from actual raw chunk: {n}')
                require(old[n]['levelParams']==row['levelParams'] and new[n]['levelParams']==row['currentLevelParams'],f'AST universes differ from raw chunk: {n}')
            for side,record_value in [('baseline',old[n]),('final',new[n])]:
                require(helper.compact_record(record_value)==compact[side]['types'][n],f'compact manifest differs from raw type: {n}:{side}')
        seen_all.update(old)
        if args.progress:print(f'Raw evidence rechecked: {i+1}/79 chunks, {len(seen_all)}/6297 declarations',flush=True)
    require(seen_all==original_set and identical==RAW_SAME,'raw exact-equality counts changed')
    require(actual_different==raw['mismatches'],'exact raw differences changed from immutable comparison receipt')

    for side,path in [('baseline',args.baseline_aggregate),('final',args.final_aggregate)]:
        if path is not None:add(path,f'{side}/aggregate.json',bulky=True)
    for path in [args.comparison,args.semantic,*[Path(raw['compact_outputs'][k]) for k in ['baseline','final','original_names']]]:
        add(path,'comparison/'+Path(path).name)
    for path,member in [
        (args.baseline_source_inventory,'evidence/baseline-sources.json'),
        (args.raw_comparator,'evidence/raw-compare-types.py'),
        (args.decoder,'evidence/decode-expr-repr.py'),
        (args.assembler,'evidence/assemble-kernel-type-conversion.py'),
        (args.header_generator,'evidence/prepare-kernel-type-checker-v2.py'),
        (semantic['exact_source_headers']['path'],'evidence/source-header-checks.json'),
        (Path(__file__),'evidence/semantic-type-archive.py'),
        (semantic['checker']['path'],'evidence/kernel-type-checker.lean'),
        (semantic['lean_log']['path'],'evidence/kernel-lean.log'),
        (semantic['execution_record']['path'],'evidence/kernel-execution.json'),
        (semantic['input_inventory']['path'],'evidence/ast-inventory.json'),
        (ast_path,'evidence/original-types-ast.json')]:add(path,member)
    # A source must never become a cleanup target through path aliasing.
    protected={r['path'] for r in records if not r['bulky']}
    require(not protected.intersection(r['path'] for r in records if r['bulky']),'bulky cleanup overlaps preserved evidence')
    members=[r['member'] for r in records]
    require(len(members)==len(set(members)),'duplicate archive member names')
    require(check_record(raw_record)==raw_record and check_record(semantic_record)==semantic_record,'canonical receipts changed during verification')
    return records,raw_record,semantic_record


def archive(args,records,raw_record,semantic_record):
    target=args.archive.resolve();partial=target.with_name(target.name+'.partial')
    target.parent.mkdir(parents=True,exist_ok=True)
    inventory={'format':'r1912-semantic-full-type-archive-v1',
               'original_declarations':COUNT,'raw_identical_declarations':RAW_SAME,
               'raw_different_declarations':RAW_DIFFERENT,'kernel_converted_declarations':KERNEL_COUNT,
               'source_header_checked_declarations':HEADER_COUNT,
               'raw_comparison':raw_record,'semantic_comparison':semantic_record,'members':records}
    inv=(json.dumps(inventory,ensure_ascii=False,sort_keys=True,indent=2)+'\n').encode()
    invname='comparison/archive-inventory.json'
    with partial.open('xb') as output:
        with tarfile.open(fileobj=output,mode='w:gz',compresslevel=args.compression_level) as tar:
            for r in records:
                check_record(r)
                tar.add(r['path'],arcname=r['member'],recursive=False)
            info=tarfile.TarInfo(invname);info.size=len(inv);tar.addfile(info,io.BytesIO(inv))
    expected={r['member']:r for r in records}
    expected[invname]={'bytes':len(inv),'sha256':hashlib.sha256(inv).hexdigest()}
    checked=set()
    with tarfile.open(partial,'r:gz') as tar:
        for member in tar:
            require(member.isfile() and member.name in expected and member.name not in checked,'unexpected/duplicate archive member')
            r=expected[member.name];digest=hashlib.sha256();size=0
            original=io.BytesIO(inv) if member.name==invname else Path(r['path']).open('rb')
            stream=tar.extractfile(member);require(stream is not None,'unreadable archived member')
            with original,stream:
                while True:
                    b=stream.read(BLOCK);original_b=original.read(BLOCK)
                    require(b==original_b,f'archived member not byte-identical to source: {member.name}')
                    if not b:break
                    digest.update(b);size+=len(b)
            require(size==r['bytes'] and digest.hexdigest()==r['sha256'],f'archived member provenance mismatch: {member.name}')
            checked.add(member.name)
    require(checked==set(expected),'archive member coverage incomplete')
    # Publish only after direct decompressed-byte comparisons have all passed.
    os.link(partial,target);partial.unlink()
    receipt={'format':'r1912-semantic-type-archive-v1','status':'passed',
             'finished_at_utc':dt.datetime.now(dt.timezone.utc).isoformat(),
             'original_declarations':COUNT,'raw_identical_declarations':RAW_SAME,
             'raw_different_declarations':RAW_DIFFERENT,'kernel_converted_declarations':KERNEL_COUNT,
             'source_header_checked_declarations':HEADER_COUNT,
             'raw_comparison':raw_record,'semantic_comparison':semantic_record,
             'archive':record(target)|{'verified_members':len(checked)},
             'verification':'All raw comparisons repeated exactly;267 original-Expr kernel conversions and2 exact archived source-header kernel checks bound to original/current captures and code. Every decompressed archive member directly compared byte-for-byte with its source, then size and SHA256 checked.',
             'raw_receipt_modified':False,'semantic_receipt_modified':False,'removed_inputs':[]}
    write_json(args.archive_receipt,receipt)
    if args.remove_archived_inputs:
        bulky={r['path']:r for r in records if r['bulky']}
        # All originals must still match before any removal starts.
        for r in bulky.values():check_record(r)
        for path in bulky:
            Path(path).unlink();receipt['removed_inputs'].append(path);write_json(args.archive_receipt,receipt)
    require(check_record(raw_record)==raw_record and check_record(semantic_record)==semantic_record,'canonical receipts changed during archive')
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--comparison',type=Path,default=V/'r1912-type-comparison.json')
    p.add_argument('--semantic',type=Path,default=Path('external/temporary/r1912-kernel-type-conversion.json'))
    p.add_argument('--raw-comparator',type=Path,default=Path('external/temporary/r1912-raw-compare-types.py'))
    p.add_argument('--decoder',type=Path,default=Path('external/temporary/r1912-decode-expr-repr.py'))
    p.add_argument('--assembler',type=Path,default=Path('external/temporary/r1912-assemble-kernel-type-conversion.py'))
    p.add_argument('--header-generator',type=Path,default=Path('external/temporary/r1912-prepare-kernel-type-checker-v2.py'))
    p.add_argument('--baseline-source-inventory',type=Path,default=A/'baseline-sources.json')
    p.add_argument('--archive',type=Path,required=True)
    p.add_argument('--archive-receipt',type=Path,default=Path('external/temporary/r1912-type-archive.json'))
    p.add_argument('--baseline-aggregate',type=Path)
    p.add_argument('--final-aggregate',type=Path)
    p.add_argument('--compression-level',type=int,choices=range(1,10),default=6)
    p.add_argument('--remove-archived-inputs',action='store_true',help='Explicit opt-in: remove only full-type chunks/optional aggregates after verified archive publication; immutable raw/semantic receipts and all compact evidence remain.')
    p.add_argument('--progress',action='store_true')
    args=p.parse_args()
    require(A.resolve() in args.archive.resolve().parents,f'archive must be inside {A}')
    require(not args.archive.exists(),'refusing to overwrite existing archive')
    require(not args.archive.with_name(args.archive.name+'.partial').exists(),'refusing to overwrite unfinished archive')
    require(not args.archive_receipt.exists(),'refusing to overwrite existing archive receipt')
    require(args.archive_receipt.resolve() not in {args.comparison.resolve(),args.semantic.resolve()},'archive receipt cannot overwrite canonical receipts')
    records,raw,semantic=prepare(args)
    require(str(args.archive_receipt.resolve()) not in {r['path'] for r in records},'archive receipt would overwrite evidence input')
    receipt=archive(args,records,raw,semantic)
    print(json.dumps({'status':receipt['status'],'raw_identical':RAW_SAME,'raw_different':RAW_DIFFERENT,
                      'kernel_converted':KERNEL_COUNT,'source_header_checked':HEADER_COUNT,'archive':receipt['archive'],
                      'archive_receipt':str(args.archive_receipt.resolve()),'removed_inputs':len(receipt['removed_inputs'])},indent=2))


if __name__=='__main__':main()
