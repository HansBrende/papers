#!/usr/bin/env python3
"""Decode the 269 unequal Lean Expr repr strings without normalization.

Only constructor syntax is accepted. Input strings, names, universe levels,
binder names/info, let nondep flags and literal values are preserved. The JSON
AST is a transport representation, NOT evidence of definitional equality:
Lean must reconstruct each Expr and verify `reprStr e == baselineRepr` before
performing a kernel conversion check. No Lean processes are invoked here.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

P = Path('/Users/hansbrende/Documents/Codex/papers/Local-coding-barriers-and-the-limits-of-tape-geometry-for-matrix-transposition')


def strict_object(pairs):
    d = {}
    for k,v in pairs:
        if k in d: raise ValueError(f'duplicate key {k!r}')
        d[k] = v
    return d


def load(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=strict_object)


def sha_bytes(value):
    return hashlib.sha256(value).hexdigest()


class Parser:
    def __init__(self, source):
        self.source = source
        self.pos = 0
        self.counts = Counter()
        self.depth = self.max_depth = 0

    def fail(self, message):
        raise ValueError(f'{message} at character {self.pos}: {self.source[max(0,self.pos-30):self.pos+100]!r}')

    def ws(self):
        while self.pos < len(self.source) and self.source[self.pos].isspace(): self.pos += 1

    def literal(self, expected):
        self.ws()
        if not self.source.startswith(expected, self.pos): self.fail(f'expected {expected!r}')
        self.pos += len(expected)

    def word(self):
        self.ws()
        start = self.pos
        while self.pos < len(self.source) and (self.source[self.pos].isalnum() or self.source[self.pos] in '._'):
            self.pos += 1
        if start == self.pos: self.fail('expected constructor/boolean')
        return self.source[start:self.pos]

    def nat(self):
        self.ws()
        start = self.pos
        while self.pos < len(self.source) and '0' <= self.source[self.pos] <= '9': self.pos += 1
        if self.pos == start: self.fail('expected natural number')
        return int(self.source[start:self.pos])

    def boolean(self):
        word = self.word()
        if word not in ('true','false'): self.fail('expected true or false')
        return word == 'true'

    def string(self):
        self.literal('"')
        chars = []
        while self.pos < len(self.source):
            c = self.source[self.pos]; self.pos += 1
            if c == '"': return ''.join(chars)
            if c != '\\': chars.append(c); continue
            if self.pos >= len(self.source): self.fail('unterminated escape')
            escape = self.source[self.pos]; self.pos += 1
            escapes = {'n':'\n','t':'\t','\\':'\\','"':'"'}
            if escape in escapes: chars.append(escapes[escape])
            elif escape == 'x':
                digits = self.source[self.pos:self.pos+2]
                if len(digits) != 2 or not re.fullmatch('[0-9a-fA-F]{2}', digits): self.fail('expected two hex digits')
                chars.append(chr(int(digits,16))); self.pos += 2
            else: self.fail(f'unsupported Lean repr string escape {escape!r}')
        self.fail('unterminated string')

    def quoted_name(self):
        self.literal('`')
        parts = []
        while True:
            if self.pos >= len(self.source): self.fail('empty name component')
            if self.source[self.pos] == '«':
                self.pos += 1; start = self.pos
                while self.pos < len(self.source) and self.source[self.pos] != '»': self.pos += 1
                if self.pos == len(self.source): self.fail('unterminated escaped name component')
                parts.append(self.source[start:self.pos]); self.pos += 1
            else:
                start = self.pos
                while self.pos < len(self.source):
                    c = self.source[self.pos]
                    if c.isspace() or c in '.()[],': break
                    if c in '`«»"': self.fail('unexpected name delimiter')
                    self.pos += 1
                if start == self.pos: self.fail('empty unescaped name component')
                parts.append(self.source[start:self.pos])
            if self.pos < len(self.source) and self.source[self.pos] == '.': self.pos += 1
            else: break
        name = ['anonymous']
        for part in parts: name = ['str',name,part]
        return name

    def parens(self, method):
        self.ws(); parenthesized = self.source.startswith('(',self.pos)
        if parenthesized: self.pos += 1
        self.depth += 1; self.max_depth = max(self.max_depth,self.depth)
        result = method()
        self.depth -= 1
        if parenthesized: self.literal(')')
        return result

    def name(self):
        return self.parens(self.name_inner)

    def name_inner(self):
        self.ws()
        if self.source.startswith('`',self.pos): return self.quoted_name()
        word = self.word(); self.counts[word] += 1
        if word == 'Lean.Name.anonymous': return ['anonymous']
        if word == 'Lean.Name.mkStr': return ['str',self.name(),self.string()]
        if word == 'Lean.Name.mkNum': return ['num',self.name(),self.nat()]
        self.fail(f'unknown Name constructor {word!r}')

    def level(self):
        return self.parens(self.level_inner)

    def level_inner(self):
        word = self.word(); self.counts[word] += 1
        if word == 'Lean.Level.zero': return ['zero']
        if word == 'Lean.Level.succ': return ['succ',self.level()]
        if word in ('Lean.Level.max','Lean.Level.imax'): return [word.rsplit('.',1)[1],self.level(),self.level()]
        if word in ('Lean.Level.param','Lean.Level.mvar'): return [word.rsplit('.',1)[1],self.name()]
        self.fail(f'unknown Level constructor {word!r}')

    def levels(self):
        self.literal('['); items = []; self.ws()
        if self.source.startswith(']',self.pos): self.pos += 1; return items
        while True:
            items.append(self.level()); self.ws()
            if self.source.startswith(']',self.pos): self.pos += 1; return items
            self.literal(',')

    def binder(self):
        return self.parens(self.binder_inner)

    def binder_inner(self):
        word = self.word(); self.counts[word] += 1
        if word.startswith('Lean.BinderInfo.'):
            value = word.rsplit('.',1)[1]
            if value in ('default','implicit','strictImplicit','instImplicit'): return value
        self.fail(f'unknown BinderInfo constructor {word!r}')

    def lit(self):
        return self.parens(self.lit_inner)

    def lit_inner(self):
        word = self.word(); self.counts[word] += 1
        if word == 'Lean.Literal.natVal': return ['natVal',self.nat()]
        if word == 'Lean.Literal.strVal': return ['strVal',self.string()]
        self.fail(f'unknown Literal constructor {word!r}')

    def expr(self):
        return self.parens(self.expr_inner)

    def expr_inner(self):
        word = self.word(); self.counts[word] += 1
        if not word.startswith('Lean.Expr.'): self.fail(f'expected Expr constructor, got {word!r}')
        tag = word.rsplit('.',1)[1]
        if tag == 'bvar': return [tag,self.nat()]
        if tag in ('fvar','mvar'): return [tag,self.name()]
        if tag == 'sort': return [tag,self.level()]
        if tag == 'const': return [tag,self.name(),self.levels()]
        if tag == 'app': return [tag,self.expr(),self.expr()]
        if tag in ('lam','forallE'): return [tag,self.name(),self.expr(),self.expr(),self.binder()]
        if tag == 'letE': return [tag,self.name(),self.expr(),self.expr(),self.expr(),self.boolean()]
        if tag == 'lit': return [tag,self.lit()]
        if tag == 'proj': return [tag,self.name(),self.nat(),self.expr()]
        # MData intentionally unsupported: fail instead of silently dropping it.
        self.fail(f'unsupported Expr constructor {word!r}')

    def all_expr(self):
        e = self.expr(); self.ws()
        if self.pos != len(self.source): self.fail('unconsumed suffix')
        return e


def flat_name(text):
    p = Parser('`'+text)
    n = p.name(); p.ws()
    if p.pos != len(p.source): p.fail('unconsumed flat name suffix')
    return n


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--comparison',type=Path,default=P/'verification/r1912-type-comparison.json')
    p.add_argument('--baseline-pattern',default='/private/tmp/r1912-baseline-types-{index:03d}.json')
    p.add_argument('--final-pattern',default='/private/tmp/r1912-final-types-{index:03d}.json')
    p.add_argument('--output',type=Path,default=Path('/private/tmp/r1912-original-types-ast.json'))
    p.add_argument('--chunk-dir',type=Path,default=Path('/private/tmp/r1912-original-types-ast-chunks'))
    args=p.parse_args()
    comparison=load(args.comparison)
    names=[m['name'] for m in comparison['mismatches']]
    if len(names)!=269 or len(set(names))!=269: raise ValueError('expected exactly 269 distinct mismatches')
    baseline_receipts={r['index']:r for r in comparison['input_chunks'] if r['side']=='baseline'}
    final_receipts={r['index']:r for r in comparison['input_chunks'] if r['side']=='final'}
    if set(baseline_receipts)!=set(range(79)) or set(final_receipts)!=set(range(79)):
        raise ValueError('missing baseline/final chunk provenance')
    pending=set(names); records={}; counts=Counter(); max_depth=0; inputs=[]
    for index in range(79):
        path=Path(args.baseline_pattern.format(index=index)); raw=path.read_bytes()
        receipt=baseline_receipts[index]
        if len(raw)!=receipt['bytes'] or sha_bytes(raw)!=receipt['sha256']:
            raise ValueError(f'baseline chunk {index} differs from exact-comparison provenance')
        values=json.loads(raw,object_pairs_hook=strict_object)
        selected=pending.intersection(values)
        if not selected: continue
        inputs.append({'side':'baseline','index':index,'path':str(path),'sha256':sha_bytes(raw),'bytes':len(raw)})
        final_path=Path(args.final_pattern.format(index=index)); final_raw=final_path.read_bytes()
        receipt=final_receipts[index]
        if len(final_raw)!=receipt['bytes'] or sha_bytes(final_raw)!=receipt['sha256']:
            raise ValueError(f'final chunk {index} differs from exact-comparison provenance')
        final_values=json.loads(final_raw,object_pairs_hook=strict_object)
        inputs.append({'side':'final','index':index,'path':str(final_path),'sha256':sha_bytes(final_raw),'bytes':len(final_raw)})
        for name in selected:
            old=values[name]
            current=final_values[name]
            if set(old)!={'type','levelParams'}: raise ValueError(f'unexpected fields: {name}')
            if set(current)!={'type','levelParams'}: raise ValueError(f'unexpected final fields: {name}')
            parser=Parser(old['type']); ast=parser.all_expr()
            counts.update(parser.counts); max_depth=max(max_depth,parser.max_depth)
            records[name]={'name':name,'nameAST':flat_name(name),
                           'levelParams':old['levelParams'],
                           'levelParamsAST':[flat_name(s) for s in old['levelParams']],
                           'baselineRepr':old['type'],'baselineReprSHA256':sha_bytes(old['type'].encode()),
                           'baselineTypeAST':ast,'baselineChunk':index,
                           'currentRepr':current['type'],'currentReprSHA256':sha_bytes(current['type'].encode()),
                           'currentLevelParams':current['levelParams'],'currentChunk':index}
        pending-=selected
    if pending: raise ValueError(f'missing originals: {sorted(pending)}')
    doc={'format':'r1912-preserved-expr-ast-v1','expectedDeclarations':269,
         'warning':'AST transport only. Require Lean reprStr roundtrip equality before kernel checking. No normalization performed.',
         'comparisonPath':str(args.comparison),'comparisonSHA256':sha_bytes(args.comparison.read_bytes()),
         'decoderPath':str(Path(__file__).resolve()),'decoderSHA256':sha_bytes(Path(__file__).read_bytes()),
         'inputChunks':inputs,'maxParserRecursionDepth':max_depth,'constructorCounts':dict(counts),
         'declarations':[records[n] for n in names]}
    args.output.write_text(json.dumps(doc,ensure_ascii=False,separators=(',',':'))+'\n')
    args.chunk_dir.mkdir(parents=True,exist_ok=True)
    chunk_inventory=[]
    for index,start in enumerate(range(0,len(names),8)):
        declarations=doc['declarations'][start:start+8]
        path=args.chunk_dir/f'{index:03d}.json'
        chunk={'format':doc['format'],'expectedDeclarations':len(declarations),
               'comparisonSHA256':doc['comparisonSHA256'],'decoderSHA256':doc['decoderSHA256'],
               'declarations':declarations}
        raw=(json.dumps(chunk,ensure_ascii=False,separators=(',',':'))+'\n').encode()
        path.write_bytes(raw)
        chunk_inventory.append({'index':index,'path':str(path),'bytes':len(raw),'sha256':sha_bytes(raw),
                                'declarations':[r['name'] for r in declarations]})
    inventory={'format':'r1912-preserved-expr-ast-chunks-v1','declarations':269,
               'source':str(args.output),'sourceSHA256':sha_bytes(args.output.read_bytes()),
               'chunks':chunk_inventory}
    inventory_path=args.chunk_dir/'inventory.json'
    inventory_path.write_text(json.dumps(inventory,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'output':str(args.output),'bytes':args.output.stat().st_size,
                      'declarations':len(records),'maxParserRecursionDepth':max_depth,
                      'chunkInventory':str(inventory_path),'chunks':len(chunk_inventory),
                      'constructorCounts':dict(counts)},indent=2))


if __name__=='__main__': main()
