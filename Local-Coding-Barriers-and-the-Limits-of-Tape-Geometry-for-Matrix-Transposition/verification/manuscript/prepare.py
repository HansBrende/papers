#!/usr/bin/env python3
"""Generate the declaration inventory, paper axiom audit and printed index.

The input is the manuscript's explicit formal/upformal annotations. This tool
does not infer that the English statement matches Lean; that is a separate
source review. It refuses missing modules or unannotated numbered results.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'paper'
OUT = ROOT / 'verification/manuscript'
UPSTREAM = ROOT.parent / 'Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean'
FORMAL = re.compile(r'\\(formal|upformal)\{([^{}]+)\}\{([^{}]+)\}')
NUMBERED = re.compile(r'\\begin\{(theorem|lemma|corollary|proposition|definition)\}(?:\[([^\]]*)\])?')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    # Follow actual input order; generated appendices and macros are outputs or
    # formatting, not mathematical input to the inventory.
    main = (PAPER / 'main.tex').read_text()
    for relative in re.findall(r'\\input\{(sections/[^{}]+)\}', main):
        path = PAPER / (relative + '.tex')
        if not path.is_file():
            raise SystemExit(f'Missing manuscript section: {path}')
        yield path


def tex_string(value):
    # Inputs are trusted labels/titles already in TeX; paths/names use nolinkurl.
    return value.replace('&', r'\&').replace('%', r'\%')


def main():
    annotations, items, inventory = [], [], {}
    for source in sources():
        content = source.read_text()
        inventory[str(source.relative_to(ROOT))] = sha(source)
        matches = list(FORMAL.finditer(content))
        for match in matches:
            kind, module, names = match.groups()
            module = module.strip()
            names = [name.strip() for name in names.split(',') if name.strip()]
            if not names or any(not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.\u2080-\u2089\u208a-\u208e]*', n) for n in names):
                raise SystemExit(f'Invalid declaration annotation: {match.group(0)}')
            qualified = 'TransposeFollowup.' + module if kind == 'formal' else module
            relative = Path(*qualified.split('.')).with_suffix('.lean')
            location = (ROOT / 'lean' / relative) if kind == 'formal' else (UPSTREAM / relative)
            if not location.is_file():
                raise SystemExit(f'Annotation module does not exist: {location}')
            annotations.append({
                'kind': kind, 'module': qualified, 'declarations': names,
                'manuscript': str(source.relative_to(ROOT)),
                'line': content.count('\n', 0, match.start()) + 1,
                'source': str(location.relative_to(ROOT)) if kind == 'formal' else '../' + str(location.relative_to(ROOT.parent)),
                'source_sha256': sha(location),
            })
        numbered = list(NUMBERED.finditer(content))
        for i, match in enumerate(numbered):
            end = numbered[i+1].start() if i+1 < len(numbered) else len(content)
            body = content[match.start():end]
            label = re.search(r'\\label\{([^{}]+)\}', body)
            links = list(FORMAL.finditer(body))
            if label is None or not links:
                raise SystemExit(f'Unmapped numbered result at {source}:{content.count(chr(10),0,match.start())+1}')
            # The first annotation is the primary public endpoint. All further
            # annotations remain fully represented in declarations.json.
            link = links[0]
            module = ('TransposeFollowup.' if link.group(1) == 'formal' else '') + link.group(2)
            items.append({'label': label.group(1), 'kind': match.group(1), 'title': match.group(2) or '',
                          'module': module, 'declarations': [x.strip() for x in link.group(3).split(',')],
                          'manuscript': str(source.relative_to(ROOT)),
                          'line': content.count('\n', 0, match.start())+1})
    names = sorted({n for a in annotations for n in a['declarations']})
    modules = sorted({a['module'] for a in annotations})
    (OUT / 'declarations.json').write_text(json.dumps({'sources': inventory, 'annotations': annotations,
                                                     'numbered_results': items,
                                                     'unique_declarations': names, 'modules': modules}, indent=2)+'\n')
    audit = ['-- Generated from paper formal/upformal annotations; do not edit by hand.']
    audit += [f'import {module}' for module in modules]
    audit += [''] + [f'#print axioms {name}' for name in names]
    (ROOT / 'lean/PaperAxioms.lean').write_text('\n'.join(audit)+'\n')
    extension = json.loads((OUT / 'packet-strengthening/source-extension.json').read_text())
    packet_modules = sorted(Path(path).with_suffix('').relative_to('lean').as_posix().replace('/', '.')
                            for path in extension['files'])
    packet_audit = ['-- Generated audit of every declaration in the additive packet modules.',
                    '-- This is verification tooling, not a mathematical axiom or proof source.',
                    'import Lean', *['import ' + module for module in packet_modules], '',
                    'open Lean Elab Command', '', 'set_option maxHeartbeats 0 in',
                    'run_cmd do',
                    '  let env ← getEnv',
                    '  let modules : Array Name := #[' + ', '.join('`' + m for m in packet_modules) + ']',
                    '  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]',
                    '  let mut count : Nat := 0',
                    '  let mut actual : Array Name := #[]',
                    '  for (name, _) in env.constants.toList do',
                    '    if let some idx := env.getModuleIdxFor? name then',
                    '      if modules.contains env.header.moduleNames[idx]! then',
                    '        let axioms ← collectAxioms name',
                    '        for ax in axioms do',
                    '          unless allowed.contains ax do',
                    '            throwError "Forbidden axiom {ax} in {name}"',
                    '          if !actual.contains ax then actual := actual.push ax',
                    '        count := count + 1',
                    '  if count == 0 then throwError "Empty packet declaration audit"',
                    '  logInfo m!"Packet declaration audit: {count} declarations; axioms {actual}"']
    (ROOT / 'lean/PacketAxioms.lean').write_text('\n'.join(packet_audit)+'\n')
    lines = [r'\section{Declaration and dependency index}\label{app:index}',
             'The primary endpoints of every numbered result are listed below. The',
             r'complete inventory, including definitions and imported results cited in the',
             r'text, is generated as \lean{verification/manuscript/declarations.json}.',
             'It records source modules, manuscript locations and source hashes. All',
             r'names in that inventory are checked by \lean{lean/PaperAxioms.lean}.',
             r'\begin{description}[style=nextline,leftmargin=1em,labelindent=0pt,labelwidth=0pt]']
    for item in items:
        lines += [r'\item[\Cref{' + item['label'] + '}. ' + item['title'] + ']',
                  r'{\small\nolinkurl{' + item['module'] + '}',
                  *[r'\par\noindent\nolinkurl{' + n + '}' for n in item['declarations']], '}']
    lines += [r'\end{description}', r'\paragraph{Dependency structure.}',
              r'The original model and $M^*$ theorem feed the native motion and approximation',
              r'obstructions, which feed the scan-palette and recursion exclusions. The',
              r'finite original-row, two-coordinate packet and two-stage interfaces support the',
              r'three local-coding families independently of the analytic padding chain.',
              r'For padding, rational expansion feeds finite overlap graphs and their',
              r'paid excursion implementation; cleanup and payload composition preserve',
              r'the computation, and the original cut-to-limit theorem supplies the',
              r'full $M^*$ conclusion. These are logical dependencies; the manuscript',
              r'order is chosen for exposition rather than to reproduce the import graph.']
    (PAPER / 'generated/theorem-index.tex').write_text('\n'.join(lines)+'\n')
    print(json.dumps({'numbered_results': len(items), 'declarations': len(names), 'modules': len(modules)}))


if __name__ == '__main__':
    main()
