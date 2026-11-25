#!/usr/bin/env python3
"""Search actual extracted/reference theorem statements without loading full proof files."""
import argparse
import json
from pathlib import Path
import re


def records(skill):
    shared = skill / 'assets/shared-semantics'
    for module in json.loads((shared / 'manifest.json').read_text())['modules']:
        for item in module['declarations']:
            if item['kind'] in {'Lemma', 'Theorem', 'Corollary'}:
                yield {'bundle': 'shared', 'name': module['module'] + '.' + item['name'],
                       'statement': item['declaration'], 'file': str(shared / module['asset']),
                       'source': module['source_relative'], 'line': item['line'],
                       'reuse': 'shipped exact-copy proof; instantiate stated premises'}
    reference = skill / 'assets/same-reference'
    texts = {}
    for item in json.loads((reference / 'provenance.json').read_text())['declarations']:
        if item['kind'] not in {'Lemma', 'Theorem', 'Corollary'}:
            continue
        module = item['output_module']
        file = reference / 'coq' / (module + '.v')
        if module not in texts:
            texts[module] = file.read_text()
        src = texts[module]
        match = re.search(r'(?m)^[ \t]*' + item['kind'] + r'\s+' + re.escape(item['declaration']) + r'\b', src)
        if match is None:
            raise ValueError('Missing extracted declaration: ' + item['declaration'])
        proof = src.find('Proof.', match.end())
        if proof < 0:
            raise ValueError('Missing proof boundary: ' + item['declaration'])
        yield {'bundle': 'reference', 'name': module + '.' + item['declaration'],
               'statement': src[match.start():proof].strip(), 'file': str(file),
               'source': item['source'], 'line': item['line'],
               'reuse': 'shipped isolated reference proof; instantiate stated premises'}
    catalog = skill / 'references/reference-theorem-catalog.json'
    for module in json.loads(catalog.read_text())['modules']:
        for item in module['declarations']:
            yield {'bundle': 'history', 'name': module['module'] + '.' + item['name'],
                   'statement': item['statement'], 'source': module['source'],
                   'line': item['line'], 'family': module['family'],
                   'reuse': 'source inventory only; prove reference embedding and reconnect combined-model wrappers'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('terms', nargs='+', help='Case-insensitive terms; every term must match')
    ap.add_argument('--bundle', choices=['all', 'reference', 'shared', 'history'], default='all')
    ap.add_argument('--limit', type=int, default=8)
    ap.add_argument('--max-statement', type=int, default=1800)
    args = ap.parse_args()
    if args.limit < 1 or args.max_statement < 1:
        ap.error('limit and max-statement must be positive')
    terms = [term.casefold() for term in args.terms]
    selected = []
    for item in records(Path(__file__).resolve().parents[1]):
        if args.bundle != 'all' and item['bundle'] != args.bundle:
            continue
        corpus = (item['name'] + ' ' + item['statement'] + ' ' + item.get('family', '')).casefold()
        if all(term in corpus for term in terms):
            score = sum(10 if term in item['name'].casefold() else 1 for term in terms)
            selected.append((score, item))
    selected.sort(key=lambda pair: (-pair[0], pair[1]['name']))
    result = []
    for _, item in selected[:args.limit]:
        statement = item['statement']
        item['statement_truncated'] = len(statement) > args.max_statement
        item['statement'] = statement[:args.max_statement]
        result.append(item)
    print(json.dumps({'matches': len(selected), 'shown': len(result), 'lemmas': result}, indent=2))


if __name__ == '__main__':
    main()
