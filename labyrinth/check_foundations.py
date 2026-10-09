"""Check map provenance and anchors; this is not a mathematical proof checker."""
import json
import re
from pathlib import Path
from snapshot import snapshot, validate_revision

ROOT = Path(__file__).resolve().parent.parent
LAB = ROOT / 'labyrinth'

def check():
    knowledge = json.loads((LAB / 'knowledge.json').read_text(encoding='utf-8'))
    baseline = json.loads((ROOT / knowledge['scope']['source_snapshot']).read_text(encoding='utf-8'))
    current = snapshot()
    if (knowledge['scope']['commit'], knowledge['scope']['branch']) != (baseline['commit'], baseline['branch']):
        raise ValueError('The map must describe the reviewed snapshot base and branch.')
    if knowledge['scope'].get('revision_mode') != baseline.get('revision_mode'):
        raise ValueError('Publication revision mode differs from the reviewed snapshot.')
    validate_revision(baseline, current)
    if {f['path']: f['sha256'] for f in baseline['files']} != {f['path']: f['sha256'] for f in current['files']}:
        raise ValueError('A mapped source changed since the reference snapshot.')
    ids = [n['id'] for n in knowledge['nodes']]
    if len(ids) != len(set(ids)):
        raise ValueError('Duplicate node IDs.')
    anchored = 0
    for n in knowledge['nodes']:
        for r in n.get('lean_refs', []):
            text = (ROOT / r['file']).read_text(encoding='utf-8-sig')
            lines = text.splitlines()
            if not lines[r['line']-1].startswith(r['anchor']):
                raise ValueError(f"Stale line anchor: {n['id']}: {r}")
            if r['declaration'] not in re.findall(r'^#print axioms (\S+)', text, re.M):
                raise ValueError(f"Unaudited declaration: {r['declaration']}")
            anchored += 1
        for evidence in n.get('evidence', []):
            if not evidence.startswith(('http:', 'https:')) and not (ROOT / evidence).exists():
                raise ValueError(f"Missing evidence: {n['id']}: {evidence}")
        review = n.get('review', {})
        if n['kind'] == 'theorem' and (n.get('tier') != 'T2' or not n.get('lean_refs') or not review):
            raise ValueError(f"Formal result without evidence/review contract: {n['id']}")
        for reviewer in review.get('by', []):
            if not (ROOT / reviewer / 'report.md').exists():
                raise ValueError(f'Missing referee report: {reviewer}')
    sota = json.loads((LAB / 'sota.json').read_text(encoding='utf-8'))
    mapped = {n['id']: n for n in knowledge['nodes']}
    for row in sota['entries']:
        if row['result'] != mapped[row['id']]['statement']:
            raise ValueError(f"SOTA statement drift: {row['id']}")
    print(f'Provenance OK: {len(ids)} unique nodes, {anchored} audited declaration anchors, {len(baseline["files"])} unchanged sources.')
    print('This validates provenance and metadata, not proof semantics or scientific adequacy.')

if __name__ == '__main__':
    check()
