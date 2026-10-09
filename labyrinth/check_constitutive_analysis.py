"""Check coverage and provenance of the constitutive rereading, not its semantics.

The formal source snapshot and proof reviews remain independent. A new analysis
snapshot covers this interpretation and its reports; it never replaces Lean's
evidence or promotes a result's tier.
"""
import argparse
import json
from datetime import datetime, timezone
from pathlib import Path

from snapshot import HASH_MODE, REVISION_MODE, git, source_hash, validate_revision

ROOT = Path(__file__).resolve().parent.parent
LAB = ROOT / 'labyrinth'
SNAPSHOT = LAB / 'evidence/relations-first-analysis-snapshot.json'
BASELINE = LAB / 'evidence/iterations/roles-lot4-published-bf13840/knowledge.json'
AUTHOR = 'research/agents/relations-first-analysis'
REFEREE = 'research/agents/referee-relations-first'
FIELDS = ('received', 'constructed', 'readout', 'scope', 'correction')
FILES = (
    'labyrinth/knowledge.json', 'labyrinth/sota.json', 'labyrinth/STYLE.fr.md',
    'labyrinth/README.md', 'labyrinth/render_foundations.py',
    'labyrinth/dashboard/template.html', 'labyrinth/check_constitutive_analysis.py',
    'docs/priorite-relationnelle-et-perimetre-interieur.fr.md',
    AUTHOR + '/assessment.json', AUTHOR + '/report.md',
    AUTHOR + '/author-phase2-corrections.md',
    REFEREE + '/report.md', REFEREE + '/phase2-report.md', REFEREE + '/final-acceptance.md',
    'labyrinth/evidence/iterations/roles-lot4-published-bf13840/knowledge.json',
    'labyrinth/evidence/iterations/roles-lot4-published-bf13840/sota.json',
)


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def check_metadata(require_review=True):
    knowledge = read_json(LAB / 'knowledge.json')
    baseline = read_json(BASELINE)
    old = {n['id']: n for n in baseline['nodes']}
    nodes = {n['id']: n for n in knowledge['nodes']}
    if len(nodes) != len(knowledge['nodes']) or set(nodes) != set(old):
        raise ValueError('The rereading must cover each original node exactly once.')
    analysis = knowledge['analysis_scope']
    validate_revision({**analysis, 'hash_mode': HASH_MODE, 'revision_mode': REVISION_MODE},
                      {'branch': git('branch', '--show-current'),
                       'commit': git('rev-parse', 'HEAD'), 'hash_mode': HASH_MODE})
    if analysis['referee'] == analysis['author'] or analysis['referee'] != REFEREE:
        raise ValueError('Author and independent referee must remain distinct.')
    if require_review and analysis['review_state'] != 'refereed':
        raise ValueError('Constitutive rereading is not yet independently accepted.')
    for node_id, node in nodes.items():
        if node['kind'] != old[node_id]['kind']:
            raise ValueError('A node changed kind during the rereading: ' + node_id)
        constitution = node.get('constitution', {})
        if any(not isinstance(constitution.get(f), str) or not constitution[f].strip()
               for f in FIELDS):
            raise ValueError('Incomplete constitutive assessment: ' + node_id)
        if old[node_id]['kind'] == 'theorem':
            for key in ('kind', 'tier', 'status', 'statement', 'lean_refs', 'review'):
                if node[key] != old[node_id][key]:
                    raise ValueError('Formal claim/review changed without a new proof review: '
                                     + node_id + ':' + key)
        review = node.get('constitutive_review', {})
        if review.get('human_check') != 'pending':
            raise ValueError('Human review must not be inferred from AI review: ' + node_id)
        if require_review and (review.get('state') != 'refereed'
                               or review.get('by') != [REFEREE]):
            raise ValueError('Missing independent constitutive review: ' + node_id)
        for evidence in review.get('evidence', []):
            if not (ROOT / evidence).is_file():
                raise ValueError('Missing constitutive evidence: ' + evidence)
    sota = read_json(LAB / 'sota.json')
    old_sota = read_json(BASELINE.with_name('sota.json'))
    row_ids = [r['id'] for r in sota['entries']]
    if len(row_ids) != len(set(row_ids)) or set(row_ids) != {r['id'] for r in old_sota['entries']}:
        raise ValueError('SOTA results changed during a document-only rereading.')
    if sota['entries'][0]['id'] != 'th.perimeter-exact':
        raise ValueError('The interior constitution must lead the new reading.')
    for row in sota['entries']:
        if row['result'] != nodes[row['id']]['statement']:
            raise ValueError('SOTA claim drift: ' + row['id'])
    print(f'Constitutive coverage OK: {len(nodes)} original nodes; '
          '58 formal claims and their proof reviews preserved.')
    print('This validates coverage/provenance; semantic acceptance is in the independent reports.')
    return analysis


def current_snapshot(analysis):
    return {
        'branch': git('branch', '--show-current'),
        'commit': analysis['commit'],
        'date': datetime.now(timezone.utc).isoformat(),
        'hash_mode': HASH_MODE, 'revision_mode': REVISION_MODE,
        'scope': 'Constitutive rereading only; the formal 47-source snapshot remains separate.',
        'files': [{'path': name, 'sha256': source_hash((ROOT / name).read_bytes())}
                  for name in FILES],
    }


def verify_snapshot(analysis):
    saved = read_json(SNAPSHOT)
    actual = current_snapshot(analysis)
    validate_revision(saved, {**actual, 'commit': git('rev-parse', 'HEAD')})
    if (saved['commit'], saved['branch']) != (analysis['commit'], analysis['branch']):
        raise ValueError('Analysis provenance differs from its snapshot.')
    if {f['path']: f['sha256'] for f in saved['files']} != {
            f['path']: f['sha256'] for f in actual['files']}:
        raise ValueError('An analysis input changed: obtain a renewed constitutive review.')
    print(f'Analysis snapshot verified: {len(FILES)} unchanged inputs.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument('--draft', action='store_true', help='Check coverage before acceptance.')
    action.add_argument('--record', action='store_true', help='Freeze accepted analysis once.')
    args = parser.parse_args()
    analysis = check_metadata(require_review=not args.draft)
    if args.record:
        data = current_snapshot(analysis)
        validate_revision(data, {**data, 'commit': git('rev-parse', 'HEAD')})
        # Refuse overwrite: archive and obtain a new review for a later revision.
        with SNAPSHOT.open('x', encoding='utf-8') as handle:
            handle.write(json.dumps(data, ensure_ascii=False, indent=2) + '\n')
        print('Accepted analysis inputs frozen separately from mathematical sources.')
    elif not args.draft:
        verify_snapshot(analysis)


if __name__ == '__main__':
    main()
