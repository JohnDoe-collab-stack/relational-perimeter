"""Generate the French reader guide from the canonical map and SOTA table."""
import json
from collections import Counter
from pathlib import Path

LAB = Path(__file__).resolve().parent

def generate():
    knowledge = json.loads((LAB/'knowledge.json').read_text(encoding='utf-8'))
    sota = json.loads((LAB/'sota.json').read_text(encoding='utf-8'))
    nodes = knowledge['nodes']
    counts = Counter(n['kind'] for n in nodes)
    scoped = knowledge['scope']
    text = [
        '# Carte des fondations relationnelles', '',
        'Document généré depuis `knowledge.json` et `sota.json` ; modifier les données, puis régénérer.', '',
        f"Référence : arbre de travail de `{scoped['branch']}`, basé sur le commit `{scoped['commit']}`, analyse du {scoped['date']}. Les ajouts ne sont pas encore committés.", '',
        f"{counts['theorem']} résultats T2, {counts['deadend']} voies réfutées, {counts['question']} questions suivies et {counts['hunch']} pistes T6. Certaines questions sont désormais résolues dans un périmètre précis. Ces nombres ne mesurent pas la part totale de recherche résolue.", '',
        'Les résultats T2 sont propres au projet. Leur compilation Lean et leur relecture IA sont deux contrôles distincts ; une vérification humaine reste en attente. Les interfaces du plan de reconstruction sont des propositions tant qu’une déclaration précise et sa preuve ne les réalisent pas.', '',
        'Le plan de reconstruction est un fichier local non suivi par Git, consigné par empreinte dans `evidence/source-snapshot.json`. Sa référence historique ne remplace pas une vérification sur la révision courante.', '',
        'Les liens du graphe sont des dépendances sélectionnées et relues. Ils ne sont pas une extraction exhaustive des termes Lean, ni une preuve de nécessité minimale de chaque hypothèse. `supports` exprime un soutien mathématique ; `uses` signale un raccord explicite sélectionné.', '',
        '## Résultats et hypothèses', '',
    ]
    for n in nodes:
        if n['kind'] != 'theorem':
            continue
        text += [f"### {n['title']}", '', f"`{n['id']}` · {n['tier']} · {n['review']['state']}", '',
                 n['statement'], '', '**Hypothèses.** '+n['hypotheses'], '',
                 '**Preuve consommée.** '+n['consumed'], '']
        if n.get('note'):
            text += ['**Portée.** '+n['note'], '']
        text += ['**Déclarations.**', '']
        for r in n['lean_refs']:
            text += [f"- `{r['declaration']}` — [{r['file']}:{r['line']}](../{r['file']})."]
        text += ['', '**Relecture.** '+n['review']['verdict'], '']
    text += ['## Voies réfutées et leçons', '']
    for n in nodes:
        if n['kind'] == 'deadend':
            text += [f"### {n['title']}", '', n['statement'], '', '**Leçon.** '+n['lesson'], '']
    text += ['## Portes de recherche', '']
    for n in nodes:
        if n['kind'] == 'question':
            text += [f"### {n['title']}", '', f"`{n['id']}` · {n['status']}", '', n['statement'], '',
                     '**Test proposé.** '+n.get('test',n.get('next','')), '']
    text += ['## Pistes T6 — spéculation explicite', '']
    for n in nodes:
        if n['kind'] == 'hunch':
            text += [f"### {n['title']}", '', n['statement'], '', '**Test.** '+n['test'], '']
    text += ['## État des questions suivi', '', '| Question | Statut |', '|---|---|']
    for row in sota['entries']:
        text += ['| '+row['cls'].replace('|','\\|')+' | '+row['status'].replace('|','\\|')+' |']
    text += ['', '## Première prochaine exploration', '',
             'Les lots 1 à 4 sont achevés dans leurs signatures : frontière avant choix, génération relative, transports complets et grammaire relative des rôles équipés. Les prochaines questions portent sur la rigidité, la minimalité universelle, les accords entre formations arbitraires et le transport des pôles et de l’obstruction. La livraison Git conserve les sources figées dans le snapshot relu ; une nouvelle source exige une nouvelle revue.', '',
             'Aucun atlas taille × invariant n’est défini pour ce chantier architectural. `frontier.json` reste absent plutôt que de produire une fraction artificielle de questions résolues.', '']
    (LAB/'FONDATIONS.fr.md').write_text('\n'.join(text),encoding='utf-8')
    print('Generated labyrinth/FONDATIONS.fr.md from canonical data.')

if __name__ == '__main__':
    generate()
