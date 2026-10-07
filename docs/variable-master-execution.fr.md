# Décomposition variable dans l'exécution maître

Le calcul peut maintenant conserver une ou deux branches selon les contextes
constitués qu'il reçoit. La partition n'est pas un paramètre du nouveau chemin.
Il s'agit d'une extension de l'exécuteur maître, pas d'une substitution au
résultat audité de largeur un ni au théorème binaire sur `carry`.

## Chaîne effective

`VariableMasterExecution` utilise les producteurs de ressources existants :

1. `masterHead` matérialise les quatre producteurs maître existants dans
   l'ordre : découverte, application, décomposition, assemblage. Les supports
   produits sont partagés par les lectures et la continuation du curseur.
2. L'ouverture lit la variable découverte de cette tête et les contextes SAT
   engendrés reçus. La fraîcheur est vérifiée ; une variable déjà décidée ne
   crée pas de fausse nouvelle formation.
3. Le chercheur de relations d'inversion examine la frontière ouverte. Chaque
   absorption utilise une action totale et une preuve séparée de préservation
   de SAT. Une recherche non résolue conserve les branches concernées.
4. La frontière réellement retenue devient l'entrée du prochain pas. Le
   curseur suivant provient du même support maître, sans réexécuter sa tête.

Les références typées distinguent le curseur, la frontière reçue, la tête
produite, l'ouverture et sa réduction. `History` indexe sa suite par le curseur
et la frontière effectivement produits. Aucune queue future n'entre dans la
construction de la tête.

`step` matérialise ses cinq producteurs dans le même corps, puis lit leurs
sorties partagées. `scripts/check-variable-master-codegen.py`, intégré aux deux
vérificateurs, contrôle dans le C généré les applications de la tête maître,
de sa découverte, de l'ouverture et du normaliseur. Il rejette la reconstruction
du support par les anciens auxiliaires sur ce chemin. Ce contrôle porte sur
ces applications nommées, pas sur un coût total ou une taille du tas.

`execute_erases` prouve, pour tout nombre de pas, que l'effacement est
exactement `MasterResources.execute`. `execute_viable_iff` compose les
transports de préservation de SAT de toute la chaîne. L'extension ne modifie
aucune des quatre fondations.

## Variation construite

`VariableMasterInstance` fixe le même maître public initial, la formule
`x10 ∨ x1 ∨ x2`, la même variable sélectionnée `x10` et le même critère SAT.
Les deux parents ont la même profondeur ; leur histoire a fixé `x1` à vrai ou
à faux. Les quatre enfants possèdent chacun une continuation acceptée.

- Après `x1 = vrai`, l'inversion recherchée est reconstruite et la largeur
  retenue vaut un.
- Après `x1 = faux`, ce chercheur ne trouve aucune relation entre les deux
  enfants et la largeur retenue vaut deux.

Ces largeurs sont démontrées sur `step`, donc sur les sorties des producteurs,
et non sur une liste choisie comme réponse attendue. La variable est prouvée
égale à celle du rôle exécuté. Il n'y a ni masque de regroupement ni mode fourni.
Le scénario ne prétend pas que les deux parents sont tous deux émis par la
course canonique : ce sont deux entrées constituées légitimes de son extension.

## Distinctions futures : contrat fixé

`VariableMasterFutures` déclare un seul contrat : lire, autant de fois que
demandé, `x10` dans la continuation après l'action réellement produite. Il ne
promet ni les reprises de recherche, ni l'inspection de l'affectation originale.

Pour ce contrat, les deux continuations du cas regroupant ont exactement les
mêmes futurs. Dans le cas non résolu, une lecture distingue positivement les
deux continuations. `every_exact_realization_distinguishes` impose cette
distinguabilité à toute réalisation exacte, sans imposer son encodage mémoire.
Ce résultat ne caractérise pas encore toutes les distinctions d'un runtime
avec reprise, impulsion ou autre interaction.

`exact_future_fibres` caractérise, sur toutes les sources de ce contrat,
l'égalité des états réduits par l'équivalence de tous leurs futurs.
`covers_read_values` construit une source pour chacune des deux valeurs
réduites. Les états originaux du couple regroupé restent prouvés distincts :
la réduction élimine une distinction devenue inutile pour ce contrat,
sans affirmer l'égalité des sources.

## Portée

L'échec de ce chercheur ne démontre pas l'absence de toute autre relation
utile. La préservation établie est celle de SAT, pas l'identité de toutes les
affectations. Le contrat de lecture est distinct des contrats de reprise du
projet. Le normaliseur parcourt une frontière explicite : aucune borne générale
de coût non extensif, aucune imprévisibilité et aucune résolution efficace de
SAT arbitraire ne sont revendiquées.

L'audit indépendant de la chaîne intégrée au commit
[`b32946c708393fc3574bd492edc32d5022a0cfec`](https://github.com/JohnDoe-collab-stack/relational-perimeter/commit/b32946c708393fc3574bd492edc32d5022a0cfec)
a conclu `EXACT INTEGRATED TARGET REQUIRES CORRECTIONS`. La révision de
référence des sources Lean publiées,
[`a6785356c5e9ecc879386064c52df5f9ce205247`](https://github.com/JohnDoe-collab-stack/relational-perimeter/commit/a6785356c5e9ecc879386064c52df5f9ce205247),
inclut les corrections ultérieures. Aucun nouveau verdict indépendant sur
cette révision n'est enregistré dans le [registre scientifique](scientific-claims.json).
Le verdict antérieur ne vaut pas validation de cette révision.

## Vérification locale reproductible

Avec Lake et Python 3 disponibles (ou `RELATIONAL_PERIMETER_PYTHON` défini),
exécuter `pwsh -File scripts/check-variable-master.ps1` depuis le dossier.
Le script fige ses entrées par empreinte avant les builds propres, exécute
le vérificateur Windows et contrôle les empreintes finales. Les preuves,
exemples et contrôles du code compilé sont vérifiés ensemble. Les journaux
sont créés dans un nouveau dossier voisin, hors des sources, sans écraser
un résultat antérieur. Ce protocole n'est ni un benchmark ni un audit indépendant.
