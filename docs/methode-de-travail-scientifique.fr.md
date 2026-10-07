# Procédure de travail scientifique

Cette procédure applique les [instructions obligatoires](../AGENTS.md).
Elle organise le travail ; elle ne remplace ni les fondations ni la cible
scientifique. Aucun changement Lean, aucune installation de skills ni aucun
audit extérieur ne découle de son adoption.

## 1. Fixer la tâche avant d'agir

Identifier la demande, la branche, la révision, les changements déjà présents,
les collaborateurs concernés et les fichiers autorisés. Une demande d'analyse
n'autorise pas une correction ; une demande de correction n'autorise pas un
push ou une soumission d'audit. Ne pas travailler dans le checkout d'un autre
agent quand une isolation est nécessaire.

Lire intégralement les sources pertinentes. Pour une tâche globale, étendre
cette lecture à toute la chaîne et à ses consommateurs. Un inventaire de noms
ou un résumé ne remplace pas cette lecture.

Les quatre paragraphes en tête de la
[conclusion canonique](conclusion-largeur-exponentielle-conservation-identites.fr.md)
sont protégés dans le registre par quatre ancrages, sans copie concurrente.
Une cible nouvelle exige une décision humaine explicite. La présente procédure
ne réinterprète pas cette cible.

## 2. Cartographier la chaîne, pas seulement le théorème terminal

Pour chaque affirmation, reconstruire les passages nécessaires :

```text
relations primitives et témoins positifs
  -> histoires, occurrences et contextes constitués
  -> recherche réellement exécutée
  -> relation trouvée, action totale, préservation séparée
  -> autorisation et décomposition produite
  -> continuation et état suivant
  -> mémoire exacte sous contrat explicite
  -> observations et readouts
```

Les contextes reçus font partie des entrées déclarées ; ils ne sont pas à
présenter comme des sorties de la course canonique s'ils ne le sont pas.
L'endogénéité est relative aux primitives et aux entrées reçues, non une
production de ses propres primitives.

Chaque fiche du registre sépare quatre lectures de dépendance :

1. **Formation** : indices et témoins qui constituent l'objet dans les types.
2. **Exécution** : producteurs, données reçues et données effectivement lues.
3. **Preuve** : obligations consommées pour établir l'énoncé précis.
4. **Transport** : distinctions conservées, regroupées ou oubliées, avec les
   lois et le contrat qui autorisent ce passage.

Une preuve de largeur peut ne consommer que des faits finis, tandis que son
carrier appartient à une chaîne relationnelle plus riche. Ne pas inventer une
dépendance logique de ce lemme envers chacun des témoins. Pour une revendication
causale, ne pas remplacer l'action produite par un singleton ou une sortie
reconstruite indépendamment. La question est celle de la chaîne typée et
exécutée entière, pas celle d'un champ seulement présent dans une structure.

## 3. Un registre, un texte canonique

[scientific-claims.json](scientific-claims.json) est l'inventaire initial des
affirmations majeures. Il couvre la constitution, la recherche, les régimes,
la continuation, les signatures et le raccord machine. Ce n'est pas encore
un index de chaque phrase du dépôt.

Une entrée désigne le passage exact par fichier, titre unique et éventuellement
numéro de paragraphe. Elle donne la portée, les déclarations et leurs modules,
le rôle production/test, les consommateurs et les quatre dépendances.
Les traductions sont liées à la même entrée, pas traitées comme deux preuves.
Les synthèses uniquement françaises ne requièrent pas une traduction fictive.

Les empreintes utilisent l'UTF-8 et les fins de ligne LF ; seule la conversion
CRLF vers LF est faite. Elles ne normalisent ni le vocabulaire ni la ponctuation.
L'empreinte source couvre conservativement les imports locaux transitifs des
modules cités, les fichiers de configuration et les contrôles cités. Elle ne
prétend pas être le graphe minimal des dépendances d'un terme Lean.

La révision d'évidence est un commit existant. Le contrôle compare le snapshot,
les sources actuelles et les empreintes enregistrées. Une dépendance ajoutée
ou modifiée invalide cette évidence. Les fichiers nouveaux doivent d'abord
avoir une révision de référence avant de recevoir une évidence figée.

Une modification intentionnelle demande une lecture des changements, une
révision des consommateurs et une réouverture explicite des revues. Le checker
ne comporte aucun mode de rafraîchissement et n'écrit pas le registre.
Un changement de titre ne doit pas être compensé par un ancrage approximatif.

## 4. Séparer quatre verdicts

| Niveau | Ce qu'il autorise à dire |
| --- | --- |
| Références et empreintes cohérentes | Le lien enregistré n'est pas périmé |
| Lean et contrôles locaux exécutés | Les commandes citées ont réussi sur cet arbre |
| Lecture mathématique et revue du texte | Les hypothèses, contrats, quantifications et explications ont été confrontés |
| Audit indépendant | Le rapport lu conclut sur sa révision et sa portée propres |

Un niveau n'entraîne pas automatiquement le suivant. Les revues de lecture
et de traduction du registre commencent à `pending`. `not_recorded` pour
l'audit signifie que le registre ne porte pas de verdict indépendant, non
que les résultats antérieurs seraient réfutés. Le résultat d'un audit
historique reste attaché à son ancien snapshot. Une soumission « acceptée »
ou un identifiant de tâche n'est pas une validation scientifique.

Toute revue enregistrée exige un fichier d'évidence réel, son empreinte et
un responsable identifié ; aucune commande ne remplit ces champs à sa place.
Une revue qualifiée garde ses limites. Ne pas éliminer un avis défavorable en
changeant de relecteur ou en réécrivant l'audit.

## 5. Lire pour un lecteur humain

Faire d'abord lire le passage sans noms Lean ni résumé de preuve. Noter ce
qu'il lui fait affirmer : objet, dépendances, hypothèses, quantification,
contrat et conclusion. Confronter ensuite cette reconstruction aux énoncés
complets et à la chaîne. Un nom formel peut servir de repère, pas d'explication.

Contrôler chaque paire FR/EN sur ces mêmes éléments. Distinguer exemple,
interface conditionnelle, instance construite et théorème général. Ne pas
promouvoir une largeur un en borne de coût total, une équivalence de futurs
en minimum physique, ou un échec de chercheur particulier en impossibilité.

Pour les figures, identifier ce qui est exact, ce qui est schématique et
ce qui manque. Vérifier le sens des flèches, l'ordre des strates, les étiquettes
et un rendu visuel. Un diagramme ne ferme pas une obligation de preuve ; son
extension ou son remplacement exige une tâche autorisée.

## 6. Vérifier sans modifier la science

Depuis la racine, avec Python 3 et la toolchain épinglée :

```text
python3 scripts/check-scientific-docs.py --self-test
python3 scripts/check-scientific-docs.py --static
lake build
python3 scripts/check-scientific-docs.py --lean
```

Les deux gates complètes incluent désormais ces contrôles dans leur build
existant, sans ajouter un second build :

```text
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
```

`--static` vérifie le schéma, les ancrages, les empreintes, les liens locaux,
les références de modules, le snapshot et les évidences éventuellement
enregistrées. `--lean` compile hors du dépôt deux petits clients (surface
publique et références de tests) qui demandent les types et les audits des
noms cités. Il ne fabrique aucune preuve scientifique et ne modifie aucune
source. Le build complet garde son propre audit exhaustif des constantes.

`--self-test` teste notamment les ancrages ambigus, les empreintes périmées,
les traversées de chemin, les imports multilignes/commentés et les statuts
sans évidence. Une erreur étrangère au défaut attendu ne vaut pas réussite.
Les noms absents sont rejetés par Lean, pas supposés existants d'après le texte.

Les sorties `SCIENTIFIC_DOCS_*_OK` ne signifient jamais « cible prouvée »,
« papier compris », « audit réussi » ou « nouveauté établie ». Les statuts
ouverts restent imprimés, même après une gate réussie.

## 7. Préparer une livraison honnête

Donner le diff, les commandes réellement lancées, la révision et les limites
observées. Ne pas annoncer un résultat à partir d'un test non exécuté.
Les audits et expériences sont préparés dans un espace distinct ; leur
soumission demeure soumise à autorisation humaine. Les prompts citent la cible
canonique sans la remplacer, le SHA distant exact et les clauses à examiner.

Les plans, journaux et autres documents temporaires ne doivent pas rester dans
l'arbre fusionné de `main`. Les README, cette procédure, le registre, les
documents scientifiques et les rapports finaux sont des livrables permanents.
La fusion ne clôt la tâche qu'après vérification du commit fusionné, et doit
elle-même avoir été explicitement demandée.
