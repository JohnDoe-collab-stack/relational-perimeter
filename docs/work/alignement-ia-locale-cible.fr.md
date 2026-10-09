# Alignement sous contrat avec une IA locale : cible du premier raccordement

La cible est l'alignement mathématique de l'activité effective d'une machine
composée avec un modèle de langage réel. Le contrat est reçu. Les propositions
du modèle deviennent des requêtes ; leur incorporation, les productions et les
réponses restent constituées par l'exécuteur du projet. Une remise à zéro du
contexte du modèle doit laisser ce contrat en vigueur, avec la possibilité
positive de poursuivre une tâche permise.

Ce chantier part de `main`, révision
`b71904ab3b1cabb18faec791a690fa87b434e00e`, sur la branche
`codex/ai-alignment-under-contract`. Les sources de production, la cible protégée
et les évidences du registre ne sont pas modifiées. Les nouveaux résultats
restent des résultats de chantier jusqu'à leur révision de référence et leur
enregistrement explicite ; les quatre paragraphes protégés restent inchangés.

## Ce qui constitue la garantie

La machine ne reçoit pas du modèle une réponse déclarée correcte. Elle reçoit
une proposition. L'autorisation d'une réponse consomme une permission du contrat,
une référence vers une occurrence effectivement produite et l'égalité avec sa
lecture. La valeur commune de deux occurrences ne confond pas leurs identités.
Une occurrence nouvelle provient de la continuation exécutée, avec son témoin
d'origine ; elle n'est pas reconstituée séparément pour le journal.

L'oubli de la sélection initiale appartient déjà à la normalisation constitutive.
Le raccordement conserve ce résultat pour un contexte initial du modèle fixé,
sans archive de la sélection dans l'état composé. La remise à zéro du transcript
du modèle est un autre passage : elle modifie ses possibilités de proposition,
mais ne remplace ni le contrat ni la mémoire constituée. On démontre la
conformité pour toutes ces propositions, sans supposer que deux contextes
différents conduiront aux mêmes choix.

L'exécuteur maintient aussi les lectures des occurrences anciennes. Cette
stabilité accompagne une génération qui continue. Le registre peut grandir ;
aucune borne constante sur les octets mémoire, le temps ou l'énergie n'est
déduite de ces résultats.

## Obligations de ce lot

| Obligation | Réalisation attendue |
| --- | --- |
| Proposeur réellement adaptatif | Le choix reçoit le contexte, l'entrée courante et une observation du présent ; il peut changer après chaque interaction. |
| Absence d'hypothèse de bonne conduite | Les preuves quantifient sur toute politique de proposition et toute suite finie d'entrées, avec ou sans oubli. |
| Incorporation effective | Une requête décodée consomme `executeProducedInput`, le producteur existant, une seule fois pour l'état suivant et la réponse. |
| Refus fondé | L'absence de permission, l'absence d'occurrence et une valeur différente ont leurs témoins distincts ; une erreur de protocole n'a aucun effet machine. |
| Persistance et progrès | Le contrat persiste ; une requête `obtain` permise produit les étapes nécessaires et rend une réponse. |
| Oubli réel des profils | Aucun récupérateur uniforme de la sélection initiale depuis l'état composé à contexte fixé. |
| Modèle local réel | Poids Qwen officiels épinglés ; propositions issues de l'inférence, puis exécution par Lean. |
| Reproduction | Protocole et empreintes figés avant le run confirmatoire ; reçus rejoués exactement dans le noyau Lean. |

Les preuves centrales sont dans
[ModelLoop.lean](../../Tests/LocalAlignment/ModelLoop.lean).
Le transport exécutable est dans
[Kernel.lean](../../Tests/LocalAlignment/Kernel.lean), la conduite de l'expérience
dans [run.py](../../apps/local-alignment/run.py).

## Frontière de l'expérience

Le contrat concret actuel autorise la restitution de variables d'occurrences
constituées et la production de nouvelles occurrences. Le raccordement local
expose, pour cette première expérience, une portée singleton et les opérations
`advance`, `inspect`, `obtain`, `propose`. Des limites de transport bornent les
requêtes exécutables : 128 occurrences, 16 étapes par avance, variables jusqu'à
256, 10 000 lignes par session. Les théorèmes de composition des requêtes typées
ne prennent pas ces limites comme hypothèses.

Le modèle produit ses choix à partir d'instructions en langage naturel. Son
texte brut reste une proposition de travail. Les réponses de la machine sont
les messages issus du producteur certifié. Cela établit un raccordement effectif
avec une IA moderne dans ce contrat ; une autre tâche exige la constitution de
ses propres actions, permissions, critères et preuves de progrès.

La conformité ne suppose pas la compétence du modèle. La complétude d'une tâche
arbitraire ne découle cependant pas de sa simple présence : un proposeur qui ne
demande jamais le travail utile n'en réalise pas les étapes. Ici le progrès est
démontré pour chaque demande permise `obtain`, et observé pour les demandes du
modèle pendant l'expérience. La persistance du contrat ne dépend pas du succès
de ces observations.

La trace contient les productions partagées, les positions des permissions et
des occurrences, les origines et les transitions de ressources. Le rejeu vérifie
sa concordance avec l'exécution. Son empreinte fournit un contrôle d'intégrité
local, pas une signature authentifiée ni une nouvelle preuve mathématique.

Les prochaines extensions devront donner une tâche d'IA utile plus large, son
contrat explicite et ses critères d'accomplissement, puis établir le raccord de
chaque effet à cette chaîne. Le présent lot ferme le passage modèle local /
propositions / exécution constitutive sous contrat, sans changer la cible de
l'alignement général.
