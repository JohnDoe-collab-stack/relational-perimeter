# Indéfinissabilité de Tarski et fermeture opérationnelle relationnelle

## Portée et statut

Ce passage est le texte canonique d’une affirmation scientifique distincte.
Son enregistrement ne vaut ni revue de lecture, ni revue de traduction, ni
audit indépendant. Il sépare un théorème sémantique constructif de Tarski,
sa factorisation par un runtime relationnel et deux constructions positives.
Il établit aussi que le séparateur terminal immédiat dérivé de la certification
impose à toute réalisation exacte du contrat de séparer les deux terminaux.
Il ne revendique ni nouveauté historique, ni hiérarchie tarskienne déjà
construite, ni résultat sur Kripke, les théories de la révision ou tous les
langages munis d’une vérité.

La [figure comparative Gödel–Tarski](figures/godel-tarski-operational-closure.fr.svg)
résume cette architecture. Elle est une représentation synoptique du résultat,
pas une preuve supplémentaire.

## Production exécutée du diagonal

Un candidat arithmétique de vérité est reçu avant la diagonalisation. Une
production syntaxique unique construit successivement le corps diagonal,
exécute la substitution à son propre code, produit la phrase diagonale et
enregistre quatre occurrences ordonnées dans la même histoire.

Dans l’instance de l’arithmétique de Heyting, la substitution est exécutée par
`PRFunction.captureAvoidingDiagonalSubstitution`. Le code terminal est celui
retourné par `PRFunction.runCore`, et le témoin du graphe de substitution est
dérivé du certificat `PRFunction.Evaluates` porté par cette même exécution. La
phrase, son code calculé et la certification sémantique ne proviennent donc pas
de reconstructions indépendantes.

La syntaxe exécutée ne contient encore aucune famille de vérité. Le readout
sémantique est ajouté ensuite : pour une phrase arithmétique `S`, il est le type
relevé de sa satisfaction dans la sémantique constructive standard.

## Théorème sémantique constructif

Pour la phrase diagonale exécutée `L` et le candidat reçu `Cand`, la certification
issue de `diagonal_spec` fournit les deux directions entre la vérité de `L` et
la négation de la vérité de `Cand` appliqué au code calculé de `L`.

Une adéquation locale fournirait en sens inverse les deux transports entre la
vérité de `L` et celle de `Cand` appliqué à ce même code. Leur composition produit
`Empty` constructivement. Aucun tiers exclu, aucune cohérence supposée et aucun
prédicat de preuve n’interviennent.

Une adéquation globale est définie par deux transports dirigés, pour toute
phrase arithmétique, entre sa vérité externe et la satisfaction du candidat
sur son code. Sa spécialisation à la production diagonale donne l’adéquation
locale rejetée. Il en résulte que, pour tout prédicat arithmétique candidat,
une telle adéquation globale bilatérale conduit à `Empty`.

L’instance HA expose les deux présentations sans les confondre.
`heytingArithmeticRejectsSemanticTruthCandidate` reçoit directement les deux
implications entre propositions `sentence.models`.
`heytingArithmeticRejectsTotalTruthCandidate` reçoit leur présentation en
`PLift` destinée au runtime. La première construit explicitement la seconde en
relevant puis en redescendant les témoins ; aucune égalité de types n’est
utilisée.

## Regroupement opérationnel positif

Deux sources sont initialisées depuis la même production exécutée. Elles
partagent les occurrences et l’histoire de production, mais conservent deux
positions distinctes : la valeur de la phrase diagonale et la lecture du
candidat sur son code.

Les lemmes `tarskiRuntimeNext_occurrences` et
`tarskiRuntimeRun_occurrences`, puis leurs spécialisations aux deux terminaux,
établissent explicitement que ces occurrences sont celles de la production
maître après la transition et après tout run.

La requête autorisée `close` exécute un véritable passage de la phase active à
la phase terminale. La mémoire active conserve la position ; la projection
terminale l’oublie et produit une mémoire opérationnelle commune. Les deux
runs, leurs autorisations, leurs transitions et leurs événements sont
construits sans aucune correspondance de readout.

Le contrat canonique calcule ses événements depuis la phase, l’histoire et la
requête, sans y copier la position. Cette cécité au pôle est une hypothèse de
conception explicite. Elle est exactement ce qui permet de construire
l’égalité des traces enregistrée dans `TarskiObservedOperationalGrouping`.
Les sources et la mémoire active continuent, elles, à distinguer les deux
positions.

Cette hypothèse ne doit pas être surinterprétée. Si la position était ajoutée
à l’événement, l’exactitude événementielle resterait possible avec une mémoire
active qui la conserve, mais les traces des deux sources ne pourraient plus
être égales. Le regroupement minimal par collision mémoire resterait un objet
distinct ; c’est le regroupement observationnel commun qui ne se construirait
plus.

Le test de régression positif construit une seule réalisation alternative dont
l’événement expose le pôle pendant la phase active. Dans cette même
réalisation, `event_exact` est satisfait, les deux runs sont construits et la
collision terminale des mémoires est calculée. Le test prouve ensuite que les
deux traces du pas `close` sont distinctes. La fixture négative complémentaire
échoue exactement lorsqu’elle tente d’ajouter leur égalité. Le cas terminal de
cet événement alternatif est volontairement indépendant du pôle, puisque la
mémoire terminale l’a déjà oublié.

Ce test réutilise aussi le pont générique de readout dirigé. Sous les deux
préservations terminales conditionnelles, il retrouve l’adéquation locale puis
le rejet de Tarski avec ces événements qui exposent le pôle. La dépendance à
la cécité événementielle est ainsi écartée par construction, et pas seulement
par inspection du corps du théorème canonique.

## Localisation de l’obstruction exacte

La certification diagonale construit aussi un séparateur fini des deux
terminaux pour le contrat déjà fixé. Sa liste de requêtes est vide parce que
l’issue associée à la liste vide lit immédiatement le terminal reçu. Toute
`ExactRealization` de ce contrat doit donc projeter les deux terminaux vers des
mémoires distinctes. Cette séparation provient du readout terminal et non
d’une dynamique cachée. Elle ne contredit pas le regroupement positif, qui
porte sur une réalisation opérationnelle sans loi de préservation du readout.

La dépendance formelle est seulement dirigée : une même mémoire projetée impose
les mêmes futurs, donc un séparateur de futurs impose des mémoires projetées
distinctes. La réciproque « mêmes futurs implique même mémoire » n’est pas
établie. Le résultat ne présente donc pas la mémoire comme un quotient canonique
des futurs.

L’interface commune minimale est une préservation terminale dirigée. Elle
complète une réalisation opérationnelle donnée par une famille `memoryRead`,
une fonction de la lecture source vers la mémoire et une fonction de la mémoire
vers la lecture cible. Elle ne reçoit ni égalité des types de readout, ni
`propext`, ni loi de retour. Une correspondance terminale bilatérale réunit
deux préservations opposées et comporte donc quatre fonctions dirigées.

Pour une seule et même réalisation, un regroupement exécuté fournit l’égalité
des mémoires projetées des deux terminaux. Le transport dépendant le long de
cette égalité, composé avec une préservation dirigée, dérive une direction de
l’adéquation locale. Les deux préservations opposées dérivent les deux
directions. Cette dérivation ne consulte ni la
certification diagonale, ni un théorème d’impossibilité, ni un témoin gödelien.

La même interface dirigée sert désormais aux deux branches sans les
confondre. Dans la branche Gödel, une seule direction transporte
`Truth(G)` vers `Proof(G)`. Dans la branche Tarski, les deux directions sont
requises pour obtenir l’adéquation locale bilatérale.

La factorisation dirigée localise aussi ce que produit chaque fermeture
partielle. En posant `C = Truth(Cand(⌜L⌝))`, la certification diagonale donne
`Truth(L) ↔ ¬C`. Alors :

- la seule direction valeur vers candidat donne `¬Truth(L)` et `¬¬C`
- la seule direction candidat vers valeur donne `Truth(L)` et `¬C`
- les deux directions réunies donnent `Empty`

Ces conséquences sont démontrées séparément dans Lean et spécialisées à
l’instance HA. Aucun des deux théorèmes partiels ne dépend du pont opposé ni du
rejet bilatéral. Au niveau du seul diagonal produit, elles expriment une
cohérence locale minimale. Elles ne construisent pas à elles seules un prédicat
de vérité partiel global non trivial.

Le rejet final est ensuite une composition séparée :

```text
collision des mémoires calculées
+ correspondance bilatérale des readouts de la même réalisation
→ adéquation locale au diagonal exécuté
+ certification diagonale constructive
→ Empty
```

Le théorème minimal ne dépend pas de l’égalité des traces événementielles. Un
second théorème reçoit le `TarskiObservedOperationalGrouping` canonique afin
que la cécité au pôle et l’égalité des traces apparaissent explicitement dans
son énoncé. La contradiction reste localisée dans la combinaison collision de
mémoire + correspondance des readouts, et non dans l’événement seul.

## Possibilité ouverte conservée

La réalisation identité fournit positivement une correspondance exacte des
readouts aux deux terminaux. Elle conserve cependant les positions, de sorte
que ces terminaux restent distincts et ne collisionnent pas.

Les deux possibilités positives sont donc séparées : le runtime opérationnel
canonique regroupe sans readout exact, et la réalisation identité préserve les
readouts sans regrouper les terminaux. L’impossibilité porte seulement sur leur
combinaison dans une même réalisation aux mêmes terminaux calculés.

## Limites exactes

Le résultat sémantique porte sur les prédicats arithmétiques de l’instance HA
et sur la sémantique constructive fournie dans le dépôt. Il ne constitue pas
une dérivation interne, dans HA, de l’indéfinissabilité syntaxique d’un
prédicat de vérité.

La continuation hiérarchique de Tarski n’est pas encore construite. Le runtime
présent montre une fermeture locale impossible et une réalisation ouverte qui
sépare les positions ; il ne construit pas une famille de langages et de
readouts indexée par niveaux. Il n’établit aucun résultat sur les réels, AC ou
CH et ne renforce pas les théorèmes de Gödel.
