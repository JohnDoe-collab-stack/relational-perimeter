# Composition dirigée sous regroupement opérationnel

## Portée et statut

Ce développement isole deux noyaux constructifs d’incompatibilité dirigée et
construit une instance positive non diagonale du même mécanisme de composition.
Il distingue trois données qui ne sont pas interchangeables : une collision de
mémoires calculée par deux exécutions, deux factorisations locales de readout,
et le transport transversal rendu possible par l’égalité des mémoires
terminales.

Le résultat ne caractérise pas une mémoire quotient et ne prouve aucune
réciproque entre équivalence des futurs et égalité des mémoires. Il ne dit pas
que tout regroupement est impossible. Il ne porte ni sur tous les réels, ni
sur AC ou CH, ni sur un coût physique, ni sur une nouveauté bibliographique.

## Deux incompatibilités constructives génériques

Le noyau unidirectionnel reçoit un transport `P → Q`, un témoin de `P` et une
réfutation `Q → Empty`. Il produit `Empty` en appliquant successivement ces
trois données. Il ne contient aucune donnée gödelienne, tarskienne ou
opérationnelle.

Le noyau bilatéral reçoit deux transports `P → Q` et `Q → P`, ainsi qu’une
certification constructive formée de `P → Q → Empty` et de
`(Q → Empty) → P`. Il construit d’abord une réfutation de `Q`, puis un témoin
de `P`, et enfin `Empty`. Il n’utilise ni égalité de types, ni `propext`, ni
tiers exclu.

Les wrappers opérationnels ne reçoivent pas les transports transversaux comme
hypothèses. Ils reçoivent un `ExecutedOperationalGrouping` et une ou deux
préservations terminales dirigées. Chaque transport transversal est produit
par `directedReadout` ou `reverseDirectedReadout`, donc par composition des
factorisations locales le long de l’égalité des mémoires terminales dérivée
des deux runs et de leur collision calculée.

## Instance positive non diagonale

Pour un même rôle constitutif et le même run maître, l’instance utilise les
deux sources acceptées déjà construites `variedLeftSource role` et
`leftSource role`. Leur distinction est prouvée avant la construction du
runtime. Les positions `source` et `target` servent uniquement à les indexer et
ne remplacent pas cette distinction constitutive.

La requête `close` est autorisée uniquement en phase active et calcule une
phase terminale. Les deux runs sont non vides. Les événements actifs exposent
la position, si bien que les deux traces restent distinctes. La projection
mémoire conserve la position en phase active et ne conserve au terminal que le
booléen effectivement lu à la ressource `run.selected`.

L’égalité des deux booléens terminaux n’est ni postulée ni obtenue par une
simplification indépendante. Elle suit de la chaîne existante
`same_sources_other_resource_agree`, `produceRoleSignature_exact` et
`FutureEquivalent.read`. L’égalité des mémoires terminales est ensuite obtenue
par transport de cette égalité sous le constructeur `grouped`.

Les readouts terminaux sont des types dépendants indexés par les booléens
produits. La factorisation source encode explicitement un booléen en naturel.
La factorisation cible décode explicitement ce naturel et utilise la loi de
décodage de l’encodage. Le transport entre les deux readouts terminaux est
produit uniquement par `positiveDirectedGrouping.directedReadout` appliqué à
ces factorisations. Un témoin source concret est transporté vers un témoin
cible concret. Cette construction ne construit aucun terme de type `Empty` ni
aucune preuve de `False`.

L’instance établit donc positivement que la collision opérationnelle et la
préservation dirigée peuvent être compatibles lorsque les lectures terminales
le sont. Les obstructions de Gödel et de Tarski ne proviennent pas de la seule
existence du mécanisme de transport. Elles apparaissent lorsque les données
propres à ces instances rendent le transport produit incompatible.

## Raccord Gödel

La réalisation gödelienne sans readout est exposée sous l’interface
`OperationalRealization` en réutilisant ses transitions, événements,
autorisations, décisions, projection et lois d’exactitude. Son readout réduit
constant n’est pas transporté.

Le regroupement gödelien déjà calculé est exposé sous
`ExecutedOperationalGrouping` en réutilisant exactement ses deux runs, leurs
événements, leurs terminaux et leur collision. Seule l’enveloppe structurelle
de la trace non vide est reconstruite. Aucune recherche, autorisation,
décomposition, exécution ou collision n’est recalculée.

Sur cette même réalisation et ce même regroupement, une préservation terminale
dirigée produit `Truth(G) → Proof(G)`. Cette production reste indépendante de
`trueWitness` et de `unprovable`. Le rejet final applique ensuite le noyau
unidirectionnel au transport produit et aux deux témoins du même témoin
gödelien. L’instance de Heyting Arithmetic expose séparément la réalisation,
le regroupement, le transport positif conditionnel et le rejet.

## Raccord Tarski

La certification diagonale de Tarski est adaptée au certificat bilatéral pur
en réutilisant uniquement ses deux directions. La construction de l’adéquation
locale reste antérieure à l’emploi de cette certification : les deux
transports canoniques sont dérivés des runs, de la collision et des deux
préservations dirigées. Le noyau bilatéral consomme ensuite ces transports et
la certification.

Les deux conséquences unidirectionnelles restent disponibles séparément.
Aucune direction isolée n’est promue en correspondance bilatérale ou en
contradiction.

## Séparation finie et limites

La séparation par futur fini demeure un mécanisme distinct. Elle établit que
toute réalisation exacte doit conserver une différence révélée par une
requête finie. Elle ne fournit pas la réciproque selon laquelle les mêmes
futurs imposeraient la même mémoire.

Les noyaux dirigés ne remplacent pas automatiquement les régimes abstraits de
totalisation du dépôt. Aucun adaptateur vers ces régimes n’est construit. La
forme qu’il devrait prendre n’est pas établie. Aucun raccord supplémentaire
n’est revendiqué ici.
