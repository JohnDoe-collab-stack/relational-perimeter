# Revue de lecture et de traduction — correction native des réels relationnels

Responsable : Codex (OpenAI), lectures autonomes puis confrontation formelle.

Date : 18 octobre 2026.

Révision examinée : `129e38de51437ea26488f8db8b4991305e6a37cc`.

## Périmètre et ordre de lecture

La lecture française autonome a porté intégralement, dans cet ordre, sur
`godel-regroupement-completude-reels.fr.md` puis
`runtime-real-cauchy-effective-correspondence.fr.md`. La lecture anglaise a
ensuite porté intégralement sur
`godel-grouping-relational-real-completeness.en.md` puis
`runtime-effective-cauchy-real-correspondence.en.md`. La confrontation aux
types, aux corps Lean et aux contrôles compilés a été effectuée après ces deux
lectures séparées.

La confrontation formelle a distingué la formation des objets et de leurs
indices, les données réellement produites, les ressources consommées par les
preuves, puis les transports et oublis aval. Elle a porté en particulier sur la
médiation native de l'unicité, la continuation de sa banque et de ses archives,
la fermeture des constructeurs d'archives, la place du champ installé et les
limites explicites des interfaces reçues.

## Revue de lecture française

Le passage gödelien conserve sa portée : le même témoin diagonal rejette la
boucle totale et la fermeture globale du même régime, tandis que le maître
commun produit les futurs finis de la famille reçue. Il ne transforme pas la
contradiction en approximation numérique et n'affirme ni couverture de tous
les réels classiques, ni complétude par borne supérieure, ni résultat sur
`AC` ou `CH`.

Le passage de correspondance place les relations, les occurrences, les
archives, les banques et les exécutions avant leurs readouts. La complétude
native part d'une `NativeCauchyFamily` reçue. Pour chaque requête d'unicité,
`mediateNative` exécute un seul pas du terme depuis l'entrée courante de la
banque, transmet cette même donnée aux deux lois de convergence, puis la trace
continue le successeur de ce pas et les deux archives candidates. La projection
numérique intervient seulement après cette construction. Les adaptateurs
`toEffectiveFamily`, `realizedFamily` et `asExecutedCandidate` ne constituent
plus `nativeUnique`.

La mémoire est décrite relativement au contrat effectif de chaque service. Le
runtime autoritatif historique peut reprendre une cible par
`continueInstalled`. Dans les services arithmétiques et natifs, le dernier code
installé est une mémoire d'observation lue par la façade live ; le calcul riche
suivant consomme les archives enfants ou la banque et le journal continués. Le
texte ne prétend donc plus que toute cible installée devient l'entrée de toute
transition suivante.

Les constructeurs des archives d'addition, multiplication, négation,
réciproque et limite native sont privés. Les fabriques publiques concernées
reçoivent uniquement les contextes initiaux autorisés et imposent une racine de
journal, un historique retenu vide et aucune sortie installée. Les historiques
non vides restent ainsi issus des fonctions de transition du dépôt.

La portée est volontairement bornée. `NativeCandidate.converges` demeure une
loi générique reçue ; le type ne certifie pas à lui seul le procédé interne
d'une implémentation extérieure. À service, archive et précision fixés, une
réévaluation pure est propositionnellement égale : le partage prouvé lie une
donnée dans la trace canonique, mais ne crée pas un jeton génératif distinct.
L'identité historique est portée par la position de trace et les archives
continuées. Le constructeur `certified` garde également le porteur ouvert aux
services extérieurs satisfaisant son contrat explicite.

Verdict de lecture française : **reviewed** pour
`GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS` et
`RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE` sur la révision indiquée. Ce
verdict ne vaut ni audit indépendant, ni verdict d'originalité.

## Revue de traduction anglaise

La version anglaise conserve les mêmes quantifications, entrées reçues,
directions constitutives et exclusions. `closed runtime carrier` décrit la
fermeture syntaxique par les cinq constructeurs, tandis que la phrase suivante
conserve explicitement l'ouverture du contenu de `certified`. `downstream
readout` ne devient jamais une donnée primitive. `one term step` et `that same
datum` correspondent exactement au pas stocké une fois dans la médiation et
transmis aux deux lois.

Les deux langues distinguent de la même manière la cible installée comme
observation et la banque, le journal ou les archives utilisés par le calcul
riche suivant. Elles énoncent aussi la même limite de réévaluation pure, la même
portée conditionnelle des lois génériques, la même unicité seulement numérique
et comportementale, et les mêmes non-conclusions sur tous les réels
classiques, la complétude d'ordre, `AC`, `CH` et l'originalité.

Verdict de traduction : **reviewed** pour les deux affirmations sur la révision
indiquée. Aucune inversion du primitif relationnel ni variation de portée n'a
été relevée entre le français, l'anglais et les types Lean.

## Confrontation formelle

`NativeMediation` est indexé par la famille, les deux candidats, la banque, les
deux archives et la requête. Son constructeur privé conserve les trois pas,
leurs égalités d'exécution, les deux témoins de proximité obtenus des lois
reçues et leur composition. `produceNativeUniquenessTrace` appelle une seule
médiation par requête, remplace l'entrée diagonale de la banque par le
successeur possédé et continue les deux successeurs candidats.
`NativeUniquenessTrace.toNumerical` transporte cette trace sans réexécuter les
pas ni les lois. `nativeNumericalFutures` choisit explicitement
`initialBank`; le producteur riche général accepte, lui, toute banque courante.
Enfin `nativeUnique` dérive à la fois l'équivalence ponctuelle et les futurs de
cette route native directe.

Les tests opposent le candidat natif autoritatif à un candidat construit par
addition avec zéro, dont les constructeurs `Real` sont distincts. Ils vérifient
le pas issu de la banque courante, son usage par les deux lois, la continuation
de la banque, la trace riche et sa projection. Les fixtures négatives vérifient
que les constructeurs privés et les mises à jour structurelles externes ne
permettent pas de forger les archives visées.

La chaîne ne prouve pas que toute loi extérieure examine computationnellement
ses arguments, ne distingue pas deux évaluations pures aux mêmes indices et ne
reconstruit aucune famille, histoire ou occurrence depuis un readout. Ces
limites correspondent aux non-conclusions canoniques ; elles ne sont pas
masquées par un changement de définition.

## Contrôles techniques de la révision

La révision a passé le build Lean complet (`398` travaux), l'audit global des
constantes (`37092` constantes, `395` modules, `737` exceptions générées et
aucune exception écrite), les audits d'axiomes des déclarations modifiées et le
contrôle des blocs terminaux `AXIOM_AUDIT`.

Les `189` fixtures négatives passent avec leur diagnostic et leur site exacts.
Le contrôle du code compilé natif couvre neuf routes et rejette les mutations
de remise à zéro d'archives, perte des extensions ou des pas partagés,
composition erronée, reconstruction par les adaptateurs numériques et double
médiation. Le harnais des façades a passé ses deux baselines puis ses dix-huit
mutations ; ses résultats temporaires restent hors du dépôt.

Ces contrôles établissent la reproductibilité mécanique annoncée, pas le sens
à eux seuls. L'audit indépendant doit viser exactement la révision indiquée et
reste `not_recorded` jusqu'à réception et lecture de son rapport.
