# Évaluation contrôlée du routage conservé

Cette tranche forme la préservation complète du code de routage reçu, démontre
sa borne locale et la raccorde à la décision du même maître documentaire.
L'égalité porte sur les paquets originaux entiers. La décision consomme la
préservation produite et la continuation qu'elle transporte effectivement.

Ce résultat répond à la prochaine obligation de D2 du
[plan v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md), après la
[normalisation contrôlée](controle-normalisation-frontiere.fr.md). Il conserve
la priorité A avant B. Les comptes ci-dessous concernent le catalogue abstrait
de transitions du contrôle ; les applications différées et le paiement du
bootstrap de la borne sont encore des obligations de D2.

## Chaîne conservée

1. `expandedSearchCode` a déjà produit l'ouverture et la réduction originales
   dans le même `Master.Stage`. La réduction conserve son code de routage.
2. `ControlFrontierEvaluation.code` parcourt ce code reçu, avec ses six
   constructeurs et les témoins dirigés présents dans ses absorptions. Il
   construit un `Actual route.eval` entier : transport avant, transport
   arrière et leurs lois de préservation de l'acceptation.
3. `ControlStagePreservation.code` consomme `stage.reduction.code` et compose
   le résultat avec `stage.opening.preservation`. Il produit un
   `Actual stage.preservation` entier.
4. `ControlCompletion.expandedDecideCode` consomme ce paquet réel, applique
   son transport avant à l'entrée effective et transmet la continuation
   retenue à `completeCode`. La loi d'acceptation accompagne cette continuation.
5. `expandedRunCode` conserve la `Decision` et le `Dossier.Step` originaux
   entiers, avec la même tête, les contrôles reçus et le curseur suivant.

Une composition évalue ses deux sous-codes dans l'ordre, puis compose leurs
paquets réellement retournés. Le transport avant applique le premier puis le
second ; l'arrière applique le second puis le premier. Les deux directions
ne sont pas supposées inverses : après une absorption, l'arrière peut inclure
la continuation dans l'occurrence retenue de la frontière source. Le code
source et ses identités restent constitués séparément du regroupement.

L'action absorbante conserve la variable sélectionnée et forme une closure de
transport. Lors de son invocation, cette closure reçoit la continuation et
forme son lecteur d'affectation différé. Le témoin relationnel
et ses lois sont présents dans les types et les preuves originales. Ses champs
propositionnels sont effacés par compilation ; leur effacement n'est pas une
suppression de la garantie typée. Les maps, la variable sélectionnée, les vrais
sous-paquets et les deux directions sont conservés dans le code exécuté.

## Énoncés et bornes fermés

Pour toute formule, variable sélectionnée, frontière source et frontière cible
de contextes engendrés, et tout `AcceptedFrontierCode` reçu de l'action SAT
originale, `bounded` prouve `Within (code formula selected route)
(bound formula selected route)`. Aucune réussite du secours n'est ajoutée
comme hypothèse. La borne parcourt la syntaxe reçue ; elle ne découvre pas son
budget en exécutant l'évaluateur natif.

| Constructeur reçu | Borne locale de formation |
| --- | ---: |
| Identité | 5 |
| Échange | 5 |
| Absorption du premier | 8 |
| Absorption du second | 8 |
| Préfixage d'un sous-code | borne du sous-code + 5 |
| Composition de deux sous-codes | somme des deux bornes + 5 |
| Préservation du Stage | borne du code reçu + 4 |

Chaque nœud paie une cellule d'évaluation, les deux closures de transport,
le paquet de préservation et le retour du paquet. Une absorption paie aussi
l'action relationnelle : atome, closure différée et témoin positif. La
préservation du Stage paie sa cellule et la composition avec l'ouverture.

La décision étendue possède la borne uniforme
`(ControlStagePreservation.bound stage + pairBound left right) + 3`.
Elle utilise la syntaxe reçue et les deux références de sources. Son calcul
ne dépend ni du verdict de `seed`, ni d'une évaluation native du routage.
`expanded_decide_bounded` et `expanded_decide_finite` ferment cette interface
concrète. La voie étendue du maître consomme cette finitude.

Les définitions et preuves historiques de `ControlCompletion` et du maître,
avant leurs APIs étendues, ont été comparées au HEAD et conservées exactement.
Leurs bornes restent attachées à leur catalogue historique. Les quatre labels
nouveaux sont ajoutés après les indices 0 à 107, sans changer ces indices.

Les sources du raccord sont
[Evaluation](../../Tests/LocalAlignment/DocumentaryControlFrontierEvaluation.lean),
[Stage](../../Tests/LocalAlignment/DocumentaryControlStagePreservation.lean),
[Completion](../../Tests/LocalAlignment/DocumentaryControlCompletion.lean) et
[Master](../../Tests/LocalAlignment/DocumentaryControlMaster.lean).

## Vérification et supervision

L'agent a écrit les modules Lean et le raccord consommateur. L'agent principal
a relu leurs énoncés complets, les constructeurs et lois originaux, les
hypothèses des bornes et les chemins de données du C. Il a écrit séparément
les attentes des clients et les gardes de compilation, puis exécuté les
vérifications. Le résultat de l'agent ne tient pas lieu de revue indépendante
extérieure.

Le [client d'évaluation](../../scripts/run-documentary-frontier-evaluation-smoke.py)
contient treize contrôles de développement. Ils couvrent les six constructeurs,
les trois positions de chaque absorption, le préfixage, l'ordre de composition,
un échange double imbriqué, les codes effectivement retournés par la
normalisation, le Stage reçu et les trois décisions : regroupée, distincte et
interdite. Vingt-six observations avant/arrière lisent la position et les bits
0, 1, 2 et 17 ; le cas Stage lit aussi la variable du maître. Ces applications
sont observées hors du coût local de formation.

Les attentes ont été écrites avant le premier run : le code regroupant sept
nœuds doit payer 38 transitions d'évaluation et 42 pour le Stage ; le code
distinct à dix nœuds doit payer 50 et 54. Les tests exigent le carburant exact,
l'échec avec une unité de moins, la stabilité avec surplus et la même trace
complète. Les trois décisions utilisent aussi la nouvelle borne uniforme.

Les 31 contrôles d'intégration gardent les valeurs, les origines, les refus,
la progression du curseur, l'oubli, le reset et le rechargement. Les citations
épinglées de ce client conservent deux branches : elles exigent dix cellules,
dix paquets d'évaluation et un raccord de Stage, soit onze paquets de ressources
supplémentaires. Le refus ne forme aucune préservation supplémentaire.

La [garde C](../../scripts/check-documentary-frontier-evaluation-codegen.py)
exige les vrais transports, les résultats récursifs, le code de réduction du
Stage, la préservation de son ouverture et leurs consommateurs uniques.
Elle interdit les références aux évaluateurs et constructeurs natifs de
préservation dans les corps nommés, y compris les adresses de closures.
Elle vérifie aussi l'ordre avant/arrière. Ses mutations modifient les entrées
textuelles du checker ; elles ne sont pas des corruptions exécutées du binaire,
ni une certification transitive du coût physique.

La gate complète `powershell -NoProfile -ExecutionPolicy Bypass -File
scripts/verify.ps1` réussit : 349 fichiers Lean, 348 modules et 27 996 constantes,
avec aucune exception pour une déclaration écrite. Les 364 exceptions du sweep
concernent les déclarations engendrées par le compilateur et sont comptées
séparément. Les 703 audits explicites des 50 modules de contrôle sont sans
axiome, dont 23 nouvelles déclarations de cette tranche.

Les treize contrôles d'évaluation, les 31 contrôles d'intégration, les
dix-neuf contrôles de normalisation, les onze contrôles d'ouverture, les quatre
histoires de génération et les 23 fixtures d'échec attendu passent. La garde
nouvelle rejette 2 293 mutations textuelles dans 80 corps nommés ; les gardes de
normalisation et de contrôle étendu rejettent respectivement 1 735 et 2 289
mutations. Ces résultats et les empreintes sont enregistrés dans la
[qualification](controle-evaluation-frontiere-verification.json).

Les deux points d'entrée de la gate incluent le nouveau composant. La gate
shell reprend aussi les contrôles de génération, d'ouverture et de
normalisation déjà présents dans la gate PowerShell. `bash -n scripts/verify.sh`
passe ; la gate shell complète n'a pas été exécutée dans cette qualification.

Les premiers builds de développement de l'agent ont rencontré une différence
d'élaboration des motifs dépendants. Les corps littéraux ont été alignés avec
les sources originales ; l'égalité entière est ensuite prouvée par réduction.
La preuve de décision a aussi nécessité une annotation de type explicite.
Le client de l'agent principal a nécessité des imports et paramètres dépendants
explicites. Aucune attente sémantique ou de coût n'a été changée pour faire
passer ces corrections. Les journaux des essais restent conservés hors du dépôt.

La qualification est celle de l'arbre de travail sur
`codex/align-persist-recovery`, à partir de
`a620b54470645c3aba46f468d4f4669916f51a17`. Elle conserve les empreintes des
423 fichiers Lean, outils et configurations nommés, figées avant la gate.
Les qualifications de l'ouverture et de la normalisation restent historiques
et inchangées. Le registre et le plan canonique restent inchangés.

## Prochaine obligation

La formation de la préservation et son raccord à la décision sont traités.
Il reste à ouvrir l'application de ces transports à la continuation réellement
reçue, puis les requêtes de leur affectation transformée. `citationRouting`
et `citationAssignment` restent les primitives complexes explicites de cette
application ; cette tranche ne leur attribue pas le coût de leurs calculs
internes.

D2 comprend aussi le paiement et le majorant indépendant des bootstraps,
les autres indices exécutables, les frames et codecs, ainsi que les coûts
complets de composition, d'administration, de traces et d'allocations.
Les enveloppes globales et réserves de D3 puis le secours borné de D4 sur le
présent effectivement conservé et rechargé restent à fermer dans l'ordre du
plan. `RecoveryData.prepare` utilise encore `Memory.step` natif.
