# Plan de correction du certificat de l’agent constitutif

## 1 Objet et état de référence

Fermer les sept défauts précis de l’audit de l’agent, sans remplacer sa cible,
affaiblir ses garanties ni modifier les résultats antérieurs. La correction
porte d’abord sur les constructions et leurs consommateurs scientifiques ;
les tests et les contrôles compilés vérifient ensuite ces raccords.

Les sections 1 à 15 fixent le plan et ses obligations. L'implémentation est
désormais raccordée aux déclarations effectives relevées en section 16.
Le compte rendu local reste distinct du verdict indépendant : aucune case
de ce plan ne vaut nouvelle validation par Aristotle.

| Référence | Valeur |
| --- | --- |
| Dépôt | `JohnDoe-collab-stack/relational-perimeter` |
| Branche examinée | `codex/unified-foundation-master-instance` |
| Commit scientifique audité | `f6c6d2c051ae0886056d47cf5357253c137a1319` |
| Parent scientifique | `75057f09cc9a535e8be3390999fa688c9ee3a96d` |
| Ancien résultat computationnel validé | `4e0febf032821882069e7cfefd7e631fc8461d95` |
| Base de référence | `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685` |
| HEAD lors de la préparation | `9354e757e9dc2fbd429c34ff6cf9990140b6eed9` |
| Projet Aristotle | `9827d5fe-0cd1-40ce-9af6-69826c9af653` |
| Tâche Aristotle | `d5cd5c55-6aa0-418f-8ed8-31888eeae028` |
| Rapport | `audit/CONSTITUTIVE_AGENT_PERSISTENCE_AUDIT.md` |
| Verdict sur l’agent | `AGENT TARGET REQUIRES CORRECTIONS` |
| Verdict sur les acquis | `NO REGRESSION VERIFIED` |

Le rapport et ses matériaux bruts restent hors du dépôt. Ses sections 14 à 18,
les réponses Q01 à Q42 et les patches M02a, M04a2, M11a–c, M14, M15, M06c,
M18d et M20c fondent le diagnostic de ce plan.

L’arbre de travail contient aussi des modifications parallèles de l’unification
et des signatures de continuation. Elles ne sont pas le commit audité. Ne pas
les écraser, les annuler, les attribuer à cet audit ou les inclure silencieusement
dans la correction. Avant l’implémentation, relever leur diff et les interfaces
partagées nécessaires. Les scripts de vérification et d’analyse C sont notamment
des fichiers partagés.

Ce fichier est un document de chantier. Il doit être absent de l’arbre finalement
intégré dans `main`. La présente demande autorise sa préparation, pas un commit,
un push, une nouvelle soumission ou une fusion. La demande ultérieure
« implenente le plan » autorise les corrections locales, pas ces opérations Git.

## 2 Cible conservée sans substitution

L’exigence reçue reste exactement celle du protocole audité :

> Poursuivre le moteur autorisé depuis ses productions réelles ; ne restituer
> une valeur que pour une production effectivement formée et une variable du
> périmètre reçu ; restituer la valeur de cette production, non une valeur
> choisie par le contrôleur ; préserver les garanties d’acceptation annoncées
> par les actions utilisées ; conserver ces droits et ces accords après reprise.

Le critère d’achèvement reste également inchangé :

> La première instance est achevée lorsque l’exigence concrète gouverne ses
> autorisations, que sa production opérationnelle est celle du moteur réel,
> que ses réponses et refus satisfont la spécification indépendante, et que
> le suivi de ces garanties se compose sur toutes ses interactions finies.
>
> La mémoire complète doit permettre cette continuation tout en ne permettant
> pas de reconstruire uniformément le profil initial oublié. Cette propriété
> doit être réalisée sur des sources distinctes effectivement construites.
>
> L’ensemble doit être livré comme une instance construite et exécutable, non
> comme une liste d’interfaces abstraites supposées satisfaites. Le résultat
> scientifique sera ce paquet fermé ; la transposition à d’autres exigences ou
> à d’autres agents restera une nouvelle tâche de preuve.

Conserver la [spécification initiale de l’agent](PLAN_AGENT_CONSTITUTIF_PERSISTANCE.fr.md),
la [note scientifique de référence](../constitution-calcul-et-persistance-pour-ia.fr.md)
et la [cible sur la largeur exponentielle](../conclusion-largeur-exponentielle-conservation-identites.fr.md).
Cette correction ne les remplace pas par une simple liste de contrôles.

Les invariants protégés sont :

- les quatre fichiers fondamentaux, la licence et la toolchain ;
- la constitution des profils depuis l’histoire dépendante des rôles ;
- la production locale dans l’exécution et l’absence de lecture du futur ;
- l’action effective, sa préservation séparée et les fibres exactes du régime ;
- le `iff` de pleine largeur sur les régimes finis surjectifs, les largeurs
  `2^n`, un et `2^k` dans leurs domaines déjà démontrés ;
- les sources constituées distinctes, même lorsque leurs obligations coïncident ;
- le périmètre reçu, les quatre opérations et les motifs de refus existants ;
- le nombre exact d’étapes d’`obtain`, les anciennes lectures et les refus
  préservant la mémoire entière ;
- les accords riches/réduits pour toutes les interactions finies, y compris
  les refus, et les deux lois de retour des témoins d’admission ;
- la factorisation et la non-reconstruction du profil depuis la mémoire complète.

L’extensivité demeure une lecture en aval. Ne pas ajouter une énumération des
profils pour autoriser une réponse. Ne pas confondre longueur du registre et
largeur opérationnelle. Le lot n’ajoute aucune revendication de coût total,
mémoire physique constante, SAT général ou alignement humain universel.

## 3 Méthode appliquée à chaque raccord

Pour chaque correction, identifier dans cet ordre : les relations et témoins
disponibles, les occurrences constituées, le producteur effectif, ses ports
d’entrée, le consommateur, puis les accords nécessaires à la continuation.
Le même objet doit être suivi à travers ces passages ; une valeur égale ou un
label de provenance ne suffit pas à remplacer sa formation.

```text
exigence reçue et maître réellement constitué
    → code interprété sur ses rôles
    → cible normalisée et registre produits
    → mémoire courante et demande courante
    → lecture de la production désignée
    → autorisation et garantie contextuelle de cette production
    → réponse ou refus motivé
    → transports réels et mémoire suivante
    → composition sur toutes les interactions finies
```

Séparer explicitement :

1. les extensions de références, avec lecture, injectivité, positions et
   composition ; elles sont des prolongements, pas nécessairement des bijections ;
2. les actions dirigées sur continuations et leurs garanties de critère ;
3. les correspondances riches/réduites et les retours des témoins d’admission ;
4. la projection qui perd la distinction du profil initial sous le contrat annoncé.

Une preuve en `Prop` peut établir un accord. Elle ne doit pas remplacer une
provenance constitutive dans `Type` ni masquer une donnée non calculable.
Une égalité Lean ne démontre pas le partage physique de deux appels compilés.
Inversement, un contrôle du graphe C ne démontre pas les accords relationnels.

La consommation attendue est utile au résultat : éliminer l’origine pour
obtenir sa garantie, lire le support pour produire l’autorisation, transporter
les références pour construire le successeur. Ajouter une dépendance morte,
un contrôle de nom ou un champ final jamais utilisé n’est pas une correction.

## 4 Diagnostic et obligations de fermeture

| Défaut | Déclarations concernées dans `ConstitutiveSearch.Agent` | Ce qui doit être fermé |
| --- | --- | --- |
| F1 M02a | `Prepared`, `prepare`, `Prepared.memory`, `Prepared.certificate` | L’initialisation publique correspond au profil effectivement décodé ; un code invalide donne le refus annoncé. |
| F2 M04a2 | `TargetOrigin`, `AnswerTarget`, `Authorization`, `authorized_target_accepted` | La provenance produit une garantie consommée par la restitution, non une donnée adjacente. |
| F3 M11a–c | `initialRegisterRealization`, `materialRegister`, `sourcePerform`, `RichAuthorization` | La formation et la lecture riches proviennent du support et des ports réellement produits, pas d’un registre déclaré donné ou de sa projection. |
| F4 M14 | `FollowedStages`, `RequestStages`, `Followed`, `Certificate.followed` | Chaque étape interne transporte les deux supports distincts et ferme les accords de production et de successeur. |
| F5 M15 | `AnswerTarget.accepted`, `authorized_target_accepted`, `Certificate.retainedCriterion` | L’acceptation reste une conclusion construite, jamais une hypothèse externe de la même conclusion. |
| F6 M06c M18d | `check-agent-codegen.py`, entrées publiques et auxiliaires | Le contrôle suit les appels compilés transitifs et les voies de reprise réellement exposées. |
| F7 M20c | Manifestes et contrôleurs des échecs attendus | Seule l’erreur voulue, au site voulu, peut valider un refus de compilation. |

Ces constats portent sur le commit audité. Un patch qui change la proposition
annoncée ne réfute pas la preuve originale : il montre ici que son affaiblissement
n’est pas détecté. Maintenir donc les propositions à vérifier indépendamment
des définitions modifiées lors de la correction.

## 5 F1 Fermer l’initialisation publique

Fichiers principaux :
[PublicInstance](../../RelationalPerimeter/Agents/Constitutive/PublicInstance.lean)
et [tests des exigences](../../Tests/ConstitutiveAgentRequirements.lean).

### Construction

Construire un contrat d’initialisation sur `input`, `scope`, `code` et le résultat
effectif de `prepare` ou d’`initializeAgent`. Le placer dans `PublicInstance` :
`Persistence` ne doit pas importer `Prepared`, défini dans une strate ultérieure.

Le cas réussi doit fournir le maître exact déjà construit, l’exigence reçue,
le profil sélectionné avec `decodeSelection master.roles code = some profile`,
la mémoire `start master requirement profile` et le certificat de continuation
sur ces mêmes données. Le cas refusé doit établir le motif réel : périmètre
vide ou échec du décodage, avec la priorité existante.

`Prepared.certificate` doit exposer ce raccord d’initialisation en plus du
certificat de continuation, et non seulement appeler `certify master requirement`
en ignorant son lien avec le code reçu. Énoncer aussi les lois publiques de refus
des codes invalides et d’admission des codes construits par `encodeSelection`.

Le certificat scientifique peut être indexé par le code et le profil.
`Memory` et `Session` ne doivent pas conserver ces données. Ne pas lancer un
second maître pour obtenir le certificat : réemployer le paquet déjà préparé.

### Clôture

- Une initialisation réussie ferme les égalités de réception, décodage et mémoire.
- Le refus d’un code de mauvaise longueur est un théorème de l’API publique,
  pas seulement de `parseCode`.
- Les deux codes des profils effectivement distincts sont positivement admis.
- Un périmètre vide reste refusé avant toute initialisation inutile du maître.
- La modification M02a ne peut plus conserver ce contrat en ignorant le code.

Deux codes valides peuvent donner la même mémoire : c’est le résultat d’oubli,
non une erreur de décodage. Comparer seulement les mémoires ne suffit donc pas
à vérifier F1. La distinction doit être suivie dans le paquet scientifique
d’initialisation, puis sa perte démontrée dans la projection.

## 6 F2 et F5 Relier provenance et acceptation à la restitution

Fichiers principaux :
[ProducedEvidence](../../RelationalPerimeter/Agents/Constitutive/ProducedEvidence.lean),
[Execution](../../RelationalPerimeter/Agents/Constitutive/Execution.lean),
[Agreement](../../RelationalPerimeter/Agents/Constitutive/Agreement.lean)
et [Persistence](../../RelationalPerimeter/Agents/Constitutive/Persistence.lean).

### Construction depuis les témoins existants

La correction préférée est d’éliminer positivement `TargetOrigin` pour dériver
l’acceptation de sa continuation exacte. Les données nécessaires existent :

- le cas `.normalized license` désigne
  `retainedExecutedRoleOperationalTarget license` et dispose de
  `license.retainedAccepted` ;
- le cas `.resumed production` désigne l’output exact de l’application et
  dispose de `production.built.stage.outputAccepted`.

Construire une déclaration telle que `TargetOrigin.accepted`, puis faire
dépendre `AnswerTarget.accepted` de cette élimination. Si le champ d’acceptation
stocké devient redondant, le remplacer proprement par cette projection calculée,
en conservant les énoncés publics utiles. Ne pas maintenir deux voies concurrentes,
l’une constitutive et l’autre libre, vers la même garantie.

La provenance reste une donnée positive dans `Type`, indexée par la racine,
le contexte et la continuation. La garantie d’acceptation conserve sa portée
contextuelle : elle ne devient ni une preuve SAT globale, ni une équivalence
des contextes initiaux et repris.

### Consommateur et théorème fixé

À partir de l’occurrence réellement résolue par `Authorization`, construire
l’évidence de lecture produite et sa garantie contextuelle via cette origine.
La réponse certifiée et `authorized_target_accepted` doivent utiliser ce raccord.
Maintenir aussi une spécification indépendante de la réponse choisie.

Le théorème final doit conclure, pour toute réponse effectivement autorisée,
la lecture de la bonne continuation et son acceptation dans le bon contexte.
Il ne reçoit aucune hypothèse supplémentaire d’acceptation de cette cible.
Le champ `retainedCriterion` doit conserver cet énoncé sans le transformer en
`P → P`, et ce contenu doit entrer dans la satisfaction composée des réponses
sur les interactions finies.

Les fabriques `initialTargets` et `resumedTarget` doivent continuer à imposer
l’accord de sortie exécutée. L’acceptation seule ne permet pas d’introduire une
cible indépendante. Les garanties de préservation restent celles des actions
réelles déjà démontrées ; aucune nouvelle hypothèse n’est demandée à l’utilisateur.

### Clôture

- L’origine n’est plus remplacée par un tag sans perdre le raccord scientifique.
- L’acceptation est construite depuis le producteur de la cible et consommée
  par la garantie de réponse.
- Les cas initiaux et repris sont couverts, ainsi que les anciennes cibles après
  plusieurs reprises.
- La version M15, avec hypothèse externe, ne satisfait pas le théorème public fixé.
- La mémoire entière continue à factoriser par l’output produit. Aucun code,
  profil source ou payload gauche/droit oublié n’est réintroduit dans l’origine.

Une suppression de champ est légitime si sa garantie est reconstruite depuis
les mêmes données constituées et reste consommée. Exiger le maintien du sens,
pas la nécessité artificielle d’un champ syntaxique redondant.

## 7 F3 Certifier les formations et les lectures historiques

Fichiers principaux :
[State](../../RelationalPerimeter/Agents/Constitutive/State.lean),
[Agreement](../../RelationalPerimeter/Agents/Constitutive/Agreement.lean)
et [ConstructedSupport](../../RelationalPerimeter/Constitution/Resources/ConstructedSupport.lean)
comme interface existante à consommer, non comme fondation à remplacer.

### Formation

Raccorder la réalisation initiale à la chaîne exacte déjà exécutée sur le côté
scientifique : donnée initiale maître/profil, `normalizationProducer`,
`initialCursorProducer`, puis `componentProducer` et `installTargets`.

Le maître et le profil reçus peuvent être des ressources données. Leur bundle
normalisé et ses composantes ne peuvent pas être déclarés donnés à leur place.
Construire une évidence dépendante de cette formation, de ses ports, de ses
extensions et de leurs références. La garantie doit porter sur `Support.formation`
et les producteurs concernés, pas seulement sur l’égalité des valeurs lues.

Une formation `.given` ayant les mêmes valeurs ne possède pas, pour cette
seule raison, l’évidence de cette production `.produced`. Ne pas ajouter un
booléen « a été produit » ni un identifiant libre comme substitut.

### Lecture et admission riches

Produire la lecture riche depuis `realization.support.read (realization.reference ref)`.
Son témoin doit désigner l’occurrence, le support et la formation dont cette
valeur provient. Les autorisations riches consomment cette lecture et les
permissions reçues ; leur réalisation réduite consomme ensuite l’accord de
lecture avec le registre.

Si l’interface actuelle `sourcePerform : Source → Request → Source × Event`
n’expose pas cette dépendance, construire une opération riche munie de son
évidence et définir `sourcePerform` comme projection de cette opération.
Le certificat doit porter sur l’opération entière, ses ressources et ses lois,
pas seulement sur son résultat égal à celui du runtime.

Les observations et admissions riches ne doivent pas être définies par
`project` puis par l’implémentation réduite. Le partage de la logique de décision
indépendante reste permis lorsqu’elle reçoit les valeurs réellement lues du
support riche.

### Clôture et limite de la preuve

- Fermer la formation initiale et chaque formation après reprise.
- Fermer le carré registre/support, les lectures, l’injectivité, les positions
  et la composition des extensions.
- Fermer `RichAuthorization.realize`, son inverse et les deux lois de retour
  avec ces évidences, sans supposer une lecture riche indépendante correcte.
- Le certificat consomme la formation et la lecture de l’opération riche entière.
- M11a–c ne doivent plus pouvoir supprimer ce raccord tout en le prétendant fermé.

Une égalité de résultats ne prouve pas quel chemin de lecture a été utilisé.
Des programmes observationnellement égaux peuvent garder les mêmes lois
extensionnelles. La correction doit donc porter sur la construction munie de
ses ressources, pas promettre qu’une équation de valeurs seule distingue toutes
les implémentations. Une reconstruction positive du même raccord demeure valide ;
une projection accompagnée d’une provenance décorative ne le remplace pas.

La source riche reste scientifique. Ne pas l’appeler dans le runtime pour
justifier chaque réponse ; cela réintroduirait l’archive et un second calcul.

## 8 F4 Fermer le suivi de toutes les étapes internes

Fichiers principaux : [State](../../RelationalPerimeter/Agents/Constitutive/State.lean),
[Agreement](../../RelationalPerimeter/Agents/Constitutive/Agreement.lean)
et [Persistence](../../RelationalPerimeter/Agents/Constitutive/Persistence.lean).

### Évidence d’une étape

Renforcer le nœud d’étape suivi sur sa source courante, sa production effective
et son successeur. Il doit construire conjointement :

1. la production de tête entière et son accord avec le moteur vivant ;
2. la cible issue de son application, son origine et sa garantie contextuelle ;
3. le registre successeur formé en ajoutant précisément cette cible ;
4. l’extension du support moteur, de `source.cursor.support` au support du
   curseur produit, depuis `cursorReferences` et les extensions effectives ;
5. l’extension distincte du support historique des cibles, depuis
   `RegisterRealization.advance` ;
6. le transport des anciennes références, leurs lectures, injectivité et positions,
   avec leur composition sur le préfixe reçu ;
7. les accords de mémoire suivante, d’événement et de persistance du périmètre.

Éviter `realizationExact : realization = réalisation canonique` comme unique
contenu : cette égalité doit relier les constructions et être utilisée pour
leurs lectures et transports. Ne pas confondre l’extension depuis la source
courante avec `History.references`, qui compose depuis le maître initial.

### Récursion et frontière de demande

Construire ces évidences dans l’ordre des têtes produites par `runSteps` ou
son raccord riche. La queue commence au successeur exact de la tête. Aucun
futur n’est un argument du producteur de tête. La spécification riche peut
décrire ces productions ; elle ne commande pas une réexécution runtime.

Pour `advance count`, suivre exactement `count` productions. Pour `obtain`,
suivre exactement `needed r h` productions lorsque la variable est permise.
Pour une lecture, une proposition ou un refus hors périmètre sans avancement,
le suivi contient zéro production interne, avec le motif approprié.

Les réponses appartiennent à la demande : ne pas inventer une réponse utilisateur
à chaque étape interne. Chaque étape ferme l’acceptation de son output et les
accords de transition ; la frontière de demande ferme `ResponseEvidence` sur
le registre réellement atteint.

### Consommateur final

`Certificate.followed` doit fournir une évidence dont les projections donnent
ces lois à toute étape réelle, avec raccord à la liste d’événements et à la
mémoire finale de l’exécuteur. Des extracteurs de production doivent permettre
de lire les deux transports, la cible et leurs accords à chaque tête.

Ne pas laisser la définition modifiable de `RequestStages` constituer à elle
seule la spécification de « suivi complet ». Fixer les obligations sur les
productions de l’exécuteur ; remplacer le suivi par `Unit` ne doit plus les fermer.
Réutiliser ensuite cette évidence pour composer les accords sur toute suite
finie de demandes, pas seulement sur ses frontières.

## 9 Fermer le certificat composé et préserver l’oubli

Le certificat final doit réunir les lots précédents sans import inverse ni
paramètre scientifique extérieur supplémentaire. Le contrat d’initialisation
reste dans `PublicInstance` ; les lois de continuation restent dans `Persistence`.

Compléter les pins déjà existants par : l’évidence de provenance consommée,
la formation et la lecture riches, les deux transports à chaque étape interne,
la garantie contextuelle inconditionnelle et la localité de la mémoire entière
de tête. L’exactitude de l’événement seule ne suffit pas à cette dernière.

Construire `certify` sur l’instance et l’exécuteur existants. Les garanties
doivent être accessibles depuis `import RelationalPerimeter` et consommées
par le théorème composé de satisfaction, pas disponibles seulement dans les tests.
Ne pas créer un second certificat faible conservé comme voie publique alternative.

Après tout changement des cibles ou des autorisations, reprendre les preuves
sur le type complet de `Memory`, y compris les données de provenance retenues :

- `agent_memory_factors_through_output` ;
- `initial_memories_equal` pour les profils effectivement distincts ;
- `initial_profile_not_recoverable` ;
- `forgotten_sources_same_future` ;
- les admissions dans les deux sens et leurs retours sur témoins.

La réception conserve le code uniquement dans le paquet scientifique de
préparation. La source riche peut conserver l’histoire et ses évidences.
La reprise runtime ne les stocke ni ne les consulte. Ne pas restreindre la
mémoire du théorème à une projection plus petite pour sauver l’oubli.

## 10 F6 Corriger le contrôle de l’exécution compilée

Fichier principal : [check-agent-codegen.py](../../scripts/check-agent-codegen.py).
Réemployer l’analyseur local et coordonner ses modifications avec celles du
lot d’unification, sans écraser ses changements. Ne pas importer les outils
de l’archive d’audit comme dépendance technique ou scientifique.

### Couverture

Inventorier les entrées publiques réellement générées, notamment `publicAgent`,
`prepare`, `initializeAgent`, `Prepared.memory`, `Session.ofMaster`,
`Session.execute`, `Session.produce`, `Session.executeAll`, `executeRequests`,
`executeInput`, `executeProducedInput`, `runSteps`, `step` et `decideReply`.
Une entrée attendue absente ou ambiguë ne doit pas être silencieusement ignorée.

Séparer les catégories : initialisation pouvant construire le maître une fois ;
initialisation depuis un maître déjà reçu ; reprise n’ayant pas le droit de
reconstruire le maître ou l’histoire riche ; découverte avec ses propres
exclusions de lectures d’image et de frontière.

Suivre transitivement les auxiliaires, les objets de producteurs, les cibles
statiques de fermetures et les initialisateurs. Compter les sites d’application
avec leur multiplicité, pas seulement les noms uniques de fonctions atteignables.
Respecter les branchements et les bornes de récursion : la production par étape
n’est pas la production totale d’un `advance count`.

La reprise doit exclure les dépendances d’archive, de préparation et d’énumération
globale des profils. La lecture locale à deux occurrences du moteur existant
reste distincte de cette énumération et ne doit pas être interdite arbitrairement.

### Contrôles et portée

Vérifier le programme compilé réel, puis des copies isolées exerçant M06c
et M18d : auxiliaire non inliné portant une production supplémentaire ; voie
de session réintroduisant le calcul maître. Inclure la double application d’une
même fermeture afin de ne pas répéter le défaut du contrôle d’unification.

Une duplication effectivement éliminée par le compilateur n’est pas une double
exécution. Une branche encore présente dans le graphe C peut nécessiter une
analyse conservatrice même si une preuve Lean la dit inaccessible. Distinguer
ces situations dans les diagnostics.

Le contrôle doit indiquer sa couverture et échouer explicitement lorsqu’un
appel indirect nécessaire ne peut pas être résolu. Ce n’est ni une preuve
universelle de multiplicité des appels, ni un théorème de coût ou de mémoire
physique. Ne pas publier une garantie plus forte que son analyse.

## 11 F7 Vérifier la cause des refus de compilation

Fichiers principaux :
[manifestes](../../scripts/expected-failures.tsv),
[contrôleur Bash](../../scripts/check-expected-failures.sh),
[contrôleur PowerShell](../../scripts/check-expected-failures.ps1)
et [autoévaluation des contrôleurs](../../scripts/test-expected-failure-gates.py).

Remplacer la recherche d’un texte arbitraire dans toute la sortie par le contrôle
d’un diagnostic émis par Lean : fichier, position de l’expression voulue, sévérité,
classe d’erreur et contenu caractéristique. Utiliser la sortie structurée si elle
est disponible sur la toolchain, sinon un parseur explicite des diagnostics avec
positions. Ne pas supposer cette disponibilité sans la vérifier.

Le manifeste commun doit identifier le site attendu et le motif spécifique.
Une sortie `#eval` qui imprime ce motif n’est pas un diagnostic. Une erreur de
syntaxe, un import manquant, un timeout, un processus interrompu ou un fichier
absent ne peuvent pas valider un refus de type dépendant à un autre endroit.
Rejeter également toute erreur supplémentaire non prévue : la présence d’un
message attendu ne doit pas masquer la véritable cause de l’échec. Les fixtures
de compilation ne doivent pas exécuter d’opérations d’affichage destinées à
imiter les diagnostics. Si une fixture produit légitimement plusieurs erreurs,
leur ensemble attendu doit être explicite plutôt que toléré indistinctement.
Les deux contrôleurs doivent appliquer exactement la même classification.

Vérifier les cas suivants sur des copies jetables : le refus voulu ; la fixture
qui compile ; le mauvais diagnostic ; le bon texte imprimé avec une autre erreur ;
la bonne classe au mauvais site ; un timeout ; une fixture manquante ou non
inventoriée. M20c doit échouer comme contrôle du contrôleur.

La confidentialité d’un constructeur et l’impossibilité sémantique d’un objet
étranger restent deux catégories distinctes. Un échec de `#check X.mk` ne prouve
pas à lui seul l’impossibilité d’un certificat scientifique falsifié.

Les petites autoévaluations sont des contrôles du dispositif, pas des expériences
confirmatoires de performance. Conserver les sorties de référence et versionner
tout protocole scientifique déjà cité qui doit changer.

## 12 Ordre d’implémentation et fichiers concernés

| Lot | Travail | Condition avant le lot suivant |
| --- | --- | --- |
| 0 | Relever le diff courant, les interfaces parallèles et les références protégées ; fixer les obligations publiques à conserver. | Aucun travail parallèle écrasé ; aucune cible substituée. |
| 1 F1 | Contrat d’initialisation et refus publics dans `PublicInstance`. | Codes réels, mémoire exacte et refus fermés sans conserver le profil dans la session. |
| 2 F2 F5 | Élimination de l’origine, acceptation dérivée, consommateur de restitution et loi inconditionnelle. | Cible et réponse réellement justifiées dans leur contexte ; oubli toujours démontré. |
| 3 F3 | Formation du support riche, lecture munie de ses ressources et admission indépendante. | Les accords portent sur les productions et lectures exactes, pas seulement sur des listes égales. |
| 4 F4 | Suivi de chaque étape avec les deux extensions et leurs compositions. | Étapes de `advance` et d’`obtain` raccordées au même exécuteur. |
| 5 | Certificat composé, localité entière, interactions finies et oubli complet. | Toutes les obligations scientifiques fermées par les producteurs effectifs. |
| 6 F6 F7 | Analyse C et contrôle des diagnostics, intégrés aux deux verifiers. | Les cas oubliés par l’audit sont correctement distingués et détectés. |
| 7 | Documentation bilingue et vérification finale de non-régression. | Même portée en français et en anglais ; aucune garantie seulement annoncée. |

Conserver les sept modules de la couche `Agents/Constitutive` et leurs rangs
terminaux. Une petite interface dépendante peut être ajoutée dans le module
qui possède ses données ; ne pas introduire une nouvelle fondation, un carrier
de remplacement ou une bibliothèque parallèle de compatibilité.

Les trois fichiers `Tests/ConstitutiveAgent*.lean` doivent utiliser le certificat
composé pour exercer les garanties finales avec leurs énoncés fixés. Leurs tests
ne remplacent ni les constructions de production ni les démonstrations.
Une nouvelle fixture ou un fichier de test doit être déclaré dans tous les
inventaires appropriés, le build et le balayage des constantes.

## 13 Vérification des preuves et absence de régression

### Obligations scientifiques

Préparer une table finale par défaut : producteur, ressources d’entrée,
occurrence et indices, consommateur, transport ou loi, champ du certificat,
théorème de production et constat de fermeture. Aucun défaut F1 à F7 ne doit
être déclaré corrigé à partir d’un commentaire ou d’un nom de test.

Compiler un client important seulement `RelationalPerimeter`, qui consomme le
certificat final pour obtenir l’initialisation exacte, la réponse avec son
origine et son critère, les lectures riches, les deux transports à chaque
étape et l’oubli dans la mémoire entière. Les lois nécessaires doivent d’abord
exister en production ; un résultat montré seulement dans ce client est
encore un raccord à intégrer.

Contrôler au minimum : codes valides et invalides ; scopes distincts sur la même
lecture ; proposition correcte et opposée ; absence de handle ; priorité du
refus hors périmètre ; `obtain` absent, déjà disponible et distant ; plusieurs
étapes internes ; deux queues partageant la même tête ; anciennes lectures
après plusieurs demandes ; mêmes futurs après deux initialisations distinctes.
Ces exemples positifs contrôlent aussi que les garanties ne sont pas vacues.

Rejouer les modifications pertinentes de l’audit seulement après construction
des raccords, dans des copies isolées. Adapter honnêtement les interfaces sans
changer la cible. Un rejet doit porter sur l’accord voulu, pas sur un nom
supprimé, un warning, une erreur de préparation ou un timeout. Une reconstruction
positive de la même garantie est légitime et doit être identifiée comme telle.

### Construction et calculabilité

Tous les fichiers Lean créés ou modifiés restent strictement constructifs.
Aucun `axiom`, `sorry`, `admit`, `noncomputable`, `Classical`, `native_decide`,
`unsafe` ou `implemented_by` ; aucune dépendance manuscrite à `propext`,
`Quot.sound` ou à un autre axiome. Aucune extension fonctionnelle interdite
pour obtenir une égalité de mémoires ou de lecteurs.

Les données dans `Type` doivent compiler et produire leurs témoins. Chaque
fichier possède exactement un bloc `AXIOM_AUDIT` final, avec tous les noms
principaux valides. Mettre à jour le bloc existant, sans en ajouter un second.
Effectuer le balayage exhaustif des constantes ; les exceptions générées
doivent être identifiées par leur origine et aucun consommateur manuscrit
ne peut en dépendre.

Comparer les énoncés et la couverture de régression avec le commit audité,
le parent scientifique et le résultat computationnel validé. Les quatre
fondations, la licence, la toolchain et les figures existantes restent intacts.
Les modifications parallèles des descendants doivent être examinées séparément,
pas supprimées pour retrouver artificiellement les anciennes empreintes.

### Vérification finale sur un arbre identifié

Après accord sur les modifications parallèles, relever l’état exact et exécuter :

```text
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
lake update
```

Comparer le manifeste avant/après `lake update`. Vérifier les sources construites,
les modules accessibles depuis le root, l’inventaire de stratification et les
liens locaux. Les listes sélectionnées par Bash et PowerShell doivent être
identiques à normalisation des chemins près.

Relever les versions, plateformes, commandes complètes, empreintes et sorties.
Exécuter PowerShell sur Windows lorsqu’il est disponible : son exécution sur
Linux ne valide pas Windows. Ne pas effacer les éléments `NOT RUN` en lisant
simplement un script. Les wrappers de reproduction destinés au nouvel audit
doivent être exécutés de bout en bout sur des clones frais lorsqu’ils existent,
et pas seulement syntaxiquement vérifiés.

## 14 Documentation et nouvelle soumission

Mettre en accord, après fermeture du code :

- [présentation française de l’agent](../agent-constitutif-et-persistance.fr.md) ;
- [présentation anglaise](../constitutive-agent-and-persistence.en.md) ;
- [note scientifique](../constitution-calcul-et-persistance-pour-ia.fr.md) ;
- [présentation des résultats](../resultats-constitution-calcul-alignement.fr.md) ;
- README, en-têtes des modules et tableau de réalisation du plan initial.

Présenter les dépendances réellement consommées, les garanties du certificat,
les contrôles compilés et leurs limites dans des catégories distinctes. Conserver
les conclusions auditées sur la continuation et l’oubli ; ne pas élargir leur
portée aux coûts ou à tous les agents. Le présent audit ne doit plus être marqué
en attente, ni présenté comme une validation complète de l’ajout.

Un nouveau prompt indépendant reprendra l’exigence et le critère d’achèvement
inchangés. Il indiquera le dépôt, la branche effectivement publiée, le SHA
scientifique distant exact, ses bases, le rapport antérieur et les sept raccords
à examiner, avec les commandes et preuves attendues. Aucun champ à remplir
ne doit rester dans le prompt livré.

La préparation d’une nouvelle branche publiée, son commit, son push, l’appel
à Aristotle et une fusion sont des actions distinctes qui nécessitent les
demandes correspondantes. Ne pas les effectuer sur la seule autorisation de
rédiger ce plan. Ne pas fusionner un paquet encore matériellement qualifié.

## 15 Critères de clôture sans approximation

La correction est prête pour l’audit indépendant uniquement lorsque :

- [x] F1 relie l’entrée reçue à son décodage, son refus éventuel et sa mémoire.
- [x] F2 consomme la provenance de chaque cible dans sa garantie de restitution.
- [x] F3 ferme la formation et la lecture riches indépendantes sur leurs ressources.
- [x] F4 suit chaque étape effective, ses deux supports et leurs transports composés.
- [x] F5 conserve l’acceptation inconditionnelle dans le certificat et le suivi fini.
- [x] La production entière et la mémoire de tête sont locales à la demande courante.
- [x] La mémoire complète conserve le contrat et ne reconstruit pas le profil oublié.
- [x] F6 couvre les entrées publiques et les auxiliaires dans le code compilé réel.
- [x] F7 rejette une erreur sans rapport avec le diagnostic et le site attendus.
- [x] Les constructions positives sont exécutables et les preuves manuscrites sans axiomes.
- [x] Les acquis antérieurs restent démontrés avec leur portée et leurs carriers exacts.
- [x] Builds, vérifications, manifeste, stratification et liens sont contrôlés sur l’état final.
- [x] Les documents français et anglais décrivent uniquement ce qui a été fermé.

Ces cases consignent la réalisation locale vérifiée le 5 octobre 2026, détaillée
en section 16. Elles ne signifient pas qu'un nouvel audit indépendant a été
effectué. La réussite locale ne remplace pas ce verdict et le verdict ne
remplace pas la fusion explicitement autorisée et sa vérification.

Si un raccord ne peut pas être construit, décrire la signature, les données
manquantes et la garantie qui reste ouverte. Ne pas compenser par une prémisse
externe, une preuve adjacente, une restriction du contrat, une cible différente
ou un contrôle qui ne vérifie que le nom d’une déclaration.

## 16 Réalisation des corrections et contrôles locaux

La cible et le critère de la section 2 sont conservés. Les corrections portent
sur les sept modules existants de l'agent, sans nouvelle fondation ni carrier.
`Requirement` et `Execution` gardent leurs comportements ; `Prepared.certificate`
renvoie désormais le paquet d'initialisation et de continuation. Le champ
d'acceptation indépendant de `AnswerTarget` est remplacé par une loi dérivée
de son origine. Ce sont des renforcements explicités, pas des alias de
compatibilité ou des changements silencieux de contrat.

| Défaut | Production, ressources et consommateur | Accord final |
| --- | --- | --- |
| F1 | `prepare` reçoit le scope et le code ; `Prepared.prepare_exact` élimine leurs décisions effectives ; `Prepared.certificate` réutilise le maître de ce résultat. | `InitializationCertificate.initialized`, `received`, `decoded`, `memoryExact` et `continuation` ; lois publiques des sélections invalides. |
| F2 | `TargetOrigin.accepted` élimine la licence de normalisation ou la production reprise ; `AnswerTarget.accepted` et l'autorisation consomment cette origine. | Critère contextuel de la cible, sans champ indépendant ni prémisse d'acceptation extérieure. |
| F3 | `HistoricalFormation` est indexée par le support réel et ses extensions de producteurs ; `MaterialReading` porte les références exactes ; ses valeurs sont calculées par lecture du support, non fournies. `RichOperation.result` élimine la lecture et la décision de `sourceProduced`. | Formation et lecture riches dans `Certificate`, résultat riche exact et accords de `sourcePerform_exact` ; `HistoricalFormation.not_given` exclut le support de cibles déclaré donné. Le graphe compilé exclut le recours au répondeur projeté sur ce chemin riche. |
| F4 | Chaque `InternalStepAgreement` relie la production réelle, sa cible, son critère, l'extension du moteur courant et l'extension historique ; `FollowedStages` compose ces deux extensions. | `execution_exact`, `engineTransport`, `historicalTransport`, leurs lectures et les lois d'injectivité/position des extensions ; mémoire finale et événements exacts dans `Followed`. |
| F5 | `ReplyCriterion` exige l'autorisation et l'acceptation contextuelle ; `RequestEvidence.criterion` l'obtient des réponses produites ; `Followed.satisfies` compose sur le véritable exécuteur. | `Certificate.satisfaction : FiniteResponseCriterion`, sans prémisse ouverte d'acceptation ni changement en implication conditionnelle. |
| F6 | L'analyse C suit les wrappers publics, auxiliaires, alias et fermetures ; elle compte les applications par branche et dépliage déclaré. | Une fabrique maître au maximum à l'initialisation, une route de requête et une production vivante par tête ; pas de reprise du maître dans la session. Les cycles auxiliaires ou appels indirects nécessaires non résolus ne sont pas acceptés à coût nul. |
| F7 | Les wrappers Bash et PowerShell délèguent au même `expected_failure_diagnostics.py`. Le manifeste fige 25 sites d'erreur dans 23 fixtures. | Diagnostic JSON Lean, site et motif exacts, ensemble d'erreurs fermé ; sortie imprimée, mauvais site, erreur supplémentaire, fichier absent ou interruption ne valident pas un refus. |

Les lois de tête entière, de persistance de l'exigence, de conservation des
anciennes lectures et d'irrécoverabilité dans la mémoire entière restent en
production. Les trois tests publics consomment le certificat composé et les
accords, notamment `initialized_memory_keeps_finite_contract`. La seule
adaptation du travail parallèle est la preuve `ReachableAgent.update_exact`,
qui utilise maintenant la loi publique `sourcePerform_obtain` ; son énoncé
et son interprète n'ont pas été changés.

Les cas M06c et M18d ont été repris hors du dépôt : modules modifiés élaborés
contre les dépendances construites, avec le setup du paquet et génération C.
Le contrôleur détecte respectivement deux appels effectifs et le recalcul du
maître depuis `Session.execute`. Ce contrôle ciblé n'est pas présenté comme
un rebuild intégral de toutes les mutations de l'audit. Les autoévaluations
finies exercent aussi le partage, la double application d'une fermeture,
les diagnostics et les inventaires. Le timeout et les interruptions sont
exercés par simulation du résultat de processus ; aucun timeout réel n'est
rapporté comme un résultat Lean.

L'analyse compilée complète les constructions ; elle ne prouve ni un coût
total, ni une propriété universelle de tout C, ni l'inégalité observationnelle
de programmes extensionnellement équivalents. La formation et les ports
ferment l'accord scientifique ; le graphe compilé contrôle les voies présentes
dans ces artefacts précis.

### 16.1 Vérification de l'arbre réalisé

Les contrôles suivants ont été exécutés le 5 octobre 2026 dans le worktree
`perimeter-unified-master-instance`, sur la branche
`codex/unified-foundation-master-instance`, HEAD
`9354e757e9dc2fbd429c34ff6cf9990140b6eed9` avec les corrections non commitées.
Le résultat porte sur cet arbre de travail, pas sur le seul contenu de HEAD.
Les ajouts parallèles déjà présents ont été conservés et inclus dans le build.

Plateforme : Windows, Lean 4.33.1
(`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Git Bash et PowerShell 7.

| Contrôle exécuté | Résultat |
| --- | --- |
| `lake clean`, puis `lake build +RelationalPerimeter` | Succès, 173 jobs, aucun avertissement Lean. |
| `lake build` après ce build propre | Succès, 201 jobs, aucun avertissement Lean. |
| `bash scripts/verify.sh` et `pwsh -NoProfile -File scripts/verify.ps1` | Succès sur Windows ; même ensemble de 199 fichiers Lean, y compris les fichiers non suivis du chantier parallèle. |
| Balayage axiomatique exhaustif | 18 932 constantes dans 198 modules audités ; zéro dépendance axiomatique manuscrite. Les 360 exceptions sont générées et classifiées. |
| Inventaire et frontières des imports | 172 modules de production couverts, frontières appliquées, aucun orphelin. |
| Audits finaux et constructivité | Un seul bloc final par fichier ; aucun terme interdit ; tous les noms audités existent. |
| Contrôles C de l'agent | Succès, wrappers et auxiliaires inclus ; lectures riches effectives, bornes par tête et absence de reprise de la fabrique maître vérifiées. |
| Fixtures d'échec | 23 fixtures, 25 sites d'erreur figés ; diagnostics structurés et absence d'erreur supplémentaire contrôlés par les deux wrappers. |
| `test-expected-failure-gates.py` | 20 cas passent : 2 parcours nominaux complets et 18 refus attendus ; contrôles simulés de statut, timeout et identité du diagnostic en complément. |
| Régression | Les tests antérieurs restent construits. Aucun nom de déclaration des sept modules de l'agent n'est supprimé par rapport à `f6c6d2c`. Ce dernier contrôle est un inventaire, pas à lui seul une preuve de non-régression. |
| Éléments protégés | Quatre fondations, licence, toolchain, manifeste et figures identiques au commit audité. |
| `lake update` | Succès ; manifeste inchangé, SHA-256 `558A6999B82D0FAC6C385DA1A5CABEB50A594D6ECC7996F0BE33014CFB68AFA8`. |
| Documentation | Versions française et anglaise mises en accord ; 140 liens locaux contrôlés dans les sept documents concernés, aucun lien manquant. |
| `git diff --check` | Succès. Les messages Git sur la conversion LF/CRLF ne sont pas des avertissements Lean. |

Les commandes Windows ont utilisé
`C:/Users/frederick/.elan/bin/lake.exe`,
`C:/Program Files/Git/bin/bash.exe` et
`C:/Users/frederick/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe`.
`RELATIONAL_PERIMETER_PYTHON` désignait
`C:/Users/frederick/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`.
Le test des wrappers a été lancé avec
`scripts/test-expected-failure-gates.py --output C:/Users/frederick/AppData/Local/Temp/constitutive-agent-correction-20261005/fixture-gates-v3`.

Les journaux locaux sont hors dépôt, dans
`C:/Users/frederick/AppData/Local/Temp/constitutive-agent-correction-20261005/` :
`build-root-final.log`, `build-all-final.log`, `verify-bash-final-v2.log`,
`verify-powershell-final.log` et `fixture-gates-v3/results.json`.
Les runs précédents n'ont pas été écrasés.

### 16.2 Artefacts des contrôles et limites de livraison

Empreintes SHA-256 des contrôles de la première réalisation, avant la reprise
de F7 documentée en section 16.3 :

| Fichier | Empreinte |
| --- | --- |
| `scripts/check-agent-codegen.py` | `43C9A6564C72559F34FC36FDABD76B036E0D602699E64819086A9D18D767270C` |
| `scripts/expected_failure_diagnostics.py` | `63996DCD1530BEC5F0018B36D122CE998E1E76BEC637C6A5B2A15CE024575ECA` |
| `scripts/check-expected-failures.sh` | `EABA71973BC60E30D80AFE0E278496B22DC6E49D955924D919089C0EA45614F5` |
| `scripts/check-expected-failures.ps1` | `14CF8B28A347EE00F2D6F60402D1C34F21273C4FC360330614DACD6CC96C44A7` |
| `scripts/expected-failures.tsv` | `C48EE20C09E4653E9F503353BA1EF5DC5979EC866EFAE05F09B7CC7839E8E51F` |
| `scripts/test-expected-failure-gates.py` | `9FEDA63FDF49636E93355B575588525A77855B2170BFE6B89453898D2B80B831` |

Aucun commit, push, changement de branche, nouvel appel à Aristotle ou fusion
n'est effectué dans ce lot. Un prompt annonçant une nouvelle révision distante
ne serait pas exact avant sa publication autorisée. Les contrôles locaux sont
terminés ; le nouvel audit indépendant et l'intégration ne le sont pas.

### 16.3 Reprise de F7 après une contre-vérification

La contre-vérification a trouvé un contournement réel du premier filtre :
`run_cmd` précédé d'un commentaire n'était pas reconnu. Dans une copie
temporaire, une commande fabriquait exactement le diagnostic attendu au
site figé, sans erreur de typage. Les deux wrappers acceptaient cette fixture.
Les premiers vingt cas ne couvraient donc pas cette possibilité ; leur succès
ne suffisait pas à fermer F7. Aucun fichier de production Lean n'a été modifié
par cette contre-vérification ou par sa correction.

`fixture_code` analyse désormais les commentaires de ligne, les commentaires
de bloc imbriqués, les chaînes ordinaires et brutes et les identifiants cités,
en préservant les positions. `validate_source` inspecte les tokens hors de ces
régions et refuse les commandes et tactiques de fabrication de diagnostic,
même après un commentaire, un attribut ou un modificateur. Seuls `#check` et
`#print` sont permis parmi les commandes préfixées par `#`. Les chaînes
interpolées sont exclues de cette politique de fixture. Ce n'est pas une preuve
de sécurité de Lean arbitraire ou de tout mécanisme d'élaboration imaginable.

La détection distingue notamment la tactique de diagnostic `trace` du champ
légitime `normalization.trace`. Le premier run de la reprise avait refusé à
tort ce champ et échoué sur les deux parcours nominaux ; son journal n'a pas
été écrasé. Le contrôle lexical positif et les deux parcours nominaux du run
final vérifient la correction de ce faux positif.

Le run final de `test-expected-failure-gates.py` passe 28 cas : deux parcours
nominaux et 26 refus attendus. Les nouveaux refus incluent le contournement
exact par `run_cmd`, sa variante à commentaire imbriqué, `#eval` après un
commentaire et une tactique qui fabrique un message. Les contrôles unitaires
exercent aussi les modificateurs, les chaînes, les fins de ligne CR et CRLF,
les fragments lexicaux non terminés et l'interdiction avant appel au compilateur.

Les résultats et les journaux de ce run sont conservés hors dépôt dans :

```text
C:/Users/frederick/AppData/Local/Temp/agent-f7-repair-a6677bebb9d2497bb74ee5e2289c2bb7/
```

`results.json` contient les 28 résultats. Les journaux `commented-run-cmd-bash.log`
et `commented-run-cmd-powershell.log` consignent le refus du contournement
reproduit. Le run initial avec le faux positif est conservé séparément dans
`C:/Users/frederick/AppData/Local/Temp/agent-f7-repair-6c6c1996a8d64859913eca428fe8f566/`.

Empreintes des deux scripts figés avant le run final :

| Fichier | SHA-256 |
| --- | --- |
| `scripts/expected_failure_diagnostics.py` | `90BF7692A37DBE4D9F8707D54653BA6B845DCBE5EBCEB6AAC717E5BE6305640D` |
| `scripts/test-expected-failure-gates.py` | `5B0DDD0AC85D8A5DD9FC20844F14AADA49ECEC2386A960FF5408DEBAEB2449D9` |

Les deux vérifications complètes, `bash scripts/verify.sh` et
`pwsh -NoProfile -File scripts/verify.ps1`, passent également sur Windows :
199 fichiers Lean vérifiés, 18 932 constantes dans 198 modules audités et zéro
exception axiomatique manuscrite. Leurs journaux sont `verify-bash.log` et
`verify-powershell.log` dans le répertoire du run final. Ce sont des builds
incrémentaux sur les artefacts construits, pas de nouveaux builds propres.
Les empreintes des sources Lean, des fixtures et du manifeste sont inchangées
par rapport à l'état d'avant la reprise F7. Les travaux parallèles sont préservés.

Les fixtures, leurs sites attendus et leurs motifs n'ont pas été modifiés.
Cette reprise concerne leur validation, non la cible scientifique, les
constructions de l'agent ou leurs preuves. Aucun commit, push ou nouvel audit
indépendant n'est effectué dans cette reprise.

### 16.4 Reprise de F7 : littéraux de caractère

La contre-vérification suivante a reproduit un second contournement : deux
caractères guillemets étaient pris pour les délimiteurs d'une chaîne. Une
commande `run_cmd logError` placée entre eux échappait au filtre et fabriquait
le diagnostic au site figé. Les deux wrappers acceptaient cette fixture.
Les vingt-huit cas précédents ne couvraient donc pas cette faille.

`fixture_code` reconnaît maintenant un caractère unique ou un échappement
pris en charge, avec son apostrophe fermante. Il ne cherche pas une apostrophe
plus loin dans le code exécutable. Il distingue ces littéraux des suffixes
d'identifiants comme `head'`. Une forme incomplète ou non prise en charge est
refusée. Les positions et les fins de ligne restent conservées.

Empreintes des scripts figés avant le nouveau run :

| Fichier | SHA-256 |
| --- | --- |
| `scripts/expected_failure_diagnostics.py` | `802E1F5E09E964337B2DCFACE72DA8D0B930A22CE48C3ADB8816EED35591220E` |
| `scripts/test-expected-failure-gates.py` | `41BB08925291922D76ABD852E2896814285AB6A6790A278499D24F0F93685A72` |

Le nouveau run passe 32 cas : deux parcours nominaux de 23 fixtures chacun
et 30 refus attendus. Les quatre nouveaux refus couvrent les caractères
guillemets ordinaires et échappés sur Bash et PowerShell. Les contrôles
unitaires vérifient aussi les échappements, les caractères Unicode, les
suffixes d'identifiants, les fragments mal formés et la conservation des
positions. Les imitations par commentaire ou caractères guillemets sont
refusées avant tout appel au compilateur, ce que vérifie un contrôle dédié.

`bash scripts/verify.sh` et `pwsh -NoProfile -File scripts/verify.ps1` passent
sur Windows, chacun sur 199 fichiers Lean. Les 14 déclarations du client
public `ReviewClient.lean` compilent sans axiome. `git diff --check` passe.
Aucun fichier Lean, fixture, site attendu, manifeste ou fichier du chantier
parallèle n'a changé pendant cette reprise.

Commande des tests :

```text
scripts/test-expected-failure-gates.py --output C:/Users/frederick/AppData/Local/Temp/agent-f7-character-repair-de4cbc8143ef4128a714eb31e9b15dd5
```

Ce répertoire hors dépôt conserve `results.json`, les quatre journaux
`character-run-cmd-*.log` et `escaped-character-run-cmd-*.log`, ainsi que
`verify-bash.log`, `verify-powershell.log` et `public-client.log`.
La reproduction réussie du contournement avant correction reste dans
`C:/Users/frederick/AppData/Local/Temp/agent-f7-careful-review-bf45e58b564b448e82746735a6e65b9d/`.
Aucun résultat précédent n'a été écrasé.

Les vérifications complètes utilisent les artefacts déjà construits ; ce ne
sont pas de nouveaux builds propres. Cette correction ferme les contournements
reproduits et testés, sans prétendre sécuriser toute élaboration Lean arbitraire.
Elle ne change ni la cible scientifique ni les preuves de l'agent. Aucun commit,
push, changement de branche ou nouvel audit indépendant n'est effectué.

### 16.5 Intégration permanente des contrôles supplémentaires

La contre-vérification suivante n'a reproduit aucun nouveau défaut. Ses
288 cas lexicaux positifs et 576 cas négatifs sont désormais intégrés à
`test-expected-failure-gates.py`, avec contrôle des positions et des fins de
ligne. Ce sont des tests de la politique lexicale, pas des preuves sur du
Lean arbitraire ni des expériences scientifiques.

Le mode `--policy-only` exécute ces tests et les contrôles simulés existants
sans exiger un build ou la disponibilité de PowerShell. `verify.sh` et
`verify.ps1` l'appellent automatiquement avant les fixtures d'échec.
Les deux nouveaux cas de commande et de tactique citées passent par Lean :
le test vérifie d'abord leur diagnostic réel, puis exige que les wrappers
refusent de le confondre avec l'erreur de typage attendue.

Empreintes des scripts figés avant le run de cette intégration :

| Fichier | SHA-256 |
| --- | --- |
| `scripts/test-expected-failure-gates.py` | `99D5CFFDCE9DDDEB416DAAEFDA8162590C5D90D391495318E06F946F9474A42D` |
| `scripts/verify.sh` | `BB26F66A8B6A8E2AAF0B02C87AB6B90BAE510471C1CB062128E987A87615F9CF` |
| `scripts/verify.ps1` | `B81E9F467DCEC76AC7B839B2BE93BF31ABFA2E274BB83491055476490D656DB4` |

Résultats : 36 cas des wrappers passent, dont deux parcours nominaux de
23 fixtures et 34 refus attendus ; les 864 cas lexicaux passent également.
Les deux vérifications complètes passent sur Windows pour les 199 fichiers
Lean et leurs journaux attestent l'exécution automatique du nouveau mode.
Le contrôle passe aussi sous `python -O` ; sa matrice ne repose pas sur des
assertions supprimables. Un contrôle complémentaire confirme que le mode
léger ne vérifie ni la disponibilité des shells ni les artefacts construits.
`git diff --check` passe.

Commande du run complet :

```text
scripts/test-expected-failure-gates.py --output C:/Users/frederick/AppData/Local/Temp/agent-f7-permanent-cases-5ea7c072730d478f88a41eaababf49f7/fixture-gates
```

Le répertoire parent conserve `verify-bash.log`, `verify-powershell.log` et
`policy-portability.log`. Le sous-répertoire `fixture-gates` conserve les
36 résultats dans `results.json`, les compteurs de la matrice dans
`policy-results.json`, les journaux des wrappers et les deux journaux des
refus réels de Lean. Aucun résultat antérieur n'a été écrasé.

Cette intégration ne modifie ni les sources Lean, ni les fixtures, ni leurs
sites attendus, ni le filtre corrigé lui-même. Les travaux parallèles sont
préservés. Les vérifications utilisent les artefacts déjà construits, sans
nouveau build propre. Aucun commit, push ou changement de branche n'est fait.
