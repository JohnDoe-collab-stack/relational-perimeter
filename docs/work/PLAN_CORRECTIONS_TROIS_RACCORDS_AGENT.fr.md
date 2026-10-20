# Plan de correction des trois raccords du certificat de l’agent

Préparé et relu le 20 octobre 2026.

## 1. Objet, référence et statut

Fermer les trois défauts de consommation relevés par le dernier réaudit,
sur la même instance, avec les mêmes fondations et la même cible. Il ne
s’agit ni de reconstruire un autre agent, ni de rendre les contrôles plus
faciles, ni de remplacer une garantie par une assertion documentaire.

| Référence | Valeur vérifiée lors de la préparation |
| --- | --- |
| Dépôt | `JohnDoe-collab-stack/relational-perimeter` |
| Branche | `codex/constitutive-agent-corrections-audit` |
| HEAD avant ce plan | `06234b1e81f7dabcaec3469fb53faf49717e07fc` |
| Commit scientifique réaudité | `f039bdf3d822441e9e8b976ea54cf0177f58cffe` |
| Arbre scientifique | `b42c25cbc03233e17e3577d0d45a9bb741bd1b15` |
| Parent scientifique | `27546b9db4aa72769772d9253050e92fcfb0974d` |
| Référence avant ajout de l’agent | `75057f09cc9a535e8be3390999fa688c9ee3a96d` |
| Cible computationnelle antérieure validée | `4e0febf032821882069e7cfefd7e631fc8461d95` |
| Rapport étudié | `CONSTITUTIVE_AGENT_REAUDIT.md`, notamment sections 10, 11, 14, 16 et 20 |
| SHA-256 du rapport récupéré | `2c5799a7d75cf6d3892c053d51ebe56f9d64071c6ef50b0cdec7c5b13c2f37fa` |
| Verdict de l’agent | `AGENT TARGET REQUIRES CORRECTIONS` |
| Verdict de non-régression | `NO REGRESSION VERIFIED` |

Entre le commit scientifique et HEAD, les seuls ajouts sont le protocole
de réaudit et son document de préparation. Le présent plan constitue un
nouveau document de chantier ; il ne modifie pas les anciens comptes rendus.

Le rapport vérifie la construction actuelle et ne trouve aucune clause
centrale fausse. Il constate trois garanties dont l’affaiblissement cohérent
n’est pas détecté par le paquet livré. La quatrième mutation survivante,
M16c, ne retire pas une garantie scientifique : le suivi la fournit encore.

**Statut : implémenté et vérifié localement, sans publication ni nouvel audit
indépendant.** La section 11 consigne les résultats effectivement exécutés.
Les sections d’implémentation conservent l’ordre et les obligations du plan ;
leurs cases ne sont fermées que par les preuves et les vérifications décrites.

La deuxième revue a confronté les raccords aux types et aux patches M14b,
M16a et M16d2. Elle précise la projection des suffixes du même suivi,
l’ancrage du pont à l’opération riche portée par le certificat, la
composition commune des trois garanties et la comparaison des contrats
après dépliage de leurs définitions. Ce n’est pas un résultat de build
de l’implémentation future.

Le rapport, les patches et les journaux bruts restent hors du dépôt. Aucune
dépendance scientifique ou technique envers leur projet d’audit ne doit
être introduite. Ce plan temporaire devra être retiré de l’arbre destiné à
`main` dans la PR qui intégrera le chantier. Cette préparation n’autorise
ni commit, ni push, ni envoi à Aristotle, ni fusion.

## 2. Cible inchangée et règle de méthode

### 2.1. Exigence reçue

> Poursuivre le moteur autorisé depuis ses productions réelles ; ne restituer
> une valeur que pour une production effectivement formée et une variable du
> périmètre reçu ; restituer la valeur de cette production, non une valeur
> choisie par le contrôleur ; préserver les garanties d’acceptation annoncées
> par les actions utilisées ; conserver ces droits et ces accords après reprise.

### 2.2. Critère d’achèvement

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

La cible computationnelle antérieure demeure celle de la
[conclusion scientifique](../conclusion-largeur-exponentielle-conservation-identites.fr.md).
Les corrections n’en modifient ni le texte, ni la portée, ni les preuves.
La [note de méthode](../constitution-calcul-et-persistance-pour-ia.fr.md)
et le [document canonique de l’agent](../agent-constitutif-et-persistance.fr.md)
déterminent le sens des raccords à conserver.

### 2.3. Ce que signifie appliquer la méthode ici

Suivre la détermination constituée, sans lui substituer une valeur égale
obtenue ailleurs :

```text
maître constitué et exigence reçue
→ production locale réelle et cible avec son origine
→ référence sur son support, lecture et permission
→ témoin de réponse ou faits précis du refus
→ transports effectifs et successeur produit
→ suivi de toutes les interactions finies
→ certificat fermé de cette même instance
→ client public qui consomme ces garanties
```

Pour chaque raccord, identifier le producteur, la donnée dans `Type`, son
consommateur, l’accord démontré, puis le champ du certificat qui le ferme.
Le contrôle logiciel vient ensuite ; il ne produit pas ce témoin à sa place.

Les témoins existants restent les données constitutives. Une propriété
propositionnelle peut en exprimer une conséquence ; elle ne doit pas les
remplacer par une existence non réalisée. Aucun champ de certificat ne doit
être fermé par une hypothèse supplémentaire demandée au client.

Ne pas confondre :

- le support du moteur et le support historique des cibles ;
- l’extension exacte de références et une projection avec perte ;
- l’accord de valeurs et la provenance de leur calcul ;
- la preuve d’un refus et son seul libellé ;
- une construction pendant l’exécution et une preuve ultérieure sur sa trace ;
- l’archive scientifique et la mémoire runtime ;
- une preuve Lean, la stabilité d’une interface et un contrôle du C compilé.

L’extensivité reste un readout en aval. Elle n’entre ni dans le décideur de
réponse, ni dans la reprise, ni dans la justification des trois corrections.

## 3. Diagnostic et chaîne à fermer

| Point | Producteur et témoin actuels | Consommation manquante | Fermeture recherchée |
| --- | --- | --- | --- |
| C1 / M14b | `all_executed_determinations_followed`, `Followed.cons.referencesExact` | `followedReferences` ne fixe que la tête ; `Followed.references_exact` n’a pas de consommateur de production. | Exactitude sur chaque nœud du suivi effectif, composée et exigée par le certificat. |
| C2 / M16a | `MaterialReading`, `sourceProduced`, `sourcePerform`, `bridge` | Le certificat peut continuer à comparer les événements après substitution du répondeur runtime au côté riche du pont. | Pont ancré à l’opération riche indépendante, accord fini exprimé sur elle, contrôle du chemin réellement utilisé. |
| C3 / M16d2 | `Decision`, `ResponseEvidence.missing permission absent` | Les consommateurs acceptent la suppression du fait d’absence ; `ReplyCriterion` vaut `True` pour les refus. | Faits précis éliminés du témoin produit et exigés par le contrat fini certifié. |

Un champ déjà correct mais jamais consommé ne ferme pas son raccord dans le
paquet final. Inversement, l’élimination d’un témoin dans une preuve ne permet
pas de prétendre que ce témoin est une dépense runtime ou une nécessité
mathématique universelle.

## 4. Périmètre des changements et invariants de non-régression

### 4.1. Fichiers concernés

| Fichier | Intervention prévue |
| --- | --- |
| `RelationalPerimeter/Agents/Constitutive/Execution.lean` — A13 | Conséquences précises de `ResponseEvidence` et spécification indépendante des réponses/refus, sans changer le répondeur. |
| `RelationalPerimeter/Agents/Constitutive/Agreement.lean` — A14 | Ancrages riches du pont ; contrat de demande renforcé à partir des témoins effectifs. |
| `RelationalPerimeter/Agents/Constitutive/Persistence.lean` — A15 | Exactitude récursive des références, composition des garanties et renforcement fermé de `Certificate`. |
| `Tests/ConstitutiveAgentPersistence.lean` | Consommateurs du certificat sur toute la chaîne et comparaison riche indépendante. |
| `Tests/ConstitutiveAgentExecution.lean` | Consommateurs génériques des preuves de refus et scénarios concrets. |
| `Tests/ConstitutiveAgentRequirements.lean` | Fermeture depuis `Prepared.certificate` sur les entrées publiques réellement admises. |
| `scripts/check-agent-codegen.py` et son analyse partagée si nécessaire | Contrôle des projections riches effectivement installées dans le pont, pas seulement de producteurs laissés inutilisés. |
| Documentation canonique FR/EN | Déclarations ajoutées, sens précis du contrat renforcé, distinction des preuves et contrôles. |

Ne pas créer un second agent, un second suivi ou une API « legacy ».
Réutiliser les modules actuels ; ne pas multiplier les couches pour contourner
un raccord difficile. Une déclaration auxiliaire de preuve n’est pas une
nouvelle strate constitutive.

### 4.2. Éléments à conserver

Les quatre fondations, la licence, la toolchain, le manifeste Lake, les
figures et les sources computationnelles antérieures restent byte-identiques.
Conserver les rangs A10 à A17 et leurs imports : aucun retour depuis les
strates antérieures vers l’agent, aucun import A16 dans A15.

Ne pas changer les données de `Memory`, `Session`, `Source`, `History`,
`Requirement`, `AnswerTarget`, leurs origines ou leurs producteurs. Ne pas
archiver le profil oublié, le code initial ou l’histoire riche dans le runtime.

Préserver en particulier :

- le maître public unique, le carrier constitué et les transports exacts ;
- les résultats de largeur `2^n`, un et `2^k` dans leurs portées respectives ;
- l’action découverte, sa préservation et l’autorisation de regroupement ;
- les quatre demandes, leurs réponses et leurs motifs de refus ;
- le travail exact d’`obtain`, le cache et les anciennes lectures ;
- l’absence de changement de la mémoire entière en cas de refus ;
- les deux retours des témoins d’admission ;
- la production locale sans futur et la production vivante unique ;
- l’oubli du profil initial depuis la mémoire complète et les mêmes futurs ;
- les contrôles d’imports, de diagnostics, de confidentialité et de code compilé.

Un renforcement de `RequestCriterion` ou l’ajout d’un champ de `Certificate`
est un changement d’interface à déclarer, pas une prétendue identité de toutes
les signatures. Aucun ancien théorème ne doit être supprimé ou affaibli.
Toute conséquence de l’ancien contrat doit rester dérivable du contrat renforcé.

## 5. Lot C1 — Références exactes à tous les nœuds

### C1.1. Exprimer la propriété sur le suivi effectivement porté

Définir dans `Persistence` une propriété récursive, nom de travail
`Followed.ExactReferences`, sur un objet `Followed master source requests` :

- cas vide : aucune référence de nœud à vérifier ;
- cas `cons` : l’extension portée par ce nœud est exactement
  `(sourcePerform source request).1.history.references`, et la même propriété
  vaut sur **sa queue stockée**, indexée par ce successeur précis.

Ne pas définir la propriété sur une liste d’extensions reconstruite depuis la
longueur. Ne pas la vérifier seulement sur une nouvelle histoire canonique
choisie à côté de l’objet reçu. Elle porte sur ses données et sa queue réelles.

### C1.2. Construire la preuve en consommant chaque raccord local

Prouver `Followed.all_references_exact` pour tout suivi, toute source et
toute liste finie. Procéder par élimination structurelle de `Followed` :
consommer `Followed.references_exact` à la tête, puis l’hypothèse inductive
sur la queue. Aucun axiome d’unicité des extensions, aucune égalité de
longueurs et aucune sélection de témoin arbitraire ne doivent remplacer ce lien.

L’extension considérée va du support du maître au support courant du moteur.
Les transports historiques des cibles restent ceux de `InternalStepAgreement`
et de `FollowedStages.historicalTransport`. Ne pas les remplacer ou les
confondre avec `Followed.references`.

### C1.3. Fermer le certificat et ses consommateurs

Ajouter un champ, nom de travail `followedAllReferences`, qui exige pour tout
profil et toute suite de demandes cette propriété sur **`Certificate.followed`
lui-même**. Le fermer avec `Followed.all_references_exact` appliqué à cet objet,
pas avec un suivi reconstruit indépendamment.

Sa quantification attendue est : pour tout `profile` et `requests`,
`Followed.ExactReferences (followed profile requests)`. Le champ dépend du
champ `followed` du même certificat. Ne pas lui substituer la propriété
d’un appel séparé à `all_executed_determinations_followed` sans raccord.

Conserver `followedReferences` et en obtenir le cas de tête par projection du
nouveau raccord récursif. Exposer les conséquences pour une deuxième et une
troisième demande, puis pour tout préfixe fini : l’état du nœud considéré est
celui obtenu en exécutant ce préfixe via `sourcePerform`.

Cette projection de suffixe suit les queues du même objet dépendant. Si une
fonction d’accès dans `Type` est nécessaire, l’écrire par récursion structurelle
compilable ; ne pas utiliser l’historique futur pour fabriquer la tête.

Pour lever toute ambiguïté, son interface attendue est :

```text
un suivi de (prefix ++ suffix) depuis source
→ un suivi de suffix depuis
  Continuation.run (fun s q => (sourcePerform s q).1) source prefix
```

Le cas vide restitue l’objet reçu ; le cas non vide prend sa queue puis
récure sur le préfixe restant. Les lois du suffixe s’obtiennent par la même
élimination. Cette fonction observe une histoire scientifique pour en prouver
les propriétés ; elle ne devient pas une entrée future du producteur local.

### C1.4. Vérifications de fermeture

Les clients publics doivent consommer le nouveau champ du certificat :

- liste vide, un nœud, deux nœuds et troisième nœud ;
- préfixe arbitraire suivi d’une demande ;
- demande `obtain` réalisant plusieurs étapes internes, puis lecture en cache ;
- séparation des extensions moteur/historique et maintien de leurs retours,
  lectures, injectivité et positions existants.

La suppression cohérente de `referencesExact` doit laisser une obligation
d’exactitude explicite dans ce consommateur récursif. Si une reconstruction
alternative ferme réellement la même égalité sur chaque nœud, elle conserve
la garantie et doit être examinée comme telle, non condamnée par son seul nom.

**Fin du lot :** le certificat exprime et fournit l’exactitude des références
sur toute l’histoire ; les tests ne servent pas de substitut à ce théorème.

## 6. Lot C2 — Pont vers l’interpréteur riche indépendant

### C2.1. Fixer la source de la comparaison

Conserver la chaîne de données :

```text
HistoricalFormation / RegisterRealization
→ MaterialReading du support constitué
→ sourceProduced : RichOperation
→ RichOperation.result / sourcePerform
→ sourceNext et sourceEvent du pont
→ accords avec executeInput et avec toutes ses suites finies
```

`sourceProduced` continue à lire le support riche. Ne pas le redéfinir à
partir du résultat runtime, même accompagné d’une égalité ensuite démontrée.
Le partage de `decideReply` entre deux lectures n’est pas interdit : c’est
la donnée lue et son chemin de formation qui doivent rester indépendants.

### C2.2. Ajouter les ancrages ponctuels explicites

Dans `Agreement`, exposer pour toute source et demande :

```text
(bridge master).sourceNext source request = (sourcePerform source request).1
(bridge master).sourceEvent source request = (sourcePerform source request).2
```

Les raccorder aussi au résultat de `richOperations source request` par les
champs déjà présents `richOperationsExact` et `richResultExact`. Le certificat
doit fermer ces raccords sur la même opération riche, pas uniquement fournir
une opération inutilisée à côté d’un pont indépendant.

Fixer notamment le raccord suivant dans le certificat, nom de travail
`bridgeRichResult` :

```text
((bridge master).sourceNext source request,
 (bridge master).sourceEvent source request)
  = (richOperations source request).result
```

Le premier membre de cette égalité contient le `Source master` entier,
pas uniquement sa projection `Memory`. Les deux ancrages ponctuels en sont
des conséquences, composées avec `richResultExact`. Ne pas ajouter trois
preuves libres qui ne portent pas sur la même opération.

Construire les égalités point par point. Aucune égalité de fonctions par
extensionnalité n’est nécessaire ; ne pas introduire de dépendance interdite.

### C2.3. Consommer ces ancrages jusqu’aux futurs finis

Ajouter au certificat les ancrages de source, puis un accord fini dont le
côté riche est écrit directement avec les projections de `sourcePerform`,
et non seulement avec les champs configurables de `bridge`.

Réutiliser `Continuation.run` et `Continuation.events`. Composer les ancrages
locaux par induction sur la liste de demandes, en faisant partir chaque queue
du successeur riche réellement produit. Raccorder ce résultat à `futures` et
`events` du certificat, puis à `executeRequests`.

Ces accords finis peuvent être des théorèmes dérivés des champs du certificat
plutôt que des champs redondants. Leurs preuves doivent utiliser
`bridgeRichResult`, `richResultExact` et les accords de continuation du même
certificat. Leur côté riche mentionne explicitement `sourcePerform`.

Ne pas créer un second interpréteur pour cette preuve. Ne pas conserver une
égalité indépendante inutilisée : le client du certificat doit obtenir
l’accord riche/runtime en passant par les raccords certifiés.

Préserver séparément les lois de lecture, les permissions riches/réalisées
et les deux retours des témoins d’admission. L’accord d’événements ne les
remplace pas.

### C2.4. Distinguer accord sémantique et chemin de calcul

**Une égalité seule ne suffit pas à exclure M16a.** Les événements riches
et runtime sont justement prouvés égaux ; une version qui lit le runtime
peut donc reconstruire une preuve de cette égalité. Il serait faux de
présenter le seul ajout d’un champ propositionnel comme une preuve de
l’indépendance du chemin exécuté.

Compléter le contrôle compilé existant `AGENT_RICH_READ` sur les projections
**effectivement installées** dans `bridge.sourceNext` et `bridge.sourceEvent`.
Au besoin, exposer deux applications nommées de ces projections dans
`Agreement`, sans nouvel état ni nouveau décideur. Le contrôle doit suivre
les fermetures appliquées et les auxiliaires qui fournissent ces résultats :

- suivre l’opération riche et, sur les routes qui demandent une lecture,
  sa lecture du support constitué ;
- ne pas substituer `executeInput`, `executeProducedInput`, `performCertified`
  ou une lecture de `project source` à la production de l’événement riche ;
- ne pas analyser indistinctement tout `bridge` : son côté réduit contient
  légitimement ces fonctions runtime ;
- ne pas se contenter de trouver `sourcePerform` quelque part dans le module,
  ni fixer le numéro instable d’une lambda générée ;
- refuser un chemin nécessaire non résolu, au lieu de le compter comme absent.

Ne pas imposer une lecture inutile sur `advance`, ni sur une projection de
successeur dont le résultat est légitimement l’état courant. Le contrôle
doit respecter les branches réelles et les optimisations correctes, pas
forcer un appel artificiel pour satisfaire une recherche de noms.

Réutiliser l’analyse des applications et fermetures existante. Toute extension
de l’analyse partagée doit conserver les contrôles antérieurs. Si ce chemin
n’est pas analysable correctement, le noter comme obligation ouverte ; ne pas
annoncer que les égalités de valeurs l’ont fermé.

Lors de cette revue, une lecture exploratoire du C déjà disponible a confirmé
que `AgentAnalysis` peut reconstruire le record retourné par `bridge` et isoler
les fermetures de `sourceNext` et `sourceEvent` : toutes deux atteignent
`sourcePerform`, et aucune n’atteint `executeInput` dans cet artefact. Ce contrôle
n’a ni reconstruit Lean ni exécuté une mutation ; il établit la faisabilité de
la sélection, pas la validation du nouveau contrôleur.

Dans le contrôleur final, justifier la correspondance entre projection Lean
et champ compilé à partir du schéma effectif et de l’effacement des preuves.
Ne pas utiliser aveuglément les indices de champs observés dans l’ancien C.
Vérifier l’identité et l’artefact propriétaire du `bridge` analysé, puis les
fermetures retournées à ses champs. Un auxiliaire témoin resté riche tandis
que le vrai champ est remplacé par le runtime ne doit pas suffire.

Les autotests doivent inclure : remplacement d’un seul champ, échange des
champs riche/réduit, record partiellement reconstruit, lambda indirecte,
fermeture statique et sélection non résolue. Ajouter aux négatifs un positif
où seul le côté réduit appelle normalement le runtime. Aucun nouveau contrôle
ne doit interdire cet appel légitime ou modifier le calcul scientifique.

### C2.5. Vérifications de fermeture

Clients universels sur toute source/demande et toute suite finie, puis
initialisation publique et scénario mêlant les quatre demandes. Rejouer M16a
et une variante avec ses preuves d’égalité reconstruites : le contrôle du
chemin doit détecter l’utilisation du répondeur runtime comme source riche.

Accepter en contrôle positif un auxiliaire riche équivalent, conservant la
lecture réelle et ses accords. Si la compilation élimine une dépendance
inerte, ne pas l’appeler substitution exécutée. Distinguer dans le bilan
preuve sémantique, raccord constitutif et contrôle de l’implémentation compilée.

## 7. Lot C3 — Justification précise des refus

### C3.1. Écrire le contenu indépendant attendu

La spécification doit être déterminée par l’exigence, le registre, le handle,
la variable et l’éventuelle valeur proposée, avant de consulter le message
choisi par le répondeur. Les handle et variable du message doivent être ceux
de cette demande, sans changement silencieux d’indices.

| Résultat | Données et faits nécessaires |
| --- | --- |
| Réponse | Permission typée, occurrence réellement résolue, égalité avec sa lecture et compatibilité avec la proposition éventuelle ; acceptation dans le contexte de cette cible. |
| `outsideScope` | `requirement.permission var = none`. |
| `missingHandle` | Permission positive sur `var` et `resolveHandle register handle = none`. |
| `incorrectValue` | Permission positive, occurrence réellement résolue, valeur effectivement proposée et inégalité avec la lecture de cette occurrence. |

Ne pas définir le critère comme « le message est celui de `decideReply` ».
Ne pas remplacer les raisons par `True`, une étiquette ou une absence de
changement d’état. Ne pas établir la précision du refus par un second appel
au décideur : elle doit être éliminée du témoin déjà produit.

### C3.2. Consommer le témoin positif existant

Conserver `Decision` et `ResponseEvidence` comme données de référence dans
`Type`. Dans `Execution`, ajouter leurs éliminateurs utiles :

- extraire d’un témoin `.missing` la permission réelle et la preuve d’absence ;
- extraire de `.incorrect` l’occurrence, sa résolution, la proposition exacte
  et son inégalité avec la lecture ;
- extraire de `.outside` l’absence de permission.

Ces opérations sont définies pour **tout témoin du type concerné**, pas
seulement pour un cas concret calculé dans un test. Les sorties qui portent
des données restent exécutables dans `Type`. Leurs conséquences logiques
peuvent être formulées dans `Prop`, sans faire disparaître les témoins.

Exposer une spécification précise, nom de travail `ResponseSpecification`,
et prouver sa satisfaction par élimination de `ResponseEvidence`. Elle reste
indépendante de `performCertified` et ne reçoit aucune hypothèse d’autorisation
extérieure pour justifier un résultat déjà choisi.

Son domaine conserve explicitement `requirement`, `register`, `handle`, `var`,
`candidate` et `message`. Fixer ces points avant la preuve :

- les indices du message sont ceux de cette demande, dans tous les cas ;
- une réponse autorisée satisfait `candidate = none` ou
  `candidate = some value`, avec cette même valeur lue ;
- un refus `incorrectValue` exige `candidate = some value`, pas l’existence
  d’une autre valeur incorrecte choisie pour justifier le refus ;
- aucun message `.advanced` ne satisfait cette spécification de restitution ;
  la demande `advance` garde son témoin propre dans `RequestEvidence` ;
- l’acceptation contextuelle est raccordée à l’autorisation de cette même
  occurrence dans `Agreement`, sans importer A14 depuis A13.

La spécification logique n’est pas un second témoin libre de décision.
`ResponseEvidence` reste la donnée positive, avec permission et occurrence
extractibles. Toute conséquence introduite dans `Prop` est construite depuis
cette donnée et ne sert pas à la remplacer dans la production.

### C3.3. Renforcer le contrat existant, pas créer un contrat au choix

Le `ReplyCriterion` actuel exprime l’autorisation et l’acceptation des réponses
positives ; pour les refus, il ne suffit pas. Conserver ses conséquences
utiles, mais ne plus le présenter seul comme la spécification complète.

Renforcer **`RequestCriterion`**, dans `Agreement`, pour exiger ensemble les
garanties positives existantes et la spécification précise :

- `inspect` : registre initial, aucune valeur proposée ;
- `propose` : registre initial, exactement la valeur de cette demande ;
- `obtain` : exigence et registre du résultat effectif, aucune valeur proposée ;
- `advance` : conserver ses garanties existantes, sans lui inventer un motif
  de refus ou une nouvelle interprétation.

Le cas `obtain` ne doit pas être vérifié sur un registre obsolète : une cible
absente avant la production peut être présente après les étapes nécessaires.
Une demande hors périmètre demeure refusée avant toute production.

Adapter `RequestEvidence.criterion` et `executed_reply_criterion` pour qu’ils
consomment ces conséquences de l’évidence réellement produite. Montrer que le
contrat renforcé implique les obligations antérieures, sans affaiblir celles-ci.
Il n’y aura pas de chemin public alternatif conservant le contrat faible.

### C3.4. Composer et fermer dans le certificat public

`FiniteResponseCriterion` doit appliquer le contrat renforcé à chaque demande
et à son véritable successeur. `Followed.satisfies` doit faire remonter la
précision des réponses/refus portée par ses nœuds, avec `nextExact` pour le
passage à la queue. Ne pas réutiliser un simple accord du premier message.

Le certificat doit exposer la précision des réponses issues de **`replies`**,
puis `satisfaction` sur toutes les suites finies. Fermer les champs depuis
les témoins de l’exécution ; ne pas les recalculer sur une réponse parallèle.
`Prepared.certificate.continuation` doit fournir ces garanties pour toute
entrée publique effectivement admise, sans nouvel argument utilisateur.

Dans `all_executed_determinations_followed`, lier l’évidence de la tête une
seule fois et en déduire son critère renforcé par son éliminateur. Dans
`certify`, lier le suivi canonique une seule fois : les champs `followed`,
`followedAllReferences` et `satisfaction` utilisent cet objet, la satisfaction
venant de son `Followed.satisfies`. Les accords restent scientifiques ; aucune
nouvelle exécution du répondeur n’est introduite dans la session runtime.

### C3.5. Réunir les trois raccords sur une seule chaîne

Ajouter en production un théorème de composition du certificat, nom de travail
`Certificate.followed_chain`, pour tout profil admis et toute suite finie.
Sa preuve doit relier, à chaque nœud du **même** `Certificate.followed` :

1. sa source et sa demande courantes ;
2. son champ `rich`, égal à `sourceProduced` par `richExact`, puis à
   `Certificate.richOperations` par `richOperationsExact` ;
3. le résultat de cette opération, relié aux projections du pont par
   `bridgeRichResult`, et au résultat runtime par `nextExact` ;
4. la réponse et sa justification précise, éliminées de son champ `response` ;
5. son extension de références exacte vers l’histoire de ce successeur ;
6. sa queue, dont la source est précisément ce successeur riche.

Le théorème compose ces raccords par induction sur le suivi et donne le
contrat fini renforcé et l’exactitude de toutes les références. Il ne
construit ni une autre trace ni un nouveau certificat indépendant. Les
consommateurs publics passent ensuite par `Prepared.certificate.continuation`,
y compris après un préfixe. Trois garanties correctes mais établies sur trois
histoires sans raccord ne satisfont pas ce lot.

Respecter l’ordre acyclique : éliminateurs et lois génériques, champs du
certificat, construction fermée `certify`, puis théorème consommateur de ce
certificat. `Certificate.followed_chain` ne doit pas servir d’hypothèse pour
construire les champs dont sa propre démonstration dépend.

### C3.6. Vérifications de fermeture

Consommer les lois génériques des témoins et les champs du certificat, puis
vérifier sur l’instance publique :

1. variable hors périmètre, même si le handle manque aussi : priorité au refus
   `outsideScope`, aucune production, mémoire entière inchangée ;
2. `inspect` sur handle absent et variable permise : absence réellement prouvée ;
3. `obtain` sur ce handle : productions exactes et réponse, non refus systématique ;
4. proposition correcte et proposition opposée sur une occurrence existante ;
5. même propriété après un préfixe d’interactions, puis après reprise ;
6. double application des transports d’admission conservant les témoins.

Rejouer M16d2 avec ses consommateurs syntaxiquement adaptés. La perte du fait
d’absence doit empêcher l’élimination générique vers la spécification précise,
pas seulement provoquer un changement d’arité de motif ou un nom manquant.
Ajouter les variantes hors périmètre et valeur incorrecte, sans changer
l’exécution correcte pour fabriquer un cas négatif.

## 8. Ordre d’implémentation et contrôles de non-régression

### 8.1. Préparer une référence reproductible

Avant toute modification Lean : relever l’état Git et les changements
concurrents, figer les empreintes et les énoncés publics, et produire un état
de référence local. Préserver les résultats d’audit existants sans les écraser.
Le HEAD seul ne décrit pas un arbre non commité : conserver son diff et les
hashes des sources avec chaque exécution.

Relever séparément le `main` courant et son merge-base. Ne pas reprendre
automatiquement comme tête actuelle un SHA historique indiqué dans un ancien
prompt ; les références scientifiques gelées, elles, ne changent pas.

Ne pas changer de branche ou toucher aux autres worktrees. Si un changement
concurrent recouvre ces fichiers, l’identifier avant de modifier le contenu.

### 8.2. Ordre des lots

1. C1 : propriété sur le suivi réel, preuve récursive, certificat, consommateurs.
2. C2 : ancrages à la production riche, composition finie, certificat et
   contrôle de la provenance effective des projections du pont.
3. C3 : spécification précise, élimination des témoins, contrat de demande,
   composition finie et certificat public.
4. Consommateurs publics transversaux, documentation, campagne finale.

Après chaque lot, compiler ses modules et importeurs, vérifier leurs audits
et les tests déjà présents. Ne pas reporter la fermeture du certificat
à un dernier lot supposé réparer les raccords manquants.

### 8.3. Contrôles positifs et négatifs ciblés

Les tests viennent après les constructions. Ils consomment les garanties,
sans définir leur contenu ni modifier leur portée pour obtenir un succès.

| Cas | Résultat requis |
| --- | --- |
| C1, exactitude sur les nœuds 2 et 3 et un suffixe arbitraire | Déduite du certificat sur les queues du suivi réel. |
| C1, suppression de `referencesExact` | Obligation récursive non fermée, ou reconstruction démontrée de la même garantie explicitement examinée. |
| C2, substitution runtime à l’événement riche | Détection du chemin substitué ; pas seulement échec d’une preuve `rfl`. |
| C2, même substitution avec égalités reconstruites | Les accords de valeurs ne doivent pas contourner le contrôle de provenance compilée. |
| C2, auxiliaire riche conservant les mêmes déterminations | Accepté, sans imposer une graphie arbitraire du programme. |
| C3, preuve d’absence retirée et motifs adaptés | Échec de la justification générique précise, non simple erreur d’arité. |
| C3, refus mal étiqueté ou mauvais handle/variable/proposition | Rejet par les faits de la demande et de l’occurrence exactes. |
| Contrat fini réduit à la tête, M16c | Consommateur de la deuxième/troisième demande en échec ; noter que l’ancienne garantie était également fournie par `Followed`. |

Inclure le contrôle M16c, peu coûteux et redondant, sans l’annoncer comme une
quatrième correction scientifique. Couvrir aussi les suppressions détectées
auparavant uniquement par des noms : inspecter leur énoncé consommé, sans
prétendre avoir démontré une nécessité causale par leur simple présence.

Figer les patches adaptés, leurs empreintes et les attentes avant le run
confirmatoire. Les mutations restent dans des copies jetables extérieures,
avec artefacts indépendants. Ni timeout, ni import manquant, ni erreur
adventice ne constitue un rejet substantif.

Il n’existe pas de garantie contre une réécriture arbitraire simultanée de
toute la spécification, de tous les consommateurs et du protocole. Conserver
une référence indépendante des énoncés et ne pas réécrire ces attentes après
observation des résultats. Ne pas appeler régression une autre preuve
constructive de la même garantie complète.

### 8.4. Vérification Lean, architecture et exécution

Pour chaque fichier créé ou modifié, maintenir exactement un bloc final
`AXIOM_AUDIT`, avec tous les noms complets concernés et aucun placeholder.
Aucune déclaration manuscrite ne doit dépendre d’un axiome ; aucune source
Lean ne doit introduire un construit interdit. Les données dans `Type` sont
compilables par récursion structurelle ; aucun témoin concret n’est supposé.

Exiger notamment l’absence de `axiom`, `sorry`, `admit`, `noncomputable`,
`Classical`, `propext`, `Quot.sound`, `native_decide`, `unsafe` et
`implemented_by` dans les sources Lean, conformément aux contrôles existants.
Scanner toutes les sources, pas seulement les fichiers modifiés.

Comparer avec le commit scientifique : déclarations, énoncés, hypothèses,
quantification sur les entrées, accessibilité depuis le root et strates.
Les ajouts et renforcements sont décrits explicitement. Toute suppression,
toute hypothèse supplémentaire ou toute perte de domaine est un échec.

Déplier les prédicats concernés dans cette comparaison. Conserver le nom
`RequestCriterion` ne garantit pas que son contenu est inchangé ; renforcer
un prédicat utilisé comme hypothèse peut réduire silencieusement la portée
d’un théorème. Pour chaque consommateur existant, distinguer les conclusions
renforcées des prémisses devenues plus fortes. Dans ce dernier cas, restituer
aussi la conséquence historique sous ses hypothèses initiales, ou signaler
une régression ouverte. Une recompilation seule ne suffit pas.

La référence sémantique de l’ancien contrat est figée hors du dépôt pour
cette comparaison ; elle ne devient ni une API « legacy » ni une option de
contrat faible dans l’agent. Les nouveaux accords sur l’exécuteur réel doivent
impliquer tous les anciens accords sur les mêmes entrées.

| Acquis | Déclarations ou interfaces à maintenir dans leur portée |
| --- | --- |
| Largeur et même carrier | `class_iff_on_master_carrier`, `class_iff_on_executed_regime` et les témoins du certificat maître, dans les modules computationnels inchangés. |
| Suivi interne | `FollowedStages.execution_exact`, `request_stages_exact`, `followedStages`, `internalStages`. |
| Deux supports et admissions | `engineTransport`, `historicalTransport`, les lectures transportées, `admission_received_return`, `admission_realized_return`. |
| Contrat fini | `Followed.satisfies`, `all_finite_responses_satisfy`, les champs `satisfaction`, `futures`, `events`, `reads`, `admissions`, `reflection`. |
| Mémoire complète et oubli | `agent_memory_factors_through_output`, `initial_profile_not_recoverable`, `forgotten_sources_same_future`. |
| Entrée publique | `InitializationCertificate`, `Prepared.certificate`, les refus d’initialisation et les demandes admissibles existantes. |

Vérifier les empreintes des fondations et autres fichiers protégés. Rejouer
les preuves de largeur, la continuation, les retours d’admission, l’oubli de
la mémoire entière, les contrôles compilés et la suite des diagnostics.
Une nouvelle analyse du pont ne doit pas relâcher la détection des doublons,
du rejeu du maître, des archives runtime ou des dépendances extensives.

Commandes de base de la campagne finale :

```text
git status --porcelain
git rev-parse HEAD
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
git diff f039bdf3d822441e9e8b976ea54cf0177f58cffe --check
lake update
```

Ajouter la suite complète des wrappers et leurs autotests, les clients
positifs et négatifs et les mutations ciblées. Le sweep exhaustif des
constantes et les contrôles de code compilé doivent porter sur les artefacts
fraîchement construits. Une exception générée n’autorise aucune dépendance
axiomatique d’une déclaration manuscrite.

Comparer le manifeste avant/après `lake update` ; ne pas accepter sa mutation
silencieuse. Vérifier que les deux routes sélectionnent les mêmes sources,
que tous les modules restent accessibles et que les liens locaux fonctionnent.
Ne pas figer artificiellement les anciens comptes si de nouveaux éléments
légitimes ont été ajoutés ; recalculer les inventaires concernés.

Un run PowerShell sous Linux n’est pas un run Windows. Une plateforme absente
est `NOT RUN`. Le futur paquet de reproduction doit être exécuté d’un bout à
l’autre depuis une copie neuve ; des étapes lancées séparément ne valent pas
validation de son wrapper complet.

## 9. Documentation et livraison scientifique

Mettre à jour ensemble les documents canoniques
[français](../agent-constitutif-et-persistance.fr.md) et
[anglais](../constitutive-agent-and-persistence.en.md), ainsi que le README
si ses garanties ou instructions changent :

- ajouter les six champs de certificat du lot précédent, actuellement omis ;
- documenter `Followed.references_exact`, `request_stages_exact`, puis la
  nouvelle fermeture sur tous les nœuds et ses consommateurs ;
- décrire l’ancrage du pont à l’interpréteur riche et les accords composés ;
- distinguer le critère positif projeté et le contrat complet des refus,
  désormais exigé par le suivi fini ;
- préciser les changements d’interface réels, dont l’arité de `Followed.cons`
  du lot précédent, sans conserver une ancienne lecture comme solution parallèle ;
- séparer preuves, protection de leurs interfaces, contrôle compilé et
  plateformes effectivement testées.

Ne pas transformer ces corrections en une nouvelle revendication sur
l’alignement universel, le coût total ou la mémoire constante. Ne pas réécrire
les conclusions computationnelles auditées ni modifier les SVG.

Préparer un bilan local extérieur au dépôt : pour chaque point, source,
producteur, témoin, consommateur, champ fermé, client et contrôle exécuté.
Joindre les commandes, versions, empreintes et limites de reproduction.
Ne pas copier les probes ou rapports externes comme dépendances du projet.

Un futur prompt d’audit devra désigner le nouveau commit exact après une
publication autorisée, conserver la cible inchangée et demander la revue de
la chaîne complète, pas seulement des ajouts. La récupération hors ligne
doit être possible si nécessaire, avec toutes les révisions épinglées et
des empreintes. Aucun verdict ancien ne valide par anticipation le nouveau SHA.

## 10. Conditions de clôture locale

Les cases suivantes sont fermées par la campagne de la section 11, non par
un nouveau verdict indépendant. Publication, audit et fusion restent séparés.

- [x] Cible, instance et méthode inchangées ; fondations et acquis protégés.
- [x] C1 : chaque nœud du suivi effectif fournit son extension exacte.
- [x] C1 : cette garantie entière est consommée par le certificat public.
- [x] C2 : le pont est raccordé aux opérations riches réellement produites.
- [x] C2 : les accords finis portent directement sur cet interpréteur indépendant.
- [x] C2 : le chemin compilé des projections riches ne substitue pas le runtime.
- [x] C3 : chaque motif de refus implique les faits précis de la même demande.
- [x] C3 : ces faits proviennent de l’évidence produite, sans second décideur.
- [x] C3 : le contrat renforcé se compose sur toutes les interactions finies.
- [x] Les trois garanties sont composées sur le même suivi et ses vrais successeurs.
- [x] `certify` et `Prepared.certificate` ferment tous les nouveaux raccords.
- [x] Tous les témoins de données restent constructifs et exécutables.
- [x] Audits axiomatiques, builds propres et contrôles complets réussis.
- [x] Mutations pertinentes distinguées des refactorisations inoffensives.
- [x] Aucune déclaration retirée, affaiblie ou rendue conditionnelle.
- [x] Aucun changement de prédicat ne masque une hypothèse renforcée ou une perte de domaine.
- [x] Runtime, oubli, transports, largeur et strates vérifiés sans régression.
- [x] Documentation FR/EN, manifeste, liens et diff conformes.
- [x] Reproduction finale locale exécutée intégralement, selon les périmètres explicites ci-dessous.

Une case ne se ferme ni par un champ nommé, ni par un test qui ne consomme
que ce nom, ni par un verdict espéré. Si un raccord échoue, signaler
l’obligation exacte encore ouverte ; ne pas modifier la cible pour l’effacer.

La clôture locale du correctif, sa publication, l’audit indépendant et
l’intégration dans `main` sont quatre états distincts. Les trois dernières
étapes nécessitent leurs autorisations explicites. Après fusion autorisée,
vérifier les contenus, le manifeste et les builds sur le commit effectivement
fusionné, et l’absence de documents temporaires dans son arbre.

## 11. Résultats de l’implémentation et de la validation locale

### 11.1. Fermeture des raccords en production

| Point | Données et consommateurs désormais présents |
| --- | --- |
| C1 | `Followed.ExactReferences`, `all_references_exact`, `references_of_exact`, `afterPrefix`, `afterPrefix_exact` ; champs `followedAllReferences` et `followedReferences`, puis `Certificate.suffix_references`. La propriété porte sur les queues réellement stockées. |
| C2 | `Certificate.bridgeRichResult` relie le résultat riche entier aux deux champs sources du pont. `bridge_next_exact`, `bridge_event_exact`, `rich_run_eq`, `rich_events_eq`, `rich_futures` et `rich_events` composent ces accords sans extensionnalité fonctionnelle. |
| C2, chemin compilé | Le contrôleur reconstruit le record retourné par le véritable `bridge`, sélectionne les fermetures de ses deux champs riches et vérifie leurs applications. Le schéma de `Continuation.Exact` est contrôlé dans `Tests/AllConstantsAudit.lean`, ainsi que la provenance des symboles compilés. Un observateur riche inutilisé ne suffit pas. |
| C3 | Éliminateurs de permission, occurrence, proposition et faits d’absence/inégalité ; `ResponseSpecification`, `RequestSpecification`, `ResponseEvidence.specification` et `RequestEvidence.specification`. Le champ `replySpecifications` ferme leur satisfaction depuis `replies`. |
| Composition | `Followed.ChainAgreement`, `Followed.chain_agreement` et `Certificate.followed_chain` suivent la même opération, la même réponse, les mêmes références et le vrai successeur. `certify` lie un seul suivi et en tire aussi `satisfaction`. |

Le contrat de demande est renforcé, pas silencieusement renommé :
`RequestCriterion.positive` restitue exactement sa partie positive antérieure.
Les données de `RequestEvidence` et de `ResponseEvidence` sont inchangées ;
elles fournissent déjà les faits supplémentaires exigés. Aucun client de
`certify` ou de `Prepared.certificate` ne doit fournir une hypothèse nouvelle.
Les demandes et leurs domaines d’entrée sont les mêmes. Le renforcement du
champ propositionnel `criterion` de `Followed.cons` ne demande pas de donnée
nouvelle : il se construit depuis son témoin `response` déjà requis.

### 11.2. Campagne exécutée

Les scripts, patches, attentes et empreintes ont été figés avant les runs
finaux. Les logs et matériaux bruts restent dans des répertoires extérieurs.
Le code, les tests, l’outillage et les documents canoniques n’ont pas changé
pendant ces runs ; seul ce bilan de chantier est écrit ensuite.

| Vérification | Résultat exécuté |
| --- | --- |
| Séquence complète de validation | Neuf commandes exécutées dans un seul script : clean, build public, build complet, les deux verifiers, suite complète des wrappers, deux contrôles de diff et `lake update`. Toutes sortent avec zéro. |
| Builds après `lake clean` | 160 tâches pour la façade et 183 pour le build complet, sans avertissement Lean. |
| Constructivité exhaustive | 18 333 constantes, 360 exceptions générées par le compilateur et zéro dépendance axiomatique manuscrite ; les audits des nouvelles déclarations sont sans axiomes. |
| Deux verifiers | Bash Git et PowerShell sous Windows : mêmes 181 fichiers Lean ; 26 fixtures aux diagnostics exacts, aucun diagnostic supplémentaire admis. |
| Suite complète des wrappers | 68 résultats conformes aux attentes, sur les deux routes ; les autotests lexicaux et de diagnostic sont également exécutés. |
| Client public supplémentaire | Neuf probes important seulement `RelationalPerimeter`, tous sans axiomes : refus incompatibles avec les faits, indices exacts, registre prolongé d’`obtain`, suffixe arbitraire, accord riche et chaîne complète. |
| Clients historiques | Les quatre fichiers clients positifs de l’audit recompilent contre la version corrigée, sans avertissement ni axiome. Ils restent extérieurs au dépôt. |
| Conservation | 299 fichiers suivis hors du périmètre de modification byte-identiques à la référence initiale, dont les fondations et le calcul antérieur ; aucune déclaration antérieure de l’agent retirée. |
| Diff, liens et manifeste | Les deux contrôles de diff et les liens locaux passent ; `lake update` laisse le manifeste byte-identique. |

La séquence de neuf commandes est réalisée dans le worktree après nettoyage
complet. Le wrapper de mutations est exécuté intégralement avec un clone
détaché neuf de ses sources exactes et des artefacts physiquement copiés,
recontrôlés par son build témoin. Ce sont deux périmètres de reproduction
explicitement distincts ; aucune exécution Linux ni nouveau clone GitHub
épinglé à un futur commit non publié n’est revendiqué.

### 11.3. Substitutions et contrôle positif

Le script autonome `scripts/test-agent-contract-links.py`, version 1, a
terminé d’un bout à l’autre avec cinq cas conformes et une référence intacte.
Les variantes d’effacement à `Unit` gardent noms et arités : leur échec
n’est donc pas obtenu par un simple nom supprimé ou un motif mal adapté.
Ce sont des variantes de contenu des constats M14b et M16d2, pas un prétendu
rejeu byte-identique de leurs anciens patches.

| Cas final | Résultat et raison constatée |
| --- | --- |
| Exactitude des références effacée | Rejet dans la preuve de `Followed.references_exact` : l’extension portée ne peut plus être justifiée égale à celle de l’histoire produite. |
| Fait d’absence effacé | Rejet de `ResponseEvidence.missing_absent` et de la spécification : `resolveHandle register handle = none` n’est plus justifiable depuis le témoin affaibli. |
| Source riche remplacée par le runtime, preuves sémantiques rétablies | Le build complet passe ; le contrôleur rejette le vrai champ `sourceEvent`, qui n’applique plus l’opération riche. |
| Même remplacement, observateur auxiliaire laissé riche | Même rejet : le contrôle porte sur le champ du record effectif, pas sur l’auxiliaire inutilisé. |
| Auxiliaire riche légitime | Build complet et contrôle compilé acceptés. La forme syntaxique initiale n’est pas artificiellement imposée. |

Empreintes pour retrouver les livrables extérieurs sans les importer :

| Matériau | SHA-256 |
| --- | --- |
| Script autonome de contrôle des raccords | `fb48ed7d682fced66a7e6d09d61c77b9e3d589dd747c9fd658fb8d093a97d36d` |
| Protocole figé de la campagne des cinq cas | `12b460afd37def45a0850882113e21e715f83840a3dd88a2a078f58067bbfa53` |
| Résultats des cinq cas | `448ac4a32ce7f2564719f9c1b84b96070f3cbdaa4dc534be14e32f130b998eb9` |
| Bilan final des neuf commandes et de la conservation | `6f563a22906b86f3eba69dca793327fe591a562c3089050aea0b969bfeb4ded7` |

### 11.4. Limites et essais préparatoires conservés

Une première préparation de copie a échoué sur la longueur des chemins
Windows, avant tout cas scientifique. Une campagne préparatoire a ensuite
validé les deux effacements, mais s’est arrêtée sur une inférence de
projection d’égalité dans le cas du pont. Les extrémités de cette projection
ont été rendues explicites dans les preuves, sans changer leur énoncé ;
la campagne finale accepte bien la reconstruction sémantique avant le rejet
du chemin substitué. Un build préparatoire lancé en doublon a été interrompu ;
il ne figure pas parmi les réussites. Ces essais et leurs logs ne sont pas
écrasés par la validation finale propre.

Les contrôles de code compilé restent ceux d’une analyse bornée avec
frontières explicites ; les mutations ne prouvent pas la sécurité de Lean
arbitraire ni la nécessité universelle d’une écriture de preuve particulière.
Le lemme d’égalité du pont ne suffit pas, seul, à garantir l’indépendance de
son chemin de calcul : cette distinction reste visible dans le bilan.

La clôture ci-dessus est locale, sur les fichiers identifiés par leurs
empreintes et leur diff depuis HEAD. Aucun commit, push, envoi à Aristotle
ou fusion n’a été réalisé pour ce lot. Le protocole d’audit futur devra
désigner le SHA exact après autorisation de publication, sans utiliser le
verdict historique comme validation de ce nouveau contenu.
