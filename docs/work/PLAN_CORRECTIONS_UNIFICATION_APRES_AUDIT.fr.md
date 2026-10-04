# Plan de correction de l’unification après audit indépendant

## 1. Objet et statut

Corriger les défauts de l’unification relevés par notre audit, sur la branche
`codex/unified-foundation-master-instance`, sans altérer la cible scientifique,
la méthode constitutive, l’agent ajouté ensuite ni le chantier de signatures.

Ce document est un plan, pas une déclaration de corrections déjà réalisées.
Sa préparation n’autorise ni modification du code, ni commit, push, changement
de branche, soumission d’audit ou fusion. Il s’agit d’un document de chantier à
retirer de l’arbre destiné à `main` lors d’une intégration explicitement autorisée.

Références vérifiées le 4 octobre 2026 :

| Référence | Valeur |
| --- | --- |
| Dépôt | `JohnDoe-collab-stack/relational-perimeter` |
| Branche | `codex/unified-foundation-master-instance` |
| HEAD étudié | `9354e757e9dc2fbd429c34ff6cf9990140b6eed9` |
| Commit de notre audit d’unification | `8468f88448c51a0cd0ae178865fd014968131c47` |
| Ajout scientifique ultérieur de l’agent | `f6c6d2c051ae0886056d47cf5357253c137a1319` |
| Base `main` de l’audit | `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685` |
| Projet de notre audit | `7f481268-2e92-4924-8300-ce9707678919` |
| Tâche de notre audit | `a08baec2-f5e6-4400-a255-c088e488cfdb` |
| Rapport lu | `audit/UNIFIED_MASTER_REPAIR_SCIENTIFIC_AUDIT.md` |

Le rapport a été récupéré en lecture seule depuis le résultat de ce projet.
Les sections 9 à 12, 16 et 17 et les patches M04d, M15g, M20i ainsi que
`ForgedPrefix.lean` ont été confrontés aux sources actuelles.

Ses deux verdicts ne doivent pas être confondus :

- cible scientifique immuable : `EXACT TARGET ESTABLISHED` ;
- nouvelle unification : `UNIFICATION REQUIRES CORRECTIONS`.

Les six fichiers qui portent les défauts principaux, listés dans la section 4,
n’ont pas changé entre le commit audité et le HEAD étudié. L’ajout agent est
postérieur : notre rapport d’unification ne constitue pas son audit.

## 2. Cible scientifique maintenue intégralement

> Dans ce cadre, la constitution relationnelle des dépendances est primitive. Le calcul produit lui-même, pendant son exécution et à partir de ce qu'il a déjà produit, sa décomposition opérationnelle et détermine ainsi quelles alternatives doivent continuer à être traitées comme des obligations indépendantes.
>
> Cette exécution ne produit pas d'explosion exponentielle de la largeur opérationnelle : bien que le déploiement extensif des profils constitués ait une largeur 2^n, le régime exécuté les regroupe en une seule obligation sans identifier les profils eux-mêmes.
>
> Dans la classe binaire formalisée, une largeur opérationnelle exponentielle apparaît si et seulement si le régime impose de conserver séparément toute la multiplicité extensive, c'est-à-dire si son application carry est injective.
>
> L'explosion exponentielle de la largeur opérationnelle est donc démontrée ici comme l'effet exact de cette exigence extensive de conservation indépendante, et non comme une conséquence nécessaire de la structure relationnelle du problème elle-même.

Conserver aussi sa portée formelle déjà explicitée :

- le `iff` caractérise la pleine largeur `2^stageCount` des régimes finis
  surjectifs ; il ne caractérise pas toute fonction de croissance exponentielle ;
- dans la réalisation publique, `stageCount = input + 1` ;
- les politiques partielles conservent leur largeur `2^k` et leur statut de
  comparaisons sur les rôles, sans devenir des découvertes supplémentaires ;
- l’extensivité est une lecture quantitative des profils constitués, non une
  nouvelle couche qui constituerait les rôles ;
- le lemme cardinal général n’a pas besoin des relations. Ne pas lui fabriquer
  une dépendance artificielle pour satisfaire un test ;
- le présent lot n’ajoute aucune revendication de coût total, mémoire physique
  constante, résolution générale de SAT ou oubli de toute chronologie.

## 3. Application de la méthode à chaque correction

Les principes et les sections 1, 4 et 5 de la méthode fournie ont été relus,
en particulier la distinction entre formation, production, consommation par
la preuve et conservation sous transport.

Pour chaque objet corrigé, conserver explicitement les cinq éléments suivants :

1. **Producteur** : l’opération qui le forme réellement.
2. **Entrées** : les occurrences déjà produites lues par ses ports typés.
3. **Indices** : l’origine, le support, la source et la cible auxquels il appartient.
4. **Transport** : l’application construite sur ces occurrences précises.
5. **Lois consommées** : lecture, distinction, composition, admission ou retour,
   selon l’interface concernée.

Application dans ce chantier :

| Objet | Détermination à conserver | Réparation attendue |
| --- | --- | --- |
| Préfixe conservé | Origine constituée, exécution et support terminal de cette origine | Une frontière égale ne permet plus de substituer un autre support initial. |
| Admission future | Témoins du contrat déjà défini sur la mémoire réellement projetée | Disponibilité de `advance`, passage des admissions dans les deux sens, lois fermées sur le même maître. |
| Références | Occurrences anciennes dans le support effectivement prolongé | Injectivité et composition consommées par le certificat, pas seulement disponibles dans un type. |
| Projections du maître | Données du résultat partagé, non une seconde exécution égale | Contrôles compilés sur toutes les entrées concernées. |
| Lecteurs conservés | Continuations produites sous le contrat restreint | Ne pas confondre absence de champ d’archive et absence de capture dans une fermeture. |

Ne pas utiliser une bijection des porteurs comme preuve de préservation des
relations. `Support.Extension` est un plongement construit qui préserve les
références et leurs lectures ; il n’exige pas de bijection avec les ressources
nouvelles. Les actions dirigées sur continuations gardent leur loi séparée de
préservation ; elles ne deviennent pas des transports réversibles.

Une égalité de résultats Lean ne remplace jamais la vérification du partage
d’une exécution compilée. Réciproquement, un contrôle de graphe C ne prouve
pas à lui seul une loi constitutive ou un théorème de mémoire physique.

## 4. Diagnostic exact sur le code actuel

| Défaut | Source actuelle | Constat et portée |
| --- | --- | --- |
| R04 : origine générique insuffisamment déterminée | [MasterResourceExecution](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MasterResourceExecution.lean), `ProducedPrefix`, vers la ligne 316 ; [UnifiedPublicCertificate](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean), `Growth` et `resource_history_extension` | `originBoundary` fixe seulement la frontière de `origin`. L’audit construit une origine comportant une ressource supplémentaire, la même histoire effacée et un autre curseur terminal, puis obtient un `Growth` valide. Le chemin public `Instance.grow` utilise déjà la bonne origine. |
| R01 : admission de `advance` non fermée | [ProducedProfileContinuation](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ProducedProfileContinuation.lean), `allow` ; `UnifiedPublicCertificate.Facts`, vers la ligne 460 | `allow (.advance _)` est habité, mais `Facts` ne garantit pas cette disponibilité. M19b peut rendre cette admission vide tout en conservant les accords entre les deux implémentations. |
| R01 : injectivité hors du certificat ; composition à y expliciter | `Support.Extension` dans [ConstructedSupport](../../RelationalPerimeter/Constitution/Resources/ConstructedSupport.lean) ; `Instance.referencesThrough`, `Growth.referencesThrough`, `public_growth_composes`, `public_obligations_compose` | Les lois existent. `Facts` ferme les lectures et le prolongement en une seule histoire, mais pas explicitement l’injectivité des transports et les compositions déjà consommées par les clients de test. R09 est VERIFIED dans le rapport : la composition n’est pas un résultat faux à réparer. |
| R06 : multiplicité d’appels sous fermeture non suivie | [check-unified-codegen.py](../../scripts/check-unified-codegen.py), `producer_routes`, vers la ligne 78 | Le comptage suit les noms dans les corps, pas le nombre d’applications d’une fermeture. M20i applique la même fermeture à deux arguments et conserve deux exécutions réelles pour une route comptée. |
| R07 : consommateurs non contrôlés | Même script, `main` ; `Instance.stagewise`, `normalization`, `checkpoint` | M04d maintient un ancien calcul vivant dans `stagewise`. L’entrée n’est pas vérifiée. Le code actuel ne contient pas ce rejeu ; la garantie du vérificateur est incomplète. |
| R08 : capture d’archive dans les lecteurs | `ProducedProfileContinuation.produce/project`, `Assignment` ; [AllConstantsAudit](../../Tests/AllConstantsAudit.lean) | Les champs et leurs types sont contrôlés, pas les environnements des fonctions conservées. M15g capture le résultat historique dans chaque lecteur, sans changer son comportement mathématique. L’audit n’a pas trouvé cette capture dans le commit réel. |
| R11 : provenance permanente imprécise | [FR](../continuation-et-oubli-des-profils.fr.md) et [EN](../continuation-and-profile-forgetting.en.md), section des repères dans le code | « Reconstructions locales autonomes » masque une adaptation substantielle. Le rapport mesure 397 lignes longues communes sur 625 ; ce chiffre décrit un recouvrement textuel, pas une mesure de contribution scientifique. |

Ne pas appeler « défaut du résultat » ce qui est seulement une limitation du
vérificateur. Ne pas appeler « contrôle exhaustif » un test qui laisse passer
les exemples concrets du rapport.

## 5. Frontière de modification et travail concurrent

### 5.1 Fichiers où une correction est prévue

Les modifications d’implémentation restent dans cette liste :

- `MasterResourceExecution.lean` : contrat de `ProducedPrefix` et lois associées ;
- `UnifiedPublicCertificate.lean` : adaptation du préfixe, compléments de `Facts`
  et constructions qui les ferment ;
- `ProducedProfileContinuation.lean` : témoins positifs d’admission et lois
  d’accord nécessaires ; pas de changement du contrat futur ;
- `scripts/check-unified-codegen.py` : contrôles compilés et description exacte
  de leur portée ;
- `Tests/UnifiedMasterInstance.lean` et `Tests/ProducedContinuation.lean` :
  consommateurs des garanties réellement ajoutées ;
- contrôles de script et fixtures ciblées supplémentaires, si nécessaires ;
- les deux documents permanents de continuation, et la description des
  contrôles compilés du `README.md` ;
- inventaires de vérification uniquement si de nouveaux fichiers sont ajoutés.

Les neuf modules `Constitution/Grouping` n’ont pas à être réécrits pour
corriger une attribution. La licence du dépôt ne change pas.

### 5.2 Fichiers protégés

Ne pas modifier :

- les quatre fichiers fondamentaux ;
- `lean-toolchain`, `lake-manifest.json`, `LICENSE` et les figures existantes ;
- les sept modules `RelationalPerimeter/Agents/Constitutive/*.lean` ;
- `Tests/ConstitutiveAgent*.lean` et leur fixture de cible produite ;
- `scripts/check-agent-codegen.py` ;
- les documents scientifiques et le plan de l’agent ;
- `ARISTOTLE_CONSTITUTIVE_AGENT_AUDIT_PROMPT.md` et son reçu ;
- les protocoles et reçus déjà soumis de l’unification ;
- `docs/work/PLAN_SIGNATURES_CONSTITUTIVES_CONTINUATION_MINIMALES.fr.md`,
  présent comme fichier non suivi lors de cette étude ;
- `docs/resultats-constitution-calcul-alignement.fr.md`, apparu comme fichier
  non suivi pendant la relecture, et les modifications concurrentes du README.

Le README reste dans le périmètre uniquement pour une correction ciblée de
sa description des contrôles compilés. Relire son diff avant cette édition ;
préserver ses autres ajouts. Un conflit sur le même passage doit être signalé,
pas résolu en remplaçant le document par une ancienne version.

Le nouvel audit de l’agent est identifié dans son reçu par le projet
`9827d5fe-0cd1-40ce-9af6-69826c9af653` et la tâche
`d5cd5c55-6aa0-418f-8ed8-31888eeae028`. Ne pas l’interrompre, lui envoyer de
message, modifier sa cible ou le relancer pour ce chantier.

### 5.3 Dépendances partagées à protéger

Les modules de l’agent consomment notamment `UnifiedMaster.Instance`, ses
projections, `MasterResources.Cursor`, les producteurs de tête et
`ProducedContinuation.output_is_executed`. Aucun des sept modules ne consomme
actuellement `ProducedPrefix`, `Growth` ou `resource_history_extension`.

Le contrôle `check-agent-codegen.py` charge avec `runpy` le parseur et les
fonctions `bodies`, `reachable`, `select`, `absent`, `calls`, `producer_routes`
de notre contrôle. Conserver ces noms et leurs interfaces d’appel, ainsi que
la signification de leurs résultats. En particulier, `producer_routes` reste
un comptage de routes statiques : corriger sa description excessive, mais ne
pas transformer silencieusement cette fonction en analyse de multiplicité.
Le nouveau contrôle des applications et des captures dispose de fonctions
distinctes, appelées par notre vérificateur. Une extension du parseur peut
aussi rester locale à ce nouveau contrôle.

Vérifier les appels partagés depuis le contrôle de l’agent inchangé. Sa réussite
conserve sa portée actuelle ; elle ne devient pas automatiquement une garantie
renforcée de multiplicité ou de captures sur tous les chemins de l’agent.

Si une correction exige finalement de modifier un fichier protégé ou une
interface de l’agent, ce n’est plus ce lot : arrêter cette modification et
exposer précisément le besoin avant toute extension de périmètre.

## 6. Lot 0 : référence et isolement

Avant l’implémentation :

1. Relire `HEAD` et `git status`. Une évolution concurrente impose de réexaminer
   seulement son impact ; ne pas revenir en arrière ni écraser son travail.
2. Enregistrer hors dépôt les empreintes des fichiers protégés et la liste des
   modifications préexistantes, dont le plan de signatures non suivi.
3. Garder l’audit de l’unification à son SHA et l’audit de l’agent à son autre
   SHA. Un résultat de l’un ne vaut pas verdict pour l’autre.
4. Réaliser les builds propres et les essais destructifs dans une copie isolée
   de l’état de travail pertinent, jamais dans le répertoire partagé :
   `lake clean` ne doit pas effacer les artefacts utilisés par un autre agent.
   Cette copie doit inclure les modifications non commitées pertinentes et les
   ajouts de l’agent, pas seulement le dernier arbre Git. En relever l’inventaire
   et les empreintes pour identifier exactement l’état vérifié.
5. Ne pas changer la branche de ce répertoire, créer une branche supplémentaire,
   ni modifier un autre chat sans demande explicite.

Empreintes relevées pendant cette préparation :

| Fichier | SHA-256 |
| --- | --- |
| `SegmentedResidualRole.lean` | `c996d83b8b652a82993e13e2853d00b174e1a544ac571e441ffc48c097e11098` |
| `AbstractSegmentedTurning.lean` | `4f751df72732bff8438db58dd6d1529987c47a1bcebb1c8b2cf1c9ab651bb459` |
| `ExactTypeTransport.lean` | `ddcac9e058f3c738efd92fd7951b5d88260cde25b7905080512bbebd4dadfca0` |
| `StrongPerimetralTurning.lean` | `ad6a8625392f47756730a4fc16eb29cb373a4c313fcfbf9dde60df05019984bc` |
| `lean-toolchain` | `a0ada3782cd088719516bbfdf37b9e7032230e211bf424b85d952ee650c51091` |
| `lake-manifest.json` | `558a6999b82d0fac6c385da1a5cabeb50a594d6ecc7996f0be33014cfb68afa8` |
| `LICENSE` | `3ddf9be5c28fe27dad143a5dc76eea25222ad1dd68934a047064e56ed2fa40c5` |

Critère de passage : référence identifiée, fichiers concurrents préservés,
liste de modifications autorisées fixée. Aucun résultat d’un build précédent
ne sera attribué au code corrigé à venir.

Pendant cette relecture, HEAD est resté identique, mais le README et un nouveau
document scientifique ont évolué parallèlement. Leurs modifications ne sont
pas celles de ce lot. Les empreintes et l’inventaire devront être repris au
début de l’implémentation ; le plan n’autorise pas à revenir à l’état observé
avant ces ajouts.

## 7. Lot 1 : origine constitutive du préfixe

### 7.1 Contrat à renforcer

Aujourd’hui, `ProducedPrefix` contient `origin`, `originBoundary`,
`historyExact` et `cursorExact`. Les trois dernières lois parlent d’une origine
que le client peut remplacer par un support différent de même frontière.

Retenir un **indice d’origine complète**, fixé par le contexte consommateur,
au lieu d’un champ d’origine libre dans chaque nouveau témoin :

1. Paramétrer `ProducedPrefix` par le `MasterResources.Cursor` initial désigné.
   Cet indice conserve le support constitué, ses sortes, ses valeurs et ses
   références, et pas seulement la frontière de l’état.
2. Conserver l’accord entre sa frontière et les indices de l’ancienne histoire,
   ainsi que `historyExact` et `cursorExact`, relativement à
   `executeWithReferences count origin` pour **cet indice précis**.
3. Propager le même indice dans `Growth`, `resource_history_extension`,
   `Growth.producedPrefix` et `Growth.resume`. Le résultat ne doit pas effacer
   l’origine dans un paquet existentiel qui serait ensuite réutilisable pour
   n’importe quel maître de même frontière.
4. Fixer les interfaces de `Instance` à `master.origin`. `master.originExact`
   raccorde déjà cette origine complète à `publicOrigin input`, qui constitue
   son support initial. Une croissance reçue par ce maître doit porter le même
   indice, avant toute égalité de frontière ou d’histoire effacée.
5. Conserver la généricité : une autre origine constituée, explicitement
   désignée avant son exécution, peut avoir ses propres préfixes et extensions.
   Elle ne devient pas pour autant l’origine du maître public.

Les signatures ont donc la forme `ProducedPrefix origin history cursor` et
`Growth origin old cursor boundary extra`. C’est un contrat de typage prévu,
non du code déjà élaboré. Un éventuel accesseur `ProducedPrefix.origin` lit
l’indice ; il ne réintroduit pas un choix indépendant.

Ajouter deux champs librement choisis `origin` et `expectedOrigin`, puis une
égalité entre eux, ne corrigerait rien. L’origine attendue doit être fixée par
le maître ou le contexte d’appel et rester dans le type du résultat. Un champ
`certified : True`, une égalité de profondeur ou un label ne conviennent pas.

Ne pas imposer `initialCursor` à toutes les origines génériques : cette
restriction éliminerait sans nécessité les supports constitués préchargés.
Ne pas conserver une seconde API non indexée pour contourner l’ancrage.

### 7.2 Consommation du contrat

- `Instance.producedPrefix` est indexé par `master.origin` et consomme les
  accords du résultat déjà stocké, sans relancer le moteur.
- `Growth.producedPrefix` conserve exactement son indice d’origine après ajout
  du suffixe ; l’origine ne devient pas le curseur terminal.
- `resource_history_extension` reçoit le préfixe ainsi déterminé, appelle une
  fois le producteur du suffixe depuis son curseur terminal et attache ce résultat.
- `Growth.resume` consomme le préfixe produit par la première extension.
- `Instance.referencesThrough` n’accepte que les croissances ancrées à
  `master.origin` ; les deux arguments de `Growth.referencesThrough` gardent
  le même indice d’origine au cours de la reprise.
- Adapter les preuves structurelles qui éliminent `ProducedPrefix`, en
  conservant l’accord nécessaire entre frontière et indices de l’histoire.
  Les lois de lecture et composition ne changent pas.

Ne pas déplacer une seconde exécution dans la construction d’un témoin de
provenance. Les égalités dans `Prop` peuvent citer l’exécuteur comme
spécification ; les données utilisées en runtime restent le résultat partagé.

### 7.3 Vérification de fermeture

Préfixe vide, préfixe public non vide, suffixe vide, suffixe non vide et deux
reprises successives doivent rester constructibles. Les anciennes références
restent lisibles et distinctes.

Reprendre `ForgedPrefix` avec les nouvelles signatures : une faute d’arité
due à l’ancien exemple ne compte pas comme fermeture. Son curseur terminal
étranger ne doit pas pouvoir satisfaire `cursorExact` pour un préfixe indexé
par `master.origin`, ni son origine être substituée à celle de ce maître.
La différence de taille des supports permet de justifier ce refus sans se
contenter d’une confidentialité de constructeur ou d’un timeout.

Une chaîne explicitement indexée par l’origine augmentée reste légitime en
tant que chaîne différente. Vérifier aussi ce cas positif : le correctif
interdit la substitution à une origine attendue, pas l’existence d’autres
origines constituées. Fraîcheur, frontière égale et histoire effacée égale
ne suffisent pas à convertir l’une en l’autre.

## 8. Lot 2 : fermer le certificat sur le même maître

### 8.1 Admission positive et transport des témoins

Ne pas changer `allow` ni retirer une opération du contrat pour rendre les
preuves plus faciles. Le contrat reste `advance steps` et `inspect query`.

Construire une donnée d’admission de `advance` pour toute mémoire et tout
nombre de pas, y compris zéro, depuis la branche actuelle de `allow`.
Construire aussi la donnée d’admission historique correspondante.

Réutiliser `contract`, `all_requests_admitted` et `all_requests_reflected`
pour les passages des témoins entre histoire et mémoire projetée. Vérifier
les lois de retour sur les témoins locaux et leur composition sur les listes
finies, avec les accords `next_exact` aux étapes suivantes.

Ces lois de retour concernent les conversions concrètes du contrat de
`ProducedContinuation`, dont les témoins locaux sont les `ULift Unit` et
`ULift (PLift ...)` actuels. Ne pas les présupposer pour tous les contrats
génériques `Continuation.Exact`, qui n’exigent pas cette réversibilité dans
leur définition. Aucune réécriture de cette interface générique n’est requise.

Ajouter à `Facts` :

- la disponibilité de `advance` sur la mémoire de reprise ;
- sa disponibilité sur la source historique du même maître ;
- l’équivalence d’existence des admissions pour toute suite finie, dans les
  deux directions ;
- les lois de retour des applications de témoins réutilisées, si elles ne
  sont pas déjà consommées par une interface certifiée.

`Facts` est dans `Prop`. Les producteurs et conversions de témoins doivent
rester des définitions positives dans `Type`, disponibles séparément. Ne pas
extraire artificiellement une donnée calculable d’un simple `Nonempty`.
Les champs propositionnels sont prouvés depuis ces constructions, non utilisés
pour dissimuler leur absence.

Critère décisif : rendre `advance` vide comme dans M19b empêche désormais la
construction du certificat lui-même, même après suppression des tests qui
citent une déclaration par son nom.

### 8.2 Références : lecture, distinction et composition

Fermer dans `Facts` l’injectivité du transport `master.references`, puis de
`master.referencesThrough growth` pour les prolongements du même maître.
Les égalités doivent porter sur les vraies références typées, pas seulement
sur les numéros de leurs positions.

Réutiliser l’injectivité de `Support.Extension`, celle de la composée et ses
lois de lecture. Ne pas introduire une bijection avec le support étendu.

### 8.3 Deux prolongements du maître

Exprimer les accords génériques sur les deux résultats déjà construits :
un `growth` indexé par l’origine du maître et son `growth.resume more`.
Les résultats sont les arguments des lois ; les égalités de référence dans
`Prop` ne déclenchent pas un second calcul de ces résultats.

Fermer dans `Facts` :

- la composition des transports de références et la lecture conservée ;
- la composition des plongements de profils ;
- la composition des applications sur obligations.

Les lois publiques `public_growth_composes` et `public_obligations_compose`
restent vraies. Si elles sont spécialisées depuis une nouvelle loi générique
sur `Instance`, conserver leurs signatures scientifiques et ne pas reconstruire
`publicInstance` pour prouver une propriété d’un autre `master`.

Les clients doivent consommer ces garanties par `certificate.facts`, afin
qu’elles ne restent pas uniquement dans les tests ou dans des lemmes adjacents.
Cette fermeture certifie l’interface complète ; elle n’implique pas que chaque
preuve de largeur consomme chaque champ. Ne pas ajouter de dépendance factice
au théorème cardinal pour lui faire lire l’admission ou les références.

## 9. Lot 3 : contrôle compilé du partage et des consommateurs

### 9.1 Inventaire explicite des entrées

Conserver les contrôles existants et ajouter les projections :
`Instance.stagewise`, `Instance.normalization`, `Instance.checkpoint` et les
helpers nécessaires à leur construction.

| Entrée | Exigence compilée |
| --- | --- |
| `publicInstance` | Un appel initial au producteur, sans ancien exécuteur. |
| `resource_history_extension`, `Instance.grow`, `Growth.resume` | Une exécution nouvelle du suffixe, aucune reconstruction du préfixe. |
| `publicContinuation` | Initialisation et un suffixe partagés : deux appels d’entrée. |
| `publicGrowthTwice` | Initialisation et deux suffixes partagés : trois appels d’entrée. |
| `Instance.stagewise`, `Instance.normalization`, `Instance.checkpoint` | Aucun nouvel appel à l’exécuteur de ressources ou à l’ancien exécuteur. |
| `executeRequests` et les lecteurs de reprise | Pas d’accès au producteur historique ni au support riche. |

Ces nombres décrivent les appels d’entrée aux calculs partagés. Ils ne comptent
pas les appels récursifs internes du producteur et ne sont pas une borne de temps.
Le nouveau contrôle doit établir leur multiplicité sur les chemins compilés
couverts, pas reprendre le nombre de références textuelles comme résultat.

### 9.2 Fermer précisément M20i

Le graphe actuel compte l’apparition d’un nom de fermeture une fois, même
lorsqu’un helper applique cette fermeture deux fois. Le conserver en changeant
seulement le message de succès ne constitue pas une correction.

Ajouter une analyse locale distincte du comptage partagé `producer_routes` pour :

1. identifier les appels directs et les cibles de fermetures ;
2. suivre les alias et les passages de ces fermetures aux helpers ;
3. compter leurs applications aux sites `lean_apply_*` ou aux appels directs
   produits par le compilateur, pas seulement leur allocation ;
4. distinguer le résultat partagé puis projeté de deux applications effectives ;
5. conserver la frontière du producteur récursif ;
6. refuser de conclure lorsque la cible ou la multiplicité ne peut être résolue
   sur une entrée pour laquelle le contrôle annonce cette garantie.

Modèle précis de cette analyse :

- fixer un inventaire des formes C pertinentes observées sous Lean 4.33.1 :
  appels, allocation de fermeture et d’enregistrement, captures, alias,
  projections, application de fonctions, branchements et initialiseurs ;
- distinguer une **fonction fermée** de son résultat : allouer une fermeture
  productrice ne l’exécute pas ; appliquer cette fermeture deux fois produit
  deux appels, alors que projeter deux fois le même résultat n’en produit qu’un ;
- associer aux helpers des résumés paramétriques : applications de leurs
  paramètres fonctionnels, effets producteurs propres et fonctions retournées ;
  instancier ces résumés avec les cibles et captures du site d’appel ;
- additionner les effets séquentiels, mais ne pas additionner des branches
  mutuellement exclusives. Calculer un intervalle par chemin ; n’annoncer un
  nombre exact que si les bornes coïncident. Une seule borne n’est pas un
  compte exact ;
- arrêter l’analyse du producteur à sa frontière récursive déclarée ; refuser
  un cycle amont ou une cible indéterminée qui pourrait cacher un appel sur
  un chemin pour lequel une multiplicité est annoncée ;
- utiliser l’IR optimisé effectivement compilé : un calcul éliminé ne compte
  pas comme appel runtime. Rendre explicites les objets statiques et leurs
  initialiseurs sans compter la même allocation comme plusieurs exécutions.

Séparer également l’initialisation d’un module, effectuée une fois, des appels
par invocation d’une entrée. Une fermeture chargée depuis un objet statique
peut être appliquée plusieurs fois ; sa création unique n’en borne pas les
applications. Les sorties du contrôle doivent indiquer ces frontières de
comptage, la multiplicité obtenue et le chemin qui justifie un rejet.

Une forme inconnue n’est pas assimilée à « zéro appel ». L’échec fermé porte
sur les chemins sensibles déclarés couverts, pas sur tous les callbacks
arbitraires de la bibliothèque. Le parseur local doit couvrir les objets
constructeurs statiques, déjà suivis plus largement par le contrôle agent,
sans changer le sens des fonctions partagées.

Fermer le bypass M20i réel et conserver les contrôles des helpers, initialiseurs,
récursions étrangères et artefacts manquants. Ne pas viser ici un analyseur
général de tous les programmes C ou callbacks clients.

### 9.3 Fermer précisément M04d

Vérifier le chemin compilé depuis `Instance.stagewise`, même lorsqu’un ancien
résultat n’est utilisé que dans un tuple, une fermeture ou une opération de
diagnostic gardée vivante.

La version éliminée par le compilateur est classée séparément : elle ne réalise
pas un rejeu runtime. La version réellement maintenue doit être rejetée par
son appel, pas par une interdiction ad hoc du nom utilisé dans le patch.

## 10. Lot 4 : captures dans les lecteurs conservés

L’audit de schéma de `Memory` reste nécessaire, mais insuffisant. Le chemin
qui crée les lecteurs est dans `produce`, puis `project` transmet ces fonctions
déjà construites : inspecter seulement le corps C de `project` manque M15g.

Compléter le contrôle depuis les fabriques de source et de checkpoint :

- suivre la création des `Assignment` conservées et leurs environnements ;
- distinguer les valeurs réellement produites nécessaires à la lecture des
  paquets historiques `Source`, profil, résultat de normalisation, support et
  certificat ;
- suivre les captures dans les helpers de listes et les fermetures imbriquées ;
- examiner séparément les lecteurs, la sortie et l’état vivant conservés ;
- refuser une capture d’archive sur le chemin couvert, y compris lorsque la
  fonction obtenue est mathématiquement égale à la lecture autorisée.

Le critère n’est pas « toute donnée dérivée de l’histoire est interdite » :
les continuations sont précisément produites depuis cette histoire. Suivre
ce qui reste **accessible dans l’environnement retenu**, en distinguant les
projections autorisées des paquets historiques complets. La sortie produite,
les lecteurs de continuation et la provenance vivante nécessaire à la prochaine
recherche restent autorisés sous le contrat actuel.

Utiliser un suivi de flux avec les constructions et projections de champs
pertinentes, puis la création et la transmission des fermetures. La simple
accessibilité d’une fonction dans le graphe d’appels ne prouve ni la capture
ni sa durée de conservation. Inversement, une archive lue seulement pendant
la préparation n’est pas une archive conservée dans la mémoire de reprise.
Le contrôle doit distinguer ces deux cas, y compris à travers `List.map`.

Fermer M15g à l’endroit de la capture, sans changer l’identité mathématique
des sorties ni la représentation de l’agent. La simple conservation du nom
`readersExact`, ou le contrôle d’une absence de champ `Source`, ne suffit pas.

Si l’analyse ne peut pas établir l’origine d’une capture sur un chemin déclaré
couvert, rapporter cet échec ; ne pas déclarer la capture absente. Ne pas
réécrire les sept modules de l’agent pour faire passer ce contrôle.

La conclusion reste limitée aux fabriques et chemins publiés effectivement
contrôlés, sous Lean 4.33.1. Elle n’est ni une preuve de mémoire physique
constante, ni un contrôle général de toutes les valeurs fonctionnelles qu’un
client pourrait construire.

## 11. Lot 5 : documentation et provenance exacte

### 11.1 Lois et contrôles

Synchroniser les versions française et anglaise après les corrections :

- préciser l’origine complète exigée par le préfixe ;
- nommer les garanties désormais consommées dans le certificat ;
- séparer les accords mathématiques et les contrôles du calcul compilé ;
- décrire les entrées couvertes, les constructions de fermeture suivies et
  les cas qui restent hors portée ;
- ne plus affirmer sans cette distinction qu’un helper ou une fermeture
  « ne peut pas cacher » un second appel ;
- ne pas attribuer l’absence de capture au seul contrôle du schéma Lean.

Ne pas réécrire le paragraphe scientifique validé pour corriger le périmètre
plus faible d’un outil. Le précédent plan d’unification est un historique de
travail, pas une preuve que M04d est fermé : notre nouvel audit montre le
contraire pour cette variante précise.

### 11.2 Attribution permanente

La comparaison citée par l’audit est :

- dépôt : `JohnDoe-collab-stack/relational-foundations` ;
- commit : `c98864b4a2d806581c87770d28d8c47768480e12` ;
- licence examinée par l’audit : Apache-2.0.

Les modules concernés sont `BinaryReadout`, `ContinuationContract`, `ExactImage`,
`HistoricalExtension`, `Normalization`, `Projections`, `Reindexing`, `Rules`
et `Traces`, dans `Constitution/Grouping`.

La note permanente doit décrire une **adaptation aux interfaces locales**, et
non une reconstruction indépendante simplement « informée » par une comparaison.
Vérifier les notices d’origine avant d’en rédiger la forme exacte. Aucun import,
chemin de dépendance ou archive brute de l’autre dépôt n’est ajouté.

**Point à résoudre explicitement avant cette édition :** les règles fournies
pour le dépôt interdisent les noms de projets extérieurs dans les fichiers
publiés, tandis que R11 demande précisément de nommer l’origine dans une note
permanente. Ne pas inventer une exception silencieuse. Faire valider une
attribution documentaire limitée aux références de réemploi, sans dépendance
scientifique ou technique ; si l’interdiction reste littérale, R11 reste ouvert.
Ce point ne suspend pas les corrections de code et de certificat.

## 12. Conservation de l’agent et des résultats antérieurs

Contrôler sur l’état corrigé, sans modifier les modules de l’agent :

- `publicAgent`, `prepare`, `Session.execute` et `Session.executeAll` ;
- `all_executed_determinations_followed` ;
- `all_future_requests_exact`, `all_future_events_exact`, `all_future_reads_exact` ;
- `admissions_forward`, `admissions_reflected` et les lois de retour ;
- `obtain_produces_and_returns`, `obtain_work_exact`, `refusal_preserves_memory` ;
- `initial_profile_not_recoverable` et `forgotten_sources_same_future` ;
- les accords entre le registre, les références historiques et leurs transports ;
- le certificat de l’agent, ses calculs concrets et son contrôle compilé inchangé.

Conserver aussi les résultats qui fondent l’unification :

- même carrier de classe et d’exécution, par réduction définitionnelle ;
- `iff` directement applicable au régime exécuté ;
- source de pleine largeur `2^(input+1)` et régime exécuté de largeur un ;
- deux profils distincts portés ensemble, sans identification des sources ;
- image exacte des sorties et codétermination ;
- actions sur continuations arbitraires, préservation et cohérence des traces ;
- partage du producteur et localité des têtes avant leur suite ;
- retour des transports de codage et d’image ;
- oubli du profil normalisé sous le même contrat futur ;
- reconstruction chronologique sous son contrat riche, sans contradiction
  fabriquée avec l’oubli du profil.

L’ajout de l’indice d’origine à `ProducedPrefix` et `Growth` est une correction
d’interface à déclarer. Les lois génériques restent quantifiées sur les
origines constituées désignées ; ne pas les réduire au seul support initial
public. La compilation seule ne remplace pas la comparaison des énoncés.
Ne pas supprimer un théorème scientifique pour accommoder un nouveau contrat.

## 13. Validation proportionnée et reproductible

Les contrôles vérifient les réparations ; ils ne les remplacent pas.

### 13.1 Validation Lean

Dans la copie isolée correspondant exactement à l’état corrigé :

```text
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
```

Utiliser la toolchain épinglée, sans la modifier. Vérifier toute déclaration
écrite à la main avec le sweep complet, pas seulement les blocs sélectionnés.
Chaque fichier Lean modifié ou ajouté garde un seul bloc final d’audit,
avec les noms complets réels et sans axiome. Les producteurs dans `Type`
doivent rester compilables ; aucune hypothèse externe ne ferme une réalisation.

Le nombre total de fichiers est recalculé depuis l’inventaire final. Ne pas
réutiliser les 171 fichiers de notre ancien audit pour ignorer ceux de l’agent.

Après `lake update`, comparer le manifeste à la référence. Ne pas accepter
silencieusement une dépendance nouvelle pour faire passer les builds.

### 13.2 Contrôles ciblés de fermeture

| Correction | Contrôle concret | Résultat requis |
| --- | --- | --- |
| Origine du préfixe | Cas de `ForgedPrefix` adapté aux nouveaux indices, support augmenté mais même frontière | Refus de l’utiliser comme préfixe du maître public ; exécution distincte depuis cette origine explicitement désignée toujours constructible. |
| Admission de `advance` | Construction du témoin puis variante à admission vide | Témoin construit ; certificat non constructible avec admission vide. |
| Injectivité | Lecture de la garantie depuis `certificate.facts` et composition sur deux suffixes | Preuve sur les vraies références, sans ajout d’hypothèse externe. |
| Composition | Profils, obligations et références du même maître et de ses résultats conservés | Lois accessibles par le certificat et inchangées pour les clients publics. |
| M20i | Fermeture productrice appliquée deux fois ; variantes helper et alias ; partage du résultat et branches exclusives en contrôles positifs | Deux applications détectées ; une seule production partagée ou conditionnelle n’est pas comptée deux fois. |
| M04d | Ancien calcul gardé vivant dans `stagewise`, puis variantes des autres projections | Rejet sur le chemin compilé concerné. |
| M15g | Archive capturée dans un lecteur puis transmise par `project` ; lecture d’archive uniquement pendant la préparation en contrôle positif | Capture retenue signalée ; sorties, lecteurs légitimes et provenance vivante autorisée conservés. |
| Agent | Modules, trois tests, fixture et contrôle compilé inchangés | Vérifications réussies sur la nouvelle base, empreintes des fichiers protégés inchangées. |

Un fixture négatif doit échouer pour sa raison annoncée. Un timeout, un module
absent, une erreur de syntaxe ou une déclaration renommée n’est pas une preuve
de fermeture. Une mutation rejetée uniquement par un test qui cite un nom doit
être distinguée d’une impossibilité de construire le certificat.

Geler les scripts et patches avant les exécutions de confirmation. Conserver
hors dépôt la commande, la version du compilateur, les empreintes et les sorties,
sans écraser les preuves de référence. Les auto-contrôles du parseur ne valent
pas vérification du C généré par les variantes réelles de M20i/M04d/M15g.

### 13.3 Contrôles documentaires et de périmètre

- comparaison octet par octet des fichiers protégés ;
- inventaire des déclarations et de leurs énoncés, base et ajout agent compris ;
- couverture des modules, stratification et absence d’import inverse depuis
  la constitution vers l’agent ou la computation ;
- liens locaux, correspondance FR/EN et cohérence des descriptions avec les
  garanties effectivement obtenues ;
- comparaison exacte de la cible citée en section 2 avec le texte validé,
  indépendamment des nouveaux résumés techniques ;
- absence de caches, fragments bruts et résultats générés dans le diff prévu ;
- distinction explicite entre exécution native Windows et PowerShell sur Linux.

Ne pas annoncer la plateforme Windows vérifiée si seul PowerShell Linux l’a été.
Ne pas annoncer un verdict indépendant sur les corrections avant réception de
ce verdict sur le SHA correspondant.

## 14. Ordre et critères d’arrêt

Ordre d’implémentation :

1. Référence et isolement.
2. Indice d’origine complète du préfixe, puis passage à la croissance et à la reprise.
3. Témoins d’admission, injectivité et compositions, puis fermeture de `Facts`.
4. Entrées compilées manquantes, multiplicité des appels et captures.
5. Compatibilité avec le contrôle partagé de l’agent.
6. Documentation exacte et attribution après résolution du point R11.
7. Vérification complète de l’état final et comparaison des fichiers protégés.

Arrêter le lot concerné et exposer le fait, sans affaiblir la cible, si :

- l’origine désignée ne peut pas être conservée avec les données réelles du maître ;
- une nouvelle garantie nécessite une hypothèse extérieure non construite ;
- une correction impose une modification de l’agent ou de son contrat ;
- une forme C pertinente échappe à l’analyse tout en restant déclarée couverte ;
- une preuve antérieure est perdue ou son énoncé affaibli ;
- une modification concurrente rend la référence périmée ;
- l’attribution permanente reste incompatible avec l’instruction sur les noms
  extérieurs.

Ne pas remplacer un de ces blocages par un changement de vocabulaire qui
annonce malgré tout la fermeture de la propriété manquante.

## 15. Définition de la livraison de ce lot

La correction locale est terminée seulement lorsque :

- l’origine du préfixe ne peut plus être remplacée comme dans R04 ;
- les garanties manquantes sont réellement fermées dans le certificat ;
- M20i, M04d et M15g sont détectés sur les chemins que les outils couvrent,
  avec une description honnête des limites restantes ;
- les sources et résultats protégés, y compris l’agent, sont conservés ;
- les vérifications complètes ont été exécutées sur l’état final isolé ;
- les documents FR/EN décrivent cet état et la provenance est réglée ;
- le diff reste strictement dans notre périmètre.

Cette clôture locale ne vaut ni nouvel audit indépendant, ni autorisation de
publication ou de fusion. Un futur audit d’unification devra viser le nouvel
état corrigé ; l’audit agent déjà lancé conserve sa cible scientifique figée.
Une intégration dans `main` nécessite une demande explicite et ses propres
vérifications après fusion. Les documents temporaires, dont ce plan, doivent
être absents de l’arbre intégré.

## 16. État de l'implémentation vérifié le 4 octobre 2026

L'utilisateur a ensuite demandé l'implémentation de ce plan. Les sections
précédentes décrivent la référence et les exigences de départ, pas le code
corrigé. Les corrections techniques du présent lot sont réalisées ; R11 reste
ouvert par décision explicite de l'utilisateur. Il ne faut donc pas annoncer
la clôture intégrale de l'unification ni un nouveau verdict indépendant.

### 16.1 Corrections réalisées

| Point | Construction ou contrôle obtenu |
| --- | --- |
| R04 | `ProducedPrefix origin history cursor` est indexé par l'origine complète. Le même indice traverse `Growth`, le suffixe et la reprise. Le maître désigne `master.origin`. Une origine augmentée reste utilisable sous son propre indice, mais son curseur terminal est prouvé incompatible avec le préfixe de l'origine originale, pour tout nombre d'étapes. |
| R01, admission | `advance_admission` et `source_advance_admission` produisent des témoins dans `Type`. Le certificat ferme leur existence, l'admission des suites finies dans les deux directions et les lois de retour des témoins concrets. Le contrat futur reste inchangé. |
| R01, références et composition | `Facts` ferme l'injectivité des références initiales et prolongées, les lectures composées et les compositions de références, profils et obligations. Les tests consomment ces champs du certificat sur le même maître. |
| R06 | Une analyse distincte compte les applications du producteur à travers helpers, alias, fermetures et objets statiques. Elle distingue partage et appels multiples, ainsi que branches exclusives. Le comptage statique partagé `producer_routes` conserve son interface et sa signification. |
| R07 | Les wrappers compilés complets de `stagewise`, `normalization` et `checkpoint` sont contrôlés : absence de nouvel exécuteur et multiplicité zéro. La disparition d'un helper optimisé n'est pas prise comme motif de rejet causal. |
| R08 | Le flux depuis `produce`, `Instance.source` et `Instance.checkpoint` est suivi jusqu'aux champs conservés, y compris les lecteurs et leurs captures à travers les helpers de listes. Les paquets d'archive sont distingués des valeurs exécutées et projections vivantes autorisées. |
| Documentation | Les documents FR/EN et le paragraphe ciblé du README décrivent les nouvelles garanties et leurs frontières. « Reconstructions locales autonomes » est remplacé par « adaptations aux interfaces locales ». Cette rectification n'est pas présentée comme la résolution de l'attribution R11. |

L'analyse C est bornée aux entrées et formes déclarées sous Lean 4.33.1.
Elle refuse les formes sensibles indéterminées ; elle n'est ni un analyseur
général des callbacks clients, ni un théorème de coût ou de mémoire physique.
Les sélections de la valeur exécutée et de la provenance vivante sont des
frontières autorisées explicitement documentées.

L'interface générique d'origine a changé intentionnellement : l'origine
anciennement stockée librement devient un indice du contrat. Aucun théorème
scientifique n'a été supprimé pour contourner cette correction ; les
quantifications sur des origines constituées génériques sont conservées.

### 16.2 Validation du premier lot et périmètre exact

Une copie isolée de `9354e757e9dc2fbd429c34ff6cf9990140b6eed9` contient
uniquement notre correction et l'agent déjà publié dans cette base. Elle ne
contient pas le chantier concurrent, encore non commité, des signatures.
Les sources de notre lot y sont identiques par SHA-256 à celles du répertoire
partagé. Le README de cette copie porte seulement notre paragraphe ciblé ;
le lien documentaire ajouté par l'autre agent est conservé dans le répertoire
partagé.

| Vérification | Résultat |
| --- | --- |
| `lake clean`, puis `lake build +RelationalPerimeter` | Succès, 160 jobs ; aucun warning Lean ni audit axiomatique fautif. |
| `lake build` après ce build propre | Succès, 183 jobs ; aucun warning Lean ni audit axiomatique fautif. |
| Sweep de tous les modules | 17 992 constantes, 180 modules audités ; zéro exception écrite à la main, 360 exceptions générées par le compilateur distinguées. |
| `scripts/verify.ps1`, PowerShell natif sur Windows | Succès sur 181 fichiers Lean et 23 fixtures négatives. |
| `scripts/verify.sh`, Git Bash natif sur Windows | Succès sur les mêmes 181 fichiers et 23 fixtures. |
| Contrôle compilé de l'agent, inchangé | Succès. |
| `lake update` | Succès ; manifeste inchangé. |
| `git diff --check` | Succès sur la copie validée et le répertoire partagé. |
| Liens locaux des documents modifiés et du plan | Valides. |
| Fichiers fondamentaux, licence, toolchain et agent protégés | Empreintes préservées. |
| Répertoire partagé | HEAD et branche inchangés ; aucune modification de l'index ni publication. |

Les sources Lean ont été construites proprement avec le protocole v3. La
dernière sélection des wrappers C, corrigée ensuite sans changer ces sources
Lean, a été vérifiée par les deux scripts complets avec le protocole v4.
Les empreintes vérifient que les sources Lean sont identiques entre ces deux
passes. Les deux scripts ont donc effectivement testé la version v4 du
contrôle C, pas seulement sa version intermédiaire. Une relecture ultérieure
a trouvé le défaut de reconnaissance des frontières décrit en section 17 ;
la v4 ne doit pas être présentée comme sa correction.

Cette validation ferme notre lot sur la base publiée. Elle n'attribue pas
un résultat de vérification au chantier parallèle, et ne vaut pas validation
de l'ensemble de ses modifications présentes aujourd'hui dans le répertoire
partagé. Aucun fichier de ce chantier n'a été modifié par notre correction.

### 16.3 Contrôles ciblés réellement exécutés

Les scripts et patches ont été figés avant leurs runs de confirmation, puis
leurs empreintes contrôlées. Les trois variantes suivantes compilent dans
la copie jetable, sans warning Lean ni axiome ajouté ; le contrôle C les
rejette ensuite pour leur effet réel :

| Variante | Rejet constaté |
| --- | --- |
| Producteur appelé deux fois via une fermeture et un helper | Intervalle d'applications `[2, 2]` au lieu de `[1, 1]`. |
| Ancien exécuteur gardé vivant dans `stagewise` | Dépendance transitive interdite vers l'ancien exécuteur. |
| Résultat historique capturé dans chaque lecteur, sans changer les énoncés mathématiques | Archive retenue détectée dans l'environnement des lecteurs. |

La variante qui rend `advance` vide est rejetée lors de l'élaboration de
son témoin positif, par incompatibilité `Unit` / `Empty`.
Les preuves de rejet d'un préfixe étranger et les constructions positives
depuis une origine augmentée font partie des tests Lean de production.

Les essais intermédiaires non concluants sont conservés séparément :
dépendance axiomatique d'un lemme auxiliaire ensuite remplacé, sélection
d'un helper optimisé ensuite remplacée par celle du wrapper complet, et
compte de lignes incorrect dans un patch ensuite corrigé dans une nouvelle
version. Ils ne sont pas comptés comme confirmations positives.

Les preuves brutes sont hors dépôt :

- copie de build et protocoles `validate-repair-v3.ps1` et
  `validate-repair-v4.ps1` :
  `C:/Users/frederick/AppData/Local/Temp/perimeter-repair-validation-6b65a858abd647b396274c758a680c51` ;
- patches, protocole `confirm-repair-v4.ps1`, résultats des trois variantes,
  contrôle des empreintes, admission vide et comparaison finale :
  `C:/Users/frederick/AppData/Local/Temp/perimeter-unification-repair-1dcd57e60519493382044773d0bfd44f`.

Le driver de mutation v4 termine avec le statut natif 1 de son dernier
contrôle négatif attendu. Les trois confirmations, la stabilité des entrées
figées et la restauration des sources sont vérifiées séparément par
`confirm-repair-outcomes-v1.ps1`, qui réussit avec le statut 0. Ce statut
attendu n'est pas présenté comme un build réussi.

### 16.4 Point restant et actions non effectuées

L'utilisateur a refusé l'exception documentaire permettant de nommer
l'origine externe et demandé de garder cette correction ouverte. **R11 reste
donc ouvert.** Aucun nom de projet extérieur n'a été ajouté aux documents
permanents modifiés. L'attribution devra être réglée avant toute clôture
complète ou intégration qui exige sa résolution.

Aucun commit, push, changement de branche, lancement d'audit indépendant
ou merge n'a été effectué pour ce lot. Le paragraphe scientifique immuable
de la section 2 n'a pas été modifié. Le présent document reste un document
de chantier à retirer de l'arbre destiné à `main`.

## 17. Correction de la reconnaissance des frontières du contrôle C

### 17.1 Défaut constaté et correction à la racine

La relecture postérieure à la validation v4 a montré qu'une fonction étrangère
contenant `ExecutedChainNormalization_target___redArg` dans son nom, ou
finissant par `LiveContinuation_project`, recevait à tort une politique de
frontière autorisée. Un helper réellement compilé par Lean a confirmé le
défaut : l'archive était ignorée sous ce nom, puis détectée après un simple
renommage du même helper. R08 n'était donc pas complètement fermé par v4.

Le contrôleur ne reconnaît plus ces frontières par fragment ou suffixe.
Il résout chaque déclaration par son symbole généré entièrement qualifié et
vérifie son unique artefact C de définition. Une déclaration absente, définie
dans un autre artefact ou ambiguë est rejetée. Un prototype importé ne suffit
pas à établir cette origine. Le registre explicite distingue les paquets
historiques des sélections de valeur exécutée et de projection vivante
autorisées par le périmètre du contrôle.

Cette politique est appliquée dans la même opération d'analyse aux appels
directs et aux appels via fermeture. Les getters historiques sont eux aussi
résolus exactement. Tout helper au nom ressemblant reste analysé normalement
et ne peut plus effacer la marque d'archive par son seul nom.

Les autotests couvrent les appels directs et indirects, les deux anciennes
formes de noms ressemblants, les origines absentes, étrangères ou ambiguës,
les politiques invalides et les arités incorrectes. Les interfaces statiques
partagées avec le contrôleur de l'agent sont inchangées.

### 17.2 Vérification de la version corrigée

Les deux scripts complets ont réussi dans la copie isolée décrite en 16.2,
avec les trois fichiers Python finaux et les documents FR/EN finaux. Le
protocole `validate-repair-v5.ps1`, figé avant le run, vérifie les empreintes
avant et après. Il contrôle également que les sources Lean sont identiques
à celles du build propre v3 : aucune source Lean n'a changé pendant cette
correction du vérificateur.

Résultats : 181 fichiers Lean, 23 fixtures négatives, 17 992 constantes,
180 modules, zéro déclaration écrite à la main dépendant d'un axiome.
Le contrôleur C unifié et celui de l'agent passent. `lake update` ne change
pas le manifeste. `git diff --check` réussit. PowerShell et Git Bash ont été
exécutés nativement sur Windows ; il ne s'agit pas d'une vérification Linux
extrapolée à Windows.

Le helper réellement compilé conserve maintenant la marque d'archive sous
son nom ressemblant comme sous son nom ordinaire. Le protocole figé
`confirm-boundary-repair-v2.ps1` a ensuite confirmé quatre variantes dans
la copie jetable :

| Variante compilée sans warning ni axiome ajouté | Résultat du contrôle corrigé |
| --- | --- |
| Double application via helper et fermeture | Rejet pour `[2, 2]` applications, au lieu de `[1, 1]`. |
| Replay dans un wrapper de projection | Rejet pour dépendance transitive vers l'ancien exécuteur. |
| Lecteurs capturant le résultat historique | Rejet pour archive retenue dans les lecteurs. |
| Lecteurs capturants appelant un helper au nom ressemblant | Même rejet pour archive retenue. |

Chaque variante conserve les énoncés scientifiques. Les adaptations de
preuves de lecteurs restent constructives et les nouveaux helpers du patch
sont inclus dans son unique bloc d'audit final. Les patches et scripts ont
été figés et hachés avant exécution, puis leurs empreintes vérifiées ; les
sources de la copie jetable ont été restaurées. Le protocole v2 termine avec
le statut 0.

L'essai v1 du lecteur nommé échouait dans une preuve auxiliaire de
simplification. Ce n'était pas un rejet par le contrôle de capture : son
log est conservé comme essai non concluant, et le patch corrigé v2 constitue
une nouvelle version plutôt qu'une modification silencieuse du premier run.
Les journaux v5, les empreintes et les confirmations v2 restent dans les
deux répertoires externes déjà indiqués en 16.3.

### 17.3 Portée et état du chantier

La correction porte sur les Python du contrôle C et sa documentation.
Elle ne modifie ni la cible scientifique, ni les preuves Lean du premier lot,
ni les quatre fichiers fondamentaux, ni le contrat futur, ni les modules de
l'agent protégés. Le périmètre reste un contrôle borné des chemins et
frontières déclarés, pas un théorème général sur le tas ou les callbacks
arbitraires.

Les ajouts concurrents non commités restent hors du périmètre validé et
intacts. R11 reste ouvert par décision de l'utilisateur. Aucun commit,
push, changement de branche, audit indépendant ou merge n'a été effectué.
