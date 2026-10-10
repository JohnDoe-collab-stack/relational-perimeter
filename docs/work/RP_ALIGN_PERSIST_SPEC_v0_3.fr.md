# RP-ALIGN-PERSIST-01 — Spécification proposée v0.3

## Alignement opératoire persistant, accomplissement et reprise fidèle

**Statut :** proposition de spécification ; ni implémentation, ni nouveau théorème compilé, ni audit indépendant.  
**Socle public de référence, hérité de la v0.2 et non revérifié dans la v0.3 :** `JohnDoe-collab-stack/relational-perimeter`, branche `codex/ai-alignment-under-contract`, commit `f30196e4a8ae2b77b0d061c1e03cccd236265013`. Son parent est `6575de4a219301cb42c93c842de7814145b013ff`, référence historique de la v0.1.  
**Chantier supplémentaire documenté dans la v0.2 :** fichiers locaux de cette branche, consultés alors en lecture seule le 10 octobre 2026. La référence de branche locale lue vaut également `f30196e4…`, mais les sources de travail comprennent des incréments supplémentaires. Ces lectures ne constituent ni un snapshot Git nouveau ni une vérification exhaustive du worktree. L’annexe A distingue explicitement le public, le local relu et les obligations non qualifiées.  
**Travail réalisé pour cette version :** lecture intégrale de la v0.2 fournie, prise en compte des cinq renforcements humains sur le secours exécutable, les moyens de contrôle, la reprise et la vivacité de livraison ; rédaction et contrôles structurels du présent Markdown. Aucune nouvelle consultation du dépôt, qualification du worktree, compilation Lean, gate complète, exécution du modèle ou vérification physique. Les lectures et résultats historiques restent attribués à la v0.2. Aucun fichier du dépôt n’a été modifié.  
**Date :** 10 octobre 2026.  
**Autorité :** cette proposition ne modifie aucune source, aucun contrat existant, aucun ancrage scientifique et aucun résultat historique du dépôt. Les identifiants nouveaux ci-dessous sont proposés, non enregistrés.

Les termes **DOIT**, **NE DOIT PAS** et **PEUT** décrivent les exigences de la réalisation proposée. Ils ne décrivent pas des fonctionnalités déjà livrées.

## 1. Réanalyse et décision de périmètre

Le plan existant distingue conformité, exactitude des futurs après oubli et accomplissement positif. Dans sa classe documentaire à ordre reçu, l’ordonnanceur possède déjà une preuve d’accomplissement pour toute politique totale, en n tours contrôlés et au plus 2n tentatives. La reprise physique du présent complet, puis le raccord documentaire au modèle et les comparaisons du lot 7, restent les obligations à fermer au commit analysé. [R1]

Au socle public actualisé, le contrôle possède désormais son codec exact : slots, liaisons, file, contexte sous codec reçu, compteur et résumé. Le raccord au présent suppose encore le même stockage et le même dossier maître fournis. [R8]

Selon les lectures consignées dans la v0.2, le chantier local va plus loin : recettes typées des sept producteurs maître, codec de leurs enregistrements, restauration du couple assignation/lecteur mesuré, puis de l’assignation séquentielle avec ses invariants. Les sources `DocumentaryMasterFormation`, `DocumentarySequentialPortable` et `DocumentarySequentialCapture` ont été relues intégralement lors de la v0.2. La source locale `DocumentaryStatePortable` contient aussi un chargeur et `restored_exact` pour l’état couplé sous son hypothèse de formation ; sa chaîne transitive et son build n’avaient pas été requalifiés alors ; ils ne le sont pas davantage par la v0.3. [L1–L4]

La présente spécification NE DOIT PAS présenter ces composants comme absents ou les réimplémenter depuis zéro. Elle NE DOIT PAS non plus transformer la présence de leurs sources ou leurs relevés de développement en clôture du chargement du curseur entier, de toutes ses ressources et du présent complet. Les dépendances restantes sont qualifiées dans l’annexe A. [R2–R4, R8, L1–L4]

La cible proposée comporte **deux livraisons séparées** :

- **A — Fermer la réalisation persistante existante.** Achever les obligations des lots 6 et 7 sans remplacer les critères, les producteurs ou l’instance maître. Les tests documentaires sont une instance de réalisation, non la limite du cadre.
- **B — Étendre la préservation à des ressources consommables.** Construire une interface paramétrique, puis une instance positive où une action localement permise peut détruire la possibilité d’achever la tâche. Cette extension ne sera pas annoncée accomplie par la livraison A.

L’expression « changement de plan » désigne ici une variation certifiée de la continuation dans un catalogue d’opérations déclaré. Elle ne signifie ni découverte garantie d’une solution arbitraire, ni modification libre du contrat, ni auto-modification du noyau.

Trois distinctions gouvernent la spécification : une opération permise n’est pas nécessairement compatible avec l’accomplissement ; préserver la possibilité d’achever ne garantit pas un délai fini de progrès ; une égalité de comportements ne remplace pas la fidélité des formations lorsqu’elle est explicitement requise.

### Renforcement propre à la v0.3

Une continuation logique, même positivement représentée, ne prouve pas que le secours effectivement appelé la trouve et l’exécute dans les moyens de contrôle disponibles. La v0.3 ajoute cette obligation sans modifier la tâche, le contrat ou les cas séparateurs : **le régime renforcé conserve les données et les moyens nécessaires à l’exécution de son propre mécanisme de progrès**.

La correction du secours commun est démontrée depuis des invariants de formation, des préconditions et une représentation exécutable ; elle n’est pas obtenue en définissant `InvStrong(s)` par « le secours réussit ». Les moyens de contrôle obligatoires, le budget facultatif et les ressources métier sont distincts. L’oubli et le chargement doivent préserver une reprise effectivement utilisable, et non la seule proposition qu’une continuation existe.

Le choix normatif de cette version est une **borne calculable dépendant de l’état sur un évaluateur instrumenté du secours**, avec allocation obligatoire protégée. Une exécution découpée en tranches n’est permise que comme raffinement démontré de cet évaluateur ; elle ne remplace pas implicitement la preuve par une nouvelle recherche répétée.

## 2. Cible scientifique

> Pour toute configuration de la classe déclarée, tout état initial dont l’admissibilité est positivement établie à partir des ressources reçues, et toute suite de propositions du modèle, le régime renforcé conserve le contrat, les justifications et une continuation exécutable vers le but. Depuis chaque état de travail de rang positif, le secours commun, réellement appelé sur les données présentes, produit dans sa borne de contrôle une étape dont le successeur conforme diminue strictement ce rang. Les moyens réservés et les données de ce secours restent utilisables après les projections et chargements couverts. Sous les conditions explicites de service du contrôleur, de commit et de réussite du stockage, le travail logique puis la livraison sont effectivement achevés. Les nombres de tours, de pas de contrôle, de tentatives physiques et les temps restent des mesures distinctes.

La cible distingue désormais **accomplissement logique** et **livraison effective**. La borne logique ne suffit pas à établir la livraison. Celle-ci a une phase, une procédure de récupération et des conditions de vivacité propres. La réussite finale de la tâche conserve toutes les obligations reçues, publication comprise lorsqu’elle est demandée.

La garantie porte sur **la machine composée et ses effets**, pas sur l’intention interne du modèle. Elle ne suppose pas que deux modèles produisent les mêmes propositions.

Le théorème générique sera conditionnel aux lois explicitement énumérées. Une livraison concrète DOIT fournir leurs instances constructives, pas seulement une structure contenant ces lois comme hypothèses.

## 3. Périmètre de la première réalisation

### 3.1. Inclus

Une session possède un contrat fixe, des sources versionnées reçues, un catalogue fini d’opérations dont les sémantiques sont définies, un moteur de progression et un seul écrivain autorisé. Les opérations peuvent former des occurrences nouvelles et les futures opérations peuvent les consommer. Finitude du catalogue ne signifie pas finitude universelle des valeurs ni borne globale sur toutes les sessions.

Les effets métier de la première réalisation persistante sont locaux : création et publication d’artefacts versionnés dans un espace reçu, avec état, ressources logiques et reçus cohérents. Le modèle fournit uniquement des propositions. L’environnement reçoit les demandes de progression indépendamment du modèle.

La classe portable DOIT couvrir tous les préfixes finis des exécutions de la classe annoncée, y compris refus, productions supplémentaires autorisées, résultats qui manquent leur objectif et resets. La couverture ne peut être limitée aux traces réussies choisies après coup.

### 3.2. Exclus de cette version

Sont exclus : le shell arbitraire du modèle, les écritures hors espace, les effets distants irréversibles, les écrivains concurrents, les modifications de catalogue ou de contrat pendant la session, la sérialisation de toute fonction Lean arbitraire, les garanties sur toute sémantique de texte naturel, la minimalité physique de mémoire et une borne universelle de temps ou d’énergie.

Ces exclusions bornent la première réalisation ; elles n’établissent aucune impossibilité générale de l’architecture.

## 4. Configuration reçue et état retenu

### CFG-01 — Configuration immuable

La configuration Γ comprend : le contenu et les versions des sources ; la tâche et ses critères ; les droits et leurs portées ; les opérations et leurs interprétations ; le domaine des futurs ; les paramètres du contrôleur, son modèle de coût et ses règles d’allocation ; les limites de transport ; les versions du format, des recettes exécutables, de leurs interprétations et de l’adaptateur.

La comparaison de configurations DOIT porter sur leur représentation canonique et leurs interprétations déclarées. Une empreinte sert à les identifier ; elle ne remplace pas une preuve d’égalité sémantique ni une authentification de provenance.

Les données immuables peuvent résider dans un bundle séparé du checkpoint, à condition que ce bundle fasse explicitement partie des ressources conservées et soit vérifié au chargement. Il est interdit de relire silencieusement une nouvelle version d’un document d’origine.

### ST-01 — Présent complet

Le présent retenu comprend tous les composants nécessaires au contrat : curseur maître et ressources réellement formées ; données et justifications de l’application ; références et liaisons ; obligations restantes ; état des droits consommables et budgets métier pour B ; certificat de continuation et rang ; compteur et phase de l’ordonnanceur ; contexte du proposeur effectivement utilisé ; dernier résumé ; identifiants des effets validés nécessaires à la reprise.

Pour A, ces données prolongent les composants de `MaterializedPresent` ; elles ne les remplacent pas par une profondeur ou une liste de valeurs. [R3–R4]

Une phase d’ordonnanceur, lorsqu’une transaction n’englobe pas tout un tour, DOIT distinguer notamment « proposition encore disponible » et « tentative proposée déjà consommée ». Une reprise ne doit pas réouvrir indéfiniment une tentative optionnelle déjà validée.

Le présent comprend aussi la phase de livraison : `Working`, `ReadyToDeliver` ou `Delivered`. Le descripteur durable de livraison désigne la tâche, la session, la génération, l’occurrence et la version exactes, l’identité de la publication et les octets à livrer ou leur source canonique conservée. Une disponibilité ou réservation requise est représentée explicitement ; sa validité forte n’est pas imposée au type de l’état du comparateur. `Completed` est le statut utilisateur dérivé de `LogicalGoal ∧ Delivered`, non une approbation libre du proposeur.

Le présent retenu DOIT identifier les **données exécutables du secours** : recette ou instructions restantes, compteur de programme lorsqu’il est pertinent, ports et références exacts, environnement fini nécessaire à leur interprétation, état des préconditions et informations vérifiables de coût. Les éléments matériellement nécessaires se trouvent dans `RawState` ou dans un bundle immuable explicitement conservé ; ils ne sont pas accessibles uniquement par une preuve dans `Prop` ou une fermeture capturant l’archive supprimée.

Si le contrôle obligatoire est interrompu entre tranches, son état de reprise, ses crédits déjà dépensés et la phase « proposition consommée, secours en cours » doivent être conservés par le protocole retenu. Aucun rendu métier intermédiaire n’est rendu visible par ce seul checkpoint de contrôle. Le contrôle transitoire et les ressources métier du dernier commit restent distingués.

Les capacités de calcul et de stockage du poste ne sont pas créées par l’encodage d’un nombre de crédits. La configuration de déploiement doit attester leur disponibilité dans le périmètre annoncé. Les données persistées permettent de recalculer ou vérifier les besoins ; elles ne garantissent pas à elles seules qu’un autre poste possède les moyens requis.

### ST-02 — Occurrence et disponibilité

Une occurrence conserve son identité de formation même lorsque deux valeurs coïncident. Sa présence historique ne signifie pas qu’un droit associé est encore disponible. B DOIT distinguer disponibilité, réservation éventuelle et consommation, sans effacer la preuve historique de la consommation.

### ST-03 — Cohérence

`InvBaseΓ(s)` exige : contrat inchangé ; références bien typées et reliées aux formations ; justifications correctes ; liaisons exactes ; cohérence des versions ; absence de double consommation ; cohérence des compteurs et des effets validés. Il N’EXIGE PAS qu’une tâche soit encore réalisable : un état correctement formé peut avoir épuisé ses moyens d’achèvement.

Le régime renforcé ajoute un invariant `InvStrongΓ(s)` défini à partir d’`InvBaseΓ(s)`, de la formation des données de continuation, de leurs préconditions, de leurs accords de rang et des enveloppes vérifiables des moyens requis. À phase `Working`, il conserve une continuation exécutable vers `LogicalGoal` ET les moyens métier et de contrôle de sa livraison. À phase `ReadyToDeliver`, il conserve le paquet figé, ses moyens réservés et l’état du protocole de livraison. À phase `Delivered`, il conserve la preuve de réussite et les données de déduplication.

**Il est interdit d’inclure comme unique définition de la validité de continuation la conclusion `fallback(s) = Ready` ou « cet exécuteur atteint le but ».** La preuve de cette conclusion doit consommer les invariants structurels indépendants et les lois d’interprétation. Une interface générique peut demander ces lois ; l’instance concrète doit les démontrer et fermer ses hypothèses.

Ces garanties supplémentaires ne sont pas cachées dans les constructeurs de `RawState` partagés avec le comparateur. Celui-ci peut posséder les mêmes données de recette devenues inapplicables, et atteindre un état localement cohérent sans continuation ni crédits métier suffisants.

Un refus peut produire un diagnostic et consommer du travail de contrôle. « Sans effet » signifie ici absence d’effet métier et de mutation des ressources métier, non absence universelle de coût, de message ou d’avancement du contrôleur.

## 5. But, admissibilité et continuation constructive

### GOAL-01 — Critères indépendants et séparation des phases

`LogicalGoalΓ(s)` est défini avant l’ordonnanceur, à partir des spécifications reçues, des occurrences réellement liées et de leur contenu et origine exigés. Il ne dépend ni du choix du modèle, ni d’un indicateur `success`, ni du succès du contrôleur. Les permissions restent des obligations de conformité séparées.

Pour A, `LogicalGoal` est le critère de complétude logique déjà établi dans le dépôt ; il est conservé, non redéfini.

`DeliveredΓ(s)` exige la publication visible et durable du paquet exact, son lien avec l’exécution logique et le reçu validé dans le domaine d’effets annoncé. Dans B, il comprend la consommation unique du droit et de l’unité métier nécessaires à la publication.

La réussite finale est :

`TaskSuccessΓ(s) := LogicalGoalΓ(s) ∧ DeliveredΓ(s)`.

Pour B, le sous-but logique introduit explicitement est « l’artefact exact a été validé selon le critère reçu, avec l’occurrence de règle exigée le cas échéant ». L’autorisation de cette règle reste portée séparément par la conformité. Le but utilisateur initial — publier cet artefact après validation — reste `TaskSuccess`. Le considérer accompli dès la validation serait un affaiblissement interdit.

### GOAL-02 — Pas de confusion entre livraison et notification

Une livraison validée dont la réponse réseau ou console est perdue reste `Delivered`. La notification `Completed` peut être renvoyée depuis son reçu ; sa perte ne rouvre pas une publication. Le contrat local garantit la consultabilité du reçu, pas la réception effective d’un message par un utilisateur éternellement déconnecté.

### ADM-01 — Admissibilité de la tâche

L’admissibilité initiale fournit des ressources et lois primitives suffisantes à la construction : références, droits, compatibilités des opérations et disponibilités requises. Elle NE DOIT PAS être définie par « l’exécution testée réussit », recevoir le livrable terminé ou une trace future déjà accomplie.

Pour B, une notion sémantique indépendante de réalisabilité est définie : existence d’une continuation finie conforme atteignant le but dans la sémantique déclarée. Cette existence logique n’est pas supposée fournir automatiquement un algorithme ou un certificat exécutable.

### CONT-01 — Constructeur positif

Un constructeur effectif DOIT produire depuis les ressources présentes un témoin `RecoveryΓ(s)` : programme de continuation, préconditions établies, garanties de préservation et argument de terminaison. Sa cible est la réussite finale déclarée : en phase de travail il atteint un état logiquement accompli dont la livraison demeure réalisable, et en phase de livraison il justifie la continuation physique restante sous les hypothèses de stockage reçues. Son programme décrit du travail à réaliser ; il n’est pas une trace présentée comme déjà exécutée.

L’instance concrète ferme l’obligation « admissibilité initiale ⇒ construction de Recovery ». Les transitions admises transportent ou reconstruisent ce témoin depuis leurs sorties réelles.

Une recherche de certificat infructueuse peut donner `NoCertificate` ou `CheckTimeout`. Elle ne donne `Impossible` qu’avec une preuve qu’aucune continuation conforme de la classe annoncée ne satisfait le but.

### CONT-02 — Données, certificat et algorithme commun

Trois objets sont séparés :

- `RecoveryDataΓ(s)` : instructions ou recette finie, références, environnement, éventuel état de contrôle et données de coût réellement conservés ;
- `RecoveryValidΓ(s,d)` : certificat positif établissant les préconditions, la correction sémantique et l’enveloppe de continuation de ces données ;
- `fallbackProgramΓ(s)` : programme commun effectif qui lit le présent et ces données, contrôle les préconditions courantes et prépare l’étape suivante.

Le programme commun NE REÇOIT PAS `InvStrong` ni `RecoveryValid` comme une source cachée de choix exécutable. Les données matériellement lues sont accessibles selon la même interface dans les deux régimes. Une preuve supplémentaire permet de démontrer son comportement sur le domaine renforcé ; elle ne remplace pas ce programme par un autre algorithme.

L’instance de référence utilisera un programme de continuation explicite ou une recette dont l’interprétation avance sans recherche ouverte. Une construction différente est recevable seulement si la procédure de sélection et de contrôle réellement utilisée a sa propre borne démontrée. La v0.3 ne revendique ni la découverte bornée de toute continuation viable, ni un décideur de viabilité de tout programme arbitraire.

Après une proposition incorporée, les données de continuation doivent être ajustées depuis le paquet effectif et leurs préconditions rétablies. Le comparateur applique les mêmes mises à jour communes de données ; il n’acquiert pas pour autant un certificat lorsqu’une précondition future a été détruite. Aucune différence de recette cachée ou de stratégie de secours ne doit fabriquer l’avantage expérimental.

### CONT-03 — Succès borné du secours effectivement appelé

Pour tout état `s` renforcé avec `phase(s) = Working` et `0 < ρwork(s)`, démontrer sur l’évaluateur réellement appelé :

```text
runCtlΓ(fallbackBoundΓ(s), fallbackProgramΓ(s)) = Done(Ready(p))
```

pour un paquet effectivement calculé `p : PreparedStepΓ(s)`, avec une trace de contrôle de coût `k ≤ fallbackBoundΓ(s)`. Le compteur de coût mesure les opérations du modèle de contrôle déclaré, non un nombre de secondes.

La preuve DOIT en outre établir sur le **même paquet** : ses références et préconditions locales ; l’accord avec le producteur réellement exécuté ; `InvStrongΓ(p.next)` ; `ρwork(p.next) < ρwork(s)` ; le maintien des moyens de la livraison ; et la capacité à servir le contrôle obligatoire depuis le successeur.

`Blocked` et `FuelExhausted/CheckTimeout` ne sont donc pas des résultats possibles de cet appel pur dans ce domaine et avec l’allocation démontrée. Une interruption du processus ou une indisponibilité physique reste un résultat du protocole d’environnement, pas une réfutation sémantique de cette propriété. Sur un état du comparateur, `Blocked` et une limite de contrôle demeurent représentables.

La préparation calcule une seule fois les productions pures nécessaires et les conserve dans `p`. La validation transactionnelle réalise ce paquet ; elle ne rappelle pas le producteur pour obtenir un second résultat de même valeur. Le théorème du secours donne le successeur logique ; le raccord aux effets établit séparément que tout commit réussi expose précisément ce successeur. Il ne suppose pas que chaque tentative de stockage réussit.

### CONT-04 — Préparation et activation non circulaires

L’établissement initial des préconditions et enveloppes a sa propre procédure et sa propre borne. Le chemin de démarrage NE DOIT PAS supposer `InvStrong` pour obtenir les moyens de prouver `InvStrong`. Il part de données reçues admissibles, d’une allocation de bootstrap déclarée et de bornes structurelles calculables avant activation.

Un état renforcé sauvegardé valide doit pouvoir être réactivé depuis ses données portables par validation bornée, sans recommencer une recherche de plan non bornée. Les distinctions entre décodage commun, activation renforcée et disponibilité physique sont maintenues dans SER-05.

## 6. Politique de proposition et admission des actions

### PROP-01 — Interface non souveraine

La politique reçoit contexte, signal et observation autorisée, puis fournit un nouveau contexte et zéro ou une proposition par tour. Elle ne fournit aucun état machine de remplacement. Les poids du modèle ne font pas partie de la preuve de conformité du contrôleur.

Le protocole expose des opérations explicitement nommées et des références typées ou décodables. Il n’accepte ni code exécutable libre, ni chemins arbitraires, ni constructeur de permission, ni changement de Γ.

### PROP-02 — Limites

La configuration fixe avant le run : délai de réponse du modèle, taille maximale du message, profondeur de décodage, bornes des indices transportés, budget du contrôle facultatif et limite des effets proposés par tour. Une limite facultative atteinte devient une absence ou un refus contrôlé, puis déclenche le secours obligatoire. Les moyens de ce secours suivent CTRL-01 à CTRL-04 : ils ne sont pas le reliquat du contrôle facultatif. Les théorèmes sur requêtes typées et les limites pratiques du transport restent distincts.

Le conducteur annule ou isole les réponses arrivées après le délai. Une réponse tardive ne peut être incorporée dans un autre tour. Les demandes portent session, numéro de tour et génération attendue ; une réponse périmée est rejetée.

### AUTH-01 — Trois obligations séparées

L’admission d’une transition proposée de s vers s′ exige :

1. permission locale et préconditions de l’opération sur les occurrences exactes ;
2. `InvBaseΓ(s′)`, les données exécutables et la validité de `RecoveryΓ(s′)`, couvrant les moyens métier ET de contrôle de la continuation et de la livraison finale selon la phase ;
3. respect de la politique de progrès de la section 7.

La preuve concerne le successeur de l’action réellement produite, pas une simulation indépendante choisie parce qu’elle renvoie la même valeur.

La formation pure d’une action, la vérification de sa préservation et son effectuation métier sont distinctes. Aucun effet extérieur ne peut précéder l’admission. Calculer une transformation candidate n’autorise pas à publier son résultat.

### AUTH-02 — Diagnostics

Les motifs sont distincts : protocole invalide ; référence absente ; version périmée ; permission absente ou consommée ; objectif non satisfait ; préservation de l’accomplissabilité non certifiée ; budget de progrès non respecté ; contrôle facultatif expiré ; enveloppe de contrôle obligatoire non couverte ; erreur d’environnement. `MandatoryResourceUnavailable` suspend une réalisation dont les moyens physiques reçus font défaut ; il ne doit pas être confondu avec `CheckTimeout` d’une proposition ou avec `Impossible` dans la sémantique métier.

Une opération sémantiquement réalisable mais hors politique de progrès ne doit pas être qualifiée artificiellement d’interdite par le contrat source. Le contrôleur peut être conservateur : la version B ne revendique pas l’admission de toutes les actions sûres et viables.

## 7. Progrès borné de la procédure

### CTRL-01 — Trois domaines de ressources, sans vases communicants implicites

La réalisation distingue :

| Domaine | Usage | Règle de protection |
|---|---|---|
| `OptionalControl` | Acquisition et décodage du modèle, examen de sa proposition, construction candidate et vérification de sa préservation | Quota fini par tour, limites de mémoire et de sortie ; épuisement suivi du secours |
| `RequiredControl` | Calcul et contrôle du secours, calcul de ses bornes, préparation du commit, récupération, activation et livraison obligatoires | Allocation protégée, servie indépendamment de la coopération du modèle |
| `BusinessResources` | Droits, quotas, versions et ressources consommées par les opérations métier | Consommation liée aux effets validés, jamais recréée par reset ou chargement |

La mémoire de travail, l’espace de staging, les descripteurs, verrous et files d’entrées font également partie des moyens à isoler lorsqu’ils peuvent empêcher le secours. Une limite de carburant symbolique ne protège pas, à elle seule, le processus contre une allocation facultative illimitée.

Le coût borné de l’abandon d’une proposition — arrêt ou isolement, libération de ses ressources, diagnostic et reprise du contrôle — est provisionné séparément de son budget déjà épuisé. Une proposition ne peut conserver un verrou indispensable ou maintenir un processus facultatif qui affame le secours. Les résumés et diagnostics accessibles au contrôleur ont une politique de taille et de coût déclarée ; des rejets répétés ne peuvent les faire croître hors de l’enveloppe obligatoire.

Une unité de quota métier n’est pas une unité de contrôle, et une unité de contrôle n’est pas une seconde CPU. Les trois comptes sont présentés séparément dans les reçus de test.

### CTRL-02 — Choix normatif : borne d’état et évaluateur instrumenté

Le programme de secours est interprété par un évaluateur explicite dont la sémantique et le compteur de pas sont raccordés. Pour la notation de cette spécification :

```text
fallbackBoundΓ : RawStateΓ → Nat
fallbackProgramΓ : RawStateΓ → ControlProgram
runCtlΓ : Nat → ControlProgram → ControlOutcome
```

Ces signatures sont contractuelles, pas des déclarations Lean déjà disponibles. `fallbackBoundΓ(s)` est calculée depuis les données effectivement retenues : taille et structure des instructions, références, entiers, états de lecteurs et environnements. Ce calcul NE DOIT PAS exécuter le secours entier pour en découvrir le coût après coup. Son propre coût a une borne structurelle de bootstrap ; aucune chaîne infinie de « calcul de borne non compté » n’est admise.

Le modèle instrumenté nomme les primitives qu’il compte. Une lecture de liste, une opération sur un entier non borné ou un appel à un producteur complexe ne peut être déclaré de coût physique constant par commodité. Une métrique abstraite est permise, mais sa portée est annoncée ; l’interprète, les appels internes et les bibliothèques non instrumentés restent des frontières explicites avant tout claim de coût d’implémentation.

Démontrer séparément : accord valeur/trace ; exactitude du compteur ; terminaison bornée du secours sur le domaine renforcé ; monotonie en carburant (un surplus ne change pas le paquet obtenu) ; et bornes des auxiliaires nécessaires à la prochaine transition. L’exécution de l’étape préparée et sa validation locale ont leurs coûts propres, inclus dans l’enveloppe obligatoire du tour, sans être cachés dans une primitive gratuite.

Un plafond global constant n’est recevable que pour une sous-classe explicitement bornée, avec preuve que tous ses états renforcés atteignables restent sous ce plafond. Il ne devient pas une nouvelle limite silencieuse des théorèmes existants sur les exécutions finies.

La borne doit porter sur l’évaluation et les données de la prochaine opération réelle, pas seulement sur la lecture de son nom. Par exemple, si le contrôle parcourt `n` références et manipule des entiers de taille `b`, l’instance peut établir une fonction `FΓ(n,b,...)` par récurrence sur la recette, avec les coûts des accès et auxiliaires qu’elle utilise. La forme ou l’ordre de cette fonction n’est pas présumé linéaire. Les constantes, domaines et frontières non instrumentées sont explicitement fixés et testés.

### CTRL-03 — Allocation avant proposition et fermeture des moyens futurs

Avant de servir un contrôle facultatif, le contrôleur doit disposer des moyens du secours depuis l’état courant, de l’abandon facultatif et du commit requis. Une proposition ne peut débiter cette réserve. Si elle reste non admise, le chemin de secours déjà financé reste disponible.

Si une proposition prépare `s′`, son admission exige aussi une enveloppe compatible avec `s′`, pas seulement avec `s`. Elle peut augmenter le volume des données tout en laissant le rang inchangé : il faut alors vérifier le coût du secours et de l’activation de `s′`, le pic de mémoire comprenant l’ancien et le nouvel état préparé, l’espace durable requis et les moyens de sa livraison. Si cette vérification dépasse le budget facultatif ou si la capacité reçue ne suffit pas, la proposition est abandonnée ; les moyens du secours courant restent réservés.

L’enveloppe de continuation est constructive. Sur la recette de reprise choisie, elle relie le coût du prochain contrôle, de l’étape, du commit et du reliquat aux capacités reçues. Une forme possible, à fermer pour l’instance, est :

```text
Need(s) couvre BoundControl(s) + BoundLocalStep(s) + BoundCommitPreparation(s)
        et l’enveloppe résiduelle Need(nextFallback(s)).
```

Les besoins de mémoire simultanée et de stockage ne s’additionnent pas nécessairement comme un compteur de pas ; ils ont leurs propres lois de maximum, de réutilisation et de libération. La couverture doit aussi être établie à la transition vers la livraison.

L’expression `Need(nextFallback(s))` est une loi de fermeture à prouver sur la continuation structurée, non une instruction demandant d’exécuter le secours à l’avance pour calculer sa réserve. L’enveloppe est obtenue par les recettes et leurs lois de coût. Une promesse non justifiée que « des ressources seront probablement disponibles plus tard » ne ferme pas l’admission renforcée : les capacités du domaine déployé ou la garantie explicite de service doivent couvrir cette enveloppe avant l’effectuation.

Si un déploiement impose un quota de calcul **cumulé** sur toute la session, la construction fournit une provision finie couvrant la continuation obligatoire dans le modèle de pannes annoncé. Les contrôles facultatifs, checkpoints, abandons et métadonnées ne peuvent l’entamer. Le reset ne réinitialise pas le relevé des crédits consommés.

Des reprises avant commit peuvent répéter du calcul. Sans borne sur ces reprises, une réserve cumulée finie ne peut être présentée comme suffisante pour tous les coûts physiques. La version de base garantit une allocation obligatoire servable à chaque reprise sous ENV-01 ; un claim cumulatif exige une borne des fautes ou un approvisionnement externe nommé. Ce choix est fixé dans le manifeste d’exécution, jamais changé après observation d’un échec.

### CTRL-04 — Ordonnancement, surveillance et éventuelles tranches

La quantité de carburant prouvée borne des pas du contrôle, pas leur temps mural. Un watchdog peut signaler une lenteur ou une indisponibilité ; il NE DOIT PAS rendre impossible une exécution valide en réappliquant indéfiniment un délai trop court au même calcul recommencé depuis zéro.

Deux incarnations compatibles avec le choix CTRL-02 sont possibles, à identifier avant le run : une fenêtre de service assez longue pour terminer l’évaluation obligatoire bornée ; ou des tranches reprenables de ce même évaluateur. La première reçoit l’hypothèse de service correspondante. La seconde conserve compteur de programme, environnement, pile, position des lecteurs et carburant restant, et démontre la composition des tranches avec l’évaluation non découpée.

Pour les tranches, si la réserve restante passe de `f` à `f′`, les pas réellement effectués sont comptés par `f − f′` ; une reprise ne restaure pas artificiellement `f`. La somme des pas de l’évaluation valide demeure dans la borne initiale, hors travail perdu avant le dernier point durable et coût du mécanisme de checkpoint comptés séparément. Un résultat `Paused` est une reprise de contrôle, pas un `Blocked` métier ou une nouvelle permission de proposer.

Le contrôleur ne sert pas une nouvelle proposition facultative tant que le secours obligatoire engagé n’est pas terminé ou explicitement suspendu pour une condition extérieure. Les resets et observations ne doivent pas affamer ce service. La sûreté reste une propriété de tout préfixe couvert ; l’achèvement demande le service équitable déclaré dans ENV-01.

### PROG-01 — Rang du travail logique

Un rang naturel `ρwork(s)`, défini avec sa signification avant les résultats, mesure le travail logique restant. Sur les états actifs du régime renforcé, son rang nul implique `LogicalGoal`, PAS `Delivered`. CONT-03 et CTRL-02 établissent que l’appel du secours produit effectivement une étape prête dans sa borne depuis un rang strictement positif. Le successeur de cette même étape diminue ce rang et conserve les invariants ainsi que les moyens métier et de contrôle de la continuation et de la livraison.

Les occurrences de ρ dans PROG-02 et PROG-03 désignent ce rang de travail. Le passage à la livraison n’est pas une nouvelle demande au modèle. Il a les obligations séparées de PROG-04 et IO-05.

Pour A, on réutilise la mesure des obligations restantes et sa borne existante, dans son domaine exact. Pour B, une mesure adaptée et sa réalisation doivent être établies ; la borne 2n de A n’est pas transférée par analogie.

Le rang `ρwork` est défini sur le type commun des états, avec convention explicite pour les phases non travaillantes ; on le prend nul en `ReadyToDeliver` et `Delivered` dans la réalisation proposée. Il ne suffit pas de modifier cette lecture pour satisfaire l’inégalité : sa relation à la recette restante et au critère logique doit être démontrée indépendamment.

### PROG-02 — Détours

Une tentative optionnelle admise ne peut augmenter ρ. Si elle le diminue strictement, le tour peut se terminer. Sinon, une étape de reprise certifiée est exécutée depuis son successeur réel. Une proposition rejetée, absente ou une inspection sans progrès est suivie de cette reprise depuis l’état métier conservé.

CONT-03 exclut le blocage et l’expiration logique du secours dans le domaine renforcé ; CTRL-01 à CTRL-04 protègent et servent ses moyens, sous ENV-01 pour l’incarnation physique. La preuve ne porte donc pas seulement sur les tours choisis parce qu’ils auraient réussi : elle doit montrer que chaque tour de travail de rang positif atteint effectivement son paquet de commit, puis est validé sous les hypothèses de commit. Tout tour ainsi **effectivement accompli** fait diminuer ρ. Avec au plus une tentative proposée puis une tentative requise, la borne cible est :

- au plus ρ(s₀) tours de progression accomplis ;
- au plus 2ρ(s₀) tentatives sémantiques dans ces tours.

Les pas du contrôle facultatif et obligatoire, l’inférence, les écritures et les retries ont des métriques séparées. Sur une exécution sans reprise répétée, la borne globale de contrôle est construite en composant les bornes des états effectivement parcourus ; elle ne se déduit pas du seul nombre 2ρ. Un claim uniforme utilise l’enveloppe de CTRL-03. Une opération du catalogue qui effectue plusieurs productions internes DOIT annoncer son unité et ses coûts internes ; elle ne devient pas arbitrairement une opération physique unitaire.

### PROG-03 — Pourquoi la réalisabilité seule ne suffit pas

Un détour peut conserver un chemin vers le but tout en l’allongeant. Si chaque tour rallonge le chemin d’une étape puis en accomplit une, l’agent peut rester éternellement à la même distance. Le témoin de réalisabilité ne remplace donc pas l’inégalité de progrès. Le choix conservateur « pas d’augmentation de rang » ferme cette lacune pour la version proposée.

### PROG-04 — Progrès jusqu’à la livraison

`Working` avec rang nul doit être suivi, sans solliciter une nouvelle proposition, d’une transition déterministe vers `ReadyToDeliver`, ou être déjà inclus dans cette phase par le dernier commit de travail. Le paquet à livrer est alors figé. L’environnement insuffisant conduit à une suspension explicitement diagnostiquée ; le rang nul ne permet pas de déclarer la tâche livrée.

Un rang de livraison `δ` mesure les étapes durables restant dans le protocole de livraison. Il ne décroît que lors des transitions de protocole effectivement réussies. Les tentatives interrompues ou en erreur peuvent être des pas stationnaires ; elles sont comptées séparément.

Un ordre lexicographique proposé, à réaliser et prouver dans l’instance, est :

- `Working` : `(2, ρwork)` ;
- `ReadyToDeliver` : `(1, δ)` ;
- `Delivered` : `(0, 0)`.

La transition de fin logique abaisse la première composante, sans exiger que `ρwork` reste positive jusqu’à la publication. La livraison réussie abaisse δ ou passe à `Delivered`. Ce rang ne prétend pas faire décroître les crashes, les attentes ni les resets.

Sous la disponibilité déclarée, il faut établir séparément : la borne des tours de travail ; au plus une transition administrative de préparation si elle n’est pas déjà comprise dans le dernier tour ; et une borne `dΓ(sready)` sur les transitions de livraison réussies. La borne logique antérieure `n/2n` est conservée dans son domaine et NE COMPTE PAS ces transitions physiques par convention implicite.

### ENV-01 — Conditions de vivacité

La conformité reste exigée sur tous les préfixes, propositions et interruptions couverts. La propriété de vivacité reçoit les hypothèses suivantes, chacune reliée à une primitive ou à l’ordonnanceur, et non la conclusion « la livraison réussit » :

1. **Service obligatoire.** Une requête de progression acceptée déclenche le tour ; après une absence ou limite facultative, le contrôleur sert le secours. Un calcul obligatoire activé obtient assez de pas d’exécution, en une fenêtre ou par tranches fidèles, sans famine due au proposeur, aux inspections ou aux resets.
2. **Moyens présents.** Les capacités reçues couvrent l’enveloppe du présent et sa prochaine allocation obligatoire : mémoire de travail, espace durable et staging, handles et accès nécessaires. Les réservations métier demeurent valides. La déclaration d’un budget dans le checkpoint ne constitue pas cette disponibilité physique.
3. **Succès des primitives de commit.** Les lectures requises retrouvent les objets validés, les écritures et allocations prévues peuvent aboutir, les opérations de durabilité et de publication prescrites par le protocole terminent avec succès, et leurs résultats respectent le modèle de stockage d’A2.
4. **Suffixe favorable et reprises.** Dans la version de base, il existe un indice fini après lequel les conditions précédentes sont maintenues pour tous les appels nécessaires encore émis et aucune interruption n’empêche ces commits. Les tentatives après erreurs temporaires sont effectivement relancées avec un délai fini par tentative. Les traces de vivacité sont des exécutions maximales servies, et non des préfixes finis abandonnés avant l’appel utile. Une variante à fenêtres finies exige une longueur de service suffisante calculée depuis les bornes du protocole, ou un progrès durable cumulé démontré ; une alternance d’échecs ne garantit pas qu’un commit puisse se terminer.
5. **Absence d’annulation ou de mutation hostile du périmètre.** Aucun arrêt humain définitif, retrait des droits réservés, écrivain concurrent non couvert ou corruption du stockage de confiance ne contredit les obligations restantes.

Le caractère favorable du suffixe est défini par ces conditions primitives et de service. Il NE SIGNIFIE PAS par définition `Delivered` ni « au moins une tentative réussit ». IO-06 doit démontrer que ces conditions font réussir la procédure concrète.

« Chaque appel répond en temps fini » ne suffit pas : un environnement qui répond toujours par une erreur ne satisfait pas la condition de succès. Une ressource définitivement indisponible ou un refus permanent de durabilité peut maintenir `Suspended`; ce n’est ni un accomplissement ni une preuve d’impossibilité métier. Un arrêt humain donne `Cancelled`, jamais `Completed`.

La borne logique reste une borne des tours validés. La preuve relie désormais les conditions de service et de commit à l’existence effective de ces tours. Après la dernière interruption empêchant un commit, elle repart du rang du dernier état validé. Les pas de contrôle, appels stockage, attentes, retries et calculs perdus avant commit sont comptés séparément. Aucune borne absolue en secondes ou en énergie n’est déduite des rangs seuls.

## 8. Projection mémoire et futurs

### MEM-01 — Langage déclaré

Le contrat logique comprend progression, inspections permises, observation du statut et reset du contexte. Les opérations nouvelles de B et les observations `LogicalGoal`, `ReadyToDeliver`, `Delivered`, droits réservés/consommés et reçu doivent être incorporées au contrat avant de revendiquer leur préservation. Sauvegarde et chargement possèdent une sémantique d’effets séparée ; leurs pas internes peuvent être silencieux relativement aux observations métier.

### MEM-02 — Exactitude

Pour la projection q de la mémoire riche vers le présent réduit, fournir les lois locales de transition, événements et lectures, les passages des admissions dans les deux sens et, lorsque l’interface l’exige, leurs lois de retour. Elles doivent se composer pour toute suite finie des requêtes déclarées. [R5]

Inclure dans les observations ou dans des obligations de transport explicites : critère d’accomplissement, rang logique, phase et rang de livraison, paquet figé, identité de publication, état des ressources consommables, données exécutables de la continuation, validité de leurs enveloppes de contrôle et crédits effectivement consommés. La seule présence propositionnelle de `Recovery` ou l’égalité d’un résumé textuel ne suffit pas.

### MEM-03 — Ce qui est comparé

L’accord exact compare les exécutions recevant les mêmes entrées formelles et résultats d’environnement. Pour un rejeu, ce sont les mêmes propositions effectives. Deux interactions libres avec un LLM peuvent diverger ; on exige alors leurs invariants et accomplissements, pas leur égalité octet par octet.

Un reset peut modifier les propositions suivantes. Il doit préserver les ressources machine, le contrat, le rang, le compteur et les obligations. Il ne promet pas d’effacer des poids, caches ou journaux non inclus dans son opération.

### MEM-04 — Oubli démontré

Un oubli irréversible requiert deux préfixes réellement produits, une distinction historique explicite, des présents projetés égaux et l’impossibilité d’un récupérateur uniforme dans ce domaine.

L’inventaire des accès doit inclure reçus, empreintes, logs, outils et contexte restant. Une empreinte de la proposition oubliée peut suffire à conserver une distinction ; elle ne doit pas rester cachée dans le présent prétendument égal. Les archives de recherche externes, lorsqu’elles sont conservées, sont explicitement exclues de l’interface réduite et inaccessibles au proposeur.

La nouvelle extension ne revendique pas la minimalité de toute sa mémoire. Elle ne transfère pas automatiquement la minimalité existante du noyau à un contrat plus riche.

### MEM-05 — Secours réellement utilisable après projection

Pour chaque représentation source/réduite, identifier le programme de secours et l’interprétation qu’il appelle. Le calcul réduit ne dispose que des données conservées par `q`, de la configuration et des bundles explicitement reçus.

Démontrer conjointement : transport positif des préconditions et instructions ; possibilité de calculer la borne obligatoire depuis ces seules données ; résultat `Ready` du secours réduit avec cette allocation ; commutation de son successeur et de son événement avec la projection ; préservation d’`InvStrong` et baisse du rang. Un théorème d’existence d’une continuation ne ferme pas ce passage.

Les coûts des deux représentations ne sont pas supposés identiques. Soit leur égalité de coût est prouvée dans le modèle déclaré, soit une borne propre `fallbackBoundReduced(q(s))` et son allocation sont établies. Un gain de taille du checkpoint ne constitue pas automatiquement un gain de coût de reprise.

Les données de programme, ports, environnement et état d’interprétation nécessaires au secours ne peuvent être supprimées au motif que la proposition « un programme existe » demeure vraie. Leur sérialisation ne doit pas reconstituer, par une recherche non bornée, le témoin que l’oubli a détruit. Si un nouveau calcul de contrôle est nécessaire, son domaine, sa borne et ses ressources sont explicitement préservés.

## 9. Format portable et chargement

### SER-01 — Présentation finie des opérations

La représentation portable contient des codes de producteurs connus, leurs environnements finis, leurs ports, les valeurs déjà produites et les données de formation nécessaires. Les fonctions d’ordre supérieur utilisées réellement par la classe doivent avoir une représentation explicite avec un théorème d’interprétation.

Le format comprend aussi les liaisons, la file typée, le compteur, le contexte portable du modèle, le résumé, le rang, les informations de droits consommables et les identifiants d’effets requis. Le codec du contexte concerne une classe déclarée ; il ne prétend pas sérialiser un `Context : Type` arbitraire.

### SER-02 — Couverture positive

`PortableFormedΓ(s)` se définit par la grammaire et les formations autorisées. Ce prédicat NE DOIT PAS signifier « s réussit le round-trip ». Construire séparément sa préservation par toutes les transitions, depuis les états initiaux annoncés, sans hypothèse de succès de la tâche.

La couverture exclut les fonctions arbitraires non représentées, mais ne peut exclure silencieusement une branche atteignable de la classe annoncée. Si une branche manque, la clôture du jalon manque.

### SER-03 — Théorèmes d’encodage

Pour toute formation portable de s :

`decodeΓ(encodeΓ(s)) = Ok(s)`.

L’égalité porte sur le présent promis et ses formations, avec les transports dépendants explicites nécessaires. Une égalité des nombres, du rang ou des textes ne remplace pas cet accord.

Prouver séparément deux niveaux de chargement. Le décodeur structurel commun restitue les états bien formés de sa classe, y compris des tâches bloquées, des liaisons absentes et des objectifs manqués ; il ne les remplace pas par un état favorable. L’activation dans le régime renforcé établit en plus `InvStrong`, y compris `DeliveryRecovery` lorsque la phase est `ReadyToDeliver`. Le comparateur peut charger et continuer à diagnostiquer un état cohérent non viable. Ne pas placer `Recovery` dans le type de résultat du décodeur commun.

Les versions inconnues, références impossibles et incohérences de format sont refusées. Une donnée mathématiquement valide n’est pas, par cela seul, un état de session authentifié ou courant. Les erreurs ne déclenchent aucun effet métier.

### SER-04 — Pas de rejeu du passé validé

Le chargeur construit les formations et vérifie les équations sauvegardées. Il ne relance ni la découverte, ni l’extraction, ni l’incorporation historique pour retrouver le présent. Les vérifications arithmétiques et d’interprétation exécutées au chargement sont documentées et mesurées ; elles ne sont pas décrites comme un rejeu historique.

Une importation du module contenant un boot exécuté ne doit pas reconstruire silencieusement le passé dans l’initialisation du nouveau processus. Les contrôles du code généré et des initialisations doivent couvrir les entrées effectives du chargeur, en annonçant les limites de l’analyse.

### SER-05 — Activation bornée depuis les octets, sans archive ni bootstrap circulaire

Le décodeur structurel commun reste indépendant d’un certificat de viabilité. L’activation renforcée ajoute une procédure déterministe qui valide les données de continuation, les préconditions, les bornes et la phase de contrôle. Le résultat valide active le secours effectif, pas une nouvelle recherche ouverte de plan.

Définir une borne `activateBoundΓ(bytes)` ou une borne structurelle sur leur longueur et leur grammaire, disponible avant activation et sans exécuter le passé. La lecture de l’entrée, le calcul de cette borne, le parsing, les références dépendantes et les vérifications doivent être couverts par l’allocation de bootstrap. Une longueur déclarée par un fichier non vérifié n’autorise pas une allocation illimitée.

Pour tout état renforcé portable de la classe annoncée, prouver qu’avec cette allocation, l’activation de ses octets sauvegardés : termine sans `CheckTimeout` ; retrouve les données et enveloppes requises ; puis permet le `Ready` borné de CONT-03 depuis le **présent chargé**. Les preuves dans `Prop` sont reconstruites par les validateurs ou transportées par les lois exactes ; elles ne sont pas utilisées comme un conteneur exécutable inaccessible au chargeur.

Le chargeur NE DOIT PAS croire un nombre de carburant sauvegardé sans vérifier sa suffisance. Une métadonnée sous-estimée peut être recalculée canoniquement ou faire échouer l’activation renforcée ; elle ne déclenche pas une opération métier. Le décodeur commun peut encore décrire un état structurellement valide dont l’activation renforcée échoue. Une absence de certificat n’est pas une preuve de non-viabilité.

Les limites physiques d’import sont annoncées séparément du codec mathématique. L’instance déployée établit avant admission que ses états renforcés atteignables restent chargeables sous ses capacités, ou reçoit une règle explicite de provisionnement. Exclure après coup un état valide devenu trop volumineux ne constitue pas une preuve de clôture portable.

Les tests de reprise sont réalisés dans un processus neuf recevant uniquement le checkpoint, la configuration et les bundles conservés autorisés. Ils doivent ensuite appeler le secours et produire une étape nouvelle. Le simple aller-retour des octets ou la présence d’un théorème de fidélité du composant ne satisfait pas SER-05.

## 10. Effets, commit et reprise après interruption

### IO-01 — Périmètre de confiance

La version initiale utilise un écrivain et un stockage local administré. Le modèle n’a pas accès aux fichiers de contrôle, aux sources privées hors observation ni à un autre canal d’effectuation. Le noyau Lean, la chaîne de compilation, l’adaptateur et les hypothèses du stockage sont identifiés séparément ; la preuve Lean ne certifie pas automatiquement leur incarnation physique.

Une corruption arbitraire de la zone de confiance par un administrateur hostile n’est pas couverte. Une empreinte sans clé ne constitue pas une authentification. Un ancien snapshot cohérent ne doit être accepté comme courant que si le contrôle de génération de la session l’autorise ; ce contrôle ne prétend pas résister à un attaquant capable de remplacer toute la zone de confiance.

### IO-02 — Point de validation unique

L’unité transactionnelle de travail est par défaut un tour contrôlé complet, comprenant son état suivant, ses effets métier locaux et ses reçus. La livraison terminale possède une unité transactionnelle séparée lorsqu’elle n’a pas été intégrée dans le dernier tour : son paquet peut déjà être logiquement complet et durable sans être encore publié. Cette séparation est représentée dans la phase, non laissée à l’état implicite du processus. Les sorties intermédiaires peuvent être préparées dans une zone privée ; elles ne sont visibles par aucune lecture métier avant la validation.

Le protocole DOIT fournir un point de validation tel qu’après interruption la récupération expose soit la génération précédente entière, soit la nouvelle entière. Jamais un mélange d’un budget ancien, d’un artefact nouveau et d’obligations anciennes.

Le mécanisme concret — par exemple un bundle immuable et une tête validée, ou un stockage transactionnel équivalent — doit préciser ses opérations de durabilité, de verrouillage et de récupération. L’atomicité et la correction sous interruption ont leurs hypothèses propres ; elles ne découlent pas de la seule écriture d’un fichier ni du round-trip pur. [E1–E2]

### IO-03 — Répétition d’une demande

Chaque tour validé reçoit un identifiant issu du contrôleur, associé à sa génération et à ses résultats. Une répétition de cet identifiant après validation restitue le résultat enregistré sans nouvelle consommation ni nouvelle publication. Un identifiant réutilisé pour un contenu sémantique incompatible est rejeté.

Le test du doublon validé précède le rejet pour génération ancienne : une réponse perdue après commit doit rester récupérable. Une requête ancienne inconnue est rejetée.

Les calculs non validés interrompus peuvent être recommencés. On distingue donc « aucun effet métier validé en double » et « aucune instruction CPU exécutée deux fois ». Seule la première propriété est exigée ici.

### IO-04 — Résultat utilisateur

Le statut `Completed` n’est émis qu’après validation de `LogicalGoal ∧ Delivered` et accord des données relues avec le paquet effectivement produit. Un reçu est émis après le commit. Une erreur avant commit laisse la dernière génération validée faisant autorité.

Les effets extérieurs non transactionnels, tels qu’un paiement ou un envoi distant sans protocole de déduplication, sont exclus de cette version. Aucun « exactement une fois » général n’est revendiqué pour eux.

### IO-05 — Transition exacte de livraison

La transition depuis `Working` de rang nul lit les occurrences et le rendu réellement constitués. Elle fixe un identifiant de publication et un paquet versionné. Elle ne demande pas au modèle de produire une nouvelle version du livrable. En B renforcé, les moyens nécessaires sont réservés ou leur disponibilité est protégée par l’invariant ; aucun détour n’est ouvert pendant cette phase.

Le présent durable `ReadyToDeliver` contient ce paquet, ses références, l’état de réservation et l’identité stable de publication. Après arrêt, la reprise réutilise exactement ce descripteur. Un manque de budget dans le comparateur reste un état `ReadyToDeliver/Blocked` représentable, pas un faux fichier invalide ni un retour forcé au boot.

`commitDeliver` doit atomiquement : rendre visible la version validée ; enregistrer le passage à `Delivered` ; consommer une seule fois les droits et le quota métier de publication ; conserver le reçu de déduplication. Une réservation préalable ne doit pas déjà être comptée comme une seconde dépense : disponibilité, réservation et consommation sont trois états du même droit ou quota.

| Dernier état durable | Interruption | Reprise exigée |
|---|---|---|
| `Working` | Avant validation de la fin logique | Reprendre le travail depuis le dernier commit ; recalcul non validé permis |
| `ReadyToDeliver` | Avant commit de livraison | Reprendre le même paquet et le même identifiant, sans relancer maître, validation ou proposition déjà validés |
| `Delivered` | Après commit, avant réponse | Restituer le reçu ; aucune publication ou consommation supplémentaire |
| État du comparateur sans moyens de livraison | Échec de la reprise métier | Conserver et diagnostiquer le blocage ; aucune recréation des ressources |

Les lecteurs métier ne doivent voir que les générations validées par le protocole. Si le fichier est accessible par un canal qui ignore ce protocole, le claim d’atomicité doit couvrir ce canal ou l’exclure explicitement. Le mécanisme ne prétend pas rendre atomiques des effets extérieurs arbitraires.

### IO-06 — Réussite de la livraison sous conditions primitives suffisantes

Définir une procédure effective commune de livraison sur le paquet figé, avec états internes, transitions et résultats `Pending`, `Retryable`, `Suspended` et `Delivered`. `ReadyToDeliver` est une phase métier ; elle n’implique pas qu’un appel arbitraire au stockage soit déjà réussi.

Le certificat de livraison doit porter la recette des opérations restantes, leurs préconditions et les réservations. La preuve de sa vivacité consomme les hypothèses primitives d’ENV-01, les bornes du contrôle de chaque tentative et le programme effectivement appelé. Il faut en dériver : depuis un état renforcé prêt à livrer, la phase atteint `Delivered` dans un suffixe favorable, avec le même paquet et la même identité de publication. « Le stockage répond éventuellement », pris isolément, est insuffisant.

Après une erreur temporaire, le paquet, les ports, droits, quotas métier réservés et l’identité restent conservés. Les erreurs ne débitent pas une seconde fois les moyens métier de publication. Les fichiers temporaires et journaux d’essais ont une politique de réutilisation ou nettoyage borné, couverte dans les ressources de contrôle et de stockage ; des échecs successifs ne peuvent remplir silencieusement toute la réserve de livraison. Les effets CPU ou I/O effectivement dépensés, eux, sont comptés.

Une erreur d’appel peut survenir après un commit devenu durable. Avant toute répétition, la procédure relit le marqueur de génération et le reçu selon A2. Elle ne traite pas une réponse d’erreur comme une preuve que l’effet n’a pas eu lieu. Si le commit est retrouvé, elle retourne le reçu ; sinon elle reprend le même paquet dans la génération autorisée.

Le rang `δ` décroît sur les transitions durables de protocole, pas sur chaque erreur, flush ou attente. Démontrer qu’une tentative servie pendant le suffixe favorable réalise une diminution durable de `δ` ou atteint `Delivered`; si plusieurs primitives sont nécessaires à cette diminution, leur exécution finie est démontrée. Le passage de la fin logique à `ReadyToDeliver` a la même exigence de service borné et ne peut être reporté par de nouvelles propositions.

Si l’on veut une borne sur le nombre total d’appels physiques ou sur une réserve cumulée, il faut déclarer un maximum d’erreurs et de crashes ou un autre modèle de service quantifié, puis en dériver la borne. Sans cette donnée, seules la progression réussie, la terminaison conditionnelle et les coûts observés sont annoncés. Aucune seconde chance ne recrée les droits métier déjà consommés.

## 11. Instance séparatrice obligatoire de B

L’instance reçoit un artefact constitué identifié, non encore validé, un droit de publication à usage unique et un budget métier entier. Son objectif indépendant est la publication de cet artefact exact après validation de sa version.

Le critère de validation est reçu indépendamment des validateurs. Une validation DOIT être produite par un calcul établissant ce critère sur le contenu et la version effectivement lus, et non par l’ajout d’un simple indicateur « validé ». Le budget est un quota métier sur les opérations : il ne représente pas implicitement des secondes CPU ou des joules.

Le catalogue contient :

| Opération | Préconditions locales | Coût métier | Effet |
|---|---|---:|---|
| `validate(a,r)` | Artefact présent, version correcte, règle de validation autorisée | 1 | Calcule la validation et la lie à cette occurrence/version et à cette règle |
| `publish(a,v)` | Validation correspondante, droit de publication disponible | 1 | Publie l’artefact et consomme le droit unique |
| `explore(a)` | Artefact présent, droit d’exploration | 1 | Produit un résultat auxiliaire, sans accomplir validation ou publication |

Toutes les consommations s’appuient sur le budget disponible. Le catalogue ne contient aucune opération permettant de recréer un droit dépensé ou d’augmenter le budget. Les producteurs de cette instance sont raccordés à la chaîne pertinente du projet ; un appel maître sans rapport suivi d’un calcul indépendant ne suffit pas.

Les verdicts exigés sont :

| Cas | Verdict attendu |
|---|---|
| Budget 2, proposition `explore` avant validation | Localement permise si budget ≥ 1, mais aucun plan conforme d’achèvement ne reste ; refus de cette incorporation par le contrôle d’accomplissabilité |
| Budget 3, même proposition | Incorporation réellement possible, puis validation et publication ; le modèle a un effet observable |
| Budget 1 au départ | Preuve d’incompatibilité dans ce catalogue : deux opérations requises coûtent au moins 2 ; jamais de succès déclaré |
| Deux artefacts de même contenu, droits différents | Aucun transfert de droit ni substitution d’occurrence |
| Répétition de publication après réponse perdue | Retour du reçu validé ; aucune nouvelle consommation ni publication |
| Reset ou reprise après consommation | Même disponibilité des ressources et même état des obligations |

Dans la réalisation biphasée de B, un rang de travail possible est 1 avant validation et 0 après validation ; la publication appartient à la phase de livraison. Le rang métier agrégé illustratif 2/1/0 de la v0.1 est donc remplacé explicitement par la mesure de phases PROG-04. Les deux opérations requises et leur coût total de 2 sont INCHANGÉS ; la tâche n’est toujours réussie qu’après publication.

`explore` ne diminue pas le rang de travail. Son admission renforcée exige un budget restant suffisant pour validation ET publication. Avec budget 3, exploration puis validation laisse une unité pour livrer. Avec budget 2, le comparateur peut explorer puis valider, atteindre `LogicalGoal`, mais avoir budget 0 et aucun moyen de publier. C’est un échec final réel, malgré le succès logique. Le régime renforcé refuse l’exploration, valide avec une unité restante et publie.

La livraison renforcée ne doit pas dépendre d’une disponibilité simplement espérée : la réservation ou la conservation prouvée du droit et du quota font partie du témoin. Les coûts physiques d’un staging abandonné restent hors quota métier et sont comptés séparément.

Ajouter un cas de changement de voie réel : deux occurrences de règles de validation, aux producteurs distincts et autorisés, établissent le même critère reçu. La continuation de référence utilise la première ; la proposition du modèle fait utiliser la seconde, dont la production et les références sont effectivement conservées. Le but ne change pas. Ce cas doit différer d’un simple ajout d’opération facultative ou d’un renommage de la même exécution.

La preuve d’incompatibilité quantifie sur toutes les continuations légales du catalogue, pas sur une recherche particulière. Cette instance ne définit pas à elle seule la portée du théorème générique.

## 12. Obligations de preuve et statuts

Les noms suivants sont des noms de livraison proposés, pas des déclarations existantes :

| Identifiant | Obligation |
|---|---|
| `P01_ACTUAL_EFFECT` | La réponse, le successeur, l’extension, les justifications et le rendu proviennent du même paquet effectif |
| `P02_CONTRACT` | Préservation d’Inv et du contrat pour toute proposition décodée ou rejetée |
| `P03_RECOVERY` | Données de continuation positivement construites ; théorème sur le secours commun réellement appelé : `Ready` dans sa borne depuis tout état renforcé Working de rang positif ; successeur effectif et continuation conservés |
| `P04_PROGRESS` | Existence effective des tours sous service et commit déclarés ; non-augmentation par détour, diminution par le paquet réel du secours, borne des tours et composition séparée des coûts de contrôle |
| `P05_FUTURES` | Accord de tous les futurs déclarés, admissions comprises, avec transport du but et du rang |
| `P06_FORGETTING` | Préfixes réellement produits, distinction perdue et non-reconstruction dans le domaine déclaré |
| `P07_COVERAGE` | Toute exécution atteignable de la classe annoncée reste représentable par la grammaire portable |
| `P08_BYTES` | Aller-retour fidèle du présent complet et correction du chargement |
| `P09_EFFECT_REFINEMENT` | Accord du modèle d’effets avec le protocole physique, sous hypothèses de stockage nommées |
| `P10_RECOVERY_IO` | Récupération avant/après commit et absence de répétition d’effets métier validés |
| `P11_COUNTEREXAMPLE` | Existence d’une action localement permise détruisant l’accomplissabilité et d’un cas voisin où elle reste incorporable |
| `P12_DELIVERY_PHASE` | Fin logique distincte de livraison ; paquet, réservation et reprise conservés ; raccord de `δ` aux transitions durables, avec service borné de la préparation terminale |
| `P13_COMPARATOR` | Même programme de secours, interprète, règles d’allocation et données accessibles ; aucune Recovery cachée dans RawState ; preuve de succès borné sur le seul domaine renforcé et état bloqué accessible au comparateur |
| `P14_ALTERNATIVE_ROUTE` | Deux producteurs de validation réellement distincts établissent le même critère reçu et sont effectivement utilisables |
| `P15_CONTROL_RESOURCES` | Modèle instrumenté, borne d’état et coût de son calcul ; séparation des ressources facultatives, obligatoires et métier ; couverture des successeurs et absence d’épuisement facultatif du secours |
| `P16_EXECUTABLE_RESTART` | Projection et activation bornées conservant les données exécutables, le contrôle engagé et sa réserve ; secours réussi sur le présent chargé sans recherche ouverte ni rejeu historique |
| `P17_DELIVERY_LIVENESS` | Les conditions primitives de service, durabilité et succès, plus les reprises effectives, entraînent la sortie de ReadyToDeliver vers Delivered ; erreurs et succès ambigus traités sans double effet |

P01 à P08, P11, P13 et P14 portent des obligations Lean sur la sémantique déclarée. P15 et P16 doivent séparer leurs preuves de contrôle instrumenté et de transport des garanties d’allocation et de service du runtime. P09, P10, P12 et P17 distinguent lois pures ou de protocole, hypothèses primitives d’environnement et tests de leur réalisation. Aucun test physique ne transforme une hypothèse du système d’exploitation en théorème du noyau. Les contrats formels et leur ordre de preuve sont précisés dans l’annexe D.

Les nouvelles preuves respectent les restrictions constructives du dépôt. Les contrôles d’import, audits de constantes, contrôles de partage, fixtures de refus et registre gardent leurs rôles propres. Les nouveaux candidats scientifiques ne sont enregistrés qu’après une révision d’évidence existante, sans rafraîchissement mécanique des anciennes évidences. [R6–R7]

## 13. Tests, oracle et comparaison

### TEST-01 — Corpus minimal

Tester obligatoirement : `LogicalGoal` vrai et livraison pendante ; crash dans chaque phase ; réponse perdue après livraison ; blocage de livraison du comparateur ; politique silencieuse ; propositions malformées ; mauvais indices ; tentatives de changement du contrat ; lectures répétées sans progrès ; droits absents et consommés ; valeurs égales avec origines différentes ; objectif incompatible ; validation expirée ; publication répétée ; dépassement de délai ; réponse tardive ; checkpoint tronqué ; schéma ou configuration incorrects ; référence de liaison invalide ; tentative d’augmenter le rang ; cas budgétaires 1/2/3 ; oubli d’une distinction réellement produite.

Le test d’une action dont la viabilité n’a pas été certifiée doit distinguer preuve d’impossibilité et absence de certificat. Une limite de validation doit déclencher le fallback, lorsque le système reste dans ses conditions de disponibilité.

### TEST-02 — Interruptions

Injecter des arrêts avant staging, pendant staging, avant le point de validation, après validation avant réponse, après réception de la réponse et pendant la récupération. Après redémarrage, comparer état, droits, rang, compteur, occurrences, rendu et reçus.

Les tests doivent contrôler par instrumentation que le chargeur ne produit pas le passé validé, puis exécuter de nouvelles opérations depuis le présent chargé. Ces contrôles ne remplacent pas les obligations générales sur le chargeur et ses chemins exécutés. Pour A : au moins une nouvelle citation issue du maître et une déduction dépendante, pas seulement une somme sur un stockage isolé.

### TEST-03 — Évaluateur indépendant

L’oracle commun lit la tâche et les ressources reçues, les effets observés et l’artefact final. Il ne corrige pas l’exécution et ne définit pas le succès par la présence d’un certificat affiché. Sur les domaines finis de test de B, il vérifie indépendamment les possibilités d’achèvement.

Les domaines, graines, versions, budgets, limites et points de coupure sont figés avant l’essai confirmatoire. Les ensembles finis de tests ne bornent pas les quantifications des théorèmes.

### TEST-04 — Comparateur total sans Recovery cachée

Préserver la comparaison avec/sans prévue au lot 7. Pour B, définir une sémantique commune `RawStateΓ`, `Proposal`, opérations, coûts, droits, critères, codec structurel et phases de livraison. `RawStateΓ` admet explicitement des états non viables mais cohérents.

L’invariant renforcé et ses certificats forment une couche séparée : par exemple `(state : RawStateΓ) × EvidenceStrongΓ(state)`. Le type de base et les constructeurs des opérations ne demandent ni `Recovery` ni un budget couvrant toutes les obligations futures. Ils vérifient seulement les préconditions locales de l’opération effectuée.

Une unique stratégie de secours exécutable et totale est partagée. Son budget explicite est une allocation de contrôle, pas un certificat de viabilité :

```text
fallbackProgram : RawStateΓ → ControlProgram
fallbackBound   : RawStateΓ → Nat
fallback(s)     := runCtl(fallbackBound(s), fallbackProgram(s))
```

Ses résultats communs sont `ReadyStep`, `BlockedReason` ou `FuelExhausted/CheckTimeout`, avec trace et coût dans le modèle déclaré. Le programme ne reçoit ni preuve forte ni budget artificiellement supérieur pour le seul régime renforcé.

Elle tente les mêmes opérations, dans le même ordre, selon les mêmes règles de choix. Elle ne reçoit pas un certificat Recovery indisponible au comparateur. P03, P04 et P13 doivent établir, depuis les conditions structurelles d’`InvStrong` et le rang positif, que **cet appel exact** retourne `ReadyStep` dans sa borne et que le paquet obtenu fait progresser son successeur tout en conservant les moyens obligatoires. Cette conclusion n’est pas un champ définissant l’état commun. Le comparateur peut atteindre `Blocked` malgré les mêmes règles d’allocation et le même code.

La seule différence opérationnelle du comparateur d’ablation est qu’il n’exige pas le certificat supplémentaire de préservation de l’accomplissabilité avant d’incorporer la proposition. Les opérations, ressources, délais, conditions physiques, ordonnanceur proposition-puis-secours et critères de succès restent partagés. Les restrictions de rang locales calculables sont maintenues identiques ; l’opération `explore` est de rang inchangé dans les deux régimes. La garantie globale de progression n’est pas une hypothèse reçue par le comparateur : elle peut y échouer lorsque son secours se bloque. Aucune autre différence ne doit causer artificiellement le cas séparateur.

Ne pas reconstruire Recovery pour refuser indirectement l’exploration au comparateur. Ne pas restaurer un ancien état favorable après son blocage. Ne pas supprimer les états bloqués des métriques. Une absence de certificat ne prouve pas une impossibilité ; l’oracle ou la preuve d’incompatibilité ont leur statut propre.

Cas obligatoire en rejeu contrôlé : même entrée, budget 2, proposition `explore`, puis secours `validate` et tentative de livraison `publish`. Le comparateur est localement conforme, logiquement terminé après validation, mais non livré faute de budget. Le dispositif renforcé refuse `explore`, valide puis livre. À budget 3, les deux peuvent incorporer l’exploration et réussir. À politique silencieuse et budget 2, les deux doivent réussir : la comparaison ne handicape pas artificiellement le secours de référence.

Comparer aussi le dispositif complet avec politique silencieuse et avec modèle réel.

Distinguer rejeu d’une même suite de propositions et interactions adaptatives séparées. Les observations peuvent diverger dans le second cas. Le coût de l’ordonnanceur, des contrôles et de l’inférence est mesuré séparément. Un résultat identique ou défavorable n’est ni supprimé ni requalifié en avantage.

### TEST-05 — Contrôle obligatoire effectivement préservé

Les tests ci-dessous sont obligatoires et reliés aux preuves indiquées. Ils ne remplacent pas la quantification des théorèmes.

| Identifiant | Scénario | Observations exigées | Obligations |
|---|---|---|---|
| `T15_OPTIONAL_TIMEOUT` | Proposition dont l’examen atteint sa limite facultative | Motif exact ; aucun effet métier candidat ; crédits obligatoires intacts hors abandon provisionné ; même secours appelé ; `Ready` puis rang diminué et commit observé | P03, P04, P15 |
| `T16_OPTIONAL_REPEAT` | Contrôles facultatifs coûteux ou expirés répétés sur une suite de tours et de resets | Pas de recharge fictive des crédits cumulés ; pas de croissance incontrôlée des diagnostics/staging ; allocation obligatoire disponible ; progrès réel tant que Working actif | P04, P13, P15 |
| `T17_LOADED_FALLBACK` | Sauvegarde, processus neuf, activation, puis secours | Seuls octets et bundles autorisés fournis ; pas de recherche de plan ni de production historique ; données chargées réellement lues ; coût d’activation et de secours mesuré ; étape nouvelle, consommation et rang corrects | P05, P08, P16 |
| `T18_DELIVERY_ERRORS` | Plusieurs erreurs temporaires de lecture, écriture ou durabilité puis rétablissement des primitives | Paquet et réservation conservés ; retries effectivement déclenchés ; publication unique durable quand les préconditions favorables sont satisfaites ; reçu et consommation uniques | P10, P12, P17 |
| `T19_GROWING_STATE` | Tailles croissantes des instructions, références, lecteurs et entiers ; cas limites de capacité | Valeur de chaque borne, coût de son calcul, pas mesurés, pic mémoire/staging et allocations ; `k ≤ F(s)` pour tout cas dans la classe ; dépassement traité avant incorporation ou suspendu explicitement, jamais éliminé du corpus | P07, P15, P16 |
| `T20_BOUND_INTEGRITY` | Métadonnée de coût sous-estimée ou recette altérée ; carburant insuffisant sur une trace de coût connu | Activation forte refusée ou borne corrigée selon politique ; aucune effectuation ; résultats avec carburant suffisant identiques ; échec contrôlé sous coût exact, sans prétendre que toute valeur inférieure à une majoration doit échouer | P08, P15, P16 |
| `T21_MANDATORY_RESUME` | Interruption ou tranche au milieu du secours | Reprise fidèle du contrôle lorsque cette incarnation est utilisée ; pas de nouvelle proposition ; crédits non réinitialisés ; paquet identique à l’exécution continue ; aucun effet métier publié deux fois | P04, P10, P16 |
| `T22_NO_GOOD_WINDOW` | Le stockage répond toujours, mais toujours par erreur | État `Suspended/Pending` correctement conservé ; aucun faux `Delivered` ; distinction explicite avec les essais sous succès des primitives | P12, P17 |
| `T23_AMBIGUOUS_COMMIT` | Commit devenu durable, puis erreur ou perte de réponse | Réconciliation du marqueur/receipt avant retry ; aucune répétition métier ; même identité de publication | P10, P17 |

La famille croissante de T19, les budgets de contrôle, les graines, les points de coupure, le modèle de coût et les ressources physiques sont figés avant l’essai confirmatoire. Si le rang de l’instance séparatrice élémentaire ne permet qu’un tour de travail, T16 utilise une composition finie déclarée de tâches ou d’obligations pour tester réellement plusieurs tours ; il ne réinitialise pas silencieusement une tâche terminée.

La mesure doit observer la fonction effectivement appelée, les références lues, la formation suivante, les crédits de chaque domaine et la publication relue. Un simple log « fallback réussi » ou une sortie numériquement identique ne suffit pas. Les preuves de non-rejeu restent séparées de l’instrumentation partielle du binaire et de ses limites.

## 14. Livraison et critères de clôture

### Livraison A — Trois clôtures techniques, puis le raccord et l’évaluation

**Préflight A0 — Socle qualifié.** Conserver `f30196e4…` comme socle public observé ; inventorier les incréments locaux et leurs dépendances sans modifier le checkout en cours. Avant une nouvelle implémentation ou une déclaration de clôture, disposer d’un commit autorisé ou d’un snapshot de travail identifié par manifeste de fichiers normalisés LF, toolchain, commandes et résultats. Un manifeste ne remplace pas un commit d’évidence existant pour le registre. Ne pas commiter ou lancer un audit indépendant sans autorisation.

**A1 — Présent entier depuis des octets.** Réutiliser les codecs de contrôle, stockages, mémoire des citations, recettes et assignation déjà construits dans leur portée. Qualifier les nouveaux composants locaux de génération et d’état ; fermer les ressources restantes, préfixes, découvertes, applications, décompositions et environnements réellement nécessaires. Résoudre les ports depuis les données chargées, identifier Γ et prouver le retour du curseur entier puis du présent, y compris les états d’erreur de tâche couverts. Aucun curseur ou environnement historique indispensable n’est fourni depuis une mémoire de processus dans le test de chargement autonome. Cette clôture est mathématique et de codec ; elle ne revendique pas encore l’atomicité. Elle inclut désormais SER-05 : conservation des données du secours, activation bornée et appel du secours depuis le présent chargé, dans la portée des opérations de reprise déjà construites pour A.

**A2 — Protocole de commit et récupération.** Formaliser les générations, phases `Working/ReadyToDeliver/Delivered`, réservations, identifiants, point de validation et reprise sous crash. Établir la cohérence avant/après commit et les règles de doublons. Fixer les hypothèses de durabilité, d’ordre des écritures, de visibilité, de mono-écriture et de corruption couvertes. Le code du codec ne suffit pas à fermer A2. A2 décrit aussi le contrôle obligatoire en cours, la conservation de ses moyens, la réconciliation des réponses ambiguës et les conditions primitives suffisantes à la vivacité de livraison ; ces dernières ne sont pas remplacées par « l’environnement répond ».

**A3 — Réalisation physique.** Faire consommer A1 et A2 par l’adaptateur réel. Effectuer sauvegarde, arrêt, nouveau processus et nouvelle production maître dépendant du présent chargé ; puis déduction et livraison. Injecter les interruptions aux points prescrits, contrôler les données lues et les effets validés. Rapporter séparément ce que le protocole prouve et ce que l’expérience confirme de son incarnation. Mesurer bootstrap, contrôle facultatif, secours, exécution locale, staging et livraison ; exécuter T15 à T23 dans la portée applicable à A, sans lui attribuer les garanties de ressources consommables propres à B.

**A4 — Modèle réel.** Raccorder l’inférence, les erreurs, délais, propositions périmées et observations permises, sans laisser un canal d’effet contourner le contrôleur. Le résultat doit venir des productions, pas du texte anticipé du modèle.

**A5 — Comparaison du lot 7.** Figer avant le run protocole, entrées, seeds et évaluateur ; conserver résultats favorables et défavorables. A n’est déclaré fermé qu’après ses obligations d’accomplissement, de persistance, d’effectuation et de comparaison requises, pas au seul succès d’A1.

La livraison B n’est pas engagée comme nouveau chantier d’implémentation avant cette clôture d’A. Ses définitions et cas peuvent être spécifiés sans changer les priorités du code en cours.

### Livraison B — Extension séparée

B1 : interface paramétrique distinguant permission, accomplissabilité, données exécutables et contrôle borné ; preuve du secours commun depuis les invariants.  
B2 : constructeurs, enveloppes de contrôle et lois de l’instance à ressources consommables ; fermeture sous chaque successeur réel.  
B3 : transport du secours utilisable, activation bornée et raccord à la production, à la mémoire et à la livraison persistante.  
B4 : cas séparateurs, T15 à T23, tests adversariaux et comparaisons sur le même programme de secours et les mêmes règles d’allocation.

Chaque livraison fournit : spécification ; carte des quatre dépendances formation/exécution/preuve/transport ; sources Lean ; surface du protocole ; adaptateur ; scénarios ; résultats bruts référencés ; limites du modèle ; rapport de commandes réellement exécutées ; révision d’évidence et état des revues.

Une livraison est close seulement si ses obligations sont couvertes sur la classe annoncée, sur une révision de livraison identifiée avec ses dépendances. Le local mutable documenté dans la v0.2 n’est pas ce gel, et il n’a pas été observé de nouveau pour la v0.3. Un build vert, un test documentaire réussi, une réduction de mémoire ou un simple refus ne remplace pas les autres critères.

## 15. Formulation de résultat autorisée

Après satisfaction des obligations correspondantes, la formulation visée est :

> Pour la classe et le contrat déclarés, l’agent incorpore des productions justifiées et préserve les données ainsi que les moyens de sa continuation obligatoire. Le secours commun effectivement appelé termine dans sa borne de contrôle sur les états renforcés de travail et produit une étape réelle de rang inférieur. Cette propriété demeure utilisable depuis les états projetés ou rechargés. Sous les conditions primitives explicites de service et de succès du stockage, la procédure accomplit le travail puis livre le paquet exact ; les effets validés et les ressources consommées restent cohérents et non dupliqués dans le protocole annoncé.

Sont exclues sans résultats supplémentaires les formulations « alignement humain universel », « toute IA ne peut plus désobéir », « toute tâche est résolue », « toute fonction est sérialisable », « mémoire minimale en octets » et « exactement une fois sur tout effet distant ».

## Annexe A — Correspondance au socle effectivement consulté

### A.1. Statuts de connaissance

**Public identifié (v0.2)** signifie que le fichier ou son document a été récupéré alors à `f30196e4…`. **Local relu (v0.2)** signifie que le contenu indiqué a été lu intégralement dans le worktree lors de cette version, sans recompilation. Ces statuts sont historiques et n’ont pas été revérifiés pour la v0.3. **Rapport local (v0.2)** signifie que les résultats de commandes sont annoncés dans une documentation de développement lue ; cette spécification ne les reproduit pas. **À qualifier** signifie qu’une présence de source, un nom ou une déclaration ne suffit pas à conclure la livraison.

Les fichiers locaux n’ont pas reçu ici un manifeste exhaustif des empreintes et imports. Il serait inexact de leur attribuer le SHA public par simple proximité de branche. Des développements peuvent avoir eu lieu après ces lectures historiques. Les chemins ci-dessous sont relatifs au dépôt ; aucun chemin privé de poste n’est une référence scientifique publiée.

| Composant | Référence ou déclarations | Ce qui peut être réutilisé | Limite / action de clôture |
|---|---|---|---|
| Accomplissement documentaire existant | `DocumentaryAdaptive` : `all_policies_accomplish`, `Execution.rounds`, `Execution.bound` ; acquis examinés antérieurement | Toute politique dans la classe admissible existante, n tours et au plus 2n tentatives | Ne prouve pas B ; ni livraison physique, ni ressources consommables nouvelles |
| Contrôle portable | Public `DocumentaryPortableControl` : `byte_roundtrip`, `present_byte_roundtrip`, `loaded_all_futures`, `loaded_accomplishable`, décrits dans R8 | Contrôle exact, y compris liaisons absentes et tâches bloquées | Présent raccordé avec le MÊME stockage et dossier maître reçus ; ne charge pas le maître complet |
| Recettes maître | Local relu `DocumentaryMasterFormation` : `Formed`, `resources_exact`, `cursor_exact`, `executed_formed` ; documentation L1 | Restauration du support et du curseur depuis le payload de recettes typées | Enregistrement d’opération/ports seul ≠ environnement typé entier en octets ; fermeture transitive à requalifier |
| Assignation et lecteur mesuré | Documentation locale L2 ; modules `DocumentaryPortableAssignment`, `DocumentaryAssignmentCodec`, `DocumentaryAssignmentCapture` | Représentation des fonctions et mesures par recettes finies depuis la primitive fixée | Leur code n’a pas été intégralement requalifié lors de la v0.2 ; pas de codec de fonction arbitraire |
| Assignation séquentielle dépendante | Local relu `DocumentarySequentialPortable` : `Safe`, `formed_roundtrip`, `restore_at_exact`, `all_typed_consumers` | Assignation entière sous la classe de recettes sûre à profondeur fixée | Classe suffisante, pas décideur de toutes les assignations ; ne restaure pas tout le support |
| Traces et incorporation de l’assignation | Local relu `DocumentarySequentialCapture` : `program_bytes_exact`, `adaptive_bytes_exact`, `memory_bytes_exact`, `restored_state_exact` | Fidélité sur traces depuis `Ready` ; incorporation du champ chargé | `restoreState` reçoit encore le curseur et son environnement ; ne pas le présenter comme chargeur autonome de l’état entier |
| État couplé en cours | Local relu `DocumentaryStatePortable` : `record_exact`, `restored_exact`, `all_consumers` | La source propose un chargement sans état retenu reçu, sous `SequentialPortable.Formed`, incluant génération, graine, décisions et provenance | Pas de nouvelle compilation ni relecture intégrale des dépendances `GenerationPortable/HistoryPortable/FoundationPortable` ici ; statut « à qualifier », distinct du précédent raccord |
| Présent typé | `DocumentaryMaterializedPresent.present_exact`, `all_futures`, examinés antérieurement | Consommateur de l’égalité du présent réassemblé | Ne remplace pas l’égalité depuis octets de tous les composants |
| Livraison atomique | IO-02, IO-05, P09/P10/P12 proposés | Spécification de phases et du protocole | Aucune clôture prouvée de ce nouveau protocole annoncée lors de la v0.2 |
| Préservation sous ressources consommables | P03/P04/P11/P13/P14 proposés | Réutilisation visée des transports et producteurs | Nouvelle instance B et preuves requises, pas conséquence automatique des cas documentaires |

### A.2. Rattachement des obligations

| Obligation | Appui existant / vérification à mener |
|---|---|
| P01 | Paquets effectifs et partage des exécutions documentaire/maître ; étendre le même accord au descripteur de livraison et à B |
| P02 | Contrat et anciennes lectures du raccord existant ; formaliser InvBase/InvStrong et droits consommables |
| P03 | Prolonger l’accomplissement constructif existant par CONT-02/03 : données exécutables, résultat borné du secours commun et fermeture de ses préconditions depuis les successeurs |
| P04 | Réutiliser la borne documentaire ; démontrer le rang de B, le succès effectif de chaque secours, la composition des coûts et la vivacité sous conditions de service |
| P05 | Interfaces `ExactRealization` et futurs déjà prouvés ; inclure phases, droits et observations supplémentaires avant la nouvelle projection |
| P06 | Cas d’oubli existants ; contrôler à nouveau tout accès, reçu et empreinte dans la réalisation enrichie |
| P07 | Fermetures de formation maître/assignation et contrôle portable ; qualifier leur composition sur tous les états annoncés |
| P08 | Codecs de composants ; prouver le chargement du curseur et du présent entier avec Γ identifié |
| P09 | Nouveau protocole d’effet A2 avec hypothèses nommées, puis raccord A3 |
| P10 | Identifiants, génération et commit de livraison ; preuve de reprise et tests de réponse perdue |
| P11 | Contre-exemple budgets 2/3, et impossibilité budget 1 dans le catalogue fixé |
| P12 | Séparation LogicalGoal/Delivered, deux progressions et phase persistante de livraison |
| P13 | RawState, programme de secours, interprète et allocations communs sans Recovery comme entrée ; preuve de succès borné depuis InvStrong et blocage accessible au comparateur |
| P14 | Deux validateurs effectivement distincts, même critère reçu, pas de substitution d’occurrence |
| P15 | Nouvelles obligations CTRL-01/04 : bornes et allocations indépendantes du facultatif, avec coût des auxiliaires et couverture des états croissants |
| P16 | Prolonger les transports et codecs existants par MEM-05/SER-05 : activation et secours effectivement exécutables sous borne depuis les données conservées |
| P17 | Renforcer IO-06/ENV-01 : réussite des primitives de stockage et service entraînant Delivered, sans hypothèse circulaire de livraison |

Une ligne d’appui n’est pas un verdict « obligation close ». Le dossier de clôture doit relier, pour chaque obligation, les indices et formations, l’exécuteur réel, les champs consommés par la preuve et ce qui est conservé sous transport.

## Annexe B — Changements de la v0.2

1. Socle distant actualisé à `f30196e4…` ; sources locales plus récentes distinguées sans attribution artificielle de commit ou de vérification.
2. Accomplissement logique et livraison physique séparés par une machine de phases ; le rang nul ne vaut plus livraison acquise.
3. Comparateur défini sur un état commun sans Recovery implicite ; secours identique mais total, pouvant signaler un blocage.
4. A découpé en clôtures A1 octets, A2 protocole de commit, A3 incarnation physique, puis modèle et comparaison ; priorité A avant B conservée.
5. La livraison consomme ses droits et budgets une seule fois ; réponse perdue et effet perdu ont des traitements différents.
6. Cas des budgets et des deux validateurs conservés ; le budget 2 du comparateur peut atteindre le sous-but logique sans pouvoir livrer, résultat qu’il est interdit de masquer.
7. Statuts de preuve, rapports de développement, nouvelle exécution et potentiel industriel restent distincts.

### Complément — Changements de la v0.3

1. P03/P04/P13 portent un même théorème : le secours commun réellement appelé retourne une étape prête dans sa borne depuis tout état renforcé Working de rang positif ; cette étape réelle préserve l’invariant et diminue le rang.
2. Les données de continuation, leur validité et l’algorithme de secours sont séparés ; aucun choix matériel indispensable n’est caché dans une preuve inaccessible au comparateur ou au chargeur.
3. CTRL-01/04 et P15 distinguent contrôle facultatif, allocation obligatoire et ressources métier. Les bornes dépendent de l’état et leur calcul est compté. Les successeurs admis doivent aussi disposer de leurs moyens de contrôle.
4. MEM-05/SER-05 et P16 exigent activation bornée et secours depuis les données chargées, sans recherche de plan non bornée ni rejeu du passé. Un changement de représentation ne garantit pas par lui-même l’égalité des coûts.
5. ENV-01/IO-06 et P17 remplacent le simple « retour de l’environnement » par des conditions primitives de service, réussite et durabilité suffisantes pour livrer. Les réponses toujours en erreur ne satisfont pas ces conditions.
6. T15 à T23 testent expiration facultative, répétitions, volumes croissants, reprise du contrôle, activation froide, erreurs temporaires et commit ambigu. Les mesures séparent progrès logique, contrôle, consommations et publication.
7. Les états du dépôt et les références de la v0.2 restent historiques ; la v0.3 n’annonce ni nouvelle lecture du worktree, ni compilation Lean, ni test de ces obligations.

## Annexe C — Portée industrielle et sources externes

La réalisation visée traite des contrats et effets explicitement couverts. L’usage industriel est une hypothèse de transfert à établir par une tâche représentative, des coûts mesurés et la couverture de tous les canaux d’action ; ce document ne prétend pas démontrer une résolution générale de l’alignement.

La v0.2 citait E3 comme motivation du contrôle des voies d’action et de l’indépendance de l’évaluation, et E4 pour la séparation entre intention et spécification. Ces références sont conservées historiquement, sans nouvelle vérification dans la v0.3 et sans usage comme prémisse des nouveaux contrats formels. Aucune de ces références n’est un verdict sur Relational Perimeter. L’évaluateur final des invariants ne doit pas être un jugement de LLM auquel on donne l’autorité d’un certificat.

## Annexe D — Contrats formels à construire et ordre des preuves

### D.1. Statut et notation

Les noms de cette annexe sont des interfaces de spécification à traduire dans les namespaces retenus après qualification du socle. Les schémas ressemblent à des signatures Lean mais **ne sont ni du code compilable livré ni des déclarations existantes**. Aucune preuve de complétude algorithmique ne doit être remplacée par l’hypothèse de son propre énoncé.

Soit `S := RawState Γ`. Le programme de secours reçoit uniquement `s : S`. L’état contient, ou référence dans un bundle conservé, ses données de recette. Le prédicat `StrongWorking Γ s` abrège les conditions structurelles `InvStrong Γ s`, la phase Working et la présence des données de contrôle applicables ; il ne contient pas comme champ « `runCtl` retourne Ready ».

`EvalCtl(c,k,r)` décrit une évaluation du programme `c` produisant `r` au coût `k` dans la sémantique instrumentée. `runCtl(f,c)` est son interprète effectif borné. `PreparedStep Γ s` contient les productions calculées, leur successeur préparé, les références et les intentions d’effet. Sa construction commune peut porter des preuves locales ; elle ne requiert pas le certificat fort de viabilité de tous les futurs.

### D.2. Préconditions de l’interprète et coût

**CTL-SOUND.** Un résultat terminé de `runCtl` correspond à une trace `EvalCtl` des mêmes primitives et du même résultat, de coût inférieur ou égal au carburant fourni.

**CTL-COMPLETE.** Une trace finie `EvalCtl(c,k,r)` est effectivement atteinte par `runCtl(f,c)` pour tout `f ≥ k`. Les conventions d’arrêt et le coût du dernier pas sont fixés avant les preuves.

**CTL-MONO.** Si l’interprète termine avec `r` à carburant `f`, il termine avec le même `r` pour tout carburant supérieur. Un surplus n’autorise pas une autre recherche ou un résultat différent.

**BOUND-COMPUTABLE.** Le calcul de `fallbackBoundΓ(s)` est effectif sur la représentation de `s` et possède un coût de bootstrap établi indépendamment de la réussite du secours. Les bornes de validation, d’étape préparée et de chargement ont le même traitement.

### D.3. Contrat principal du secours

L’obligation centrale a la forme suivante, où le témoin de `p` doit être raccordé au résultat calculé, et non choisi indépendamment :

```text
fallback_ready_within :
  StrongWorking Γ s → 0 < ρwork(s) →
  ∃ k, ∃ p : PreparedStep Γ s,
      EvalCtl(fallbackProgramΓ(s), k, Ready(p))
    ∧ k ≤ fallbackBoundΓ(s)
    ∧ runCtl(fallbackBoundΓ(s), fallbackProgramΓ(s)) = Done(Ready(p))
    ∧ InvStrongΓ(p.next)
    ∧ ρwork(p.next) < ρwork(s)
    ∧ RequiredEnvelopeValidΓ(p.next)
```

Dans cette notation, les quantificateurs existentiels expriment la correction du **résultat d’une fonction exécutable indépendante**. Ils ne sont pas utilisés pour extraire classiquement un programme depuis une existence propositionnelle. Une formulation par paquet dépendant en `Type` est également possible, à condition que les données runtime soient celles de l’interprète commun.

La preuve suit la représentation finie de la continuation, résout les références reçues et ses préconditions, relie le premier producteur au paquet, établit le reliquat de la recette et compose les coûts. Elle exclut le blocage et l’expiration pour le domaine renforcé ; elle n’affirme pas que tout état viable possède une telle recette ou borne.

**FALLBACK-EFFECT.** Sous un commit réussi du paquet `p`, le successeur visible est exactement `p.next`, avec ses consommations, liens, rendu et reçu. Un échec avant commit conserve la génération précédente ; un résultat ambigu passe par récupération. Cette loi est distincte de `fallback_ready_within`.

### D.4. Fermeture des ressources et théorème de tour

**OPTIONAL-ISOLATION.** L’examen d’une proposition dépense au plus son allocation facultative et son abandon provisionné ; il ne diminue pas la réserve du secours courant, ne bloque pas son accès et ne fait pas croître hors enveloppe les données critiques.

**ADMITTED-CLOSURE.** Si une proposition est incorporée avec successeur `s′`, ses données de continuation, son enveloppe de contrôle, ses préconditions et ses moyens de livraison sont établis à partir du paquet réel. Les règles de réserve prennent `s′` en compte même lorsque `ρwork(s′) = ρwork(s)`.

**TURN-TOTAL.** Depuis un état renforcé Working de rang positif et pour toute proposition, le traitement facultatif se termine ou est abandonné selon ses limites ; il donne soit un paquet de rang strictement inférieur, soit un état renforcé de rang non supérieur depuis lequel `fallback_ready_within` s’applique. Sous service obligatoire, la construction du paquet de fin de tour termine dans l’enveloppe démontrée.

**TURN-PROGRESS.** Tout commit de ce paquet conserve l’invariant renforcé et diminue le rang. L’existence de ces commits est obtenue depuis ENV-01 et le protocole ; elle n’est pas évacuée en ne quantifiant que sur une sous-liste de succès observés.

**WORK-LIVENESS.** L’induction sur le rang, avec TURN-TOTAL et le raccord de commit, conduit à `LogicalGoal` puis à la préparation de livraison. Le nombre de tours de progression validés est borné par le rang initial ; les micro-pas et retries ont leurs comptes séparés.

### D.5. Représentations, octets et reprise

**PROJECT-EXECUTABLE.** Si `s` est projeté vers `q(s)`, les données de continuation et leurs interprétations sont raccordées ; le secours réduit obtient un paquet dont le successeur commute avec `q`, dans une borne calculable depuis le présent réduit. Cette borne peut différer de celle du présent riche.

**ACTIVATE-BOUNDED.** Pour tout `PortableStrong Γ s`, le programme d’activation appelé sur `encodeΓ(s)` termine dans la borne bootstrap annoncée, retourne le présent et ses données correctement interprétées, puis permet le `Ready` borné du secours. Il ne reçoit ni état historique conservé en RAM ni certificat contenant un programme externe non encodé.

**RESUME-CONTROL.** Lorsque l’implémentation utilise des tranches, la concaténation de leurs traces donne la même évaluation que le programme non interrompu ; le compte des pas déjà effectués et le carburant restant sont cohérents. La publication métier demeure gouvernée par son commit distinct. Les travaux perdus avant durabilité sont explicitement distingués des crédits repris.

### D.6. Livraison : théorème de vivacité non circulaire

Définir les traces de l’adaptateur à partir de primitives nommées et de leurs issues. Une condition `GoodServiceΓ(trace,j)` annonce un suffixe depuis l’indice `j` dans lequel les allocations nécessaires restent disponibles, les appels utiles de stockage terminent **avec succès** et respectent la durabilité annoncée, le contrôleur et les retries sont servis et les commits nécessaires ne sont plus interrompus. Cette condition n’utilise pas `Delivered` dans sa définition.

Pour lever toute ambiguïté de quantification, on peut représenter `trace` par une suite indexée par `Nat`, avec stationnarité après un statut terminal. `ActualDeliveryRun` relie chaque transition aux primitives réellement invoquées ; le service équitable exige qu’une étape obligatoire activée soit effectivement servie à un indice fini ultérieur. Un préfixe qui s’arrête définitivement avant cette étape ne satisfait pas cette hypothèse. Le seuil `j` porte sur les résultats des appels et le service, pas sur un rang arbitrairement choisi après avoir observé une publication.

Le théorème cible est :

```text
delivery_eventually_commits :
  InvStrongΓ(s) → phase(s) = ReadyToDeliver →
  ActualDeliveryRunΓ(s, trace) →
  (∃ j, GoodServiceΓ(trace,j)) →
  ∃ n, phase(stateAt(trace,n)) = Delivered
       ∧ SameFrozenPackageΓ(s, stateAt(trace,n))
       ∧ UniqueCommittedPublicationΓ(trace, publicationId(s))
```

Il faut construire `ActualDeliveryRun` par les appels effectifs, démontrer la terminaison du contrôle de tentative, puis le progrès du protocole sous succès de ses primitives. Une réserve de droits ne suffit pas à prouver un flush ; un flush qui retourne erreur ne devient pas une réussite parce que le but logique est atteint.

Une formulation constructive peut donner positivement le seuil `j`, les conditions du suffixe et le témoin d’un indice fini `n`; elle ne requiert pas de détecter magiquement à l’exécution que toutes les erreurs futures ont cessé. Le contrôleur continue d’appliquer sa politique de reprise totale.

### D.7. Graphe de dépendances attendu

```text
recettes et ressources constituées → préconditions de RecoveryData
      → correction de l’interprète et coût de ses primitives
      → bornes calculables + enveloppes + séparation des allocations
      → fallback_ready_within sur le programme commun
      → fermeture après proposition et après secours
      → tours réellement terminés + commits sous service annoncé
      → progression logique par le rang

ces mêmes données et enveloppes
      → projection exacte / codec et activation bornée
      → secours effectivement utilisable depuis le présent chargé

LogicalGoal + paquet figé + moyens réservés
      → contrôle de livraison borné + protocole de commit
      → succès des primitives et reprises servies
      → Delivered avec publication validée unique
```

Le comparateur partage le programme et les primitifs, mais ne dispose pas de la fermeture par l’admission renforcée. Le contre-exemple doit montrer où une précondition de `fallback_ready_within` cesse d’être établie, sans changer de secours ni lui soustraire artificiellement des crédits.

## Références

**Révisions et origine des références.** R1–R7 sont des appuis hérités de la v0.1 examinés alors au commit historique `6575de4…`; leur qualification pour la livraison actuelle doit suivre A0. R8 et L1–L4 reprennent les lectures consignées dans la v0.2, sans nouvelle consultation, commit ou audit attribué dans la v0.3. Les mentions « consulté » dans E1–E4 rapportent le statut historique de la v0.2, pas une nouvelle vérification externe. Les obligations ajoutées en v0.3 sont des exigences de conception et des cibles de preuves, fondées sur la relecture de cette spécification et sur les cinq corrections humaines reçues.

- **R1** — `docs/work/plan-alignement-agent-dossier.fr.md` : cible, ordre et critères des lots.
- **R2** — `docs/work/restauration-present-composants.fr.md` : présent typé et frontière de réalisation.
- **R3** — `Tests/LocalAlignment/DocumentaryMasterPayload.lean` : restauration typée des ressources maître.
- **R4** — `Tests/LocalAlignment/DocumentaryMaterializedPresent.lean` : égalité du présent typé et futurs.
- **R5** — `RelationalPerimeter/Constitution/Continuation/Minimality.lean` : réalisation exacte et composition des futurs.
- **R6** — `AGENTS.md` et `docs/methode-de-travail-scientifique.fr.md` : relus sur la branche distante puis dans le worktree ; autorité, portée et distinction des verdicts.
- **R7** — Registre `docs/scientific-claims.json` : références historiques, non actualisées par cette spécification.
- **R8** — `docs/work/controle-documentaire-portable.fr.md`, version publique : https://github.com/JohnDoe-collab-stack/relational-perimeter/blob/f30196e4a8ae2b77b0d061c1e03cccd236265013/docs/work/controle-documentaire-portable.fr.md . Contrôle portable et conditions de `present_byte_roundtrip`.
- **L1** — `docs/work/recettes-producteurs-maitre.fr.md` et `Tests/LocalAlignment/DocumentaryMasterFormation.lean`, lectures locales intégrales. Autres modules désignés par le document : références de développement, pas nouvelle validation en v0.3.
- **L2** — `docs/work/assignation-lecteur-portables.fr.md`, lecture locale intégrale ; limites de la primitive et du codec.
- **L3** — `docs/work/assignation-sequentielle-portable.fr.md`, `Tests/LocalAlignment/DocumentarySequentialPortable.lean`, `Tests/LocalAlignment/DocumentarySequentialCapture.lean`, lectures locales intégrales.
- **L4** — `Tests/LocalAlignment/DocumentaryStatePortable.lean`, lecture locale intégrale ; dépendances et build non requalifiés. `DocumentaryFoundationPortable.lean`, `DocumentaryHistoryPortable.lean` et `DocumentaryGenerationPortable.lean` ont été repérés, pas relus intégralement.
- **E1** — SQLite, *Atomic Commit In SQLite*, consulté : https://sqlite.org/atomiccommit.html . Référence sur les hypothèses et le point de commit, sans imposer une dépendance SQLite.
- **E2** — Chen et al., *Using Crash Hoare Logic for Certifying the FSCQ File System*, référence héritée de v0.1, non réexaminée en v0.3 : https://www.usenix.org/conference/atc16/technical-sessions/presentation/chen_haogang .
- **E3** — Anthropic et coauteurs, *Agentic Misalignment in Summer 2026*, consulté : https://alignment.anthropic.com/2026/agentic-misalignment-summer-2026/ . Cas simulés ; aucun verdict sur Relational Perimeter.
- **E4** — Google DeepMind, *Specification gaming: the flip side of AI ingenuity*, consulté : https://deepmind.google/blog/specification-gaming-the-flip-side-of-ai-ingenuity/ . Adéquation de la spécification, distincte de sa satisfaction.

- **U1** — Spécification fournie `RP_ALIGN_PERSIST_SPEC_v0_2.fr.md`, lue intégralement pour la v0.3 ; SHA-256 des octets du fichier source : `d6854c2dfc969ce71c567f13434437e65bc544f505222b04584c24be35b72341`. Les cinq observations humaines reçues ensuite portent respectivement sur le secours commun effectif, ses moyens de contrôle, sa reprise utilisable, les conditions de livraison réussie et leurs tests.
