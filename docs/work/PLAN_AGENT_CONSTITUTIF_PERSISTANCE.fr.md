# Plan d’implémentation : agent constitutif et persistance sous contrat

## 1. Objet, statut et état de départ

Construire une première instance d’agent symbolique interactif sur le calcul
existant. L’agent poursuit la recherche réelle, utilise ses productions pour
organiser ses obligations et restitue uniquement des réponses autorisées par
une exigence explicitement constituée. Sa continuation doit rester correcte
après la perte d’une distinction de profil source.

Ce plan applique la [note scientifique de référence](../constitution-calcul-et-persistance-pour-ia.fr.md).
Les sections 2 à 16 conservent la spécification du chantier. La réalisation
locale et ses vérifications sont consignées en section 17 ; elles ne constituent
pas un verdict d’audit indépendant ni une intégration dans `main`.

État examiné :

- branche : `codex/unified-foundation-master-instance` ;
- HEAD : `75057f09cc9a535e8be3390999fa688c9ee3a96d` ;
- dernier commit scientifique soumis :
  `8468f88448c51a0cd0ae178865fd014968131c47`.

La soumission d’un audit n’est pas sa validation. Le présent plan ne transforme
pas les corrections soumises en verdict indépendant acquis.

Ce fichier est un document de chantier : il doit être absent de l’arbre intégré
dans `main`. Les spécifications scientifiques finales et les instructions de
reproduction seront des livrables distincts.

## 2. Ce qui reste invariant

La [cible scientifique existante](../conclusion-largeur-exponentielle-conservation-identites.fr.md)
reste inchangée. La construction de l’agent ne remplace aucun de ses résultats :

- les profils proviennent de l’histoire des rôles constitués ;
- les productions locales ont lieu dans l’exécution, sans lecture du futur ;
- les cibles proviennent de l’action exécutée et de la chaîne exacte ;
- le regroupement conserve les identités sources et possède son autorisation ;
- l’image du régime reste exactement raccordée aux cibles produites ;
- le `iff` de pleine largeur porte sur les régimes finis surjectifs ;
- les lectures extensives et quantitatives restent en aval ;
- l’oubli reste relatif à une mémoire déterminée et à un contrat explicite.

Les quatre fichiers initiaux restent intacts. Aucune nouvelle « fondation
d’agent » ne doit leur être substituée. Les nouvelles constructions sont des
consommateurs de leurs descendants déjà établis.

La méthode demeure constitutive de bout en bout : former positivement les
objets, produire leurs réalisations depuis leurs ressources, démontrer leurs
accords, puis suivre les déterminations à travers les passages concernés.
Stocker une preuve, une provenance ou un identifiant à côté d’une sortie
indépendante ne satisfait pas cette méthode.

Séparer aussi les trois passages concernés : les transports de références
conservent positivement les occurrences anciennes ; l’action de normalisation
porte les garanties de son critère sans être un transport réversible ; la
projection de mémoire peut perdre une distinction tout en préservant le
contrat futur. Le terme « exact » ne les transforme pas en une même sorte
d’équivalence. Formation, réalisation, admission et satisfaction de l’exigence
doivent garder leurs types et leurs lois distincts.

## 3. Première instance proposée et exigence concrète

### 3.1. Un agent de recherche et de restitution certifiée

La première instance n’est pas un modèle de langage général. C’est un agent
symbolique qui dispose d’une session persistante et reçoit des demandes
explicites : poursuivre la recherche, consulter une production et soumettre
une réponse candidate à autorisation.

Sa demande centrale est `obtain handle var` : obtenir une lecture autorisée,
y compris lorsque la production désignée n’existe pas encore. Le contrôleur
vérifie le périmètre, consulte les ressources disponibles, produit les étapes
manquantes si nécessaire, puis construit la réponse. Il ne délègue pas à
l’utilisateur le choix de chaque appel interne au moteur.

Il utilise la famille publique actuelle, paramétrée par `input`. Il ne prétend
pas résoudre des instances SAT arbitraires. Ses décisions de décomposition
restent celles effectivement découvertes par ce moteur, pas une politique
supplémentaire donnée sous le nom d’agent.

### 3.2. L’exigence reçue

L’utilisateur fournit un périmètre de restitution : une liste finie non vide
de variables dont les valeurs peuvent être demandées dans les continuations
produites. Ce périmètre ne contient ni les réponses attendues ni une table de
normalisation préconstruite.

L’initialisation reçoit aussi un code de sélection du profil initial. Sa
longueur est contrôlée contre le nombre de rôles réellement exécutés. Ce code
est interprété seulement après leur formation, par sélection des occurrences
constituées ; il ne définit pas un carrier de booléens substitué à ces rôles.
Cette interprétation se fait par récursion sur l’histoire, sans énumérer ses
profils. Le code source et le profil réalisé ne sont pas conservés dans la
mémoire de reprise.

Une initialisation à périmètre vide ou à code de mauvaise longueur est refusée
par une vérification exécutable. Les initialisations admises doivent être
effectivement construites, pas postulées par une hypothèse de validité.

L’exigence est la suivante :

> Poursuivre le moteur autorisé depuis ses productions réelles ; ne restituer
> une valeur que pour une production effectivement formée et une variable du
> périmètre reçu ; restituer la valeur de cette production, non une valeur
> choisie par le contrôleur ; préserver les garanties d’acceptation annoncées
> par les actions utilisées ; conserver ces droits et ces accords après reprise.

Cette exigence n’est pas définie par les réponses que l’agent décide d’émettre.
Une réponse candidate peut être fausse, une demande peut être hors périmètre,
et un identifiant peut ne désigner aucune production. Ces cas doivent avoir
des réponses négatives distinctes et exécutables.

La correction de restitution et la préservation du critère du calcul sont
deux garanties séparées. Leur réunion ne sera pas appelée alignement humain
général. Cette première instance est la réalisation concrète sur laquelle
fermer le suivi d’une exigence ; elle ne remplace pas la cible future plus large.

### 3.3. Où l’exigence est effectivement consommée

Le périmètre fourni détermine les inspections admises. Il est lu par le
producteur d’autorisation d’une réponse. Modifier ce périmètre doit pouvoir
modifier une admission sur une même production, sans changer la vérité de
cette production.

Le périmètre est une liste de variables `SAT.Var` reçue, pas une restriction
nouvelle du domaine du moteur. L’admission teste l’appartenance à cette liste ;
les éventuels doublons n’ajoutent aucun droit. La fraîcheur, la recherche et la
préservation SAT restent les invariants du moteur. La nouvelle exigence
gouverne la restitution, non le choix des variables de découverte. Ne pas lui
attribuer une influence sur cette découverte que le producteur n’a pas.

La valeur proposée est comparée à la lecture calculée depuis la cible réelle.
Le témoin positif de cet accord entre dans la construction de la réponse
autorisée. Une preuve conservée seulement dans le certificat final ne suffit pas.

## 4. Socle à réutiliser, sans le réexécuter comme justification

| Besoin de l’agent | Construction existante | Réemploi exact |
| --- | --- | --- |
| Formation et ressources antérieures | [ConstructedSupport](../../RelationalPerimeter/Constitution/Resources/ConstructedSupport.lean) | `Producer`, `Formation`, `Support.extend` et transports des références. |
| Session initiale commune | [UnifiedPublicCertificate](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean) | `publicInstance`, ses rôles, son régime, son curseur et son checkpoint. |
| Découverte et production locale | [MasterResourceExecution](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MasterResourceExecution.lean) | Producteurs réels et ordre de formation de chaque tête. |
| Moteur après réduction de mémoire | [LiveResourceContinuation](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/LiveResourceContinuation.lean) | `produce`, `Production.next`, `execute` et accords avec le curseur riche. |
| Action sur les données et préservation | [RoleIndexedProgram](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleIndexedProgram.lean), [RoleProfileSemantics](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleProfileSemantics.lean), [RoleGroupingSemantics](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleGroupingSemantics.lean) | Actions typées, préservation distincte et cohérence des traces dans leur domaine annoncé. |
| Normalisation et regroupement autorisé | [ExecutedCausalNormalization](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExecutedCausalNormalization.lean) | Résultat par élimination de chaîne, cibles, traces, autorisation et fibres exactes. |
| Première mémoire avec inspections | [ProducedProfileContinuation](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ProducedProfileContinuation.lean) | Lecteurs de la cible préparée et non-reconstruction du profil source. |
| Composition de la continuation | [ContinuationContract](../../RelationalPerimeter/Constitution/Grouping/ContinuationContract.lean) | Lois distinctes de transition, d’événement, de lecture et d’admission ; fermeture sur les requêtes finies. |

Ces constructions ne certifient pas déjà les nouveaux types de requêtes ou
l’exigence de restitution de l’agent. Il faut construire leurs raccords.

Deux limites du contrat actuel doivent être traitées explicitement :

1. `advance` conserve la cible préparée et ses lecteurs ; il n’ajoute pas les
   lecteurs des nouveaux rôles exécutés.
2. Les lectures et admissions riches actuelles sont définies via la projection.
   Pour l’agent, la spécification riche des nouvelles observations doit être
   écrite depuis ses productions, indépendamment de l’implémentation réduite.

## 5. Types et stratification à construire

### 5.1. Exigence et demandes

`AgentRequirement` porte le périmètre fini reçu et sa réalisation positive.
Il ne porte pas le profil source destiné à être oublié.

Sa formation doit venir de la réception effective de ces données. Les demandes,
leurs autorisations et les réponses doivent ensuite être produites depuis ces
ressources par les `Producer` locaux et leurs références typées, non par des
constructeurs de sorties libres accompagnées de labels.

`AgentRequest` distingue :

- `advance steps` : demander un nombre fini de nouvelles étapes réelles ;
- `inspect handle var` : consulter une continuation produite ;
- `obtain handle var` : produire, si nécessaire, la continuation désignée puis
  en restituer la lecture autorisée ;
- `propose handle var value` : proposer une valeur à autorisation.

Le handle est une adresse dérivée d’une production constituée. Un nombre reçu
de l’extérieur ne devient pas, à lui seul, une occurrence. La résolution de
l’adresse doit construire le témoin de la production désignée ou une preuve
concrète de son absence dans le registre courant.

Les adresses externes sont locales à cette session. Une adresse numérique
identique dans une autre session ne constitue pas une occurrence identique.
Ce lot ne promet pas une authentification globale entre processus ; les
accords internes, eux, doivent empêcher un raccord à une production étrangère.

Les entrées sont ajoutées en fin de registre. Leur adresse externe est un
ordinal de création stable, distinct de la position actuelle d’une référence
dans un support étendu. Le passage entre cette adresse et l’occurrence riche
doit consommer le transport de références approprié ; les anciennes positions
du support ne restent pas numériquement fixes lors de son extension.

### 5.2. Productions et données

`ProducedAnswerTarget` doit porter la continuation cible réelle et son accord
avec la production qui l’a calculée. Le type ne doit pas permettre d’insérer
une affectation indépendante en lui ajoutant après coup une étiquette de rôle.

La cible initiale est un `ExecutedOperationalTargetProfile`, c’est-à-dire une
famille dépendante de continuations, et non une unique `SAT.Assignment`.
Initialiser le registre avec une entrée par rôle de l’histoire maître, dans
l’ordre de ses rôles, depuis les composantes de cette cible effectivement
normalisée. Sa longueur initiale est donc le nombre de rôles exécutés. Le
handle `0` lit la première de ces continuations, pas la cible globale entière.
Cette préparation parcourt une seule histoire de rôles ; elle n’énumère pas
ses profils. Réutiliser la construction de `targetReaders`, mais conserver
les accords des composantes et leur contexte plutôt qu’une liste de lecteurs
libres.

Chaque étape exécutée après reprise ajoute ensuite une entrée depuis
`production.built.stage.application.output`. Les entrées initiales et les
nouvelles entrées ont des contextes de continuation distincts : les premières
relèvent du rôle normalisé concerné, les secondes de la cible du schedule de
cette étape. Les représenter par une somme dépendante de ces provenances,
sans créer une seconde famille ni convertir arbitrairement l’une dans l’autre.

La lecture commune est seulement la projection calculable vers l’affectation
de la continuation, puis son application à la variable demandée. Sa garantie
reste attachée au contexte exact : `RoleSemantics.TargetAccept` fournit les
accords initiaux composante par composante ; `SequentialStageRun.outputAccepted`
fournit l’acceptation de la nouvelle sortie. Ces garanties ne disent ni qu’une
réponse booléenne satisfait une formule globale indépendante, ni que toutes
les entrées satisfont une même formule. Les champs de source riche, leur
projection réduite et les preuves doivent exprimer cette portée.

Le registre contient plusieurs productions consultables ; sa taille n’est pas
la largeur des obligations indépendantes. Son extension ne démontre pas une
nouvelle largeur globale un pour toutes les interactions d’un agent arbitraire.
Les résultats de largeur existants restent ceux de leurs régimes et carriers
respectifs.

`AnswerAuthorization` consomme ensemble :

- la réalisation de l’exigence reçue ;
- l’occurrence positive du handle ;
- l’appartenance de la variable au périmètre ;
- la lecture de la continuation effectivement produite ;
- l’accord de la valeur candidate avec cette lecture ;
- la garantie d’acceptation applicable à cette cible.

### 5.3. Source riche et mémoire d’agent

| Source scientifique riche | Mémoire de reprise |
| --- | --- |
| Exigence formée et ses références historiques. | Réalisation de la même exigence nécessaire aux opérations futures. |
| Curseur, supports et productions de l’exécution. | État vivant effectivement projeté et fraîcheur requise. |
| Profil initial, résultat et trace de normalisation. | Composantes de la cible initiale produite et leurs lecteurs, sans profil initial. |
| Provenance des productions consultables. | Registre de handles et de continuations cibles réellement produits. |
| Histoire des actions et autorisations. | Données nécessaires aux futures actions ; pas une archive intégrale ajoutée implicitement. |

Le type de mémoire ne doit pas être indexé par le profil initial oublié. Tous
ses champs, y compris les files de demandes, identifiants, diagnostics et
journaux conservés, entrent dans la preuve d’oubli. Une projection vers un
petit sous-champ ne démontrera pas l’oubli dans la mémoire complète de l’agent.

Le registre réduit porte la provenance des cibles et des étapes, pas le choix
de l’occurrence source gauche ou droite du profil initial. Ce choix et sa trace
restent sur la source riche. Prouver une factorisation explicite de la mémoire
initiale par l’exigence commune, le curseur commun et la cible produite :
l’égalité de ces données doit donner l’égalité de la mémoire complète. Un
registre qui retient ce choix source détruirait cette factorisation et la
preuve d’oubli, même si ses lecteurs rendent les mêmes valeurs.

Les formations historiques et leurs transports restent sur la source riche.
Les ressources retenues par la projection possèdent leurs réalisations et
leurs accords de lecture propres ; le runtime ne conserve pas le support
historique intégral pour justifier ces accords. Former une nouvelle ressource
depuis la mémoire projetée n’autorise pas à la déclarer simplement « donnée »
si sa garantie annoncée est celle d’une production antérieure. Le raccord de
cette réalisation avec la production source doit être fermé avant son usage.

Le registre peut croître avec les productions que le contrat promet encore
de consulter. Aucune mémoire constante ou minimale n’est annoncée. Supprimer
des productions de ce registre exigerait un contrat distinct, explicitement
restreint ; cela ne fait pas partie de cette première implémentation.

### 5.4. Ordre des producteurs

```text
exigence reçue et ressources constituées
    → session initiale réelle
    → demande reçue et occurrence formée

advance : découverte → application → décomposition locale
application → output cible → composante réelle, lecteur et entrée de registre
application → nouvel état
étape + préfixe reçu → décomposition → nouveau préfixe riche
nouvel état + registre étendu → prochaine demande

inspect/propose : exigence + handle réalisé + cible produite
    → lecture → décision d’admission → réponse autorisée ou refus motivé

obtain : exigence + registre courant + demande
    → refus hors périmètre, lecture disponible ou étapes manquantes
    → même worker d’avancement → handle formé → réponse autorisée

sorties de la demande courante
    → état et registre transmis à la demande suivante
```

La recherche consomme l’état transmis ; la décomposition riche consomme le
préfixe transmis. Ces producteurs ne doivent pas être confondus. Une requête
courante ne reçoit pas la suite des requêtes futures.

## 6. Exécuteur et partage effectif des productions

Construire une seule entrée runtime par requête, retournant conjointement la
mémoire suivante, l’événement et les témoins d’autorisation concernés.

Pour `advance steps`, une récursion structurelle sur `steps` produit chaque
étape une fois, puis réutilise son résultat pour :

1. former l’événement de cette étape ;
2. former l’entrée de registre depuis son output ;
3. transmettre son état suivant à la récursion.

Le côté réduit utilise le moteur vivant existant. Le côté riche spécifie les
mêmes étapes par le moteur à ressources et leurs raccords. Il ne doit pas être
exécuté une seconde fois pour justifier la reprise runtime.

Les fonctions séparées de transition et d’événement servent de spécifications.
Les accords entre ces fonctions et l’entrée runtime sont des théorèmes ; ils
ne commandent pas plusieurs passages runtime.

Pour `obtain`, vérifier d’abord que la variable est autorisée. Si le handle
désigne déjà une entrée, la lire sans avancer. Sinon, calculer le nombre fini
d’entrées manquantes depuis l’adresse demandée et le registre actuel. La loi
« une étape produit une nouvelle entrée » doit être prouvée sur ce moteur,
puis utilisée pour borner une récursion structurelle qui réemploie le même
worker d’avancement. Après ces productions, construire le témoin positif du
handle et l’autorisation de la lecture.

Cette borne est une lecture du registre constitué, non la constitution d’une
occurrence future par son numéro. La réponse ne peut être construite avant
la production réelle de l’entrée manquante. Une demande hors périmètre ne doit
pas déclencher cette recherche pour être refusée.

Fixer la borne exactement : avec `r` entrées actuelles et l’adresse `h`, le
nombre d’étapes supplémentaires est `0` si `h < r`, sinon `h + 1 - r`.
Prouver que le registre atteint alors `h + 1` entrées dans ce second cas.
Cette terminaison utilise la réussite de découverte établie sur les états
frais du moteur et la conservation de cette fraîcheur par `Production.next`.
Elle ne vaut pas pour un moteur arbitraire susceptible d’échouer. Le langage
initial n’offre aucune opération modifiant directement cet invariant.

Les registres et les mémoires intermédiaires portent leurs invariants
constructifs. Chaque étape doit construire simultanément : son output réel,
sa nouvelle entrée, la conservation des lectures anciennes, l’état transmis
et son invariant de réussite. La preuve de progression ne doit pas être
reconstruite depuis une liste artificielle ayant seulement la bonne longueur.

Pour `inspect` et `propose`, le producteur lit le registre disponible et
l’exigence effectivement portée par la mémoire. Il construit une réponse
autorisée seulement à partir de l’autorisation produite. Un refus ne modifie
ni l’exigence ni les résultats déjà produits.

L’exécuteur sur une liste finie de requêtes est ensuite une récursion
structurelle qui transmet le résultat de chaque tête à sa queue. Il ne doit
pas calculer la tête depuis l’histoire finale.

La production « pendant l’exécution » est ici cet ordre constitutif : le worker
de tête reçoit la mémoire courante et la seule requête courante, et sa sortie
alimente ensuite la queue. Le certificat et l’entrée runtime portent sur ce
worker et cette récursion. Ce n’est pas une preuve d’ordonnancement physique
des instructions par le processeur ou de temps réel.

## 7. Contrat d’interaction et refus

Le contrat doit annoncer avant les preuves les observations suivantes :

- les événements des étapes réellement exécutées ;
- les handles disponibles et leurs droits de consultation ;
- les valeurs restituées pour les requêtes autorisées ;
- les motifs de refus des demandes non autorisées.

Les motifs sont au minimum : handle absent, variable hors périmètre et valeur
candidate différente de la lecture produite. Chaque motif possède son accord
avec la vérification exécutée. Un refus de réponse candidate n’est pas une
preuve que la branche de recherche correspondante est impossible.

L’exigence reste celle reçue à l’initialisation. Ce langage ne contient pas une
révision silencieuse de son périmètre. Ajouter ultérieurement une opération de
révision exigera un nouveau contrat et ses lois, pas la réutilisation automatique
du théorème de persistance pour une exigence différente.

La correction doit être prouvée pour toute requête reçue, refus compris.
La satisfaction des opérations autorisées doit être prouvée pour toute suite
finie admise. Toute inspection autorisée obtient une réponse en un nombre fini
d’étapes structurelles ; une implémentation qui refuse systématiquement n’est
pas une réalisation de ce contrat.

Sur la source riche, la lecture d’une réponse doit désigner la continuation
de la production historique identifiée. Sur la mémoire réduite, elle doit lire
le lecteur effectivement stocké. Leur accord ne doit pas être obtenu en
définissant la première comme la seconde après projection.

Les handles anciens restent consultables après `advance`. Les nouveaux handles
deviennent consultables après la formation de leurs entrées. Démontrer leurs
bornes et la conservation des lectures anciennes, pas seulement une égalité
de longueurs de listes.

Fixer également la priorité des réponses négatives : pour `inspect`,
`obtain` et `propose`, une variable hors périmètre est refusée d’abord ; dans
le périmètre, `inspect` et `propose` refusent un handle absent ; `propose` refuse
ensuite une valeur incorrecte. `obtain` produit le handle manquant au lieu
d’appliquer le refus « absent ». Aucun de ces refus ne modifie la mémoire.

Pour utiliser `Continuation.Exact`, choisir comme observation une table finie
des lectures autorisées du registre courant, calculée sur le périmètre reçu.
Sur la source riche, ses cases sont évaluées depuis les continuations
historiques ; sur la mémoire réduite, depuis les lecteurs réalisés. Les lois
de réponse pour chaque requête couvrent aussi les lectures particulières et
les refus. La table est une spécification observable : ne pas la matérialiser
à chaque requête si le runtime n’a besoin que d’une case. Les événements sont
des données communes de réponse ou d’étape, sans profil source ni archive
historique cachée dans leurs témoins.

Prouver les égalités sur ces données finies et les lectures ponctuelles.
L’égalité de deux fonctions `SAT.Assignment` ne doit pas être obtenue par
extensionalité fonctionnelle interdite ; réutiliser les égalités de cibles
effectivement produites lorsqu’une égalité de mémoire est requise.

« Reprise » signifie ici continuation à partir de la valeur mémoire construite.
Une sauvegarde sur disque, sa sérialisation ou une reprise entre processus
ajouterait un autre transport et ses lois ; elle n’est pas déjà démontrée par
ce contrat Lean. De même, les suites finies garantissent chaque interaction
finie, pas une disponibilité infinie ou une borne de temps réel.

## 8. Théorèmes de suivi à fermer

Les noms suivants sont proposés. Chacun devra être énoncé sur l’instance
concrète et son exécuteur canonique.

| Déclaration à construire | Contenu exigé |
| --- | --- |
| `initialize_from_master_exact` | Exigence, normalisation, curseur et première mémoire proviennent de la même session initiale ; pas de deuxième run indépendant. |
| `head_uses_current_resources` | La tête ne lit pas le futur ; ses ressources et, pour les restitutions, l’exigence consommée par l’autorisation sont celles de l’état courant. La production entière, son résultat et sa décision sont épinglés au producteur réel. |
| `executed_step_register_exact` | Chaque nouvelle continuation consultable vient de l’output de cette étape exécutée, dans son contexte et avec sa garantie propre. |
| `register_grows_by_one` | Une étape réelle ajoute exactement une entrée et conserve l’accord de toutes les entrées antérieures ; cette loi justifie la borne d’obtention. |
| `requirement_transport_exact` | Les références riches et la réalisation réduite portent la même exigence avec les accords de lecture requis. |
| `candidate_authorization_exact` | Une réponse candidate est autorisée exactement selon le handle, le périmètre et la valeur effectivement produite. |
| `authorized_response_correct` | Toute réponse publiée satisfait la spécification riche et sa garantie de critère, pas seulement un prédicat sur le résultat publié. |
| `admitted_inspection_returns` | Toute inspection admise produit la lecture promise ; pas de correction vacuement obtenue par refus de toutes les demandes. |
| `obtain_produces_and_returns` | Toute demande d’obtention dans le périmètre atteint une production réelle et restitue sa lecture ; les étapes supplémentaires sont celles du worker exécuté. |
| `old_handle_read_preserved` | Ajouter des productions conserve les droits et lectures des handles anciens. |
| `next_event_read_admission_exact` | Lois distinctes de transition, d’événement, de lecture et d’admission entre source riche et mémoire réduite. |
| `all_future_requests_exact` | Composition de ces accords pour toute suite finie de requêtes, sur les états réellement atteints. |
| `all_executed_determinations_followed` | Suivi de l’exigence constituée et des garanties consommées le long de toute la chaîne exécutée. |
| `agent_memory_factors_through_output` | À exigence et curseur communs, la mémoire initiale dépend de la cible produite, non du code de sélection ou du profil source. |
| `initial_profile_not_recoverable` | Aucune fonction de la mémoire complète de l’agent ne reconstruit uniformément son profil initial. |

Le théorème de suivi devra réunir ces trois quantifications :

```text
pour toute initialisation effectivement admise de cette famille d’agents,
pour toute liste finie de demandes reçues par l’exécuteur,
à toute étape réellement produite de cette exécution :
    la détermination reçue est suivie par ses accords,
    les réponses publiées sont autorisées et correctes,
    les refus correspondent à leurs motifs,
    la continuation riche et la reprise restent raccordées.
```

La version sur les demandes admises ajoute l’effectuation des réponses promises
et la conservation de leurs droits. Elle ne remplace pas la version qui couvre
aussi les demandes refusées.

Ne pas supposer une histoire quelconque déjà munie de ces propriétés. Démontrer
les propriétés de l’histoire construite par l’exécuteur depuis l’initialisation.

Le certificat concret doit consommer chaque loi nécessaire : exactitude de la
production entière et indépendance de l’horizon, origine des entrées, lecture
du périmètre, acceptation dans les contextes exacts, raccord riche/réduit,
effectuation des demandes admises et oubli dans la mémoire complète. Des lois
isolées absentes de ce certificat ne permettent pas d’affirmer que le paquet
final ferme leurs obligations.

## 9. Oubli réel dans la mémoire complète

Réutiliser les deux profils distincts de
`ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster.Instance.distinctPair`
et leur codétermination, à session maître et exigence fixées. Construire leurs
deux initialisations d’agent sans identifier leurs sources.

Prouver que la totalité de leurs mémoires de reprise est égale : moteur vivant,
exigence, composantes initiales, registre, files et tout autre champ retenu.
La preuve du checkpoint existant ne suffit pas si une nouvelle couche garde
ailleurs la distinction oubliée.

Cette égalité doit être construite depuis la convergence des cibles et la
factorisation de mémoire de la section 5.3. Les noms de session, adresses et
témoins retenus sont dérivés des ressources communes, pas des codes sources
distincts. Ne pas retirer des champs du domaine du théorème après avoir constaté
qu’ils gardent cette distinction.

Fermer ensuite :

- la non-reconstruction uniforme du profil depuis la mémoire entière ;
- l’égalité des réponses et événements pour la même suite future de requêtes ;
- la conservation et la réflexion des admissions pour cette suite ;
- l’exactitude des nouvelles productions après reprise.

Ces lois comparent la même suite future de demandes dans les deux reprises.
Une entrée ultérieure qui fournirait à nouveau le profil oublié serait une
nouvelle ressource externe, non sa reconstruction depuis cette mémoire.

Un journal scientifique externe peut conserver les sources. Il doit être
séparé du runtime et déclaré hors de la revendication d’oubli. Si l’agent lit
ce journal pour agir, il redevient une ressource de son contrat et de sa preuve.

L’oubli ne concerne pas les données de provenance que la prochaine découverte
lit encore. Il ne concerne pas non plus toutes les histoires chronologiques
canoniques reconstructibles depuis la profondeur.

## 10. Organisation des fichiers

Ajouter une couche terminale, sans inversion des imports :

```text
RelationalPerimeter/
  Agents/
    Constitutive/
      Requirement.lean
      ProducedEvidence.lean
      State.lean
      Execution.lean
      Agreement.lean
      Persistence.lean
      PublicInstance.lean
Tests/
  ConstitutiveAgentRequirements.lean
  ConstitutiveAgentExecution.lean
  ConstitutiveAgentPersistence.lean
```

Responsabilités :

1. `Requirement` : données reçues, formation des demandes, spécification et
   vérifications finies ; aucune décision d’exécution fournie d’avance.
2. `ProducedEvidence` : cibles réellement produites, handles constitués,
   registre et lecteurs ; dépend des rôles et sorties existants.
3. `State` : source riche, mémoire et projection ; ne produit pas un régime
   indépendant ni une seconde normalisation.
4. `Execution` : producteurs de requêtes, moteur réel et récursion unique.
5. `Agreement` : lois locales et contrat exact de continuation.
6. `Persistence` : composition globale et oubli du profil dans la mémoire
   complète ; ne remplace pas l’exécuteur.
7. `PublicInstance` : initialisations positives, usages concrets et certificat
   fermé sur cet exécuteur.

Les modules antérieurs n’importent aucun module d’agent. Le fichier public
`RelationalPerimeter.lean` pourra importer `PublicInstance` après réalisation.
Le lakefile devra inclure `RelationalPerimeter.Agents.+` et l’inventaire de
stratification devra couvrir tous les nouveaux modules avec des contraintes
effectives, pas une strate terminale sans règle.

Les deux checkers de stratification n’acceptent actuellement que `A0` à `A10`.
Leur extension est donc un livrable explicite : attribuer `A10` à `Requirement`,
puis `A11` à `ProducedEvidence`, jusqu’à `A16` pour `PublicInstance`, et déplacer
seulement le root d’agrégation `RelationalPerimeter` vers `A17`. Chaque rang
d’agent n’autorise que les strates antérieures, jamais le root ni un module
d’agent ultérieur. Conserver les contraintes de tous les anciens modules.
Les tables Bash et PowerShell doivent exprimer le même graphe autorisé, y
compris sur les chemins transitifs. Les dépendances de l’exécuteur ne doivent
pas servir à lire les frontières extensives pour choisir les actions.

## 11. Lots de réalisation et critères de fermeture

### Lot A — Exigence, demandes et premières cibles

Construire `AgentRequirement`, la résolution des handles et les deux motifs
structurels de refus. Réaliser un périmètre concret non vide. Raccorder la
cible initiale à la normalisation maître, préparer ses entrées par rôle avec
leurs garanties contextuelles et construire une inspection admise.

Construire aussi l’interprétation des codes valides sur les rôles formés, puis
son accord avec l’encodage des profils. Les codes des deux profils du témoin
de distinction doivent être réellement admis. Le périmètre singleton `[0]`
fournit un premier cas concret de restitution ; un autre périmètre doit réaliser
la différence d’admission annoncée en section 3.3.

Fermeture : une valeur réellement lue peut être autorisée ; la valeur opposée
est refusée pour son désaccord ; une variable hors périmètre est refusée sans
modifier la vérité de la cible. Ces témoins sont des constructions Lean, pas
des valeurs seulement annoncées dans la documentation.

### Lot B — Session et productions nouvelles

Construire la mémoire initiale depuis un seul résultat maître. Implémenter
`advance` depuis le moteur vivant réel et alimenter le registre depuis chaque
production, en partageant cette production avec l’événement et le successeur.

Fermeture : une nouvelle entrée est effectivement créée ; ses lectures sont
celles de son output ; les anciennes entrées restent correctement consultables ;
la mémoire atteinte correspond au curseur riche atteint sans réexécution du passé.

### Lot C — Autorisation des réponses et contrat exact

Construire `inspect` et `propose`, leur décision exécutable, leurs réponses et
leurs refus. Écrire la spécification riche indépendante de la projection,
puis démontrer les lois locales du contrat.

Construire ensuite `obtain` : consommation de l’exigence, choix de poursuivre
ou de lire depuis le registre courant, avancement réel si nécessaire et
réponse autorisée. Fermer sa terminaison structurelle et son raccord avec le
worker ; fournir un exemple où il produit une nouvelle entrée et un autre où
il réutilise une entrée sans réexécuter la recherche.

Fermeture : les droits dépendent du périmètre reçu et des occurrences réelles ;
les accords ne sont pas obtenus en remplaçant toutes les observations par une
lecture vide ou par l’implémentation réduite elle-même.

### Lot D — Suivi composé et oubli

Fermer la récursion sur toutes les requêtes finies. Composer les transports de
l’exigence et les garanties des actions. Réaliser les deux sources distinctes,
leur même mémoire complète et la preuve de non-reconstruction. Construire cette
égalité via la factorisation par la cible produite et fermer son usage après
les extensions réelles du registre, sans conserver les choix sources.

Fermeture : les garanties concernent l’exécution construite, y compris après
les reprises et les nouvelles productions ; elles ne sont pas des hypothèses
laissées ouvertes dans une interface abstraite.

### Lot E — Instance publique et restitution scientifique

Construire `AgentSession.ofMaster master requirement profile` depuis le
résultat maître déjà formé, l’exigence réalisée et le profil constitué. Son
certificat porte sur son exécuteur et consomme les résultats de chaque lot.
Ajouter des scénarios finis d’interaction qui exercent progression, lecture,
bonne proposition, mauvaise proposition, refus et reprise après oubli.

L’entrée publique `publicAgent input scope selectionCode` appelle une procédure
`initialize` qui reçoit ces données brutes, vérifie le périmètre, construit un
seul résultat maître, réalise le code sur ses rôles et transmet ce résultat à
`AgentSession.ofMaster`. Elle retourne une initialisation autorisée ou un refus
motivé. Ne pas cacher un second appel au moteur dans le décodage ou le certificat.

Fermeture : l’API publique ne permet pas de remplacer sa mémoire, ses cibles ou
ses réponses par des champs indépendants ; toutes les déclarations nouvelles
sont accessibles depuis le root public et axiomatiquement auditées.

Une mémoire abstraite peut avoir son interface propre, mais le certificat
public est fermé sur `initialize`, `AgentSession.ofMaster` et cet exécuteur.
Il ne reçoit pas une mémoire, un registre ou un répondeur choisis séparément
en supposant leur correction. Les témoins d’autorisation sont les produits
des vérifications définies ici, pas des permis libres.

## 12. Ce qui ne doit pas être présenté comme une solution

- Un champ `goal` recopié à l’identique mais jamais lu par une autorisation.
- Un prédicat de satisfaction défini comme « la réponse est celle de l’agent ».
- Une preuve conditionnelle supposant déjà la préservation de la nouvelle
  exigence, sans instance qui la ferme.
- Une continuation post-hoc reconstruite après réception des demandes futures.
- Une réponse stockée librement avec une trace ou un label ajouté ensuite.
- Un registre contenant des cibles arbitraires que leur longueur suffit à valider.
- Une admission riche définie par l’admission réduite pour éviter de prouver le
  raccord indépendant des droits sur les productions.
- Une preuve d’oubli portant seulement sur un sous-champ, alors que la mémoire
  entière garde encore le profil dans un code, un hash ou une file.
- Une nouvelle énumération de tous les profils présentée comme condition de
  la preuve d’action ou comme définition du coût de l’agent.
- Une preuve de largeur constante présentée comme coût runtime polynomial.
- Un solveur externe ou un modèle appelé en dehors de la chaîne et décrit
  comme s’il était certifié par les théorèmes du noyau.

Une impossibilité rencontrée doit être exposée avec le type ou le raccord
concerné. Elle ne doit pas conduire à modifier silencieusement la cible, les
opérations promises ou le contenu de l’exigence.

## 13. Vérification, sans remplacer la démonstration

Pour chaque nouveau fichier Lean : définitions exécutables dans `Type`, témoins
positifs, aucune hypothèse scientifique laissée ouverte dans l’instance, et
exactement un bloc final d’audit des principales déclarations avec leurs noms
complets. Aucun audit ne doit signaler de dépendance interdite. Respecter toutes
les interdictions de constructivité du dépôt, y compris dans les helpers.

Les vérifications doivent distinguer :

- les constructions et les théorèmes qui ferment les lots ;
- les exemples qui prouvent que leurs domaines sont effectivement habités ;
- les évaluations finies qui contrôlent le chemin runtime ;
- les contrôles qui détectent un raccord manquant.

Compiler et évaluer les fonctions de données utilisées par les scénarios,
notamment le décodage du profil, la préparation du registre, l’avancement,
`obtain` et les producteurs d’autorisation. Une preuve élaborée sans erreur
ne suffit pas si la fonction qui doit fournir son témoin n’est pas acceptée
par le générateur de code. Les petites évaluations sont des contrôles de
calculabilité, pas une campagne de mesure de complexité.

Vérifier en particulier une session ayant le même passé et des suites futures
différentes ; une réponse erronée sur un handle valide ; une adresse absente ;
deux initialisations de périmètres différents ; une reprise sans archive ;
et la mémoire entière des deux profils sources. Un échec de compilation ne
compte que pour la cause de type recherchée, pas pour n’importe quelle erreur.

Avant livraison du code, exécuter les builds propres, les deux verifiers
disponibles et le contrôle du diff. Vérifier les audits axiomatiques, la
couverture de stratification, les dépendances des nouveaux imports, les liens,
les versions françaises et anglaises et le manifeste final. Identifier
explicitement toute vérification qui n’a pas été exécutée.

Les quatre fondations et les résultats antérieurs restent protégés. Une
nouvelle instance ne doit pas affaiblir leurs énoncés pour faciliter un certificat.

## 14. Audit indépendant et intégration

L’audit de l’agent portera sur l’exigence de la section 3 et le théorème composé
de la section 8, pas sur le seul regroupement déjà démontré. Il devra retrouver
les formations, producteurs, accords et usages dans l’ordre annoncé, puis
vérifier le contrat et l’oubli sur la mémoire complète.

Préparer cet audit seulement après fermeture des lots : commit scientifique
exact, branche distante disponible, prompt complet, commandes de reproduction
et tableau reliant chaque clause aux déclarations de production. Ne pas
réutiliser le verdict de la cible exponentielle comme validation de l’agent.

Commit, push et fusion nécessitent une demande explicite. L’intégration ne
sera achevée qu’après fusion autorisée et vérification de `main`. Retirer ce
plan et les autres documents de chantier de l’arbre final ; conserver les
spécifications scientifiques et résultats finaux déclarés comme livrables.

## 15. Extension ultérieure à un composant appris

Ce lot ne nécessite pas un appel à un modèle de langage. Un composant appris
pourra ensuite proposer des actions ou réponses dans la même session, sans
devenir une autorité sur leur admission.

Cette extension nécessitera un raccord supplémentaire : décodage des
propositions, contrôle des ressources qu’elles désignent, construction des
autorisations et accord entre l’implémentation externe et l’entrée Lean.
Les propositions non autorisées devront rester sans effet sur les garanties.

La certification du noyau ne démontrera ni que le modèle propose toujours une
action utile, ni qu’il comprend une instruction naturelle, ni qu’il est aligné
sur toute exigence humaine. Ces conclusions demanderaient leurs propres
instances et preuves, sans abandonner la méthode ni substituer une cible moindre.

## 16. Définition d’achèvement

La première instance est achevée lorsque l’exigence concrète gouverne ses
autorisations, que sa production opérationnelle est celle du moteur réel,
que ses réponses et refus satisfont la spécification indépendante, et que
le suivi de ces garanties se compose sur toutes ses interactions finies.

La mémoire complète doit permettre cette continuation tout en ne permettant
pas de reconstruire uniformément le profil initial oublié. Cette propriété
doit être réalisée sur des sources distinctes effectivement construites.

L’ensemble doit être livré comme une instance construite et exécutable, non
comme une liste d’interfaces abstraites supposées satisfaites. Le résultat
scientifique sera ce paquet fermé ; la transposition à d’autres exigences ou
à d’autres agents restera une nouvelle tâche de preuve.

## 17. Réalisation locale et vérifications du 4 octobre 2026

Les cinq lots sont implémentés dans les sept modules annoncés, sans changement
des quatre fondations ou des énoncés scientifiques antérieurs. L’entrée réelle
se nomme `initializeAgent` (`initialize` est un mot réservé de Lean) ; le
namespace est `ConstitutiveSearch.Agent`. Les noms proposés dans le plan sont
reliés ci-dessous aux constructions effectives, pas remplacés par des hypothèses.

| Lot | Constructions qui le ferment |
| --- | --- |
| A | `receive`, `Requirement.scope_exact`, `TargetOrigin`, `initialTargets` avec son accord de sortie exécutée, `decode_encode`, `wrong_selection_length`, `initialized_codes_admitted`, `firstAuthorization`, `candidate_authorization_exact`. |
| B | `start`, `initialize_from_master_exact`, `step`, `runSteps`, `executed_step_register_exact`, `register_grows_by_one`, `resolveHandle_transport`, `History.realization`, `History.handle_transport`, `RegisterRealization.advance_position`, `RegisterRealization.injective`, `History.references`. |
| C | `performCertified`, `interactionProducer`, `executeProducedInput`, `head_production_entire_exact`, `ResponseEvidence`, `admitted_inspection_returns`, `obtain_produces_and_returns`, `obtain_register_exact`, `obtain_work_exact`, `refusal_preserves_memory`, `cached_obtain_runs_no_stage`, `sourcePerform_exact`, `bridge`, les deux lois de retour des admissions. |
| D | `FollowedStages`, `followStages`, `all_executed_determinations_followed`, les trois lois `all_future_*_exact`, `all_future_old_reads`, `requirement_transport_exact`, `admissions_forward`, `admissions_reflected`, `agent_memory_factors_through_output`, `initial_profile_not_recoverable`, `forgotten_sources_same_future`. |
| E | `prepare`, `Prepared.memory`, `Prepared.certificate`, `publicAgent`, `Session.ofMaster`, `Session.produce`, `Session.executeAll`, `certify`, les trois fichiers `Tests/ConstitutiveAgent*.lean`. |

`Certificate` consomme l’exactitude de la production entière, les autorisations
et leur effectuation, les garanties contextuelles des cibles, les transports
des handles, les deux lois de retour des permissions et les accords de toutes
les continuations finies. Son constructeur est privé. `Session` ne conserve
que `Memory`, dont les seuls champs sont l’exigence, le moteur vivant et le
registre de cibles. Le contrôle de schéma vérifie aussi le type des entrées de
ce registre ; le théorème d’oubli porte sur la mémoire entière.

La réinspection a fermé les raccords qui manquaient à la première réalisation :

- La provenance d’une cible est un témoin positif dans `Type`, dépendant de
  sa continuation. `initialTargets` exige son accord avec la sortie des rôles
  exécutés ; une acceptation seule ne suffit plus. Ce témoin ne stocke pas le
  choix du profil source.
- `History.realization` produit un support riche des cibles. La normalisation
  lit le paquet maître/profil déjà constitué ; les composantes lisent le bundle
  produit ; chaque reprise produit une tête partagée, sa cible et son curseur
  suivant. Ce support de restitution est distinct du support interne du moteur,
  dont les extensions restent suivies par `History.references`.
- Les références du registre passent vers ce support par un raccord de lectures
  et un carré de transport. Les handles de création restent stables tandis que
  les positions historiques se décalent par l’extension réelle. L’injectivité
  des références est préservée ; elle ne se confond pas avec l’égalité des valeurs.
- L’interprète et les autorisations riches lisent les valeurs de ce support.
  L’accord est consommé dans `sourcePerform_exact`, `bridge` et les deux lois
  de retour, pas seulement stocké à côté du répondeur réduit.
- Le certificat consomme le suivi de chaque étape interne, la taille finale
  exacte pour un handle absent, le nombre d’événements du worker et la
  conservation de toute la mémoire lors d’un refus.

Les preuves d’égalité des mémoires complètes et de non-reconstruction du profil
initial sont conservées avec ces témoins renforcés. Les éléments riches restent
hors de la mémoire de reprise et du chemin compilé de l’exécuteur.

Vérifications effectivement exécutées dans le worktree dédié, sous Lean 4.33.1 :

| Commande ou contrôle | Résultat |
| --- | --- |
| `lake clean` | Succès. |
| `lake build +RelationalPerimeter` | Succès, 160 jobs. |
| `lake build` | Succès, 183 jobs, aucun avertissement Lean. |
| `scripts/verify.ps1` sous PowerShell 7 sur Windows | Succès, 181 fichiers Lean et 23 fixtures d’échec attendu. |
| `scripts/verify.sh` sous Git Bash sur Windows | Succès, les mêmes 181 fichiers et 23 fixtures. |
| Balayage de tous les modules et tests | 17 945 constantes, 180 modules ; zéro déclaration écrite à la main dépendant d’un axiome. Les 360 exceptions sont classifiées comme générées par le compilateur. |
| Schéma de reprise et dépendances du code compilé | Succès ; une production réelle par étape et une tête par requête, pas d’archive riche ou d’énumération globale des profils dans la reprise. |
| Stratification | 159 modules de production, tous couverts et contrôlés ; aucun orphelin. |
| `lake update` | Succès, manifeste inchangé. |
| `git diff --check` et liens locaux des nouveaux documents | Succès. |

Le moteur antérieur conserve sa lecture locale de deux occurrences après
l’action. Le contrôle n’en fait pas une énumération globale et ne prétend pas
qu’aucune lecture locale n’existe : la découverte possède son contrôle de
dépendances séparé, excluant ces lectures de la sélection de son action.

Le scénario exécuté obtient le handle 2 par deux étapes réelles, puis le relit
sans nouvelle étape ; il distingue handle absent, variable hors périmètre et
valeur candidate incorrecte. Les bons et mauvais candidats sont construits
depuis la lecture réellement rendue. Ce sont des contrôles de calculabilité,
non une campagne confirmatoire de complexité.

Les documents scientifiques de restitution sont
[la version française](../agent-constitutif-et-persistance.fr.md) et
[la version anglaise](../constitutive-agent-and-persistence.en.md).
Cette clôture locale précède la publication du lot et sa demande d’audit.
Le protocole d’audit indépendant fixe ensuite le commit scientifique publié ;
la validation indépendante et l’intégration autorisée restent distinctes
de cette réalisation vérifiée localement. Aucune fusion n’est autorisée ici.
