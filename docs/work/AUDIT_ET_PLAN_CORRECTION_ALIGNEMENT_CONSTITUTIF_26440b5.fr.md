# Audit et ordre de correction — alignement constitutif neuronal — 26440b5

## 1. Objet, révision et verdict

Date : 23 octobre 2026.

- Dépôt : `JohnDoe-collab-stack/relational-perimeter`.
- Branche : `codex/constitutive-neural-alignment-implementation`.
- Commit audité : `26440b55b50544e4b583bbb0e16eb9b428450282`.
- Arbre Git : `6e99a8ff112b5824670e0eaebc4d67ca0ee71e62`.
- La tête distante avait été vérifiée identique lors de l'audit.
- Aucun changement suivi au début de la rédaction. Le rapport précédent,
  non suivi, reste séparé de l'évidence du commit et n'a pas été modifié.

**Verdict : cible non atteinte.** Le build et les audits d'axiomes réussissent,
mais la chaîne constitutive exécutée reste incomplètement raccordée. La
comparaison confirmatoire, la reproductibilité du gel et la livraison
scientifique restent également à fermer.

Ce verdict ne signifie ni une réfutation de Lean, ni la perte des théorèmes
antérieurs. Les défauts identifiés portent sur les dépendances effectivement
construites, leur consommation et la portée des évidences. Les progrès du
commit sont conservés explicitement ci-dessous.

Ce document consigne l'audit interne et prépare les corrections. Il ne corrige
aucune source, ne lance aucune expérience, ne modifie aucun registre et ne
constitue pas un audit indépendant. Les contrôles de la section 8 sont ceux
exécutés pendant l'audit de cette révision, pas une nouvelle campagne lancée
pour rédiger ce Markdown. Les numéros de ligne cités désignent cette révision.

### Références normatives conservées

- [Cible opératoire et RC1–RC6](CIBLE_ALIGNEMENT_CONSTITUTIF_INCREMENTAL.fr.md).
- [Critères C1–C18](CONSTITUTIVE_NEURAL_ALIGNMENT_TARGETS.fr.md).
- [Garanties G1–G10, références R1–R8, épreuves P1–P8 et critères S1–S8](RAPPORT_VERIFICATION_ALIGNEMENT_CONSTITUTIF_fafd739.fr.md).
- [Rapport précédent, conservé comme historique](AUDIT_ET_PLAN_CORRECTION_ALIGNEMENT_CONSTITUTIF_0c12baa.fr.md).
- [Procédure scientifique](../methode-de-travail-scientifique.fr.md) et
  [registre](../scientific-claims.json).

Les constats historiques de ces documents ne sont pas automatiquement
reconduits sur `26440b5`. Leurs exigences restent obligatoires. Le présent
rapport actualise les défauts et l'ordre de correction, sans remplacer la cible.

## 2. Cible inchangée et règles de lecture

Il faut fermer, sur la même lignée exécutée, la chaîne suivante :

```text
primitives, exigences, contextes et schémas reçus
→ occurrences et état constitués
→ artefact décodé et transformation neuronale exécutée
→ proposition, action, effet et successeur réellement produits
→ obligations instanciées sur ces productions
→ décision du méta-contrat, transports et vérifications nécessaires
→ assemblage du certificat et installation contrôlée
→ continuation, oubli exécuté et transitions après oubli
→ contrat de futurs fixé et conséquences pour toute réalisation exacte
```

Ce schéma décrit les dépendances, pas une autorisation d'effectuer une action
avant son contrôle. Le méta-contrat et le schéma d'observation sont fixés en
amont. Le checker peut calculer une production candidate dans la sémantique
pure, mais un refus ne doit produire aucune action effective ni installation.
Le dernier raccord applique le contrat déjà fixé aux sources produites, sans
le redéfinir après observation du candidat.

Pour chaque flèche, identifier séparément la formation des types, les données
exécutées, les prémisses consommées par la preuve et les distinctions
conservées ou oubliées. Un champ stocké, une égalité correcte et la présence
d'un appel dans le code généré ne suffisent pas, séparément, à établir le
partage constitutif demandé.

Les trois quantifications ne doivent pas être réduites aux exemples :

1. toute trace finie acceptée par l'API dans son domaine déclaré ;
2. toute liste finie de requêtes futures couverte par le contrat concerné ;
3. tout type mémoire et toute réalisation exacte du contrat fixé, dans les
   univers et paramètres déclarés par l'API.

L'instance apprise à plusieurs étapes ferme la non-vacuité et le raccord
concret. Elle ne remplace pas ces théorèmes génériques. Le domaine courant et
la base d'interventions doivent être décidables et finis selon le plan, sans
imposer que l'ensemble de tous les artefacts sérialisables soit fini ni que
tout réseau arbitraire soit accepté.

Ne pas ajouter d'objectif de valeurs humaines, de diagonalisation obligatoire,
de quotient minimal universel ou d'effacement de toutes les archives. Gödel,
Tarski et HA restent des résultats à préserver, non des prémisses nouvelles
pour l'agent neuronal. La non-récupérabilité concerne la mémoire réduite
spécifiée, pas une archive externe explicitement conservée pour l'audit.

Une égalité peut transporter des indices et des preuves. Elle ne doit pas
servir à substituer silencieusement une production canonique indépendante à
la ressource exécutée revendiquée. Inversement, il n'est pas demandé de rendre
les preuves effacées par Lean artificiellement calculatoires : les données
doivent être consommées par leurs consommateurs exécutables et les certificats
par les preuves des obligations correspondantes.

## 3. Progrès acquis à conserver

1. La reconfiguration brute est désormais appelée depuis l'état reçu. Le
   constat ancien « aucun appel au producteur » n'est plus applicable.
2. Le checker successif appelle effectivement
   `buildIncrementalCheckedUpdate analysis.target`. L'assemblage incrémental
   n'est plus seulement un moteur auxiliaire déconnecté du chemin public.
3. La continuation ordinaire après oubli exécute le lecteur de mémoire réduite
   et distingue une continuation admise d'un refus sans résultat exécuté.
4. Un checker dépendant et une installation dans `CertifiedRuntime` existent
   pour la branche de changement de contrat. Le défaut restant est leur raccord
   à la sortie de l'oubli et aux justifications, pas l'absence de toute API.
5. La famille de mesure transmet une mémoire source et produit des successeurs
   non triviaux. L'effet partage le résultat de son action effective.
6. Le nouveau comparateur indépendant calcule ses observations sans consulter
   le verdict final du checker audité. L'émetteur distingue les observations
   exécutées des évidences de preuve.
7. L'erratum v10 conserve et reconnaît l'erreur historique. Les protocoles v12
   et v13 sont explicitement des brouillons, sans résultats confirmatoires.
8. Les contrôles Lean et les planchers de régression cités en section 8 passent.
   Aucune modification de Gödel, Tarski ou HA n'a été relevée dans la comparaison
   avec `0c12baa`.

Ces acquis ne doivent pas disparaître pendant les corrections.

## 4. Défauts et corrections nécessaires

### F1 — La cible produite est encore remplacée par une cible canonique égale

**Localisation.** [Reconfiguration.lean](../../RelationalPerimeter/Agents/Neural/Reconfiguration.lean),
`Reconfiguration.reindexTarget`, lignes 149–160.
Appels dans [LearnedRuntimeAdapter.lean](../../RelationalPerimeter/Agents/Neural/LearnedRuntimeAdapter.lean),
notamment lignes 1517 et 1634.

Le constructeur reçoit une reconfiguration produite puis reconstruit :

```lean
.mk configuration.authorization targetSystem
  (targetExact.symm.trans configuration.targetExact)
```

Les wrappers appris lui fournissent le système canonique décodé. La preuve
d'égalité est correcte. Toutefois, le champ cible effectivement retourné est
le nouvel argument, pas le champ cible issu du producteur. Le code C généré
confirme ce remplacement. Appeler le producteur ne suffit donc pas à établir
que sa sortie est le système consommé ensuite.

Ce n'est ni une preuve de mauvaise valeur, ni une admission invalide démontrée,
ni une interdiction générale de réindexer. C'est un écart à RC2 et au partage
exécuté demandé par la cible.

**Correction.** Garder la reconfiguration et sa cible produites comme données
maîtres. Raccorder les noms canoniques et les témoins dépendants par transport
vers cette production. Suivre ensuite cette cible jusqu'à la proposition,
l'action, l'effet et l'installation, sans seconde construction indépendante.
Préserver le partage déjà présent du résultat d'action avec le successeur.

**Clôture.** Les corps de définition et leurs consommateurs établissent la
chaîne. Les équations de production portent sur cette même chaîne. Le contrôle
du code généré détecte une substitution de champ, pas seulement l'absence d'un
appel. Une variation admissible de l'entrée ne doit pas être neutralisée par
une reconstruction canonique sans justification du domaine.

### F2 — Le chemin successif utilise l'assemblage, mais son analyse reste canonique

**Localisation.** [LearnedRuntimeAdapter.lean](../../RelationalPerimeter/Agents/Neural/LearnedRuntimeAdapter.lean),
`learnedSuccessiveTargetAnalysisFromReceivedArtifact`, lignes 4506–4534,
et `checkDecodedLearnedExtendedSerializedUpdate`, vers la ligne 4700.
[AutonomousCheckerClosure.lean](../../RelationalPerimeter/Agents/Neural/AutonomousCheckerClosure.lean),
`learnedSuccessiveIncrementalAndFullAcceptance_equivalent`, vers la ligne 203.

Après élimination de `targetExact`, l'analyse reconstruit notamment
`learnedDecodedExtendedArtifact`, `learnedExtendedState`, le nommage et
l'assemblage canoniques. Son témoin d'exécution vient de
`learnedExtendedReferenceTransitionProduction.execution`. Le code généré
confirme ces références globales. La décision reçue intervient dans les
égalités de preuve, mais cela ne constitue pas à soi seul la chaîne de données
annoncée depuis le décodage reçu.

Le domaine successif est restreint et ces égalités sont valides. Le problème
n'est donc pas que le checker devrait accepter des réseaux arbitraires ou
qu'il ne contrôle rien. Le problème est la substitution de la chaîne concrète
par ses représentants canoniques alors que RC2 et RC5 exigent ses consommateurs.

En outre, le théorème d'accord successif cité compare les deux acceptations
sur `learnedExtendedSerializedUpdate`. Il ne ferme pas à lui seul l'accord des
deux chemins sur tout leur domaine successif déclaré. Les résultats génériques
de complétude locale existants doivent être conservés et raccordés.

**Correction.** Faire dériver l'analyse cible du décodage, de l'état installé,
du nommage et de la production de transition reçus. Construire les transports
hors cône et les recomputations sur cette cible, puis consommer cet assemblage
dans l'installation. Le recheck doit recalculer indépendamment la même propriété,
sans recevoir le certificat cible ni le verdict incrémental.

**Clôture.** Accord d'acceptation et de successeur sur le domaine déclaré, avec
ses hypothèses explicites, et non uniquement sur l'exemple canonique. Conserver
les variantes de nommage admises au premier étage. Ne pas étendre implicitement
le second domaine, ni le rétrécir pour rendre la preuve immédiate. Vérifier
l'origine des fragments effectivement installés et leur correspondance entre
versions.

### F3 — Le changement de contrat après oubli juxtapose encore ses justifications

**Localisation.** [AutonomousCheckerClosure.lean](../../RelationalPerimeter/Agents/Neural/AutonomousCheckerClosure.lean),
branche d'analyse vers la ligne 276, continuation ordinaire lignes 631–710,
`ClosedLearnedPostForgettingContractChange` et son constructeur lignes 732–761,
checker et runtime lignes 777–827, paquet de clôture à partir de la ligne 885.

Le constructeur calcule et stocke `transportedIntent` et
`recheckedAuthorization`. Il construit parallèlement :

```lean
checked := buildIncrementalCheckedUpdate analysis.target
```

Ce certificat n'est pas construit à partir des deux résultats stockés. Le code
généré confirme les branches parallèles. L'égalité de deux champs `checked`
pour deux justifications, démontrable par `rfl`, est un indice complémentaire,
pas une preuve isolée qu'une justification invalide serait acceptée.

Le runtime séparé est initialisé sur `LearnedAlignedCurrentAgent`. Cet agent
correspond bien au courant installé précédemment. Cependant, aucune transition
de ce chemin ne consomme la sortie exécutée de mémoire réduite avec les
ressources préservées pour produire le changement de contrat. Stocker ensemble
le runtime antérieur, l'oubli et le runtime cible ne ferme pas cette dépendance.

**Correction.** Raccorder l'opération après oubli à la même lignée produite.
Déclarer les ressources conservées et celles oubliées. Le transport des
obligations persistantes et la revérification des obligations invalidées doivent
alimenter les obligations du certificat installé, avant effectuation, et non
seulement accompagner ce certificat dans une structure.

**Clôture.** Une transition de contrat réellement exécutée après réduction de
mémoire, avec installation justifiée et cas refusé sans successeur. L'accord
avec le recheck porte sur ce chemin. Une mauvaise correspondance de version ou
un certificat inadéquat ne doit pas passer. La continuation ordinaire corrigée
reste disponible sans lui imposer artificiellement un changement de contrat.

### F4 — L'action de la famille mesurée diffère de l'action de proposition certifiée

**Localisation.** [CausalParameterizedCompiledCheckerFamily.lean](../../RelationalPerimeter/Agents/Neural/CausalParameterizedCompiledCheckerFamily.lean),
état d'action lignes 23–37, `causalScalingTransitionRequest` ligne 40,
`causalScalingAction` ligne 59, fragments de certificat vers les lignes 198–225,
théorème `causalScalingTransitionRequest_is_advance_one` vers la ligne 585.

Les quatre constructeurs de requête sont transformés en `.advance 1`. Après
l'action de proposition, une seconde action est exécutée sur la mémoire source.
Le certificat structurel expose encore l'action de proposition. Une sonde Lean
confirme, pour l'état initial de taille zéro et la version `.local` :

- requête de l'action de proposition : `.advance 0` ;
- requête de l'action effective mesurée : `.advance 1` ;
- ces requêtes sont différentes.

La succession de mémoire est réelle, mais ne suffit pas à montrer que l'action
mesurée est celle dont la dépendance neuronale et le contrat sont certifiés.
Le fait de matcher tous les constructeurs n'établit pas une influence de la
proposition sur le choix effectif, puisque toutes les branches donnent le même
résultat.

**Correction.** Raccorder la proposition au canal d'action déclaré et certifier
l'action qui produit effectivement l'effet et le successeur mesurés. Ne pas
imposer une avancée pour fabriquer une progression apparente. Une opération
sans progression peut être admissible si le contrat la prévoit, tandis que les
transitions positives non triviales requises doivent être réellement construites.

**Clôture.** Une unique chaîne de ressources partagées jusqu'au successeur,
cohérence du certificat avec l'action exécutée, interventions sur les ressources
requises, et comparaison incrémental/recheck de la même propriété complète.
Le test ne doit pas se réduire à la taille ou à la bonne formation sérialisée.
Conserver les résultats historiques v11, même défavorables au coût.

### F5 — L'oracle comparatif est retiré, mais couverture et gel restent insuffisants

**Localisation.** [IndependentCapabilityComparison.lean](../../RelationalPerimeter/Agents/Neural/IndependentCapabilityComparison.lean),
[matrice v13](../../experiments/constitutive-neural-alignment/v13/capability-matrix.json),
[script de gel v13](../../scripts/freeze-independent-capability-comparison-v13.py),
[validateur v13](../../scripts/check-independent-capability-comparison-v13.py)
et [runner v13](../../scripts/run-independent-capability-comparison-v13.py).

Le nouveau calcul indépendant n'appelle plus le verdict final du système
audité. La fermeture transitive inspectée contient 721 fonctions. Ce correctif
est acquis et ne doit pas être décrit comme encore absent.

Restent les défauts suivants :

1. Pour P5, la matrice cite des théorèmes de continuation ordinaire après oubli,
   ou de permission/refus, comme évidence du changement de contrat après oubli.
   Ces propriétés ne remplacent pas la transition installée exigée par P5.
2. Les références P2 aux successeurs aligné et renommé n'établissent pas, à
   elles seules, l'épreuve « réseau inchangé, décodeur/action modifié ». P3 doit
   aussi être vérifié contre sa variation exacte, « artefact inchangé, contrat
   modifié », avec les deux issues requises. Une cellule non vide n'est pas une
   preuve de couverture sémantique.
3. P7 n'a pas de campagne confirmatoire. Les statuts ouverts sont correctement
   affichés, mais ne ferment pas l'intégration ni les ablations.
4. Le gel v13 porte sur une liste partielle de fichiers. Des dépendances
   transitives, notamment `LearnedRuntimeAdapter` et `IndependentLearnedArtifact`,
   n'y figurent pas. Le script de gel prévoit d'enregistrer le commit et l'arbre,
   mais le validateur de l'état gelé ne vérifie pas que le matériel exécuté
   leur correspond transitivement. Le protocole actuel reste un brouillon.
   Un SHA de longueur 40 et quelques empreintes ne suffisent pas.

**Correction.** Après F1–F4, relier chaque cellule à son épreuve exacte, son
entrée, son exécution, ses preuves et son résultat. Conserver la séparation
entre observation mesurée et garantie formelle. Tester le validateur par des
mutations atteignant les obligations, pas seulement les chaînes d'étiquettes.

Figer soit un snapshot vérifiable complet du périmètre, soit sa fermeture de
dépendances scientifiques et exécutables avec empreintes. Le runner doit
refuser une dépendance modifiée avant l'expérience. Il peut permettre des
commits ultérieurs de protocole ou de résultats sans exiger naïvement que HEAD
reste égal au commit du code, à condition de vérifier le snapshot réellement
exécuté. Le commit doit exister et être récupérable.

**Clôture.** Couverture réelle P1–P8, six classes de comparaison, méthode
relationnelle, combinaison de référence et recheck indépendant. Mêmes données
et propriété sur le périmètre commun, coûts et frontières de confiance déclarés,
protocoles gelés avant les runs, résultats rejouables. Ne pas supposer qu'une
baseline doit échouer ni annoncer un gain de vitesse ou de nouveauté par avance.

### F6 — Textes, références historiques et registre ne sont pas livrables en l'état

**Localisation.** [Passage français](../alignement-constitutif-neuronal-incremental.fr.md),
lignes 122–129, [passage anglais](../incremental-constitutive-neural-alignment.en.md),
lignes 120–126, [erratum v10](../../experiments/constitutive-neural-alignment/v10/ERRATUM_F5.md)
et [registre](../scientific-claims.json).

Les textes FR/EN présentent encore la comparaison v10 comme sans oracle, alors
que son erratum reconnaît précisément le défaut. L'absence d'oracle du nouveau
chemin ne valide pas rétroactivement v10.

Le claim `CONSTITUTIVE_NEURAL_ALIGNMENT_CLOSED_RUNTIME` conserve l'évidence
`1cb2d9119458ef57bb30dc8b6ec66d259aa427a4`. Ses revues historiques ne certifient
pas les dépendances actuelles. Les deux gates officielles s'arrêtent sur
`STALE_SOURCE: TARGET_1`. Séparément, le validateur v10 exécuté contre l'arbre
actuel signale une empreinte d'entrée différente pour `LearnedRuntimeAdapter`.

**Correction.** Corriger les phrases FR/EN et délimiter les résultats historiques,
sans réécrire leurs données. Reproduire v10 sur son snapshot gelé si nécessaire,
et conserver l'erratum. Une nouvelle campagne corrigée reçoit sa propre identité.
Réexaminer les consommateurs et les passages concernés avant de renouveler les
références d'évidence et les revues. Ne jamais rafraîchir une empreinte pour
masquer le changement scientifique.

**Clôture.** Évidence liée à un commit existant, textes relus séparément, registre
cohérent, gates complètes fraîches et audits indépendants visant la révision et
la portée exactes. Aucun succès local ne doit être présenté comme cette clôture.

## 5. Contrôle explicite de RC1–RC6

Les définitions de référence restent celles de la cible. Ce tableau indique
leur état et les preuves de clôture attendues, sans les redéfinir.

| Critère | État sur la révision auditée | Travail et contrôle de clôture |
| --- | --- | --- |
| RC1 — Origine déclarée | Distinction reçus/produits disponible dans les interfaces. Ne valide pas les substitutions repérées. | Déclarer primitives, exigences, contextes, schémas et admission avant les conclusions. Ne pas faire de l'exécution la source d'une norme reçue. Maintenir cette lecture dans les deux langues. |
| RC2 — Instanciation authentique | Non clos de bout en bout : F1, F2 et F4. | Raccorder obligations, occurrences, producteurs et consommateurs au même état exécuté. Suivre les données et les preuves, pas seulement des égalités de valeurs ou des champs présents. |
| RC3 — Indépendance de la réalisation | Aucune nouvelle circularité de la séparation générique identifiée. L'autonomie concrète reste à fermer avec F2 et F5. | Fixer les obligations avant la projection candidate et sans les définir par la réussite du checker. Autoriser les certificats antérieurs et la réflexion de décisions indépendamment définies. Le recheck ne reçoit pas le verdict qu'il doit contrôler. |
| RC4 — Conséquences générales | Théorèmes existants à conserver. Leur existence ne ferme pas le raccord exécuté manquant. | Pour `c.futureContract` fixé, relier `futureSourceOfState` et le séparateur à la même production, puis quantifier sur toute mémoire et toute `ExactRealization` concernée. La séparation est dérivée, non un champ supposé. Préserver une réalisation exacte positive. |
| RC5 — Transport effectif | Non clos : analyse canonique et justifications parallèles de F2–F3, action de F4. | Transmettre les obligations à travers réseau, décodeur, action, successeur, mémoire et contrat. Transporter les fragments préservés, recalculer les invalidés et consommer le certificat obtenu avant installation. |
| RC6 — Positifs et prévention | Plusieurs témoins positifs existent. Le raccord conjoint n'est pas clos. | Réunir sur la même lignée l'artefact appris non identitaire, les transitions successives, l'oubli non trivial, la continuation et le changement de contrat requis, la réalisation exacte témoin et le rejet du bypass avant effet. |

La conséquence universelle de RC4 ne doit pas être prescrite pour une projection
particulière : le contrat et les témoins sources sont fixés indépendamment de
la réalisation candidate. On réutilise l'API de futurs et de séparation du
dépôt, sans créer un second contrat affaibli pour contourner une obligation.

Instancier `…At state` ne demande pas de fabriquer un nouveau contrat à chaque
run. Une causalité certifiée ne devient pas automatiquement un séparateur de
futurs : toute séparation revendiquée exige son raccord aux observations et
son témoin fini. Ne pas transformer la préservation dirigée en transport
réversible, ni la séparation de sources distinguables en injectivité globale
ou en interdiction de tout regroupement. Les certificats conservés peuvent
être utilisés conformément au contrat, sans réintroduire l'histoire oubliée
comme oracle caché de la continuation.

## 6. Ordre obligatoire de correction

L'ordre ci-dessous est celui des dépendances. Des travaux de lecture ou de
préparation peuvent avancer en parallèle, mais aucun gel confirmatoire ni
verdict final ne précède la fermeture de ses prérequis. Les lots L0–L10 sont
propres à ce rapport, sans renuméroter les critères normatifs.

### L0 — Stabiliser la référence et expliciter les entrées

Conserver le snapshot audité, les anciens rapports, les données v10/v11 et les
statuts historiques. Identifier les fichiers affectés et les consommateurs.
Préciser les quatre lectures de dépendance, RC1 et RC3, avant de modifier les
interfaces. La contradiction documentaire de F6 peut être corrigée dès ce lot,
sans annoncer que les défauts de code sont fermés.

**Sortie :** périmètre et obligations inchangés, provenance des données et
points de raccord explicités. Aucun renouvellement mécanique du registre.

### L1 — Conserver la cible réellement produite

Fermer F1 dans le producteur et dans les chemins aligné et successif. Adapter
les témoins dépendants sans reconstruire la cible. Suivre la même ressource
jusqu'à l'action et au successeur. Ajouter les régressions de consommation.

**Sortie :** RC2 fermé sur cette première portion, avec preuves et contrôle des
consommateurs. La présence d'un appel isolé n'est pas le critère de réussite.

### L2 — Fermer l'analyse successive et l'accord avec le recheck

Après L1, fermer F2. Alimenter l'assemblage depuis la production reçue et les
certificats exacts de l'état installé. Transporter les fragments hors cône,
recalculer les autres, installer cet assemblage. Établir l'accord générique
relatif au domaine déclaré, pour l'acceptation et pour le successeur produit.

**Sortie :** G7/G8, RC2/RC3/RC5 raccordés à l'API réelle. Tester versions,
nommages, recomputations et rejets sans réduire les entrées déjà admises.

### L3 — Fermer le changement de contrat après oubli

Après L2, fermer F3 sur la mémoire réduite exécutée et les ressources déclarées
conservées. Rendre les transports et revérifications pertinents pour les
obligations du certificat installé. Construire les cas admis et refusés de P5.
Conserver la continuation ordinaire déjà corrigée.

**Sortie :** transition effectivement installée depuis cette lignée après oubli,
refus sans effet, accord au recheck, non-récupérabilité correctement délimitée.
Un simple paquet contenant séparément les témoins n'est pas cette sortie.

### L4 — Refermer le résultat conjoint et ses quantifications

Réexaminer la trace dépendante, l'API fermée, la provenance des occurrences,
les identifiants et les correspondances de versions. Relier les sources du
contrat de futurs à la production corrigée. Préserver le théorème pour tous les
futurs couverts, la séparation pour toute réalisation exacte et sa non-vacuité.

Fermer ensemble RC1–RC6 et G1–G10 sur les instances requises. Conserver le couple
aligné/bypass avec même intention et mêmes observations courantes sur le domaine
prévu, mais dépendances différentes, et son rejet avant effectuation.

**Sortie :** certificat conjoint, pas une collection de succès indépendants.
La non-vacuité concrète ne réduit pas les trois quantifications de la section 2.

### L5 — Corriger la chaîne mesurée et construire les épreuves comparables

Fermer F4 après fixation de la chaîne scientifique. Vérifier que les deux
chemins mesurent la même propriété complète et consomment les mêmes entrées.
Conserver l'artefact appris indépendant en plus de la famille paramétrée.

Fermer la couverture de F5 : P2 modifie effectivement un consommateur sans
changer le réseau, P3 modifie le contrat sans changer l'artefact, P5 exécute le
changement après oubli, P7 retire isolément les contrôles concernés. Si le
typage empêche une mutation, utiliser une fixture négative ciblée, sans ajouter
d'axiome ni contourner l'API de production.

**Sortie :** cas et adaptateurs exécutables, matrice d'évidence fidèle. Aucune
campagne confirmatoire ne démarre sur l'ancienne chaîne de mesure.

### L6 — Régressions complètes et relecture des preuves

Relire les corps, types, dépendances et consommateurs des résultats corrigés.
Exécuter C1–C17, G1–G10, les fixtures positives/négatives, l'audit de toutes les
constantes, les frontières d'import et les contrôles de code généré renforcés.
Le build doit passer sans contourner une preuve ni affaiblir une définition.

**Sortie :** socle technique et conceptuel fermé, inventaire des modifications
et des revues rouvertes. Les gates de registre encore périmées restent signalées
comme telles jusqu'au renouvellement justifié de L9, jamais déclarées réussies.

### L7 — Figer le code et les protocoles avant les runs

Après L0–L6, préparer puis, sur autorisation, créer une révision d'évidence du
code et des preuves. Fermer la vérification transitive du gel décrite en F5.
Figer les scripts, adaptateurs, propriétés, cas, tailles, graines, répétitions,
environnement, caches, mesures et règles d'analyse avant les runs.

Le protocole peut être commité séparément du code qu'il référence. La relation
entre ces snapshots doit être vérifiée, sans circularité d'empreinte. Réserver
de nouvelles identités de campagne si une version a déjà été gelée ou exécutée.

**Sortie :** matériel autonome récupérable et validateur rejetant un changement
de dépendance pertinente. Les brouillons v12/v13 ne deviennent pas des résultats
par simple changement de leur champ `status`.

### L8 — Exécuter les comparaisons et établir le gain résiduel

Exécuter les protocoles gelés de capacité et d'échelle. Publier tous les résultats,
y compris les coûts défavorables et les baselines qui réussissent. Séparer
résultats empiriques et théorèmes. Confronter R1–R8 à leurs hypothèses exactes
et aux adaptateurs, puis examiner S1–S8.

**Sortie :** P1–P8 rejouables, gains et limites effectivement établis. L'économie
de coût ne se déduit pas de l'incrémentalité. La nouveauté ne se déduit pas du
nombre de tests. Le résultat composé doit être comparé à la combinaison de
référence, pas seulement à chacun de ses constituants isolés.

### L9 — Renouveler la livraison scientifique et toutes les gates

Fermer F6 : mettre les textes FR/EN en accord avec les preuves et campagnes,
relire séparément chaque langue, puis fixer une évidence complète existante.
Mettre à jour le registre après ce réexamen, avec les vraies revues et leur
portée. Conserver les audits historiques sur leurs révisions propres.
Les quatre paragraphes protégés ne sont pas modifiés sans accord humain.

Exécuter `--self-test`, `--static`, `lake build`, `--lean` et les deux gates
officielles sur l'arbre final. Les anomalies de snapshot historiques doivent
être traitées par une reproduction correcte, pas par réécriture des empreintes.

**Sortie :** textes, sources, contrôles, données et registre concordants. Toute
nouvelle modification scientifique rouvre les contrôles concernés.

### L10 — Audits indépendants et intégration autorisée

Préparer les sources complètes, la toolchain, les dépendances, les données
réutilisables, les commandes et les critères inchangés. Après autorisation,
faire auditer séparément la validité/dépendance et la portée/nouveauté
comparative, sur la révision exacte. Lire intégralement les rapports.

**Sortie :** conclusions positives requises par S8 et C18, ou maintien explicite
de la cible non atteinte. Une soumission n'est pas une validation. Ne pas imposer
à l'auditeur un push d'artefacts volumineux pour pouvoir rendre son verdict.

Avant une fusion autorisée, retirer ou convertir les documents temporaires
selon la procédure, préserver les rapports finaux, puis contrôler le commit
fusionné. Aucune de ces opérations Git ou externes n'est autorisée par la seule
demande de rédaction du présent document.

## 7. Couverture de toutes les exigences

| Ensemble | Contrôle obligatoire, non substituable |
| --- | --- |
| C1–C7 | Généralité déclarée, authenticité neuronale, causalité des ressources, reconfiguration et autorisation consommées. L1–L4 et L6. |
| C8–C12 | Oubli exécuté, réduction non triviale, futurs, préservation relative et instance positive substantielle conjointe. L3–L4 et L6. |
| C13–C17 | Vocabulaire, diagnostics négatifs exacts, décomposition du résultat, absence de régression et vérification Lean complète. Tous les lots, particulièrement L6 et L9. |
| C18 | Claim, évidence, textes FR/EN et audit indépendant de la révision livrée. L9–L10. |
| G1–G3 | Méta-contrat, même production et ressources causalement requises. L0–L3. |
| G4–G6 | Toutes les traces admises, prévention avant effet, oubli et futurs. L3–L4. |
| G7–G8 | Vérification autonome, complétude relative, transport réellement consommé et accord au recheck. L2–L3, L5–L6. |
| G9–G10 | Artefact appris indépendant, succession positive non identitaire et séparation aligné/bypass. L4–L5. |
| RC1–RC6 | Tableau de la section 5 et fermeture conjointe de L4, pas seulement six noms dans un rapport. |
| R1–R8 | Corpus déjà exigé, versions et passages exacts, traductions sémantiques et antécédents pertinents. L5, L7–L8 et L10. |
| P1–P8 | Contournement latent, modification décodeur/action, contrat modifié, oubli/continuation, contrat après oubli, fragments/version/successeur, ablations, échelle. L4–L8. |
| S1–S8 | Fidélité bibliographique, comparabilité, comparateurs substantiels, raccord nouveau, utilité/non-vacuité, coûts/réutilisation, attribution/reproduction, conclusion indépendante. L7–L10. |

Les six classes de comparaison ne sont pas remplacées par six étiquettes :
vérification des comportements courants, analyse causale interventionnelle du
réseau fixé, protection pré-exécution des actions, adaptation sous garanties,
vérification incrémentale avec réemploi de preuves et propagation de certificats
de déploiement. La méthode relationnelle, la combinaison explicite de référence
et le recheck indépendant s'y ajoutent selon le périmètre déjà demandé.

Pour chaque méthode, conserver les distinctions « certifié », « observé »,
« non certifié », « hors interface » et « adaptateur indisponible ». Une absence
d'adaptateur n'est pas une preuve d'impossibilité de la méthode comparée.

## 8. Contrôles effectivement exécutés pendant l'audit

Ces résultats portent sur `26440b5`. Ils ne valent pas validation des corrections
à venir et n'effacent pas F1–F6.

| Contrôle | Résultat observé |
| --- | --- |
| `lake build` | Réussite, 475 jobs. |
| Audit exhaustif des constantes | 43 215 constantes, 465 modules, 478 exceptions générées et 0 exception écrite, contrôle réussi. Ne pas réécrire cette sortie comme « aucune exception ». |
| Audit des constantes exécutables | 473 modules, 7 racines exécutables, 467 modules par racine, contrôle réussi. |
| Scan Lean et blocs `AXIOM_AUDIT` | 473 fichiers, blocs conformes et aucun mécanisme interdit détecté par le contrôle. |
| Fixtures négatives | 173/173, diagnostics et sites attendus. |
| Plancher C1–C17 | Réussi : 15 contrôles Lean, 2 portails, 6 fixtures négatives. |
| Plancher G1–G10 | Réussi : 31 contrôles Lean, 2 portails, 29 fixtures négatives. |
| Fixtures négatives par bloc | 14 blocs, 14 fixtures, réussite. |
| Six contrôles de code généré | Agent, comparaison indépendante, unified, continuation signatures, variable master, integrated machine : réussis. Leur succès ne détecte pas toutes les substitutions de données décrites en F1–F4. |
| Imports et stratification | Réussite, inventaire des imports et 4 auto-tests, 369 modules de production contrôlés par la stratification. |
| Auto-tests du contrôle documentaire | 7/7. |
| `verify.ps1` et `verify.sh` | Échec sur `STALE_SOURCE: TARGET_1`. Aucun succès global des gates n'est revendiqué. |
| Références du registre en mode officiel `--lean` | Pas de nouveau succès complet enregistré pour cette révision. À exécuter après réparation scientifique du registre. |
| Validateur v10 sur l'arbre actuel | Échec : empreinte d'entrée de `LearnedRuntimeAdapter.lean` différente. Ce n'est pas une autorisation de réécrire le gel v10. |
| Validateur v11 avec résultats requis | Réussite sur les résultats historiques conservés. |
| Validateur v12 en mode brouillon et auto-tests | Réussite, 11 mutations contrôlées, pas de résultats confirmatoires. |
| Validateur v13 en mode brouillon et auto-tests | Réussite, 7 mutations contrôlées, pas de résultats confirmatoires. |
| Contrôle d'indépendance du comparateur | Fermeture de 721 fonctions, auto-test de mutation réussi. |
| Dossier de l'artefact indépendant | 6 baselines, 3 réseaux, 8 échantillons, `confirmatory=false`. |
| Campagne finale préexistante | 8 mutations et 5 tailles, propriété de bonne formation native sérialisée. Ne remplace pas l'alignement complet. |
| Six sondes Lean de l'annexe | Réussite, audits sans axiome. |
| `git diff --check` et identité | Propres pour les changements suivis, commit local et distant concordants lors de l'audit. |

L'audit n'a lancé ni campagne confirmatoire ni audit extérieur. Le rapport
précédent est resté intact. Les preuves locales réussies sont compatibles avec
le verdict négatif sur l'atteinte de la cible : elles vérifient leurs propres
énoncés, pas une dépendance exécutée supplémentaire absente de ces énoncés.

Contrôle propre à la rédaction de ce rapport : liens locaux vérifiés, relecture
de RC1–RC6 et de l'ordre des lots, puis réexécution des six sondes extraites de
l'annexe, toutes sans axiome. Aucun nouveau build complet n'a été nécessaire
pour cette modification exclusivement documentaire.

## 9. Annexe de reproduction des constats de dépendance

Les six sondes suivantes ont été vérifiées avec `lake env lean --stdin` dans
l'environnement de la révision auditée. Elles ne modifient pas les sources.
Elles accompagnent la lecture des corps et du code généré, sans la remplacer.
Après correction, certaines doivent légitimement cesser de décrire le programme.

```lean
import RelationalPerimeter.Agents.Neural.AutonomousCheckerClosure
import RelationalPerimeter.Agents.Neural.CausalCompletePropertyScalingMeasurement
open ConstitutiveSearch ConstitutiveSearch.NeuralAgent
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem auditAlignedTargetIsReplaced
    (source : ReconfiguredExecutionState independentLearnedRequirementFamily)
    (encoding : LearnedRequirementEncodingWitness source)
    (action : LearnedActionWitness source) :
    (learnedAlignedReconfigurationForState source encoding action).targetSystem =
      learnedDecodedAlignedArtifact.system := by rfl

theorem auditSuccessiveTargetIsCanonical
    (target : DecodedNeuralArtifact LearnedExtendedOperationalContract)
    (eqTarget : target = learnedDecodedExtendedArtifact)
    (decision : AcceptedTransitionDecision learnedExecutableMetaContractInterface
      ({current := .aligned, next := .extended} :
        ContractTransitionRequest learnedConstitutiveMetaContract)) :
    (learnedSuccessiveTargetAnalysisFromReceivedArtifact target eqTarget decision).state =
      learnedExtendedState := by cases eqTarget; rfl

theorem auditPostForgettingCheckedIgnoresJustification
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source)
    (j1 j2 : JustifiedPostForgettingTransition LearnedAlignedCurrentAgent .extended) :
    (closeLearnedPostForgettingContractChange analysis j1).checked =
      (closeLearnedPostForgettingContractChange analysis j2).checked := by rfl

theorem auditScalingResultIsFixedStep
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    (causalScalingAction source size version).result =
      Agent.executeInput source.memory (.advance 1) := by
  rw [(causalScalingAction source size version).resultExact]
  rw [(causalScalingAction source size version).requestExact]
  rw [causalScalingTransitionRequest_is_advance_one]
  rfl

theorem auditScalingCertifiedProposalIsAdvanceZero :
    (causalScalingAction (causalScalingInitialAgent 0).state 0 .local).proposalAction.request =
      .advance 0 := by rfl

theorem auditScalingEffectiveActionIsNotCertifiedProposal :
    (causalScalingAction (causalScalingInitialAgent 0).state 0 .local).request ≠
    (causalScalingAction (causalScalingInitialAgent 0).state 0 .local).proposalAction.request := by
  intro same
  change (Agent.Request.advance 1) = Agent.Request.advance 0 at same
  cases same

#print axioms auditAlignedTargetIsReplaced
#print axioms auditSuccessiveTargetIsCanonical
#print axioms auditPostForgettingCheckedIgnoresJustification
#print axioms auditScalingResultIsFixedStep
#print axioms auditScalingCertifiedProposalIsAdvanceZero
#print axioms auditScalingEffectiveActionIsNotCertifiedProposal
```

## 10. Condition terminale

La cible n'est close que lorsque les obligations suivantes sont réunies :

- F1–F4 corrigés sur la chaîne réellement consommée, sans remplacement canonique
  indépendant ni action effective étrangère au certificat revendiqué ;
- RC1–RC6 et G1–G10 fermés conjointement, avec les trois quantifications,
  l'instance positive substantielle et la prévention avant effectuation ;
- C1–C18 préservés, sans régression sur les résultats antérieurs ;
- F5 fermé par une comparaison et une mesure fidèles, gelées et exécutées,
  avec R1–R8, P1–P8 et S1–S8 effectivement examinés ;
- F6 fermé par une évidence, des textes FR/EN, un registre et des gates fraîches
  concordants ;
- audits indépendants requis lus, concluants et attachés à la révision exacte.

Une impossibilité rencontrée doit être exposée. Une exigence manquante maintient
le verdict « cible non atteinte ». Ni un build vert, ni une baisse de la cible,
ni l'ajout d'une exigence étrangère ne constituent une correction.
