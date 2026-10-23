# Audit de conformité et corrections ordonnées — alignement constitutif neuronal

## 1. Révision, statut et verdict

- Mise en document : 23 octobre 2026.
- Dépôt : `JohnDoe-collab-stack/relational-perimeter`.
- Branche auditée : `codex/constitutive-neural-alignment-implementation`.
- Commit audité : `6cd785a8bc1b9c1bc0678af651b0a8343787acfb`.
- Arbre Git : `704e63492d94905fff6a7dfc3ef8b76628874353`.
- Parent : `fafd739b7f4718ab9939ccd870eb4983a4655d2e`.
- Toolchain contrôlée : Lean `4.33.1`.
- L'arbre était propre avant et après l'audit. Les sondes ont été exécutées
  sur l'entrée standard de Lean, sans modifier les sources.

**Verdict : non conforme à la cible complète.** Le build réussit et plusieurs
corrections antérieures sont réelles. Un défaut d'authenticité est néanmoins
reproduit, les obligations constitutives ne sont pas encore réunies dans la
même chaîne apprise, RC4 n'est pas fermé et la livraison scientifique reste
bloquée. Ce n'est pas uniquement une mise à jour documentaire du registre.

Ce document consigne un audit interne et son plan de correction. Il n'est pas
un rapport Aristotle et ne confère aucun statut d'audit indépendant. Les
contrôles de la section 3 sont ceux exécutés pendant l'audit de cette révision,
pas des validations anticipées des corrections ci-dessous.

La demande présente autorise l'écriture de ce document uniquement. Elle
n'autorise ni l'implémentation, ni un changement de branche, ni un commit,
push, merge ou nouvel audit extérieur. Les opérations Git et audits prévus
dans les étapes futures devront être explicitement autorisés.

## 2. Cible maintenue intégralement

Références normatives, dont aucune clause n'est remplacée par ce rapport :

- [Cible terminale et définition de RC1–RC6](CIBLE_ALIGNEMENT_CONSTITUTIF_INCREMENTAL.fr.md).
- [Critères obligatoires C1–C18](CONSTITUTIVE_NEURAL_ALIGNMENT_TARGETS.fr.md).
- [Rapport antérieur : G1–G10, corpus R1–R8, épreuves P1–P8 et critères S1–S8](RAPPORT_VERIFICATION_ALIGNEMENT_CONSTITUTIF_fafd739.fr.md).
- [Procédure scientifique](../methode-de-travail-scientifique.fr.md).
- [Registre scientifique](../scientific-claims.json).

Les verdicts historiques restent attachés à leurs révisions. Le présent
rapport ne réattribue pas à `6cd785a` les défauts de `fafd739` déjà corrigés,
ni à une révision ultérieure les résultats de l'audit présent.

La cible reste une chaîne effectivement produite et consommée :

```text
exigence et contexte reçus
→ incorporation causale et transformations neuronales exécutées
→ proposition constituée
→ action produite et autorisée
→ effet exécuté et successeur produit
→ reconfiguration causalement constituée et admise
→ continuation depuis ce successeur exact
→ oubli exécuté sous contrat
→ observations et futurs préservés
```

Les contrats et leur schéma d'observation sont fixés indépendamment de la
réalisation exacte candidate. Les obligations sont instanciées sur les
occurrences et états produits. Les contraintes observables sont démontrées
depuis les témoins de cette même production, puis appliquées à toute
réalisation exacte du contrat concerné. Une norme reçue n'est pas présentée
comme inventée ou justifiée par l'exécution.

Trois quantifications doivent rester séparées et toutes être conservées :

1. toute trace finie acceptée par le vérificateur dépendant ;
2. toute continuation finie couverte par le contrat de futurs ;
3. tout type mémoire admissible et toute réalisation exacte de ce contrat
   fixé, pour les contraintes observables démontrées sur les sources produites.

La clôture exige aussi les réalisations positives substantielles, la
réutilisation effective, les comparaisons et les audits prévus. Une
conjonction de réussites sur des dispositifs sans raccord ne remplace pas
la conjonction requise sur la même chaîne.

Ne sont pas ajoutés à la cible : valeurs humaines, injectivité universelle,
quotient canonique, réversibilité de toute préservation dirigée, décision de
toute propriété sémantique, ni dépendance nécessaire à Gödel, Tarski ou HA.
Ces derniers résultats restent protégés par la non-régression. Une causalité
interventionnelle n'est pas automatiquement un séparateur de futurs.

## 3. Vérifications réellement obtenues

| Contrôle exécuté | Résultat sur le commit audité |
| --- | --- |
| `lake build` | 451 cibles réussies, aucun avertissement détecté |
| Audit des constantes importées par `Tests/AllConstantsAudit.lean` | 39 923 constantes, 445 modules, `generatedExceptions=478`, `writtenExceptions=0` |
| Blocs `AXIOM_AUDIT` et recherche des constructions interdites | 449 fichiers Lean conformes au contrôle source |
| `scripts/check-expected-failures.ps1` | 128/128 fixtures, diagnostics et sites exacts |
| Frontières d'import, avec autotests | Réussies |
| Stratification | Réussie, 359 modules de production inventoriés |
| Cinq contrôles de code généré | Réussis |
| Contrôles de présence C1–C17 et G1–G10, fixtures par bloc | Réussis ; ce sont des contrôles de régression, pas une certification de la conjonction scientifique |
| Contrôle des adaptateurs v6 | Réussi, avec `results=false` et `run=false` |
| Contrôle de campagne v8 | Réussi, avec `practical_gain=false` |
| Contrôles d'artefact indépendant et campagne finale existante | Réussis dans leurs périmètres déclarés |
| Autotests documentaires | 7/7 réussis |
| Autotests v6, mesure v5, campagne v8 | Réussis |
| `scripts/verify.ps1` | Échec au contrôle documentaire : `STALE_SOURCE: TARGET_1` |
| Contrôle v5 lancé séparément | Échec : `frozen source hash changed: lakefile.toml` |
| `git diff --check` | Réussi |

Les cinq contrôles de code généré sont `check-unified-codegen.py`,
`check-agent-codegen.py`, `check-continuation-signature-codegen.py`,
`check-variable-master-codegen.py` et `check-integrated-machine-codegen.py`.
Les scripts Python ont été exécutés avec un Python disponible explicitement
sélectionné, sans dépendre de l'alias Windows Store.

La réussite du scan source ne signifie pas que chaque constante a été
auditée. Les 478 exceptions générées sont classées par le contrôleur existant
et ne sont pas 478 axiomes écrits. Inversement, `writtenExceptions=0` ne
permet pas de déclarer couvert un module absent du scan.

Trois modules exécutables sont absents de l'environnement importé par
`AllConstantsAudit`, absence vérifiée directement dans Lean :

- `Tests.Executables.CompiledNeuralCheckerMeasure` ;
- `Tests.Executables.CompiledNeuralComparisonAdapters` ;
- `Tests.Executables.CompiledParameterizedNeuralCheckerFamily`.

Le portail attend 449 − 1 = 448 modules, mais le scan annonce 445. Ce défaut
de couverture est distinct des deux empreintes périmées. Le portail complet
n'a pas été déclaré réussi : il s'arrête effectivement à `TARGET_1`. Le
portail Bash n'a pas été déclaré exécuté pendant cet audit.

Les sources Gödel, Tarski et HA ne diffèrent pas du parent `fafd739` dans
les répertoires contrôlés. Le build et les contrôles de non-régression réussis
ne ferment pas pour autant les obligations neuronales nouvelles.

## 4. Constats et preuves localisées

Les chemins ci-dessous désignent les fichiers du dépôt ; les numéros de
lignes sont ceux du commit audité, pas des versions corrigées futures.

### A1 — Substitution des identifiants stables après acceptation

Dans [LearnedRuntimeAdapter.lean](../../RelationalPerimeter/Agents/Neural/LearnedRuntimeAdapter.lean),
le décodeur conserve une donnée `stable` indexée par les noms reçus
(lignes 1308–1355). Mais `LearnedIncrementalEngineAnalysis.target`, à partir
de la ligne 1405, utilise la base et les fragments canoniques appris.

La sonde de l'annexe décale de 1 000 les identifiants de la mise à jour :

```text
identifiants canoniques :   [100, 101, 102]
identifiants transmis :     [1100, 1101, 1102]
acceptation incrémentale :  true
identifiants du certificat :[100, 101, 102]
identifiants installés :    [100, 101, 102]
```

Le défaut est reproduit jusqu'à `submitUpdate`, pas seulement dans une
fonction auxiliaire. Une bonne formation des noms n'est pas une preuve
qu'ils sont ceux de l'état certifié et installé. Obligations touchées :
RC2, RC5, G2, G8 et correspondance des identités entre versions.

### A2 — Obligations apprises plus faibles que la chaîne exigée

Dans le même fichier :

- `proposalActionPreservation` utilise `learnedIntentObligations`, dont le
  témoin est une intention admise (lignes 159–162 et 213–215) ;
- `LearnedEffectWitness` établit `proposal = true`, pas l'exécution d'un effet
  depuis une action produite (lignes 130–131) ;
- `learnedInitialState` et `learnedAlignedState` reçoivent tous deux
  `publicActionMemory` (lignes 274–284) ;
- `LearnedExecutedStateTransition.installAligned` relie les deux états
  prédéfinis sans construire cette chaîne action–effet (lignes 941–951).

Ces déclarations sont typées et peuvent être prouvées. Le problème est leur
insuffisance pour le sens demandé de l'alignement. Un champ nommé « effet »
ne transforme pas une propriété de proposition en preuve d'effet exécuté.

### A3 — Une seule mise à jour dans l'instance apprise

`LearnedRuntimeUpdate`, lignes 1576–1580, possède seulement un constructeur
depuis `learnedInitialCheckedAgent`. La seule permission de transition
apprise est `.initial → .aligned` (lignes 919–921).

La sonde a démontré sans axiome qu'un agent sous contrat `.aligned` ne peut
recevoir aucun `LearnedRuntimeUpdate`. La généralité du runtime abstrait
n'est pas réfutée, mais cette instance n'exerce pas les reconfigurations
successives requises par G9 et RC6.

### A4 — Raccord universel RC4 absent de l'instance neuronale

[CoveredFutureRealization.lean](../../RelationalPerimeter/Agents/Neural/CoveredFutureRealization.lean)
construit des réalisations et la préservation de leurs futurs.
[ExactSeparation.lean](../../RelationalPerimeter/Constitution/Continuation/ExactSeparation.lean)
fournit le principe générique de séparation.

Le raccord neuronal exigé entre production, témoins observables et contrainte
pour toute `ExactRealization` du contrat fixé n'est pas fermé. Une réalisation
exacte particulière, même positive, ne remplace pas cette universalité.
Le travail restant est une instanciation justifiée et consommée, pas une
nouvelle définition de l'exactitude ni une nouvelle preuve de Gödel.

La relecture précise aussi la limite C9–C10 de l'instance apprise. Dans
`LearnedRuntimeAdapter.lean`, lignes 90–100, toutes les requêtes sont admises
et le readout expose le réseau sérialisé entier. La réalisation des lignes
232–238 est l'identité. Les sondes de l'annexe établissent sans axiome :

- l'admission de toute requête dans ce contrat ;
- l'égalité des réseaux dès que leurs projections coïncident sous une
  réalisation exacte de ce contrat ;
- la distinction des deux candidats appris par le futur vide `[]`.

Le futur non vide discriminant déjà construit est valide, mais il ne montre
donc pas qu'une continuation soit nécessaire pour distinguer ces candidats.
Il faut fermer les exigences C9–C10 déjà fixées : réduction non triviale,
admission et refus, et au moins une distinction nécessitant une continuation.
Ces exigences ne sont ni une modification de RC4 ni l'obligation de rendre
tous ses séparateurs non vides.

### A5 — Réutilisation, complétude et référence encore disjointes

Dans l'instance apprise, les lignes 1240–1252 de `LearnedRuntimeAdapter.lean`
annoncent explicitement un renouvellement de toutes les identités et une
reconstruction structurelle complète. `transportedStructural` est vide.

[IncrementalReferenceEquivalence.lean](../../RelationalPerimeter/Agents/Neural/IncrementalReferenceEquivalence.lean)
prouve une équivalence d'acceptation et de résultat sur l'instance publique.
Le recheck générique existe dans
[ReferenceChecker.lean](../../RelationalPerimeter/Agents/Neural/ReferenceChecker.lean),
mais l'existence des deux API ne constitue pas encore leur équivalence
fermée sur la chaîne apprise requise.

Dans [ParameterizedCompiledCheckerFamily.lean](../../RelationalPerimeter/Agents/Neural/ParameterizedCompiledCheckerFamily.lean) :

- les obligations sémantiques et le futur sont unitaires, lignes 32–75 ;
- `calculateScalingIncrementalLocalConditions` appelle d'abord `checkInitial`
  sur toute la cible, lignes 611–645 ;
- `ScalingIncrementalEvidence.calculated` contient le succès de cet analyseur,
  puis sert de `LocalConditions` au même moteur, lignes 647–693 ;
- les compteurs de fragments, lignes 707–726, sélectionnent les observations
  selon le cône. Ils ne comptent pas tout le travail de vérification préalable.

La dernière « complétude » est donc une reformulation de l'acceptation, pas
une caractérisation par conditions sémantiques autonomes. La sélection de
fragments anciens à l'assemblage est réelle, mais elle ne prouve pas que le
reste n'a pas été revérifié auparavant.

### A6 — Pas encore de témoin conjoint sur la même chaîne apprise

[NeuralG1G10RegressionFloor.lean](../../Tests/Mechanisms/NeuralG1G10RegressionFloor.lean)
combine des références publiques, apprises et génériques. Par exemple,
la continuation à deux pas et l'oubli portent sur l'instance publique,
tandis que l'installation apprise est à un seul pas.

Ce fichier est utile pour empêcher la disparition de résultats existants.
Il ne constitue pas la preuve conjointe G1–G10 exigée. L'oubli public ne doit
pas être supprimé ; il doit être raccordé à la réalisation apprise pertinente
par une construction, et non invoqué comme résultat voisin.

### A7 — Comparaison et portée pratique non closes

Le [protocole v6](../../experiments/constitutive-neural-alignment/v6/comparison-protocol.json)
ne possède pas de résultats confirmatoires et interdit encore son run dans
l'état enregistré. Les six adaptateurs sont des interfaces locales ; plusieurs
réutilisent les certificats ou vérificateurs du projet. Par exemple,
`runGuaranteedSelfAdaptiveAdapter` renvoie le runtime appris déjà construit
dans [CapabilityComparisonAdapters.lean](../../RelationalPerimeter/Agents/Neural/CapabilityComparisonAdapters.lean),
lignes 205–214.

Ces adaptateurs ne suffisent pas à établir une comparaison indépendante avec
les méthodes R1–R8 ni avec leur combinaison. Leur existence n'établit aucune
incapacité d'une famille de méthodes.

La [campagne v8](../../experiments/constitutive-neural-alignment/v8/SCALING_ANALYSIS.md)
rapporte 35 traces mesurées et 210 mises à jour, avec un résultat temporel
défavorable. À la taille 80, les médianes publiées sont 70 777,626 ms pour la
trace incrémentale et 10,522 ms pour le recheck. Le critère de gain est faux.
Ces observations sont conservées telles quelles. Elles ne valident ni la
chaîne substantielle complète ni une économie de vérification.

### A8 — Livraison et couverture d'audit incomplètes

Les trois blocages techniques sont détaillés en section 3. Les textes
[français](../alignement-constitutif-neuronal-incremental.fr.md) et
[anglais](../incremental-constitutive-neural-alignment.en.md) décrivent une
chaîne et une équivalence dont les réalisations doivent encore être raccordées
au niveau exigé. Le claim `CONSTITUTIVE_NEURAL_ALIGNMENT_CLOSED_RUNTIME`
reste proposé et non enregistré. C18 n'est pas fermé.

## 5. Tableau de contrôle RC1–RC6

La définition normative unique reste celle du plan. Ce tableau indique
comment en vérifier la clôture, sans modifier les critères.

| Critère | Constat au commit audité | Évidence nécessaire | Étapes ci-dessous |
| --- | --- | --- | --- |
| RC1 — Origine déclarée | La distinction reçu/produit est explicitée ; elle doit rester exacte dans les réalisations renforcées. | Paramètres, primitives, exigences, contextes, admissions et schéma d'observation déclarés avant les conclusions. Aucune justification normative fabriquée par l'exécution. | L1, L8, L12 |
| RC2 — Instanciation authentique | Défaut A1 reproduit et chaîne A2 incomplète. | Noms, occurrences, artefact, états et obligations raccordés au même producteur et consommés jusqu'à l'installation. | L2, L3, L4, L5, L7, L8 |
| RC3 — Indépendance | L'interface permet des obligations indépendantes ; la famille de mesure réintroduit une condition fondée sur son propre succès. | Sens des obligations et producteurs des témoins sources indépendants de la projection candidate ; conditions locales autonomes. Réflexion constructive et certificats antérieurs justifiés restent autorisés. | L1, L4, L5, L10 |
| RC4 — Conséquences générales | Principe générique disponible, raccord neuronal non fermé. | Contraintes observables dérivées depuis les sources produites, puis théorème pour tout `M` et toute réalisation exacte du contrat fixé ; témoins finis lorsque la séparation est revendiquée. | L4, L7, L8 |
| RC5 — Transport | Décision de transition raccordée, mais identités, action–effet et réutilisation ne ferment pas encore la chaîne. | Consommation du certificat exact, transports persistants et revérification des obligations invalidées avant effet, y compris décodeur, mémoire et contrat. | L2, L3, L4, L5, L6, L7, L8 |
| RC6 — Positif et prévention | Installation alignée et rejet présents, mais pas les reconfigurations successives et l'oubli substantiel sur la même réalisation apprise. | Transformations non identitaires, plusieurs adaptations légitimes, oubli et réduction non triviaux sous le contrat requis par C9–C10, réalisation exacte témoin et contournement refusé par la même API. | L4, L7, L8, L9 |

## 6. Ordre obligatoire des corrections

Les étapes ci-dessous organisent la fermeture des écarts, sans demander de
réécrire les composants corrects. Les contrôles positifs et négatifs sont
ajoutés au bloc concerné immédiatement ; L11 ne les reporte pas à la fin.
Une étape ne devient pas acquise par l'ajout d'un nom de théorème.
Les clôtures locales ci-dessous concernent leurs sous-obligations : RC2 et
RC5 ne sont fermés intégralement qu'après leur raccord à l'installation et
aux traces de L7, puis leur réalisation conjointe en L8 et leur contrôle L11.

### L0 — Stabiliser le socle et restaurer des contrôles complets

1. Préserver le snapshot `6cd785a`, les résultats historiques et les défauts
   reproduits. Inspecter branche et diff avant toute écriture future.
2. Recontrôler les acquis C3 et C8, puis C1–C17 et les anciennes preuves.
3. Réparer la couverture des trois exécutables : audits de leurs constantes
   dans des environnements adaptés, avec inventaire vérifiant leur union.
   Plusieurs modules définissant `main` peuvent nécessiter des clients séparés.
   Ne pas simplement diminuer le nombre attendu ni exclure ces exécutables.
4. Réexaminer `TARGET_1`, ses dépendances et consommateurs. Corriger le
   registre seulement sur une révision d'évidence existante, après lecture,
   sans rafraîchissement mécanique ni statut de revue inventé.
5. Conserver le protocole et les résultats v5 intacts. Leur validation doit
   rester attachée à leur matériel historique exact. Si le matériel courant
   est remesuré, créer une version nouvelle, pas une empreinte rétroactive.
6. Préparer, puis obtenir l'autorisation du commit stable de socle nécessaire
   et faire passer ses gates avant de promouvoir les étapes suivantes.

Clôture : les défauts de preuve restent visibles, les portails contrôlent tout
leur périmètre, les évidences historiques ne sont ni effacées ni réétiquetées.
Le claim terminal n'est pas enregistré à cette étape.

### L1 — Fixer les obligations indépendamment du candidat et du verdict

1. Cartographier `ConstitutiveContract`, les familles `…At state` et
   `futureContract` comme trois niveaux distincts de la même API.
2. Pour chaque obligation, documenter formation, exécution, preuve et
   transport ; identifier producteur et consommateur réels.
3. Fixer le méta-contrat, ses transitions admissibles, le domaine, la base
   d'interventions et le schéma de lecture conformément à la cible, avant
   leur emploi par les vérificateurs et les comparaisons. Prévoir les
   reconfigurations successives requises, sans élargir les permissions après
   examen d'un candidat pour le faire accepter. Une correction d'une instance
   insuffisante rouvre ses preuves et revues ; elle ne modifie pas
   rétroactivement le contrat des résultats historiques.
4. Spécifier les conditions locales indépendantes du succès du checker.
   Les preuves de décodage et les décisions auxiliaires réfléchies sont
   utilisables ; l'acceptation du contrôle à caractériser n'est pas sa propre
   spécification.
5. Définir dès cette étape les sources et cibles des transitions en fonction
   de l'agent courant. Ne pas figer les vérificateurs autour du seul couple
   `.initial → .aligned`. L2 raccorde cette indexation au décodage ; L7 ferme
   les preuves de succession, de trace et d'accessibilité.

Clôture : RC1 et la frontière d'indépendance RC3 sont explicites. Ni une
obligation unitaire ni une intention admise ne remplace une obligation
d'action, d'effet, de causalité ou de futur exigée par la cible.

### L2 — Corriger la chaîne des identités et de la sérialisation

1. Faire dépendre le nommage certifié et installé du nommage effectivement
   décodé, avec les lois de correspondance ancien/nouveau et les mêmes
   occurrences. Retirer le recours silencieux aux noms canoniques.
2. Raccorder intégralement l'artefact et le delta : programme, encodage,
   poids, arêtes, ports, décodeur, autorisation, mémoire et contrat concernés.
3. Distinguer identité stable et position `Fin`. Vérifier insertions,
   suppressions et réindexations ; invalider les fragments non transportables.
4. Transformer A1 en régression : un nommage valide accepté doit être celui
   du certificat et du runtime. Une correspondance invalide est refusée avant
   effet avec un diagnostic exact.
5. Ne pas « réparer » A1 en interdisant toutes les évolutions d'identités
   exigées par le plan. Conserver des cas admissibles positifs et les lois
   de transport correspondantes.
6. Raccorder le décodeur de mise à jour et ses correspondances à l'agent
   courant de L1, pas seulement à `learnedInitialCheckedAgent`. Conserver
   l'API dépendante existante et fournir cette interface aux vérificateurs
   de L5–L6 avant de construire leurs réalisations successives.

Clôture : aucune donnée reçue n'est validée puis remplacée par un exemplaire
canonique non relié. Seules les sous-obligations identitaires et de décodage
de RC2 et RC5 sont fermées ici. Les producteurs, consommateurs et transports
de la chaîne complète restent à raccorder dans les étapes suivantes.

### L3 — Produire la chaîne action, effet et successeur

1. Réutiliser les producteurs constitutifs et transformations non identitaires
   existants ; les raccorder au run exact de l'artefact appris décodé.
2. Construire la proposition depuis cette exécution et sa préservation, puis
   l'action depuis cette proposition et le canal déclaré.
3. Faire consommer l'autorisation admise par l'action pertinente et produire
   ensemble l'effet et son successeur. Distinguer admission et satisfaction.
4. Remplacer les substituts insuffisants d'A2 par les témoins exécutés requis.
   La mémoire cible ne doit pas être une mémoire publique fixée indépendamment
   de l'effet. Un constructeur nominal de transition ne remplace pas son calcul.
5. Vérifier par interventions les rôles requis de l'exigence, du contexte,
   de l'autorisation et des ressources prescrites de l'état précédent.

Clôture : les producteurs de l'action, de l'effet et du successeur et leurs
dépendances G2–G3 sont raccordés à la même exécution. Ce lot fournit les
témoins nécessaires à RC2–RC5 ; il ne clôt ni le raccord aux futurs de L4,
ni les transports et leur consommation dans les traces de L5–L8.
Fixtures ciblées : action étrangère, effet d'une autre exécution, autorisation
stockée mais non consommée, successeur reconstruit, transformateur post hoc.

### L4 — Fermer le raccord aux futurs, l'oubli et RC4

1. Relier `futureSourceOfState` aux états et occurrences issus de L3.
2. Fermer C10 sur le contrat appris annoncé : construire une requête admise
   et une requête refusée avec leurs décisions, ainsi que des états dont la
   lecture immédiate ne suffit pas à distinguer les futurs, mais qu'une
   continuation finie non vide distingue. Ne pas confondre l'existence d'un
   futur non vide discriminant avec sa nécessité. Les autres séparateurs,
   y compris `[]` lorsqu'il convient, restent légitimes.
3. Construire les témoins sources des obligations observables sans recevoir
   la projection à valider ni supposer son exactitude.
4. Réutiliser `ExactRealization`, ses lois locales et les théorèmes sur toutes
   les listes finies. Pour une séparation requise, construire le
   `FutureSeparator` depuis les observations du contrat et les témoins
   produits, puis appliquer `distinct_memory_of_separator`.
5. Exposer le résultat quantifié sur tout type mémoire et toute réalisation
   exacte du même contrat fixé. Ne pas le réduire à la réalisation identité.
6. Construire aussi une réalisation exacte positive du contrat concerné.
   Une séparation démontrée n'interdit pas tous les regroupements.
7. Raccorder l'oubli à deux entrées historiquement distinctes, encore
   renseignées avant l'action. Produire leur mémoire réduite par exécution,
   démontrer la préservation des futurs et, séparément, la non-récupérabilité.
   Fermer C9 par l'omission effective d'une information source, et non par
   la réalisation identité. Les états regroupés sous réalisation exacte ne
   peuvent pas être la paire séparée sous ce même contrat ; aucune fusion
   de cette paire n'est exigée.
8. Vérifier le changement de contrat après oubli : transporter ce qui reste
   justifié ou refuser la transition ; ne pas ressusciter une provenance perdue.

Clôture : RC4 est instancié sur les productions neuronales, C9–C10 sont
fermés sur les réalisations requises et les consommateurs sont identifiés.
Leur consommation par le certificat installé reste à vérifier en L5–L8.
Pas de nouvelle API parallèle, de nouvelle preuve du principe générique,
de séparation supposée dans l'exactitude, ni de prémisse diagonale.

### L5 — Fermer les vérificateurs et leur complétude relative

1. Utiliser des entrées sérialisées sans certificat cible préfabriqué.
2. Produire les fragments depuis décodage, exécution et décisions réfléchies
   sur le domaine et la base causale déclarés.
3. Conserver un vérificateur complet indépendant du résultat incrémental,
   de ses fragments réutilisés et de son verdict.
4. Démontrer correction et complétude relative face aux conditions autonomes
   de L1. Corriger aussi la circularité `ScalingIncrementalEvidence.calculated`
   si cette famille est conservée comme instance de l'interface.
5. Distinguer un reçu d'exécution de l'analyseur, légitime dans son résultat,
   de la spécification dont l'analyseur doit décider la satisfaction.

Clôture : G7 est fermé dans les instances requises, pas seulement reçu comme
champ d'une interface. Aucun élargissement à la décidabilité de toutes les
propriétés sémantiques n'est demandé.

### L6 — Rendre la réutilisation effective et prouver l'équivalence

1. Construire le graphe hétérogène depuis les données exactes de L2–L4 :
   réseau, décodeur, action, effet, successeur, mémoire et contrat.
2. Calculer le cône affecté et justifier les correspondances entre versions.
3. Transporter réellement les fragments hors cône depuis le certificat
   précédent ; recalculer les fragments et obligations invalidés.
4. Ne pas certifier entièrement la cible avant de déclarer ce travail évité.
   Séparer décodage et calcul structurel nécessaires, revérification sémantique,
   assemblage et contrôles de cohérence.
5. Prouver l'équivalence d'acceptation et l'identité du successeur certifié
   avec le recheck indépendant, sur le même périmètre, la même propriété et
   la même mise à jour. Fermer cette équivalence pour les instances apprises
   requises, au lieu de citer uniquement l'exemple public.
6. Construire des transitions apprises à cône local avec réutilisation non
   vide et des transitions à cône étendu correctement recalculées.

Clôture : les lemmes locaux de G8 et la réutilisation requise par RC5 sont
démontrés pour les transitions examinées. Leur consommation par chaque
installation et leur portée sur les traces restent à fermer en L7–L8.
Les compteurs séparent les fragments effectivement transportés, recalculés
et les autres calculs nécessaires.
Une reconstruction complète avec une sélection finale de fragments ne suffit
pas à prouver une économie de revérification.

### L7 — Ouvrir la succession autorisée et garder l'API fermée

1. Utiliser l'indexation sur l'agent courant et le décodage établis en L1–L2,
   avec les vérificateurs de L5–L6. Ne pas introduire ici une seconde API de
   mises à jour ni reconstruire un agent source indépendant.
2. Produire les transitions admises successives, avec obligations persistantes
   transportées et obligations invalidées vérifiées avant installation.
3. Conserver `CheckedUpdate`, `checkUpdates`, l'historique dépendant et l'API
   existants ; la queue doit consommer exactement le `next` retourné.
4. Prouver l'accessibilité certifiée des états installés et l'absence de
   successeur installé ou d'action effective pour une mise à jour refusée.
5. Instancier les trois quantifications de la section 2 sans confondre la
   longueur d'un exemple avec la portée du théorème générique.

Clôture : plusieurs reconfigurations positives sont possibles dans l'instance
apprise, sans borne arbitraire ajoutée au théorème sur les traces acceptées.
La sonde historique `noLearnedSecondUpdate` n'est pas à conserver comme
propriété souhaitée : elle est remplacée par les témoins positifs requis.

### L8 — Fermer G1–G10 et RC1–RC6 sur l'artefact appris

Préalable obligatoire à toute nouvelle production confirmatoire : figer
aussi le protocole comparatif, et pas seulement l'apprentissage. Il fixe les
six classes, R1–R8, la méthode relationnelle, la combinaison de référence,
le recheck, les versions et configurations des adaptateurs, leurs traductions,
les propriétés et informations communes, les données ou règles de production,
P1–P8 et les règles de décision. Les commandes et empreintes des matériaux
déjà disponibles sont enregistrées avant le run ; celles des sorties le sont
après leur production, sans sélection opportuniste. Ce gel précède les
constructions confirmatoires ci-dessous. L9 exécute et analyse la comparaison
ainsi définie. Les essais exploratoires restent identifiés comme tels.

1. Avant toute nouvelle production confirmatoire, figer le protocole
d'apprentissage ou de transformation, sa provenance, les graines, données,
paramètres, commandes, normalisation et droits de réemploi.
2. Conserver l'indépendance de l'artefact : pas de poids choisis dans les
preuves, pas de retouche manuelle pour simplifier leur clôture. Les certificats
sont calculés depuis le décodage.
3. Réaliser sur la même chaîne les transformations non identitaires,
plusieurs exigences et contextes, plusieurs chemins causaux et observations,
plusieurs reconfigurations, l'oubli exact et la réutilisation locale.
4. Depuis le même agent et la même intention admise, construire
`alignedUpdate` et `bypassUpdate`, égaux sur tout le domaine courant canonique.
La même API accepte le premier et refuse le second pour la dépendance
effectivement manquante, non pour son nom.
5. Raccorder le futur non vide discriminant au contrat du runtime. Le candidat
refusé est évalué uniquement dans une simulation pure sans effet.
6. Produire un paquet terminal dont les dépendances relient toutes ces preuves
aux mêmes runs, occurrences, états et transitions. Conserver les régressions
publiques comme socle, sans les utiliser pour remplacer un membre manquant.

Clôture : réalisation positive substantielle conjointe et prévention effective.
Une liste de théorèmes indépendants, un refus universel ou une trace apprise
à un seul pas ne ferme pas G9, RC6 ni la cible composée.

### L9 — Comparer réellement les capacités sans fabriquer l'avantage

1. Conserver les six classes, le corpus R1–R8, la méthode relationnelle,
la combinaison explicite de référence et le recheck indépendant.
2. Pour chaque adaptateur, vérifier et rapporter la méthode, la référence,
la version, les hypothèses, la configuration, les données accessibles et la
traduction sémantique figées avant les constructions confirmatoires de L8.
Une interface locale réutilisant nos certificats ne représente pas à elle seule un travail
antérieur ni une comparaison indépendante.
3. Exécuter les raccords comparés sur le même matériel. La combinaison de
référence ne doit ni appeler notre verdict final comme oracle ni recevoir
notre certificat cible préfabriqué.
4. Donner aux méthodes les données pertinentes qu'elles savent exploiter :
interventions, modèles des futurs et contrats. Ne pas les réduire artificiellement
à la table courante pour obtenir un résultat favorable.
5. Couvrir P1–P7 et les critères comparatifs S1–S5, S7–S8. Relier chaque cellule
à une preuve ou une sortie reproductible, avec son statut exact.
6. Exécuter la campagne autorisée sur le matériel et le commit stable gelés
avant le run. Un changement depuis v6, ou après le gel de L8, exige une
nouvelle version avant la production confirmatoire concernée ; les résultats
antérieurs restent conservés. Ne pas définir les baselines après examen des
résultats. Un adaptateur absent ou un raccord non réalisé laisse la comparaison
ouverte.

Clôture : le gain résiduel est identifié après prise en compte des garanties
réelles des concurrents. La limitation universelle des vérificateurs par
table courante reste limitée à cette factorisation ; elle ne dit pas qu'ils
acceptent nécessairement le contournement ni que toute autre méthode échoue.

### L10 — Mesurer le passage à l'échelle sur la propriété pertinente

1. Conserver v5, l'échec v7 et les résultats défavorables v8 sans les modifier.
2. Construire une famille dont le graphe causal pertinent, les obligations
exercées et les traces croissent. Une famille structurelle à obligations
unitaires reste un microbenchmark identifié, pas la validation de la chaîne
substantielle. Elle ne remplace pas l'artefact appris de L8.
3. Comparer incrémental et complet sur la même propriété, le même artefact,
la même arithmétique et le même état source, avec successeurs correspondants.
4. Compter le travail réellement exécuté, y compris revérification préalable,
conversion et instrumentation. Séparer construction, vérification, installation,
exécution, initialisation, mémoire, certificat et delta. Ne pas assimiler un
compteur de sélection d'assemblage à un compteur total de calcul évité.
5. Figer avant le run paramètres, tailles, répétitions, incertitude, limites,
traitement des échecs et seuils de gain. Publier tous les résultats.

Clôture : P8 et S6 sont évalués sur leur vraie portée. L'exécution du protocole
et la publication des coûts sont obligatoires. Un gain temporel n'est annoncé
que si son critère préenregistré réussit ; aucun gain n'est promis. Un coût
défavorable ne réfute pas un théorème, mais ne devient pas une accélération.

### L11 — Prévalider exhaustivement le candidat avant son gel scientifique

1. Exécuter les fixtures locales et la campagne finale, dont la nouvelle
régression d'A1, avec diagnostic, site et obligation précis.
2. Refaire C1–C17, G1–G10 et RC1–RC6 par lecture des énoncés, producteurs,
preuves, transports et consommateurs. Les tests de présence ne suffisent pas.
3. Vérifier tous les blocs d'audit, constantes écrites et dépendances, y compris
les exécutables. Ne pas ajouter d'exception pour contourner un défaut.
4. Exécuter les contrôles de prévalidation : autotests documentaires, build,
audits, frontières d'import, stratification, code généré, fixtures, manifestes
et liens. Diagnostiquer aussi les contrôles documentaires et de snapshot
disponibles, sans confondre leurs échecs avec une réussite. Les contrôles
`--static`, `--lean` et les portails complets devront réussir après le gel
et le raccord du registre en L12, avant l'audit extérieur. Signaler tout
contrôle non exécuté ; aucune vérification obligatoire n'est supprimée.
5. Vérifier le diff et les anciennes preuves, notamment Gödel, Tarski et HA,
sans élargir la tâche à leur modification.

Clôture : les preuves et contrôles de prévalidation sont examinés sans masquer
une obligation par un build vert ou par une autre instance. Ce lot ne déclare
pas fraîches les évidences non encore enregistrées : les gates complètes du
snapshot restent une condition préalable aux audits en L12.

### L12 — Finaliser le claim, les évidences et les audits indépendants

1. Relire séparément FR et EN, puis les confronter aux preuves complètes.
Corriger les descriptions trop larges de l'état actuel sans réduire la cible
à atteindre ni déclarer acquises les obligations encore ouvertes.
2. Vérifier que le texte expose la chaîne conjointe, les trois quantifications,
RC1–RC6, les hypothèses reçues, les limites exactes et le gain effectivement
établi. Une juxtaposition de résultats publics et appris n'est pas le claim.
3. Après autorisation, créer le commit d'évidence stable contenant les sources,
contrôles, textes et matériaux nécessaires. Lier le registre à ce snapshot,
avec des statuts de revue honnêtes. L'enregistrement ne clôt pas C18 à lui seul.
4. Avant toute soumission, faire réussir les gates complètes sur les sources
et textes de cette révision avec le registre raccordé : autotests, `--static`,
build, `--lean`, audits et les deux portails `verify.sh` et `verify.ps1` dans
des environnements disponibles et identifiés. Enregistrer les révisions du
code et du registre effectivement vérifiées. Aucun échec de snapshot ni
contrôle obligatoire non exécuté ne vaut passage de cette étape.
5. Préparer deux examens distincts : validité formelle et conceptuelle, puis
portée comparative et nouveauté. Fournir les sources exactes, toolchain,
dépendances, protocoles, résultats et textes complets, sans substitution.
L'accès à un dépôt distant ne doit pas être l'unique moyen de lire le code.
6. Ne lancer les audits extérieurs qu'après autorisation et réussite de
l'étape 4. Lire leurs rapports intégralement, vérifier révision et portée,
traiter les défauts puis rouvrir
les revues affectées. Un verdict négatif ou inconclusif ne ferme pas la cible.
Toute correction affectant l'évidence exige un nouveau gel, le raccord du
registre et de nouvelles gates avant la revue correspondante.
7. Finaliser les empreintes et références des rapports réellement obtenus,
repasser les gates et distinguer le commit d'évidence des commits de registre.
8. Avant une éventuelle fusion autorisée, retirer les plans temporaires de
chantier, conserver les rapports scientifiques nécessaires et vérifier le
commit fusionné. Ne jamais antidater un audit ni transférer son verdict.

Clôture : C18, les comparaisons et les deux audits requis sont effectivement
fermés sur leurs révisions exactes. Les opérations de publication restent
distinctes de la demande actuelle d'écriture du rapport.

## 7. Couverture comparative à ne pas perdre

Le détail normatif reste dans le rapport antérieur. Les repères suivants
empêchent que les corrections techniques absorbent ou suppriment ce travail.

| Épreuve obligatoire | Où la fermer |
| --- | --- |
| P1 — Contournement latent | L8–L9 : même origine, intention et table, verdict causal et futur non vide |
| P2 — Décodeur ou action modifié | L3, L6, L9 : cas admissible et violation, invalidation et accord avec référence |
| P3 — Contrat modifié | L1, L5–L7, L9 : décision réellement consommée, admission et refus |
| P4 — Oubli et continuation | L4, L8–L9 : oubli positif, non-récupérabilité et distinction future interdite à l'oubli |
| P5 — Contrat après oubli | L4, L7, L9 : transport justifié ou refus, sans récupération fictive |
| P6 — Succession et fragments incohérents | L2, L6–L9 : rejet de versions, occurrences et successeurs étrangers |
| P7 — Intégration et ablations | L9 : méthode relationnelle, combinaison de référence et mécanisme responsable |
| P8 — Échelle et utilité | L10 : mêmes propriétés, graphes et traces pertinents croissants, coûts complets |

R1–R8 restent les références identifiées dans l'étude antérieure : code
auto-modifiant certifié, causalité interventionnelle IIT, ENTRUST, IVAN,
shielding, autorisation des agents évolutifs, succession des autorisations
et hyperpropriétés. Leur mention ici ne constitue pas une nouvelle revue
bibliographique ni la reproduction de leurs artefacts.

S1–S8 restent tous requis : fidélité du corpus, comparabilité sémantique,
comparateurs substantiels, raccord nouveau identifié, séparation utile et
non-vacuité, réutilisation et coût, attribution et reproductibilité, conclusion
scientifique contrôlée. Aucun résultat du présent audit ne les déclare clos.

## 8. Critère final de clôture

La cible n'est atteinte que lorsque toutes les exigences des documents
normatifs sont fermées ensemble. Pour chaque ligne C1–C18, G1–G10 et RC1–RC6,
le dossier final doit identifier :

- l'énoncé complet, ses hypothèses et sa révision ;
- les producteurs, indices, occurrences et consommateurs concernés ;
- les données reçues, calculées, admises, transportées, recalculées et oubliées ;
- les témoins positifs de non-vacuité et les rejets ciblés ;
- les audits d'axiomes et les contrôles réellement exécutés ;
- les correspondances avec le texte et, lorsqu'exigé, les résultats comparatifs.

Restent interdits comme moyens de clôture : renommer une proposition en effet,
afficher un certificat non consommé, substituer les noms d'une instance
canonique, réduire les futurs ou le domaine après observation, définir une
condition par son propre succès, remplacer la chaîne apprise par plusieurs
exemples indépendants, réétiqueter une reconstruction complète comme économie
incrémentale, ou confondre soumission et audit positif.

**État au commit audité : objectif non atteint. Aucun des lots L0–L12 n'est
déclaré terminé par la seule rédaction de ce document.**

## Annexe — Sondes reproductibles de l'audit

Ce client est complet et vise uniquement le snapshot `6cd785a`. Il peut être
fourni à `lake env lean --stdin` depuis la racine de cette révision, sans
ajouter de fichier au dépôt. Il démontre un défaut historique et des limites
de l'instance ; il ne faut pas conserver ces conclusions comme objectifs
positifs de l'implémentation corrigée.

```lean
import RelationalPerimeter.Agents.Neural.LearnedContractFutureDivergence

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
open ConstitutiveSearch.NeuralAgent
open ConstitutiveSearch.ContinuationSignatures

def renamedUpdate : LearnedSerializedConstitutiveUpdate :=
  { learnedAlignedSerializedUpdate with
    targetStableNaming := {
      inputKeys := learnedAlignedSerializedUpdate.targetStableNaming.inputKeys.map
        (fun n => n + 1000)
      neuronKeys := learnedAlignedSerializedUpdate.targetStableNaming.neuronKeys.map
        (fun n => n + 1000)
      outputKeys := learnedAlignedSerializedUpdate.targetStableNaming.outputKeys.map
        (fun n => n + 1000) } }

#eval learnedAlignedSerializedUpdate.targetStableNaming.inputKeys
#eval renamedUpdate.targetStableNaming.inputKeys

#eval match checkGenericIncrementalUpdate learnedIncrementalCheckerEngine renamedUpdate with
  | .error _ => false
  | .ok _ => true

#eval match checkGenericIncrementalUpdate learnedIncrementalCheckerEngine renamedUpdate with
  | .error _ => ([] : List Nat)
  | .ok success => success.checked.next.certificate.structuralObservations.filterMap
      (fun (entry : StableNodeKey × StableArtifactObservation) => match entry.1 with
        | .receivedInput n => some n
        | _ => none)

theorem noLearnedSecondUpdate
    (agent : CheckedAgent learnedConstitutiveMetaContract .aligned)
    (update : LearnedRuntimeUpdate agent) : False := by
  cases update

#eval match submitUpdate learnedInitialCertifiedRuntime (.serialized renamedUpdate) with
  | .error _ => ([] : List Nat)
  | .ok runtime => runtime.current.certificate.structuralObservations.filterMap
      (fun (entry : StableNodeKey × StableArtifactObservation) => match entry.1 with
        | .receivedInput n => some n
        | _ => none)

theorem review_learned_no_refused_request
    (source : IndependentLearnedFutureSource)
    (request : IndependentLearnedFutureInput) :
    independentLearnedFutureContract.enabled source request = true := by
  rfl

theorem review_learned_full_read_forces_network_equality
    {Memory : Type 3}
    (realization : ExactRealization independentLearnedFutureContract Memory)
    {left right : IndependentLearnedFutureSource}
    (same : realization.project left = realization.project right) :
    left.network = right.network := by
  have readSame : independentLearnedFutureContract.read left =
      independentLearnedFutureContract.read right :=
    (realization.read_exact left).trans
      ((congrArg realization.reduced.read same).trans
        (realization.read_exact right).symm)
  exact congrArg IndependentLearnedFutureObservation.network readSame

theorem review_learned_empty_future_already_separates :
    learnedCandidateOperationalFuture learnedAlignedCandidateAtInitial [] ≠
      learnedCandidateOperationalFuture learnedBypassCandidateAtInitial [] := by
  intro same
  let terminalNetwork : LearnedOperationalFutureOutcome → SerializedNetwork
    | .stop observation => observation.network
    | .step _ _ _ _ => independentLearnedInitialNetwork
  have networksEqual := congrArg terminalNetwork same
  have sourceEqual :
      learnedCandidateFutureSource learnedAlignedCandidateAtInitial =
      learnedCandidateFutureSource learnedBypassCandidateAtInitial :=
    congrArg IndependentLearnedFutureSource.mk networksEqual
  apply learnedAlignedBypass_operationalFuture_different
  exact congrArg
    (fun source => LearnedAlignedOperationalContract.futureContract.outcome
      source learnedOperationalCounterfactualRequests) sourceEqual

/- AXIOM_AUDIT_BEGIN -/
#print axioms renamedUpdate
#print axioms noLearnedSecondUpdate
#print axioms review_learned_no_refused_request
#print axioms review_learned_full_read_forces_network_equality
#print axioms review_learned_empty_future_already_separates
/- AXIOM_AUDIT_END -/
```

Sondes rejouées le 23 octobre 2026 depuis cette annexe, avec
`lake env lean --stdin` : sortie sans erreur, listes canoniques, listes
décalées, `true`, retour aux listes canoniques dans le certificat et dans le
runtime. Les cinq déclarations auditées sont sans axiome. Les trois nouvelles
sondes rendent reproductibles les précisions C9–C10 d'A4. Cette reproduction
ciblée n'est pas une nouvelle exécution de l'ensemble des contrôles de la
section 3.
