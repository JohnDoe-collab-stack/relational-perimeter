# Audit et plan de correction de l’alignement constitutif — 0c12baa

## 1. Objet, révision et verdict

Date : 23 octobre 2026. Rapport interne de lecture conceptuelle, technique et
de vérification locale. Il ne constitue pas un rapport indépendant Aristotle.

- Projet : `JohnDoe-collab-stack/relational-perimeter`.
- Branche examinée : `codex/constitutive-neural-alignment-implementation`.
- Commit : `0c12baa313ac2f69fb97a9b26c6dd73809df61e0`.
- Arbre Git : `9ef09c356741b59df91e33b62153770372055263`.
- Tête distante vérifiée identique pendant l’audit.
- Arbre de travail propre avant et après les contrôles de l’audit.
- Le présent fichier est ajouté ensuite. Aucun code, registre, protocole,
  résultat expérimental ou passage canonique n’est modifié par sa rédaction.

**Verdict : la cible terminale n’est pas atteinte. Les contrôles techniques
exécutés réussissent, mais cinq écarts empêchent de conclure à la clôture
constitutive et scientifique demandée.**

Les preuves Lean examinées ne présentent pas d’échec de compilation ou d’axiome
interdit détecté. Le problème principal est différent : plusieurs constructions
correctes existent à côté du chemin installé, sans que celui-ci consomme les
productions dont la cible exige la dépendance. Les comparaisons ne ferment pas
non plus leur contrat de preuve du gain scientifique.

RC1 et RC3 sont respectés dans les interfaces examinées. Le résultat neuronal
RC4 et sa réalisation exacte positive sont présents. **RC2, RC5 et RC6 ne sont
pas conjointement clos.** La livraison indépendante C18 reste ouverte.

Ce rapport complète l’[audit de 8a945f2](AUDIT_ET_PLAN_CORRECTION_ALIGNEMENT_CONSTITUTIF_8a945f2.fr.md).
Il ne lui substitue pas rétroactivement les résultats du nouvel arbre.

## 2. Cible et règles conservées

Les références normatives restent :

- la [cible terminale et RC1–RC6](CIBLE_ALIGNEMENT_CONSTITUTIF_INCREMENTAL.fr.md) ;
- les [critères C1–C18](CONSTITUTIVE_NEURAL_ALIGNMENT_TARGETS.fr.md) ;
- les garanties G1–G10, comparaisons R1–R8, épreuves P1–P8 et critères S1–S8
  du [rapport de référence](RAPPORT_VERIFICATION_ALIGNEMENT_CONSTITUTIF_fafd739.fr.md) ;
- la [méthode scientifique](../methode-de-travail-scientifique.fr.md).

La cible demeure un agent constitutif neuronal dont le runtime fermé consomme
les certificats issus de ses productions, conserve les obligations persistantes,
revérifie celles invalidées et refuse les violations avant effectuation. Le
raccord doit être réalisé sur l’artefact appris indépendant et ses adaptations
successives, pas seulement dans une interface conditionnelle ou des exemples
disjoints.

Trois quantifications distinctes doivent être conservées :

1. toute trace finie de mises à jour acceptées, dépendante de ses successeurs ;
2. toute liste finie de requêtes couverte par le contrat de futurs fixé ;
3. tout type mémoire et toute réalisation exacte de ce contrat, dans les
   univers et paramètres de l’API déclarée.

Aucune ne remplace les deux autres. Les exemples positifs garantissent la
non-vacuité, sans limiter le théorème générique à leur longueur.

L’alignement demandé ne reçoit aucune exigence supplémentaire de valeurs
humaines. Gödel n’est ni une prémisse, ni une étape obligatoire du raccord
neuronal. Aucun quotient canonique, aucune injectivité globale, aucune
réversibilité des transports dirigés et aucune accélération universelle ne
sont ajoutés. Les preuves Gödel, Tarski et HA existantes sont à préserver.

Pour chaque correction, documenter séparément : ce qui indexe les types,
ce qui produit les données, ce que la preuve consomme et ce que le transport
conserve ou oublie. Une égalité prouvée n’est pas une preuve que le programme
installé a exécuté le producteur ainsi nommé.

## 3. Acquis de cette révision à préserver

Les défauts des rapports précédents ne doivent pas être reconduits lorsqu’ils
ont effectivement été corrigés.

1. L’action est désormais calculée une fois dans le producteur de transition
   appris. `LearnedEffectWitness` est indexé par cette action exacte et le
   producteur d’effet la consomme. Le contrôle du code généré correspondant
   passe. Ce partage ne ferme cependant pas l’origine du programme exécuté.
2. Le constructeur incrémental générique consomme les observations de
   l’assemblage structurel. L’ancien assemblage seulement stocké n’est plus le
   défaut générique à corriger. Le raccord de la seconde installation reste
   distinct de cet acquis.
3. Des reconfigurations non identitaires et leur composition sont construites.
   Leur existence n’est pas contestée. Leur consommation par l’installation
   réelle constitue F1.
4. Deux mises à jour positives sont installées dans la lignée apprise. Le
   nommage stable accepté, y compris la variante renommée, est conservé.
5. Des conditions locales autonomes remplacent les anciennes définitions
   identiques au succès du checker global. Le chemin incrémental de la famille
   de mesure n’appelle plus `checkInitial` comme préalable complet.
6. Le théorème
   `learnedEveryExactRealizationSeparatesAlignedFromBypass` construit
   l’obligation universelle de séparation sous le contrat fixé. La distinction
   n’est pas un champ supposé d’`ExactRealization`. Une réalisation exacte
   positive est construite. Le séparateur neuronal non vide et l’égalité des
   observations immédiates sont conservés.
7. L’oubli depuis deux origines historiques distinctes, la préservation de tous
   les futurs couverts et la non-récupérabilité de l’origine depuis la mémoire
   réduite sont établis. F3 concerne leur continuation installée, pas l’absence
   de ces preuves.
8. Les théorèmes génériques sur les traces acceptées, les refus et les états
   accessibles restent disponibles. Les contrôles officiels, les audits
   d’axiomes, les frontières et la couverture des exécutables passent.
9. Les résultats v10 et v11 existent désormais. Leur absence n’est plus un
   constat actuel. Le résultat temporel défavorable de v11 est explicitement
   conservé dans le dépôt.

## 4. Constats bloquants et preuves de localisation

Les lignes indiquées ci-dessous désignent uniquement la révision `0c12baa`.
Les sondes Lean de l’annexe permettent de reproduire les points structurels
sans modifier les sources de production.

### F1 — La reconfiguration construite ne produit pas le programme installé

Source : [LearnedRuntimeAdapter.lean](../../RelationalPerimeter/Agents/Neural/LearnedRuntimeAdapter.lean).

`buildLearnedReconfiguredSystem`, ligne 1299, construit bien un système à partir
du run source, de la nouvelle exigence, du contexte et de l’autorisation.
Les constructions de reconfiguration et de composition associées existent.

Mais `learnedAlignedActionSourceStateFor`, ligne 1691, fixe directement :

```lean
{ system := learnedDecodedAlignedArtifact.system
  input := independentLearnedCertifiedInput
  memory := memory }
```

`produceLearnedTransitionData`, ligne 2539, transmet seulement
`current.state.memory` à l’action alignée ou étendue, puis partage correctement
cette action avec le producteur d’effet. Il ne consomme pas la reconfiguration
calculée depuis le système du `current` reçu. La preuve
`learnedAlignedReconfiguredProposalDerivation.proposal_exact` intervient dans
la préservation, mais n’est pas ce producteur exécuté.

Le code C généré confirme cette distinction : la construction de l’état source
charge l’artefact cible fixe ; le producteur de transition extrait la mémoire
courante, pas son système pour produire la reconfiguration.

`LearnedExecutedStateTransition`, ligne 2424, accepte aussi un état courant
arbitraire avec cette dépendance limitée à la mémoire. La sonde A construit
une transition après substitution du programme antérieur et prouve que ce
programme diffère. **Cela montre une relation interne trop faible pour la
dépendance causale revendiquée, pas une attaque démontrée contre `submitUpdate` :
la sonde ne fournit pas un agent courant adversarial certifié à cette API.**

Enfin, `learnedAlignedRequiredMechanismTransport`, ligne 1403, désigne le port
et le rôle de contexte comme ressource source avec une égalité réflexive.
Réutiliser un rôle n’est pas interdit en soi. Cela ne ferme C5/G3 que si sa
provenance et son intervention dans le producteur requis sont établies, et
non seulement son égalité avec une valeur du contexte.

**Correction :** faire consommer à l’action le programme produit par la même
reconfiguration exécutée de l’agent courant et l’entrée reçue ou produite qui
lui est effectivement associée. Consommer les ressources prescrites, puis cette
action exacte, cet effet exact et ce successeur exact. Conserver les
transformations déjà prouvées et le partage action–effet. Cela n’oblige pas à
présenter une entrée légitimement reçue comme une donnée produite.

**Clôture :** raccord producteur–consommateur vérifié dans les types, les corps
de définition et le code compilé. Mutations de source, exigence, contexte et
autorisation testées au point réel de consommation. C3–C7, G2/G3, RC2/RC5.

### F2 — Le nouveau checker successif n’alimente pas la seconde installation

Sources : [LearnedRuntimeAdapter.lean](../../RelationalPerimeter/Agents/Neural/LearnedRuntimeAdapter.lean)
et [AutonomousCheckerClosure.lean](../../RelationalPerimeter/Agents/Neural/AutonomousCheckerClosure.lean).

`learnedSuccessiveIncrementalCheckerEngine`, ligne 151 du second fichier,
construit une analyse successive avec transport de fragments et référence
complète indépendante. C’est un acquis réel.

Le chemin utilisé par le runtime reste cependant différent :

- `learnedReceivedExtendedCheckedUpdateForArtifact`, ligne 4118, élimine
  `target = learnedDecodedExtendedArtifact`, puis retourne la constante
  `learnedExtendedCheckedUpdate` ;
- `checkDecodedLearnedExtendedSerializedUpdate`, ligne 4184, décide la
  transition, reçoit `some _decision`, vérifie des gardes, puis retourne ce
  résultat canonique transporté ;
- la branche `.successive` du checker dépendant utilise ce chemin, pas
  `learnedSuccessiveIncrementalCheckerEngine`.

Les gardes sont exécutées et les égalités sont correctes. Le problème n’est
donc pas « aucune vérification ». C’est que les données décodées, la décision
reçue et l’assemblage successif nouveau ne produisent pas le certificat installé
par ce chemin. Le C généré confirme le retour de la constante canonique et
l’abandon des données intermédiaires concernées. La sonde B rend ce retour
canonique explicite comme égalité de résultats ; la dépendance exécutée est
établie par la lecture des définitions et du code généré, pas par cette égalité
seule.

Le moteur auxiliaire ne peut pas non plus être branché tel quel.
`LearnedSuccessiveEngineAnalysis.target`, ligne 76
d’`AutonomousCheckerClosure.lean`, transmet la décision reçue à
`learnedSuccessiveTargetAnalysisFromDecision`, ligne 29. Cette dernière
construction fixe encore `artifact := learnedDecodedExtendedArtifact`,
`state := learnedExtendedState` et `targetNaming := learnedExtendedStableNaming`.
Les sondes E de l’annexe vérifient ces trois égalités pour toute analyse de
cette interface. La lecture de ces corps de définition localise le défaut de
consommation, même si les gardes restreignent les entrées admises au cas
canonique. Les données décodées et les productions doivent alimenter l’analyse
cible elle-même, pas seulement autoriser son retour.

**Correction :** corriger d’abord le producteur de l’analyse successive pour
consommer l’agent courant réel, le décodage reçu, la transition décidée et les
productions correspondantes. Construire ensuite son certificat depuis les
fragments effectivement transportés/recalculés, puis raccorder ce chemin au
checker dépendant appelé par le runtime et vérifier son installation.
Réorganiser les modules si leur sens d’import empêche ce raccord, sans
maintenir deux API concurrentes. Un simple changement du moteur appelé ne
ferme pas F2.

**Clôture :** seconde installation issue de cet assemblage ; correction,
complétude relative et équivalence au recheck sur le domaine successif annoncé.
Ne pas remplacer ces propriétés par l’égalité d’un seul exemple canonique.
Ne pas exiger l’acceptation de réseaux arbitraires hors du domaine déclaré.
G7/G8, RC2/RC5.

### F3 — Après oubli, une permission n’est pas encore une transition installée

Sources : [AutonomousContractTransitions.lean](../../RelationalPerimeter/Agents/Neural/AutonomousContractTransitions.lean),
[AutonomousCheckerClosure.lean](../../RelationalPerimeter/Agents/Neural/AutonomousCheckerClosure.lean)
et [LearnedFutureConstitutiveClosure.lean](../../RelationalPerimeter/Agents/Neural/LearnedFutureConstitutiveClosure.lean).

`ForgottenCurrentAgent`, `JustifiedPostForgettingTransition` et
`PostForgettingPermission` distinguent correctement mémoire réduite,
justification du transport et admission de la continuation. Le commentaire
du premier fichier, ligne 335, précise justement que ces objets ne sont pas
encore une opération runtime effectuelle.

`checkLearnedPostForgettingIncremental`, ligne 467 du deuxième fichier,
retourne une `PostForgettingPermission`. La référence complète retourne le
même genre d’objet. Les conditions d’admission sont autonomes, mais aucune
installation après oubli ne consomme ici cette permission pour produire un
`CheckedUpdate`, un nouvel état installé et sa trace.

Le paquet conjoint relie des données de lignée et des résultats d’oubli ;
stocker les deux ne construit pas la transition contractuelle effective
après réduction. Les deux requêtes positives ne remplacent pas la correction
et la complétude relative sur le domaine de demandes annoncé.

**Correction :** intégrer la continuation et le changement de contrat après
oubli dans le runtime contrôlé existant. Consommer les obligations persistantes,
revérifier celles invalidées avant effectuation, puis installer le successeur
produit, ou refuser sans successeur.

La continuation ordinaire sous contrat inchangé n’a pas à devenir
artificiellement une transition de méta-contrat. En revanche, P5 doit exercer
un véritable changement de contrat après réduction mémoire.

**Clôture :** cas admis installé, cas injustifié refusé, accessibilité et
préservation établies sur la même lignée. La non-récupérabilité porte sur la
mémoire réduite seule : conserver un historique d’audit est permis, mais ne
doit pas servir d’oracle caché pour une garantie annoncée depuis cette mémoire.
G1/G4/G5/G6, RC5/RC6, P5.

### F4 — La succession de la famille mesurée est plus faible que la cible

Source : [ParameterizedCompiledCheckerFamily.lean](../../RelationalPerimeter/Agents/Neural/ParameterizedCompiledCheckerFamily.lean).

Les sept familles d’obligations d’état ont désormais du contenu. Il serait
faux de les décrire toutes comme `Unit`. L’analyse incrémentale ne réintroduit
pas non plus le recheck complet comme préalable.

Mais `scalingMetaContract`, ligne 852, définit :

```lean
ExecutedStateTransition := fun _ _ _ => ScalingUnit4
```

Et `scalingTransitionKernel`, ligne 870, a une production unitaire et un
`targetOf` qui renvoie l’état cible reçu. La sonde D certifie ainsi une
transition entre deux états quelconques. `scalingState`, ligne 778,
réinitialise en outre la mémoire avec `publicActionMemory`.

La trace transmet bien un `next` à l’étape suivante. Cela ne suffit pas à
certifier la production causale de ce `next` depuis le précédent lorsque la
relation d’exécution ignore cette dépendance. Le fait que `Contract := Unit`
n’est pas, à lui seul, un défaut : une famille à contrat unique est légitime.
L’écart porte sur la succession et la propriété complète mesurée.

La [campagne v11](../../experiments/constitutive-neural-alignment/v11/SCALING_ANALYSIS.md)
contient 25 répétitions acceptées sur 25, avec tailles 0, 4, 8, 16, 32 et
longueurs 3, 6, 9, 12, 15. Les rapports médians incrémental/recheck sont
respectivement 3,76 ; 15,25 ; 44,54 ; 181,51 ; 1 056,52. Le critère pratique
préenregistré vaut `false`. Ces résultats ont été contrôlés, pas remesurés
pendant cet audit.

**Correction :** mesurer une famille dont la propriété inclut la production
effective des transitions et la consommation des états, actions et effets
requis. Les obligations pertinentes doivent croître avec les tailles et traces,
pas uniquement des dimensions périphériques. Le recheck indépendant doit
vérifier la même propriété.

**Clôture :** nouvelle version de protocole gelée avant nouvelle campagne,
mesures appariées du checker compilé et du recheck, coûts complets, fragments
transportés/recalculés et résultats négatifs conservés. Une famille générée
reste autorisée ; elle ne remplace pas l’artefact appris indépendant.
Le résultat v11 ne prouve aucune économie et ne doit pas être requalifié.
Il n’invalide pas les preuves Lean, ni n’impose une nouvelle exigence de
supériorité asymptotique. G2/G4/G8, P8, S2/S6/S7.

### F5 — La comparaison utilise son propre système comme oracle et imprime des verdicts constants

Sources : [CompleteCapabilityComparison.lean](../../RelationalPerimeter/Agents/Neural/CompleteCapabilityComparison.lean),
[exécutable de comparaison](../../Tests/Executables/CompiledCompleteNeuralComparison.lean),
[protocole v10](../../experiments/constitutive-neural-alignment/v10/comparison-protocol.json)
et [contrôle v10](../../scripts/check-neural-complete-comparison-v10.py).

#### F5a — Indépendance de la combinaison de référence

Le protocole interdit à la combinaison de référence d’appeler le checker
constitutif final ou de recevoir son certificat cible comme oracle.

Or `runReferenceCombination`, ligne 144, utilise
`learnedAlignedRuntimeSubmissionDecision` et
`learnedBypassRuntimeSubmissionDecision`, lignes 107 et 112. Ces définitions
appellent `submitUpdate`, donc le checker constitutif du runtime comparé.
Cette dépendance est établie par leurs corps de définition et confirmée par
les appels et consommateurs du code C généré. La sonde C démontre l’égalité
de la décision obtenue avec celle du runtime ; elle ne démontre pas, à elle
seule, la provenance opérationnelle de cette décision. Le commentaire qui
nie l’appel au checker final doit être corrigé avec l’implémentation.

Le contrôle statique ne recherche que certains noms, notamment
`learnedConstitutiveAlignmentClosure`. Il ne suit pas ce chemin transitif.
Son succès ne certifie donc pas l’indépendance annoncée.

**Correction :** construire la combinaison depuis ses vérifications propres
et les données communes autorisées. Des primitives sémantiques partagées et
des contrôles élémentaires indépendamment spécifiés restent légitimes.
Le verdict final de la méthode évaluée ne l’est pas. Contrôler les dépendances
transitives, avec mutation qui tente de réintroduire cet oracle indirect.

#### F5b — Résultats exécutés et conséquences de preuves

L’exécutable imprime littéralement plusieurs résultats : installation/refus
et contrats préservés ligne 49, `reuse_claimed` ligne 56,
`all_steps_checked` ligne 59, résultats relationnels lignes 62–64,
correspondance du successeur et absence d’oracle ligne 98.

Certains sont des conséquences de théorèmes vrais. Les imprimer comme
constantes n’en fait pas des observations recalculées par ces lignes IO.
La distinction est nécessaire pour une campagne confirmatoire.

**Correction :** calculer les observations annoncées depuis les sorties
réellement exécutées ; identifier séparément les propriétés dérivées de preuves
avec leurs déclarations et révision. Vérifier le raccord entre chaque ligne
émise, le producteur concerné et la cellule P1–P8 correspondante.

Les neuf lignes de résultats v10 et les 63 cellules de la matrice sont des
matériaux existants à conserver. Leur nombre ne prouve ni l’indépendance des
comparateurs ni la couverture effective de toutes les épreuves. En particulier,
une continuation après oubli ne remplace pas P5, qui change le contrat.

**Clôture F5 :** combinaison réellement indépendante, recheck indépendant
distinct, observations calculées et preuves identifiées, traductions fidèles,
mêmes informations et propriétés sur le périmètre commun, puis nouvelle
campagne préenregistrée. Les adaptateurs locaux ne prouvent pas à eux seuls
l’équivalence avec les classes complètes de méthodes extérieures. Leur succès
ou celui des concurrents doit rester visible. P1–P8, S1–S8, C15/C18.

## 5. État explicite de RC1–RC6

Cette table applique les définitions du plan normatif, sans les remplacer.

| Obligation | État à 0c12baa | Critère de clôture ou de conservation |
| --- | --- | --- |
| RC1 — Origine déclarée | Respectée dans les interfaces examinées. | Primitives, exigences, contextes, schémas et admissions reçus identifiés avant leurs conclusions. Aucune norme reçue présentée comme justifiée par l’exécution. |
| RC2 — Instanciation authentique | Non close : F1 et F2. | Obligations `…At state`, occurrences, producteurs et consommateurs raccordés au même run maître jusqu’au certificat installé. Ni champ stocké ni résultat reconstruit indépendamment. |
| RC3 — Indépendance de la réalisation | Préservée dans les obligations sources examinées. | Schéma fixé indépendamment de la projection candidate et du succès du contrôle. Certificats antérieurs justifiés et réflexion de décisions autonomes restent autorisés. Les paramètres déclarés ne sont pas effacés. |
| RC4 — Conséquences générales démontrées | Théorème neuronal et réalisation positive présents. | Préserver le contrat fixé, ses sources issues de la production et la quantification sur toute mémoire et toute réalisation exacte. Refaire le raccord aux producteurs corrigés s’ils changent. La séparation demeure une conclusion certifiée, jamais un champ supposé. |
| RC5 — Transport au fil des transformations | Non close : F1–F3, et F4 pour la propriété mesurée. | Consommation effective à travers transformation, décodage, action, effet, successeur, mémoire et contrat. Transport des obligations persistantes, revérification des invalidées avant effet. |
| RC6 — Réalisations positives et prévention | Composants présents, raccord conjoint non clos. | Même lignée apprise, transformations non identitaires, adaptations successives, oubli et continuation contrôlée, réalisation exacte positive et acceptation/refus par la même API. |

L’indépendance du comparateur F5 n’est pas une redéfinition de RC3. RC3 porte
sur les obligations sources et la réalisation à examiner ; F5 porte sur la
validité de la comparaison scientifique. Les deux doivent être vérifiés.

## 6. Ordre obligatoire de correction

La numérotation L0–L12 conserve celle des rapports précédents. Il ne s’agit
pas de recommencer les éléments déjà corrects. Chaque lot reçoit immédiatement
ses preuves, tests positifs et mutations négatives au point sémantique concerné.
Les contrôles finaux ne remplacent pas ces tests locaux.

Ordre de dépendance : schémas et état courant → données reçues/décodées →
production effective → obligations et futurs → certification complète →
assemblage incrémental → installation → instance conjointe → expériences
comparables → livraison. Les futurs et la séparation déjà construits sont
préservés puis raccordés, non repoussés après la certification.

### L0 — Préserver la référence et rouvrir exactement les obligations concernées

1. Conserver `0c12baa`, les audits historiques et les résultats v10/v11.
2. Répertorier F1–F5, les acquis de la section 3 et leur portée dans le suivi
   de travail. Ne pas annoncer C1–C18/G1–G10/RC1–RC6 clos parce que les gates passent.
3. Préserver les interfaces génériques correctes, les preuves diagonales et
   les contrôles d’axiomes, d’imports, de stratification et de code compilé.
4. Dater la réévaluation des statuts surévalués. Ne pas réécrire le passé ni
   actualiser mécaniquement les empreintes du registre.

Sortie : référence reproductible et défauts localisés. Aucun commit, push,
changement de branche ou audit extérieur n’est autorisé par ce document seul.

### L1 — Fixer les obligations autonomes et les transitions depuis l’agent courant

1. Cartographier les entrées reçues, le contrat opérationnel, `…At state`,
   `futureContract` et `futureSourceOfState`, avec leurs producteurs/consommateurs.
2. Spécifier la reconfiguration à partir du système source exécuté, de la
   nouvelle exigence, du contexte et de l’autorisation effectivement requis.
3. Conserver les obligations indépendantes de la réalisation à valider et du
   succès de leur propre contrôle. Ne pas choisir un contrat après le verdict.
4. Prévoir dans les interfaces existantes les transitions après oubli :
   continuation, changement de contrat justifié, revérification ou refus.
5. Fixer le domaine courant fini d’observation et la base finie d’interventions
   pour chaque port contrôlé. La complétude reste relative aux conditions
   décidables déclarées sur ce domaine et cette base. Cela n’impose pas que
   l’ensemble des artefacts ou des mises à jour sérialisées soit fini et ne
   limite pas la longueur des traces ni des futurs couverts. Ne pas réduire
   le domaine après coup pour faire disparaître une obligation requise.

Sortie : RC1/RC3 explicites et conditions sources autonomes. Pas de seconde API.

### L2 — Faire circuler le décodage exact et les identités de versions

1. Conserver la sérialisation complète et les variantes de nommage acceptées.
2. Relier programme, encodage, poids, arêtes, ports, décodeur, autorisation,
   mémoire et contrat au matériel réellement reçu, puis décodé.
3. Préserver identifiants stables et correspondances de versions requises,
   distincts des positions `Fin`, avec invalidation des fragments non transportables.
4. Donner aux analyses successives le décodage et l’agent courant exacts.
   Ne pas remplacer leur sortie par une constante canonique après acceptation.

Sortie : données reçues identiques aux données certifiées et installées.
Tests : version incohérente refusée, renommage valide conservé, substitution
de source ou de nommage détectée au bon point, sans rejet d’un cas légitime.

### L3 — Raccorder la reconfiguration à la production de l’action et du successeur

1. Réutiliser les constructions non identitaires existantes et leur composition.
2. Faire consommer au chemin installé la reconfiguration issue du run courant.
   Dériver la proposition depuis cette production, pas seulement une égalité
   avec la proposition d’un programme cible fixé indépendamment.
3. Établir les interventions des ressources prescrites du système antérieur,
   de l’exigence, du contexte et de l’autorisation. Ne pas retoucher les poids
   appris pour obtenir les témoins voulus.
4. Conserver une seule action et un seul effet partagé ; raccorder événement,
   mémoire et successeur à cet effet. Corriger les branches alignée et étendue.
5. Examiner le code compilé du chemin effectivement appelé, pas seulement
   celui du producteur auxiliaire correct.

Sortie : F1 fermé, G2/G3 et RC2/RC5 effectifs. Les mutations doivent viser les
consommateurs réels. Une dépendance au système antérieur ne doit pas se réduire
au fait de copier sa mémoire. Une intervention ne doit pas imposer une
sensibilité à des données que le contrat autorise réellement à oublier.

### L4 — Conserver les futurs exacts et produire la mémoire réduite consommable

1. Raccorder `futureSourceOfState` aux états de L3 et conserver RC4.
2. Maintenir l’égalité immédiate aligné/contournement, le séparateur non vide,
   les requêtes admises/refusées et la réalisation exacte positive.
3. Préserver l’oubli exécuté depuis deux origines historiques distinctes,
   la réduction non triviale, tous les futurs couverts et la non-récupérabilité.
4. Fournir à la continuation contrôlée la mémoire réellement réduite et les
   ressources explicitement conservées. Déclarer les obligations transportables
   et celles à revérifier lors d’un changement de contrat.

Sortie : producteurs de futurs et d’oubli raccordés. Leur installation est
fermée en L7. Ne pas demander de fusionner les sources que le même contrat
exact oblige à distinguer, ni d’effacer les archives de preuve.

### L5 — Fermer les checkers complets autonomes sur les domaines requis

1. Construire les certificats depuis les entrées sans certificat cible,
   le décodage, la production et les décisions locales réfléchies.
2. Raccorder le recheck complet à l’agent courant pour la seconde adaptation
   et les transitions après oubli effectivement requises.
3. Prouver correction et complétude relative aux conditions autonomes sur
   ces domaines. Deux requêtes positives ne remplacent pas ces énoncés.
4. Garder le recheck indépendant du verdict et des fragments incrémentaux.
   Une sémantique d’exécution commune reste permise.

Sortie : référence complète de G7, sans oracle ni décidabilité universelle
ajoutée. Les simulations de vérification restent pures avant acceptation.

### L6 — Faire consommer l’assemblage incrémental dans les étapes successives

1. Préserver l’assemblage générique corrigé et le premier chemin incrémental.
2. Corriger d’abord le producteur de l’analyse cible du moteur successif.
   Faire consommer l’agent courant, le décodage exact, le nommage reçu, la
   décision et la production de transition, au lieu de fixer à nouveau
   l’artefact, l’état et le nommage canoniques après les gardes.
3. Calculer le cône causal hétérogène sur réseau, décodeur, action, effet,
   successeur, mémoire et contrat. Transporter les fragments hors cône depuis
   le certificat source réel et recalculer ceux invalidés.
4. Construire le certificat à installer depuis cet assemblage. Ne pas restaurer
   un snapshot cible ou appeler un recheck complet caché sous l’étiquette locale.
5. Brancher ensuite ce moteur corrigé sur le chemin dépendant appelé par
   `submitUpdate`. Vérifier que le certificat et le successeur réellement
   installés sont ceux retournés par ce chemin, sans reconstruction canonique.
6. Prouver l’accord d’acceptation et du successeur avec L5 sur la même propriété.
   Conserver un cas local à transport non vide et un cas étendu recalculé.

Sortie : F2 fermé, G8 et RC5 consommés. Vérifier les dépendances compilées et
les substitutions à l’assemblage. Un cône entièrement affecté peut légitimement
entraîner une revérification complète ; il doit être annoncé comme tel.
L’ordre interne est : production depuis les données reçues, assemblage
consommé, branchement au runtime, puis vérification de l’installation.

### L7 — Installer les transitions, y compris après oubli, par le runtime fermé

1. Faire consommer chaque `CheckedUpdate` produit par L5/L6 par l’API existante.
2. Faire partir chaque étape du `next` exact renvoyé par la précédente.
3. Après réduction mémoire, exécuter une continuation admise et le changement
   de contrat requis : transport justifié ou recheck avant installation.
4. Refuser les demandes injustifiées sans action effective ni successeur
   installé. Prouver accessibilité et conservation sur toutes les traces acceptées.
5. Préserver les trois quantifications et leurs indices, sans borne artificielle.

Sortie : F3 fermé ; P3/P5/P6 exercés par de véritables transitions et refus,
pas seulement des permissions. Aucun chemin public d’effectuation ne contourne
le certificat. L’historique conservé ne devient pas un oracle non déclaré.

### L8 — Fermer le témoin appris conjoint et la prévention du contournement

1. Réutiliser l’artefact appris indépendant et ses preuves de provenance.
   Un nouvel apprentissage n’est requis que si une raison scientifique l’impose.
2. Réunir les transformations, rôles causaux, adaptations successives, assemblages,
   oubli et continuation installée sur la même lignée de productions.
3. Conserver, depuis le même agent et la même intention admise, l’équivalence
   des sorties courantes aligné/contournement sur tout le domaine canonique.
4. Faire accepter l’aligné et refuser le contournement par la même API pour la
   dépendance manquante. Préserver le futur non vide qui en certifie la pertinence.
5. Construire le certificat conjoint depuis ces consommateurs communs, pas
   comme collection de preuves de constructions séparées.

Sortie : G1–G10 et RC1–RC6 fermés ensemble. Les variantes positives empêchent
la vacuité par refus universel. Les programmes refusés restent simulés purement.

Avant toute nouvelle production confirmatoire, geler son protocole, les entrées,
graines, scripts, traductions, paramètres, critères et révisions. Les sorties
reçoivent leurs empreintes après production. Les essais préalables restent
exploratoires. Cette règle s’applique aussi à L9/L10, sans réécrire v10/v11.

### L9 — Corriger l’indépendance et la fidélité de la comparaison de capacité

1. Fermer F5a : vraie combinaison de référence, sans appel direct ou transitif
   au verdict final de la méthode évaluée ni certificat cible fourni comme oracle.
2. Fermer F5b : résultats calculés depuis les sorties du run ; propriétés
   issues de preuves identifiées comme telles et non transformées en mesures.
3. Conserver les six classes, la méthode relationnelle, la combinaison et
   le recheck. Examiner R1–R8 selon leurs textes et hypothèses exacts.
4. Donner aux comparateurs les informations pertinentes et traductions
   admissibles. Ne pas les réduire arbitrairement à une table de sorties.
5. Raccorder chaque cellule P1–P7 aux opérations et obligations réellement
   exercées. P5 doit changer le contrat après oubli. Exécuter les ablations
   autorisées dans le harnais de test, jamais comme contournement de l’API livrée.
6. Geler une nouvelle version avant la campagne corrigée et publier aussi les
   succès des références, échecs, coûts de traduction et limites des adaptateurs.

Sortie : comparaison reproductible et équitable. Un adaptateur local manquant
ou moins puissant ne prouve pas l’incapacité d’une méthode extérieure.
Le gain résiduel reste à établir, pas à présupposer.

### L10 — Mesurer la propriété complète et la réutilisation réelle à l’échelle

1. Remplacer la relation de succession unitaire par la production effective
   des transitions exigée en F4, en réutilisant les interfaces corrigées.
2. Faire croître les graphes pertinents, obligations et traces, avec adaptations
   légitimes acceptées, cônes locaux et étendus. Préserver le partage réel des
   productions et la consommation du successeur.
3. Confronter incrémental et recheck indépendant sur la même propriété, les
   mêmes données, arithmétiques et conditions de cache déclarées.
4. Geler la nouvelle campagne puis mesurer coûts initiaux/cumulés, mémoire,
   certificats et fragments transportés/recalculés, sans omettre décodage,
   analyse, correspondances de versions ou autres coûts nécessaires.
5. Conserver intégralement v11 et son critère pratique non satisfait.
   Toute nouvelle revendication d’économie doit respecter ses propres marges
   et règles d’incertitude préenregistrées, jamais ajustées après les résultats.

Sortie : F4 fermé, P8 réellement exécutée et S6 évalué sur la propriété cible.
Le transport de fragments est une propriété distincte du gain temporel.

### L11 — Refaire la revue conjointe et toutes les régressions

1. Examiner chaque C1–C17, G1–G10 et RC1–RC6 avec énoncé complet, hypothèses,
   producteur, consommateur, preuve, contrôle compilé et fixture correspondants.
2. Réexécuter les commandes de la section 8 sur le nouvel arbre. Auditer les
   déclarations nouvelles et leurs dépendances, pas seulement les noms publics.
3. Vérifier les mutations au diagnostic et au site attendus. Une erreur de
   type incidente avant l’obligation visée ne constitue pas son test négatif.
4. Vérifier aucune régression des acquis de la section 3, des interfaces
   génériques et des preuves Gödel/Tarski/HA.
5. Relire séparément les textes français et anglais, puis confronter leurs
   affirmations aux preuves et exécutions. Dater les changements de statut.

Sortie : prévalidation interne étayée, sans anticiper un verdict indépendant.

### L12 — Livrer l’évidence scientifique et les deux examens indépendants

1. Fixer le claim exact et sa portée depuis les résultats de L0–L11.
2. Avec autorisation humaine, créer la révision d’évidence stable et exécuter
   les gates sur cette révision. Fournir sources, dépendances, outil Lean,
   manifestes, commandes, protocoles, résultats et textes complets à auditer.
3. Faire examiner indépendamment la validité, les hypothèses, dépendances et
   correspondances texte/preuve, puis le gain comparatif et la nouveauté dans
   le corpus déclaré. Les deux conclusions doivent rester distinctes.
4. Lire les rapports complets et vérifier leur révision et leur périmètre.
   Toute modification pertinente rouvre la revue correspondante.
5. Enregistrer les états et empreintes après revue effective, pas pour faire
   disparaître une alerte. Finaliser FR/EN, liens, manifeste et gates de livraison.
6. Avant une éventuelle intégration autorisée dans `main`, retirer ou convertir
   les documents temporaires de chantier selon la procédure, puis vérifier
   le commit intégré. Ne pas supprimer l’évidence historique à conserver.

Sortie : C18 réellement fermé et gain scientifique évalué. Une soumission
acceptée, un build vert ou le présent rapport ne vaut pas verdict indépendant.
Les verdicts positifs exigés restent des conditions de réussite, pas des promesses.

## 7. Couverture sans omission ni ajout de cible

| Exigences existantes | Lots et points de contrôle |
| --- | --- |
| C1, C6 ; G4/G5 | L1, L5–L7, L11 : toutes traces acceptées, source courante exacte, accessibilité, refus avant effet. |
| C2–C7, C11 ; G2/G3 | L2–L3, L6–L8 : transformations exécutées, rôles requis, proposition, autorisation, action, effet et successeur partagés. |
| C8–C10 ; G6 ; RC4 | L4–L7 : oubli historique exécuté, réduction, réalisation exacte, tous futurs couverts, contraintes universelles. |
| C12 ; G9/G10 ; RC6 | L8 : instance apprise substantielle, adaptations positives, contournement latent et même API. |
| G1/G7/G8 ; RC1–RC3/RC5 | L1–L7 : méta-contrat, décisions autonomes, décodage, transports et rechecks réellement consommés. |
| C13–C17 | Chaque lot puis L11 : vocabulaire, décomposition, fixtures, non-régression, build et audits complets. |
| R1–R8 ; P1–P7 | L9 : corpus, comparateurs substantiels, correspondances, opérations effectivement exercées et ablations. |
| P8 ; S6 | L10 : succession complète à l’échelle, coût total et accord au recheck, sans gain inféré des seuls compteurs. |
| S1–S5/S7/S8 ; C18 | L9–L12 : fidélité, équité, capacité conjointe résiduelle, attribution, reproductibilité et examens indépendants. |

Les protocoles gardent les identifiants P1–P8 : contournement latent ; changement
de décodeur/action ; changement de contrat ; oubli et futurs ; contrat après
oubli ; versions/successeurs/fragments incohérents ; intégration/ablations ;
échelle et utilité. Une ligne de matrice n’est pas la réalisation de l’épreuve.

Les critères S1–S8 restent : fidélité du corpus, comparabilité sémantique,
comparateurs substantiels, raccord nouveau identifié, séparation utile et
non-vacuité, réutilisation/coût, attribution/reproductibilité, conclusion
scientifique contrôlée. La présence de ces critères ne garantit pas leur
verdict. Un résultat négatif ou inconclusif doit rester déclaré.

## 8. Contrôles effectivement obtenus sur 0c12baa

Ces résultats proviennent de la phase d’audit précédant la rédaction du présent
fichier. Ils ne sont pas annoncés comme une nouvelle campagne expérimentale ni
comme un audit extérieur. Les sorties sont celles de la session de vérification ;
ce rapport ne prétend pas créer à lui seul une archive complète des journaux.

| Contrôle | Résultat obtenu |
| --- | --- |
| `scripts/verify.ps1` | Réussite, code retour 0. |
| `scripts/verify.sh` sous Git Bash | Réussite, code retour 0. |
| `lake build`, inclus dans les vérifications | 468 tâches, réussite sans erreur ni avertissement rapporté. |
| Sources Lean et blocs `AXIOM_AUDIT` | 466 fichiers contrôlés, contrôles de mécanismes interdits réussis. |
| `lake env lean Tests/AllConstantsAudit.lean` | `constants=42465 modules=460 generatedExceptions=478 writtenExceptions=0`. Ne pas transformer cela en « aucune exception » : les exceptions générées sont distinguées des exceptions écrites. |
| Couverture des exécutables | Union de 466 modules pour cinq racines, 462 modules par racine. |
| Fixtures négatives | 165/165, classes et sites attendus, sans erreurs supplémentaires. |
| Stratification et frontières d’import | 366 modules de production contraints, contrôles réussis. |
| Contrôles de code généré | Cinq contrôles réussis, dont partage action–effet et consommation d’assemblage. Leur périmètre ne couvre pas automatiquement F1–F5. |
| Registre, `--self-test` | 7/7. |
| Registre, `--static` | 24 affirmations, 262 déclarations, réussite. |
| Registre, `--lean` | 197 déclarations publiques et 65 tests, réussite. |
| Contrôles v10 | Protocole/résultats et sept mutations contrôlés. Ne détectent pas l’oracle transitif de F5. |
| Contrôle v11, `--require-results` | Résultats présents, empreintes et agrégations vérifiées. Aucun nouveau run confirmatoire. |
| Sondes initiales A–D de l’annexe | Cinq déclarations de diagnostic compilées sans axiome ; audits du théorème RC4 et du paquet conjoint également sans axiome. |
| Non-régression ciblée et Git | Aucun changement des sources Gödel/Tarski/HA depuis 8a945f2 ; `git diff --check` propre ; arbre resté propre durant l’audit. |

Commandes de reproduction, depuis la racine de la révision examinée, avec le
toolchain déclaré `leanprover/lean4:v4.33.1` et Python disponible :

```text
git rev-parse HEAD
git rev-parse HEAD^{tree}
git status --short
lake build
lake env lean Tests/AllConstantsAudit.lean
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/verify.ps1
bash scripts/verify.sh
python scripts/check-scientific-docs.py --self-test
python scripts/check-scientific-docs.py --static
python scripts/check-scientific-docs.py --lean
python scripts/check-neural-complete-comparison-v10.py --self-test --allow-results
python scripts/check-complete-property-scaling-v11.py --require-results
git diff --check
```

Les vérifications v10/v11 ci-dessus contrôlent les résultats existants. Ne pas
les confondre avec les scripts qui lancent de nouvelles expériences.

Lors de la rédaction initiale, les sondes ont également été extraites de l’annexe et
réexécutées : code retour 0 et sept résultats `#print axioms` sans axiome.
Les 23 liens locaux ont été résolus, `--self-test` a réussi 7/7 et `--static`
a de nouveau réussi. Le build complet n’a pas été relancé pour cette seule
création Markdown. Aucun fichier Lean ou registre n’a été modifié.

## 9. Réévaluation documentaire et registre

Le [document L11](L11_PREVALIDATION_CANDIDAT_ALIGNEMENT_CONSTITUTIF.fr.md), notamment
ses lignes 81, 84 et 85, prévalide RC2, RC5 et RC6. Les constats F1–F3 montrent
que cette clôture conjointe est trop forte. Une nouvelle évaluation datée doit
l’indiquer. Les remarques historiques sur l’absence de runs ne sont pas à
réécrire comme si elles avaient été prononcées après la campagne v10/v11.

Au [registre](../scientific-claims.json), l’entrée
`CONSTITUTIVE_NEURAL_ALIGNMENT_CLOSED_RUNTIME` possède :

- révision d’évidence `1cb2d9119458ef57bb30dc8b6ec66d259aa427a4` ;
- empreinte de sources `f61606b35a73fe4f27d0570fc50ac1235fdd696e1f2bad4624dd824ccad43e54` ;
- `reader=reviewed`, `translation=reviewed`, `independent=not_recorded`.

La [revue interne enregistrée](../reports/revue-interne-alignement-constitutif-neuronal-1cb2d91.md)
et les passages [français](../alignement-constitutif-neuronal-incremental.fr.md)
et [anglais](../incremental-constitutive-neural-alignment.en.md) doivent être
réexaminés pour les affirmations de consommation successive et de raccord
conjoint. Le registre est mécaniquement frais, mais cette fraîcheur ne résout
pas les écarts sémantiques constatés.

La [matrice d’implémentation](NEURAL_ALIGNMENT_IMPLEMENTATION_MATRIX.md), les
commentaires de F5 et l’interprétation de la famille « complete-property » sont
également à réaligner sur les consommateurs et propriétés effectivement prouvés.
Les archives gelées conservent leur contenu, accompagnées d’une rectification
identifiable plutôt que d’un remplacement silencieux.

Le présent audit ne modifie pas ces fichiers. Leur révision appartient aux
lots autorisés de correction et de livraison. Il ne demande pas de supprimer
les résultats valides ni de rétrograder la cible pour rendre le claim favorable.

## 10. Critère de clôture du travail

Le travail est clos uniquement quand :

1. F1–F3 sont fermés dans les chemins réellement utilisés par le runtime ;
2. F4 et F5 sont fermés dans les familles, comparateurs et campagnes concernés ;
3. C1–C17, G1–G10 et RC1–RC6 sont vérifiés conjointement, sans perte des acquis ;
4. R1–R8 et P1–P8 sont confrontés aux constructions et résultats réels, avec
   S1–S8 clos par les évidences exigées, et non seulement inscrits ou évalués ;
5. C18 relie la révision exacte, les textes, les preuves, les expériences et
   les deux conclusions indépendantes positives requises.

Une absence de gain comparatif démontré ne peut pas être transformée en gain
par reformulation. Une construction auxiliaire correcte ne peut pas remplacer
son installation. Une gate verte ne remplace pas la lecture de cette chaîne.

## Annexe — Sondes Lean reproductibles, sans modification des sources

Le bloc suivant a été vérifié sur `0c12baa` via `lake env lean --stdin`.
Il sert au diagnostic, pas à introduire des déclarations de production.

```lean
import RelationalPerimeter.Agents.Neural.CompleteCapabilityComparison
import RelationalPerimeter.Agents.Neural.ParameterizedCompiledCheckerFamily
import RelationalPerimeter.Agents.Neural.AutonomousCheckerClosure
open ConstitutiveSearch ConstitutiveSearch.NeuralAgent
open ConstitutiveSearch.NativeMechanism
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

-- A. La relation interne accepte une source au programme différent.
-- Ce n'est pas une démonstration d'acceptation par l'API publique.
def auditAlternativePrior :
    ReconfiguredExecutionState independentLearnedRequirementFamily :=
  { learnedInitialState with system := learnedDecodedExtendedArtifact.system }

theorem auditPriorNetworkDiffers :
    serializeNativeSystem auditAlternativePrior.system ≠
      serializeNativeSystem learnedInitialState.system := by decide

def auditTransitionStillBuilds : LearnedExecutedStateTransition
    LearnedContractTransitionPermission.installAligned
    auditAlternativePrior learnedAlignedState :=
  .executed auditAlternativePrior learnedAlignedInstallingAction rfl
    learnedAlignedInstallingEffect

-- B. La sortie reçue est transportée vers la constante canonique.
theorem auditExtendedResultIsCanonical
    (target : DecodedNeuralArtifact LearnedExtendedOperationalContract)
    (h : target = learnedDecodedExtendedArtifact) :
    learnedReceivedExtendedCheckedUpdateForArtifact target h =
      learnedExtendedCheckedUpdate := by
  cases h
  rfl

-- C. Égalité de la décision avec celle du runtime évalué.
-- L'appel effectif est vérifié séparément dans les définitions et le code généré.
theorem auditReferenceUsesRuntimeDecision :
    (runReferenceCombination frozenCompleteComparisonMaterial).bypassPreEffectDecision =
      (match submitUpdate learnedInitialCertifiedRuntime
          learnedBypassRuntimeUpdate with
       | .ok _ => FrozenReferenceDecision.allow
       | .error _ => FrozenReferenceDecision.refuse) := by rfl

-- D. La relation de succession de mesure ignore les deux états.
def auditScalingAnyTransition
    (s t : ReconfiguredExecutionState publicRequirementFamily) :
    scalingMetaContract.ExecutedStateTransition
      (current := ()) (next := ()) () s t := scalingUnit4

-- E. Le producteur cible du moteur successif fixe ces données canoniques.
-- Ces égalités ne remplacent pas la lecture de ses producteurs/consommateurs.
theorem reviewSuccessiveTargetArtifactIsCanonical
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    analysis.target.artifact = learnedDecodedExtendedArtifact := by rfl

theorem reviewSuccessiveTargetStateIsCanonical
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    analysis.target.state = learnedExtendedState := by rfl

theorem reviewSuccessiveTargetNamingIsCanonical
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    analysis.target.targetNaming = learnedExtendedStableNaming := by rfl

#print axioms auditPriorNetworkDiffers
#print axioms auditTransitionStillBuilds
#print axioms auditExtendedResultIsCanonical
#print axioms auditReferenceUsesRuntimeDecision
#print axioms auditScalingAnyTransition
#print axioms learnedEveryExactRealizationSeparatesAlignedFromBypass
#print axioms learnedConstitutiveAlignmentClosure
#print axioms reviewSuccessiveTargetArtifactIsCanonical
#print axioms reviewSuccessiveTargetStateIsCanonical
#print axioms reviewSuccessiveTargetNamingIsCanonical
```

Ces sondes vérifient les égalités et les habitations de types énoncées sans
axiome. Elles ne suffisent pas, à elles seules, à prouver une provenance ou
une dépendance exécutée : celles-ci demandent la lecture des producteurs,
des consommateurs et, lorsque pertinent, du code généré. Elles n’affirment
pas non plus que les types actuels expriment déjà la cible plus forte.
