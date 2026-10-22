# Rapport ordonné de correction de l’alignement constitutif neuronal

## Révision examinée

- Projet : `JohnDoe-collab-stack/relational-perimeter`
- Branche : `codex/constitutive-neural-alignment-implementation`
- Révision : `6a767f934556e2babdd4a43121a293364227db3c`
- Parent : `b9c042ee19336d4df4eab1864aa309e4bc144635`
- État de l’arbre pendant l’examen : propre et synchronisé avec la branche
  distante

## Verdict de départ

La révision compile et contient plusieurs composants substantiels : décodage
complet d’artefacts sérialisés, méta-contrat, certificats d’état, contrats de
futurs, identités stables, graphe causal hétérogène, calcul d’un cône affecté,
transport positif d’un fragment local, trace dépendante, runtime fermé pour
l’instance publique, artefact appris reproductible et séparation calculée
entre une mise à jour alignée et un contournement.

Elle ne satisfait cependant pas la cible terminale binaire. Les défauts ne
doivent être corrigés ni en réduisant les quantifications de la cible, ni en
renommant les résultats actuels, ni en enregistrant prématurément un claim
terminal.

Le travail doit être repris dans l’ordre ci-dessous. Cet ordre n’est pas un
ordre de présentation. C’est l’ordre des dépendances formelles nécessaires.

## Règles de correction non négociables

1. Conserver tous les résultats positifs actuels comme régressions.
2. Ne modifier ni la cible terminale ni C1–C18 pour rendre le verdict favorable.
3. Ne pas remplacer un producteur générique par une table de cas fermée sur
   l’instance publique.
4. Ne pas fournir au vérificateur un certificat, une décision de cône ou un
   successeur déjà certifié dans les données de la mise à jour.
5. Ne pas appeler « incrémental » un chemin qui reçoit d’abord un certificat
   cible complet construit indépendamment.
6. Faire passer `alignedUpdate` et `bypassUpdate` par la même API fermée que les
   autres mises à jour.
7. Distinguer à chaque étape formation, exécution, preuve et transport.
8. N’enregistrer le claim et ses empreintes qu’après gel du code et des textes
   canoniques.
9. N’accepter aucune régression Gödel, Tarski, regroupement, runtime, agent ou
   machine.

## Ordre obligatoire des corrections

### 1. Figer le socle de régression sans déclarer la cible atteinte

Avant toute refactorisation, conserver comme tests les résultats positifs de
la révision examinée :

- décodage de l’artefact sérialisé complet ;
- préservation de tous les futurs couverts ;
- transport de l’identité stable de l’entrée d’exigence ;
- calcul du cône public actuel ;
- transport effectif du payload du fragment non affecté ;
- égalité des verdicts du checker incrémental et du recheck de référence sur
  l’exemple actuel ;
- fermeture du constructeur du runtime ;
- reproduction octet par octet de l’artefact appris ;
- équivalence comportementale courante des deux mises à jour ;
- divergence contrefactuelle finie ;
- diagnostics exacts des mutations négatives.

Ces tests constituent un plancher. Ils ne constituent pas encore le théorème
terminal.

Critère de sortie : toutes les propriétés ci-dessus disposent d’un test nommé
qui continuera à compiler après les étapes suivantes.

### 2. Rendre sérialisables les données réellement modifiables

`SerializedNetworkEdit` ne couvre actuellement que `inputCount`, `neurons` et
`outputs`. Le format terminal de mise à jour doit pouvoir désigner, directement
ou par le choix certifié du contrat cible :

- les paramètres et arêtes neuronales ;
- les ports ;
- le décodeur ;
- la ressource d’autorisation ;
- la projection mémoire ;
- le contrat opérationnel cible ;
- la transition de contrat demandée.

Les identités stables doivent appartenir au format reçu ou être dérivées par un
décodage déterministe de celui-ci. Elles ne peuvent pas être ajoutées après le
décodage par une définition publique spécialement choisie pour l’exemple.

Une forme possible est un artefact constitutif sérialisé qui associe le réseau,
les clés stables des entrées, neurones et sorties, et une référence décodable au
contrat opérationnel. Le choix exact du type reste subordonné aux obligations
ci-dessus.

Critères de sortie :

- le delta reçu reste dépourvu de preuve ;
- le décodage produit la correspondance stable validée ;
- les insertions, suppressions et réindexations sont détectées ;
- une modification du décodeur, de la projection ou du contrat invalide les
  obligations aval correspondantes ;
- les anciennes fixtures sur poids, ports et décodeur restent valides.

### 3. Fournir au méta-contrat une interface de vérification exécutable

`CheckedAgent` et `CheckedUpdate` sont déjà paramétriques, mais les checkers ne
le sont pas. Une fonction exécutable générique ne peut pas être obtenue d’un
méta-contrat purement propositionnel sans décisions et lois de réflexion.

Il faut donc définir une interface exécutable, appartenant au méta-contrat ou
indexée par lui, qui fournisse :

- le décodage d’un nom de contrat reçu ;
- la décision d’admission d’un contrat ;
- la décision d’une transition de contrat ;
- le décodage complet de l’artefact sous le contrat cible ;
- les décisions locales sur le domaine courant et la base d’interventions ;
- les vérifications de l’exigence, du contexte, de l’autorisation, de l’action,
  de l’effet, de l’histoire et des futurs ;
- pour chaque décision positive, un lemme de réflexion produisant le témoin
  indexé exact.

Cette interface ne doit pas contenir le `CheckedAgent` ou le `CheckedUpdate`
qu’elle est censée produire.

Critère de sortie : aucune comparaison à un artefact littéral privilégié n’est
nécessaire au théorème générique de correction.

### 4. Généraliser le vérificateur initial

Le `checkInitial` actuel décode une source puis ne peut accepter que
`publicSerializedRequirementNetwork`. Il doit devenir paramétrique en
méta-contrat, contrat admis et artefact reçu.

Le succès doit construire le `DecodedNeuralArtifact`, la base causale finie,
l’état exécuté et le `StateConstitutiveCertificate` issus de cette même source.
Le certificat public actuel doit devenir une spécialisation du checker
générique, pas son unique résultat possible.

Obligations formelles :

- correction indexée par le résultat exact retourné ;
- complétude relative aux seules décisions finies annoncées ;
- aucune preuve de propriété sémantique illimitée ;
- refus précis des artefacts mal formés ou localement non conformes.

### 5. Généraliser le recheck complet de référence

Le checker complet ne doit plus reconnaître uniquement
`publicSerializedReconfiguredNetwork`. Il doit :

1. décoder le delta et le contrat cible ;
2. matérialiser le nouvel artefact depuis la source certifiée exacte ;
3. vérifier la transition du méta-contrat ;
4. exécuter la reconfiguration depuis l’état source exact ;
5. produire le successeur exact de cette exécution ;
6. recalculer toutes les obligations du certificat cible ;
7. retourner le `CheckedUpdate` indexé par ce successeur.

Ce chemin constitue la référence complète à laquelle le chemin incrémental
sera comparé. Il ne doit partager avec ce dernier que les fonctions
sémantiques communes, pas son verdict ni son certificat final.

Critère de sortie : un théorème `checkUpdate_complete_for_local_conditions`
porte sur tout delta sérialisé du domaine annoncé, pas seulement sur l’égalité
avec une constante publique.

### 6. Décomposer le certificat d’état en fragments réellement composables

C’est la correction conceptuelle centrale.

Dans la révision examinée, `publicReferenceUpdatedStateCertificate` est déjà
construit avant `publicIncrementalCheckedUpdate`. Les fragments transportés et
recalculés sont ensuite rangés à côté de ce certificat. Ils ne le produisent
pas.

Il faut introduire une décomposition dont les fragments couvrent réellement :

- les observations structurelles stables ;
- les obligations d’encodage ;
- les rôles causaux exécutés ;
- la préservation proposition–action ;
- l’autorisation ;
- l’effet et le successeur ;
- la politique historique ;
- les futurs couverts et leur réalisation exacte.

Une fonction d’assemblage doit recevoir uniquement :

- les fragments anciens transportés hors du cône ;
- les fragments nouvellement recalculés dans le cône ;
- les transports persistants du méta-contrat ;
- les revérifications exigées par la transition ;
- les preuves de couverture et de cohérence entre fragments.

Elle doit retourner le certificat cible complet. Il doit être impossible de
lui fournir en entrée un certificat cible déjà construit.

Critères de sortie :

- le résultat incrémental contient le certificat assemblé ;
- supprimer un fragment requis empêche l’assemblage ;
- remplacer un fragment transporté par une observation recalculée sans licence
  est rejeté ;
- la preuve d’égalité avec le certificat complet est postérieure aux deux
  constructions indépendantes.

### 7. Raccorder le cône affecté aux changements réels et au méta-contrat

Le calcul actuel du cône constitue une bonne base, mais il est appliqué à deux
certificats publics déjà connus. Le calcul terminal doit partir du delta décodé,
de la correspondance stable produite et des changements de contrat autorisés.

Il faut démontrer que :

- toute occurrence sans image stable est affectée ;
- toute observation structurelle modifiée est affectée ;
- les arêtes neuronales de poids nul ne propagent pas une causalité ;
- les changements de ports ou de décodeur atteignent proposition, action,
  effet, successeur et observations aval ;
- les obligations invalidées par le méta-contrat sont affectées ;
- seules les obligations explicitement transportées peuvent sortir du cône ;
- l’absence calculée dans le cône implique l’égalité de l’observation
  transportée correspondante.

Critère de sortie : le cône est calculé par le checker pour chaque delta admis,
et non sélectionné par une constante propre à l’exemple public.

### 8. Construire le véritable checker incrémental

Le checker incrémental doit maintenant :

1. recevoir l’agent certifié source et un delta sans preuve ;
2. décoder le delta et produire sa correspondance stable ;
3. matérialiser l’artefact cible ;
4. calculer le cône affecté ;
5. transporter les fragments hors cône ;
6. recalculer les fragments du cône ;
7. revérifier les obligations invalidées par le changement de contrat ;
8. assembler le certificat cible depuis ces seules données ;
9. exécuter la transition et identifier son successeur au nouvel état ;
10. retourner le `CheckedUpdate` exact.

Il ne doit appeler ni le checker complet ni une définition qui contient déjà le
certificat complet de référence.

Les théorèmes requis sont :

- correction pour tout succès ;
- complétude relative aux conditions décidables annoncées ;
- équivalence d’acceptation avec le recheck complet ;
- égalité des `CheckedUpdate` produits lorsque les deux chemins réussissent ;
- comptabilité exacte des fragments transportés et recalculés.

### 9. Généraliser les traces dépendantes et le runtime fermé

`CheckedReconfigurationTrace`, `checkUpdates`, `CertifiedRuntime` et
`submitUpdate` doivent être paramétriques dans le méta-contrat et consommer le
checker générique.

La trace doit accepter toute longueur finie autorisée par le méta-contrat. Un
méta-contrat particulier peut légitimement n’autoriser qu’un pas, mais cette
restriction ne peut pas être câblée dans le type ou l’algorithme générique par
le seul test « historique vide ou non vide ».

`submitUpdate` doit être l’unique opération publique produisant un nouveau
runtime. Il installe exactement `checked.next` et conserve la trace dont la
queue commence sur ce même successeur.

Les théorèmes terminaux doivent établir :

- la correction de toute trace acceptée ;
- l’accessibilité de tout runtime produit par l’API ;
- l’impossibilité d’installer une mise à jour rejetée ;
- la conservation des obligations du contrat courant à chaque étape ;
- la préservation exacte de tous les futurs couverts.

### 10. Intégrer l’artefact appris au même runtime

Le chemin appris utilise actuellement `CheckedIndependentLearnedInitial`,
`CheckedIndependentLearnedUpdate` et `installIndependentLearnedUpdate`, qui
sont séparés de `CheckedAgent`, `CheckedUpdate` et `CertifiedRuntime`.

Il faut construire un adaptateur local autonome qui transforme :

- l’artefact appris initial en entrée du `checkInitial` générique ;
- `alignedUpdate` en delta générique ;
- `bypassUpdate` en delta générique ;
- l’intention admise en obligation distincte de la certification ;
- le contrat d’autorisation et le futur contrefactuel en composantes du contrat
  opérationnel réellement utilisé par le runtime.

Les deux candidats doivent partir du même `CheckedAgent` effectivement retourné
par `checkInitial`.

Critères de sortie :

- `submitUpdate runtime alignedUpdate = .ok alignedRuntime` ;
- `submitUpdate runtime bypassUpdate = .error
  .missingConstitutiveDependency` ;
- aucun effet ni successeur n’est produit sur le chemin rejeté ;
- le runtime aligné contient la trace et le certificat issus du checker
  générique ;
- le checker spécialisé actuel n’est plus l’unique fondement du résultat
  discriminant.

### 11. Rattacher la divergence future au contrat opérationnel exact

Le témoin contrefactuel actuel doit être conservé, mais raccordé au contrat
opérationnel proposé par la mise à jour et au simulateur pur du même artefact.

Il faut montrer, sur une liste non vide calculée :

- l’équivalence courante sur tout le domaine fini déclaré ;
- l’accord de tous les vérificateurs qui se factorisent uniquement par cette
  table courante ;
- la satisfaction future du résultat aligné ;
- la violation future qu’aurait produite le contournement ;
- le rejet du contournement avant toute installation par le runtime fermé.

Le théorème discriminant doit assembler ces faits à partir du même agent
initial, du même méta-contrat, du même contrat courant et de la même API.

### 12. Exécuter réellement la comparaison de capacité

Le protocole actuel annonce six baselines, mais les six adaptateurs sont
`not-yet-implemented` et `confirmatory_results_present` vaut `false`. Cette
section ne peut donc pas être close par le seul manifeste existant.

Pour chaque classe déclarée :

1. implémenter l’adaptateur exécutable lorsque l’interface est disponible ;
2. utiliser le même artefact initial, les mêmes mises à jour et la même trace ;
3. enregistrer séparément les capacités certifiées, absentes et non couvertes ;
4. ne jamais convertir une absence d’adaptateur en résultat négatif ;
5. conserver le théorème de limitation seulement pour la classe extensionnelle
   précisément définie par factorisation.

Le run confirmatoire n’est permis qu’après gel des adaptateurs et du protocole.

Critère de sortie : `confirmatory_results_present` correspond à des résultats
réels, reproductibles et reliés aux mêmes objets que le runtime Lean.

### 13. Raccorder le passage à l’échelle à l’algorithme certifié

Les campagnes v2 et v3 sont reproductibles, mais elles mesurent des scripts
Python distincts du checker Lean public spécialisé. Le résultat terminal exige
que l’expérience mesure le même algorithme de réutilisation que celui dont les
invariants sont démontrés.

Il faut choisir une source exécutable unique :

- soit extraire ou compiler le checker générique Lean et l’appeler dans la
  campagne ;
- soit produire une correspondance vérifiée entre son exécution compilée et le
  runner expérimental.

La famille de réseaux doit continuer d’augmenter le graphe causal pertinent.
Les deux chemins doivent vérifier exactement la même propriété du même artefact
cible. Les coûts d’exécution, de vérification, de transport et de recalcul
restent rapportés séparément.

Critère de sortie : le gain mesuré porte sur la réutilisation certifiée du
runtime, pas sur un modèle parallèle du même vocabulaire.

### 14. Renforcer les mutations négatives après la généralisation

Rejouer les huit mutations terminales sur la nouvelle API générique et ajouter
les fixtures imposées par la refactorisation :

- delta fournissant une fausse correspondance stable ;
- certificat cible préconstruit présenté comme delta ;
- fragment affecté prétendument transporté ;
- fragment non affecté recalculé sans licence ;
- transition de contrat non admise ;
- contrat cible dont le décodeur ou la projection a été substitué ;
- bypass soumis directement à un exécuteur autre que `submitUpdate` ;
- queue de trace reconstruite depuis un état seulement égal en valeur.

Chaque fixture doit échouer au diagnostic, à la ligne et à la colonne annoncés.
Un échec d’arité ou un nom absent ne valide pas une obligation sémantique.

### 15. Exécuter la régression complète et réparer les évidences périmées

Après gel du code :

1. exécuter le self-test documentaire avec le Python configuré du workspace ;
2. exécuter `--static` ;
3. exécuter `lake build` ;
4. exécuter `--lean` ;
5. exécuter intégralement `verify.sh` et `verify.ps1` ;
6. exécuter les fixtures, frontières d’import, stratification, codegen,
   reproduction de l’artefact, mutations et campagnes ;
7. exécuter `git diff --check` ;
8. confirmer que l’arbre est propre.

La révision `6a767f9` échoue actuellement sur
`STALE_SOURCE: GODEL_OPERATIONAL_RUNTIME_CLOSURE_OBSTRUCTION`. Il faut déterminer
la dépendance exacte qui a invalidé l’empreinte et rouvrir la revue concernée.
Il est interdit de simplement remplacer l’empreinte ou la révision dans le
registre. Les preuves Gödel ne sont pas affaiblies par cet échec, mais leur
évidence enregistrée doit redevenir cohérente selon la procédure scientifique.

### 16. Produire la livraison scientifique après le commit d’évidence

Une fois le code, les tests et les protocoles gelés, créer un commit d’évidence
existant puis préparer :

- un identifiant de claim propre ;
- un passage canonique français ;
- une version anglaise contrôlée séparément ;
- la portée et les exclusions exactes ;
- les déclarations Lean de production et de test ;
- les quatre dépendances formation, exécution, preuve et transport ;
- les empreintes calculées sur la révision d’évidence ;
- les protocoles et résultats expérimentaux réellement utilisés.

Le registre vient après le commit d’évidence. Le document de cible et le
présent rapport restent des documents de chantier et doivent être retirés avant
l’intégration finale dans `main`.

### 17. Effectuer deux audits indépendants distincts

Le premier audit porte sur la validité :

- lecture intégrale des sources ;
- compilation ;
- axiomes ;
- dépendances ;
- chaîne constitutive ;
- checkers ;
- runtime fermé ;
- artefact appris ;
- mutations ;
- expériences ;
- cohérence FR/EN et registre.

Le second audit porte sur la portée et la nouveauté :

- comparaison avec les six classes annoncées ;
- recherche bibliographique ;
- examen de la conjonction exacte de capacités ;
- absence de glissement vers une revendication d’alignement humain général ;
- distinction entre théorèmes Lean, observations expérimentales et priorité
  historique.

Chaque rapport doit viser le SHA exact livré. Une soumission acceptée n’est pas
un verdict. Un rapport négatif ou inconclusif laisse la cible ouverte.

### 18. Nettoyer et intégrer seulement après satisfaction binaire

Avant toute fusion :

- retirer les documents temporaires de chantier ;
- conserver uniquement les passages scientifiques publiables, protocoles,
  résultats et rapports finaux ;
- vérifier les liens et la parité FR/EN ;
- vérifier le manifeste et le registre ;
- exécuter de nouveau les deux gates officielles ;
- relire le diff complet ;
- confirmer que chaque obligation de la table binaire est fermée.

Après une fusion autorisée dans `main`, répéter les vérifications sur le commit
fusionné. Aucune réussite sur la branche source ne vaut automatiquement pour le
snapshot fusionné.

## Dépendance synthétique

```text
socle de régression
→ format sérialisé complet et identités stables reçues
→ interface de vérification exécutable du méta-contrat
→ checker initial générique
→ recheck complet générique
→ certificat réellement fragmentable et assemblable
→ cône affecté calculé depuis le delta et la transition
→ checker incrémental composant le certificat cible
→ équivalence avec le recheck complet
→ trace générique
→ runtime fermé générique
→ artefact appris raccordé à ce runtime
→ alignedUpdate accepté et bypassUpdate rejeté par ce runtime
→ divergence future sur le même contrat
→ comparaison confirmatoire
→ passage à l’échelle du même algorithme
→ mutations négatives finales
→ gates et régressions complètes
→ commit d’évidence
→ passages FR et EN
→ registre
→ audit indépendant de validité
→ audit indépendant de portée et nouveauté
→ nettoyage
→ fusion autorisée
→ vérification du commit fusionné
```

## Critère terminal

La correction n’est terminée que lorsque les trois résultats sont obtenus dans
une même chaîne :

1. le checker incrémental générique construit le certificat successeur à partir
   des fragments transportés et recalculés ;
2. le runtime fermé consomme exactement ce résultat pour toute trace finie
   admise ;
3. l’instance apprise fait accepter `alignedUpdate` et rejeter `bypassUpdate`
   par ce même runtime, avant effet, malgré leur équivalence comportementale
   courante sur le domaine déclaré.

Les expériences, le registre et les audits certifient ensuite cette chaîne ;
ils ne peuvent pas la remplacer.
