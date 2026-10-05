# Plan de fermeture des corrections après le réaudit de l’agent

## 1. Objet, références et statut

Fermer les défauts restants du réaudit de l’agent constitutif, sans modifier
la cible, reconstruire une autre instance ou affaiblir les résultats acquis.
Les corrections portent sur les raccords du certificat, leur protection et
les contrôles de l’exécution compilée. Elles ne remplacent pas la démonstration.

| Référence | Valeur |
| --- | --- |
| Dépôt | `JohnDoe-collab-stack/relational-perimeter` |
| Branche de travail | `codex/constitutive-agent-corrections-audit` |
| HEAD avant ce plan | `27546b9db4aa72769772d9253050e92fcfb0974d` |
| Commit scientifique réaudité | `d52f3c0311d9572f84863481d508d38db2e5613c` |
| Parent scientifique | `924bc6c38153e6e5e7e0b2290d03b5eca28881dd` |
| Main et merge-base de l’audit | `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685` |
| Cible computationnelle antérieure validée | `4e0febf032821882069e7cfefd7e631fc8461d95` |
| Référence avant ajout de l’agent | `75057f09cc9a535e8be3390999fa688c9ee3a96d` |
| Première instance de l’agent auditée | `f6c6d2c051ae0886056d47cf5357253c137a1319` |
| Projet Aristotle | `a55ce7b7-a3b4-4d77-b963-812c1923c77b` |
| Tâche du réaudit | `1ff3164b-33e2-4763-aa8b-425695482d7f` |
| Rapport étudié | `CONSTITUTIVE_AGENT_CORRECTIONS_AUDIT.md` |
| Verdict sur l’agent | `AGENT TARGET REQUIRES CORRECTIONS` |
| Verdict sur les acquis | `NO REGRESSION VERIFIED` |
| Correctif proposé dans les livrables | `0001-Close-audit-corrections-F6-live-production-bounds-F7.patch` |
| SHA-256 du correctif | `b39b4c63772dfd34de94f4b4996a46b9a249612c322da1c9ad050bc7d0edc033` |
| Arbre annoncé pour ce seul correctif | `52ced406dd1a5e5ead96c81f43ca59168873d2f8` |

Lors de la préparation du plan, le correctif a été étudié dans une copie extérieure au dépôt. Les deux fichiers
Lean modifiés y compilent avec leurs audits sans axiomes. Les nouvelles bornes
rejettent les C enregistrés de M06g et M06h. Les trois nouvelles fixtures de
confidentialité donnent leur diagnostic attendu sur Windows. Ces vérifications
ciblées ne sont ni un build propre complet de la branche corrigée ni un nouvel
audit indépendant.

Le correctif et les compléments du présent plan sont maintenant intégrés
localement à cette branche, après autorisation d’implémenter. La fermeture des
imports de production est contrôlée ; le faux positif M06f est corrigé sans
relâcher le contrôle des productions réellement exécutées. La campagne locale
est terminée et ses résultats sont consignés en section 11. À la clôture de
cette campagne, aucune publication ni nouvel audit indépendant n’avait encore
été effectué. La publication ultérieure est autorisée séparément ; elle
n’autorise ni l’envoi de l’audit ni une fusion.

La nouvelle passe de revue a résolu les imports des 159 modules inventoriés :
290 dépendances locales, aucun module local hors inventaire, et deux modules
extérieurs, `Init` et `Init.Omega`, tous deux issus de la toolchain actuelle.
L’import explicite d’`Init.Omega` existe dans `SearchableTransportCode` : le
supprimer pour faire réussir une allowlist serait une régression. La vérification
Lake sans reconstruction des artefacts a également réussi sur la façade.

Dans la copie extérieure, l’analyse trouve `[1,1]` sur le C enregistré de
l’auxiliaire correct M06f et `[2,2]` sur M06e. Les deux variantes M06c/M06d ont
aussi été recompilées séparément : leur C révèle `[2,2]` par suivi des auxiliaires
et de la fermeture, sans le contrôle d’appel direct. Ce sont des vérifications
exploratoires de faisabilité, non le rejeu confirmatoire de toutes les mutations.

Le [plan précédent](PLAN_CORRECTIONS_AGENT_APRES_AUDIT.fr.md) décrit le chantier
antérieur et ses observations locales. Ce nouveau plan ne réécrit pas cet
historique et ne reprend pas ses cases cochées comme preuve de fermeture.

Document de chantier préparé et mis à jour le 5 octobre 2026. Les matériaux bruts restent
hors du dépôt. Ce plan devra être retiré de l’arbre destiné à `main` avant une
intégration autorisée. Sa rédaction n’autorise ni modification du code, ni
commit, push, soumission à Aristotle ou fusion.

## 2. Cible immuable

L’exigence demeure celle du [protocole réaudité](../../ARISTOTLE_CONSTITUTIVE_AGENT_CORRECTIONS_AUDIT_PROMPT.md) :

> Poursuivre le moteur autorisé depuis ses productions réelles ; ne restituer
> une valeur que pour une production effectivement formée et une variable du
> périmètre reçu ; restituer la valeur de cette production, non une valeur
> choisie par le contrôleur ; préserver les garanties d’acceptation annoncées
> par les actions utilisées ; conserver ces droits et ces accords après reprise.

Le critère d’achèvement reste inchangé :

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

Conserver également la [cible computationnelle antérieure](../conclusion-largeur-exponentielle-conservation-identites.fr.md),
la [spécification de l’agent](PLAN_AGENT_CONSTITUTIF_PERSISTANCE.fr.md) et la
[note scientifique sur la méthode](../constitution-calcul-et-persistance-pour-ia.fr.md).
Leur portée ne change pas. Aucun contrôle logiciel ajouté ici ne remplace
leur preuve ni ne devient un nouveau critère scientifique plus facile.

## 3. Méthode et invariants à respecter

Pour chaque modification, identifier les données reçues, les témoins positifs,
le producteur effectif, les occurrences qu’il forme, le consommateur et les
accords nécessaires. Suivre la même détermination dans cet ordre :

```text
maître constitué et exigence reçue
→ production normalisée ou reprise réellement exécutée
→ cible avec son origine et son contexte
→ référence et lecture sur le support approprié
→ autorisation et critère indépendant
→ réponse ou refus
→ transports réels et successeur
→ composition sur les interactions finies
```

L’ordre de construction des données, l’ordre des dépendances constitutives et
l’exposition ultérieure des preuves restent distincts. Une preuve sur une
histoire complète ne doit pas devenir un paramètre futur du producteur local.

Invariants protégés :

- Les quatre modules fondamentaux, la licence, la toolchain et le manifeste.
- Le maître public, l’histoire dépendante des rôles et les profils constitués.
- La production locale, l’action exécutée, sa préservation séparée et les
  fibres exactes du régime d’obligations.
- Le `iff` de pleine largeur, les résultats `2^n`, un et `2^k` dans leurs
  portées déjà démontrées, et la distinction des profils sources.
- Le périmètre reçu, le décodage réel, les quatre demandes et les refus.
- Le travail exact d’`obtain`, les anciennes lectures et la mémoire entière
  inchangée en cas de refus.
- Les accords riches/réduits, les deux retours des témoins d’admission et les
  garanties composées sur toutes les interactions finies.
- L’oubli démontré du profil source depuis la mémoire complète et les mêmes
  continuations futures sur des sources distinctes.

Ne pas confondre :

- formation et simple égalité des valeurs ;
- réalisation, admission et satisfaction d’une spécification ;
- extension injective de références, action dirigée et projection avec perte ;
- support du moteur et support historique des cibles ;
- donnée constitutive dans `Type` et accord démontré dans `Prop` ;
- preuve Lean, protection de l’interface et contrôle du code compilé.

L’extensivité reste un readout en aval. Ne pas l’utiliser pour produire,
autoriser ou poursuivre une réponse. La longueur du registre n’est pas la
largeur opérationnelle. Ce lot ne vise ni coût total polynomial, ni mémoire
physique constante, ni SAT général, ni alignement humain universel.

Les rangs existants restent inchangés : `Persistence` est A15, `PublicInstance`
A16, la façade A17. A15 ne doit pas importer A16, et aucune strate antérieure
ne doit importer l’agent. Les nouveaux contrôleurs Python sont de l’outillage,
pas des dépendances scientifiques du calcul.

## 4. Diagnostic précis du réaudit

| Constat | État du résultat au commit audité | Correction attendue |
| --- | --- | --- |
| F6, M06g | Une production vivante supplémentaire dans `performCertified` échappe aux contrôles. | Compter les applications hors de `step`, y compris par auxiliaire et fermeture statique. |
| F6, M06h | Même défaut dans une itération de `runSteps`. | Borner à zéro les productions supplémentaires de l’itération. |
| F6, M06f | Un auxiliaire bénin à production unique est refusé par le contrôle du nom appelé directement. | Contrôler la multiplicité effective plutôt qu’imposer cette forme syntaxique. |
| F7, M20e | Un élaborateur enregistré dans la fixture fabrique le diagnostic attendu. | Bloquer ce chemin avant compilation et conserver les contrôles JSON exacts. |
| Condition de F7 | Les imports de production n’exposent actuellement pas l’élaborateur, mais cette condition n’est pas imposée. | Vérifier les dépendances effectivement résolues et refuser tout import extérieur non autorisé. |
| M03a / M04a | Les origines actuelles sont correctes, mais leur remplacement par acceptation libre ou tag n’est pas détecté. | Fixer leurs indices et leur raccord à la production. |
| M08d | La lecture actuelle est correcte, mais sa négation peut remplacer la valeur annoncée. | Consommer l’accord entre `read` et la continuation effectivement portée. |
| M14 | Le suivi interne existe, mais sa suppression cohérente passe. | Exposer et consommer les étapes internes du suivi certifié. |
| Références de `Followed.cons` | Une extension est stockée sans être fixée à celle de l’histoire produite. | Ajouter son exactitude, l’exposer et la consommer. |
| M15b / M16b | Acceptation et retours existent, mais leur suppression du paquet n’est pas protégée. | Les consommer explicitement dans le certificat et les tests clients. |
| M19a / M19b | Les constructeurs sont privés, mais cette protection n’est pas testée. | Ajouter les trois fixtures de confidentialité, séparées des preuves sémantiques. |

Ces derniers cas sont des défauts de protection de garanties présentes, pas
des réfutations de leurs preuves actuelles. Il faut protéger leurs énoncés
sans leur inventer une nouvelle dépendance causale.

## 5. Lot A — Préparer le changement sans contamination

1. Relever branche, HEAD, parent scientifique, merge-base et diff existant.
   Préserver toute modification concurrente ; ne pas toucher aux autres
   répertoires ni changer de branche sans demande.
2. Figer les empreintes des fichiers protégés, les énoncés publics et les
   sources des 23 fixtures existantes, à leurs 25 sites diagnostiques.
3. Vérifier la provenance et les droits de réemploi du correctif proposé.
   N’intégrer que des éléments autonomes dans le vocabulaire du dépôt ; ne
   publier ni archive brute, ni chemins d’extraction, ni fichiers de l’audit.
4. Reporter les changements retenus avec `apply_patch`, sans importer un
   historique extérieur par `git am` et sans commit implicite.
5. Maintenir un tableau de conformité extérieur au dépôt : constat, modification,
   producteur/consommateur, preuve, contrôle, résultat et limitation.

Le correctif proposé est une base de travail relue, pas une validation à
accepter automatiquement. L’arbre final différera de son arbre annoncé dès
l’ajout du contrôle des imports et de la correction du faux positif M06f.

## 6. Lot B — Fermer les consommateurs scientifiques

Fichiers : [Persistence](../../RelationalPerimeter/Agents/Constitutive/Persistence.lean)
et [tests de persistance](../../Tests/ConstitutiveAgentPersistence.lean).

### B1. Origines, valeurs et acceptation

Ajouter au certificat les garanties fermées proposées :

- `targetsAccepted` : chaque cible satisfait le critère de son propre contexte,
  par élimination de l’origine existante, sans prémisse extérieure.
- `targetReads` : `target.read var = target.continuation.1 var`.
- `resumedOrigin` : l’origine de `resumedTarget production` est précisément
  `TargetOrigin.resumed production`.

Les constructions de `TargetOrigin`, `AnswerTarget`, `Authorization` et les
actions sous-jacentes ne sont pas à remplacer. Maintenir l’acceptation dérivée,
et non réintroduire un champ libre d’acceptation.

Consommer les garanties dans les tests clients :
`answer_read_is_produced_value`, `certified_answer_read`,
`normalized_origin_index`, `resumed_origin_index`, `origin_producer`,
`certified_resumed_origin`, `certified_targets_accepted` et
`answer_criterion_is_contextual_acceptance`.

Les tests d’indices doivent porter sur les types exacts des constructeurs.
Le test exhaustif des origines protège l’absence d’un troisième cas libre.
Le critère de réponse reste autorisation et acceptation contextuelle, non
une nouvelle affirmation SAT globale.

### B2. Étapes internes et références exactes

Ajouter `referencesExact` à `Followed.cons`, puis les projections
`Followed.stages`, `Followed.references` et la loi `Followed.references_exact`.
L’extension stockée doit être celle de `(sourcePerform source request).1.history.references`.

Attention aux supports : ce champ relie le support initial du maître au
support courant du moteur. Il ne remplace pas le transport distinct du support
historique des cibles. Garder `InternalStepAgreement.engine` et `.historical`,
ainsi que leurs compositions et leurs accords de lecture.

Construire `request_stages_exact` à partir de `FollowedStages.execution_exact`
et `request_internal_execution`. La conclusion porte sur la mémoire et les
événements du worker réel, pas sur une liste indépendante.

Ajouter au certificat :

- `followedStages`, qui fixe les étapes portées par la tête du suivi à
  `requestStages` sur la même source et la même demande ;
- `followedReferences`, qui fixe l’extension à l’histoire produite ;
- `internalStages`, qui ferme l’accord avec `executeInput` pour toute source
  et toute demande.

Consommer ces champs dans `certified_internal_stages` et
`certified_followed_references`. Couvrir une demande `obtain` produisant plusieurs
étapes et une demande n’en produisant aucune. Ne pas ajouter de paramètre futur
au producteur de la tête ni consulter l’archive dans la reprise runtime.

Corriger aussi les commentaires concernés : `Followed.references` transporte
les références du support du moteur depuis le maître ; ce n’est pas l’extension
du support historique des cibles. Le nom `history.references` ne justifie pas
de confondre ces deux types de supports.

### B3. Retours des admissions et règles de preuve

Les deux lois d’admission existent : les conserver et les consommer dans
`certified_received_return` et `certified_realized_return`. Une implication de
validité ne remplace pas un retour exact sur le témoin.

Construire tous les nouveaux champs avec les données et théorèmes existants.
Un `rfl` qui fixe une projection effective est légitime ; il ne doit pas servir
à définir artificiellement une obligation ou une acceptation triviale.

Mettre à jour l’unique bloc final `AXIOM_AUDIT` des deux fichiers. Vérifier les
noms complets, l’absence d’axiomes et la calculabilité des projections dans
`Type`. Le changement d’arité de `Followed.cons` doit être répercuté proprement
dans ses consommateurs ; ne pas conserver un ancien constructeur parallèle.

## 7. Lot C — Fermer le contrôle des productions compilées

Fichiers : [contrôle de l’agent](../../scripts/check-agent-codegen.py),
[analyse C partagée](../../scripts/unified_codegen_analysis.py) et leurs autotests.

### C1. Productions supplémentaires hors de `step`

Conserver le contrôle d’une production effective dans `step`. Ajouter les
bornes suivantes, en suivant les auxiliaires, alias et fermetures statiques :

| Entrée examinée | Application contrôlée | Borne hors frontière autorisée |
| --- | --- | --- |
| `runSteps` | `LiveContinuation.produce` | Zéro hors `step`, avec un dépliage structurel explicite du worker. |
| `performCertified` | `LiveContinuation.produce` | Zéro hors `step`, en examinant aussi l’itération du worker. |
| `performCertified` | `step` | Zéro hors `runSteps`. |
| `executeProducedInput`, `executeInput`, `executeRequests` | `LiveContinuation.produce` | Zéro hors `step`, avec les dépliages récursifs déclarés. |
| `Session.execute`, `.produce`, `.executeAll` | `LiveContinuation.produce` | Même exclusion transitive hors `step`. |

Conserver les contrôles de production du maître à l’initialisation, de partage
de la requête, de reprise sans archive/maître et d’absence d’énumération globale.
Ne pas transformer une route indirecte inconnue en zéro appel.

Pour les `switch` générés, explorer chaque alternative. Refuser un cas non
pris en charge, une alternative sans bloc et une continuation dans le cas
suivant. Ajouter des contrôles positifs de dispatch et des cas négatifs de
production cachée ; ne pas ignorer un `switch` pour faire passer le vérificateur.

### C2. Corriger le faux positif M06f

Le contrôle de l’appel direct de `step` au producteur impose aujourd’hui une
forme syntaxique qui rejette un auxiliaire pourtant correct. Pour cette
liaison seulement, remplacer cette exigence par la plage effective `[1,1]`
d’applications du producteur sur chaque chemin analysé.

Exiger le minimum autant que le maximum : une plage `[0,1]` ne suffit pas
pour `step`. Ne pas imposer ce minimum aux entrées qui peuvent légitimement
refuser avant production, notamment l’initialisation et les demandes.

Le cas positif est un auxiliaire qui produit une fois et partage son résultat.
Les doublons réellement vivants, directs ou cachés, doivent rester rejetés.
Regénérer leur C avant mesure. Une duplication éliminée par le compilateur
reste un cas inoffensif, pas un rejet artificiel à obtenir.

Ajouter les autotests suivants au contrôle de la plage, et pas seulement au
compteur sous-jacent : `[1,1]` accepté ; `[0,0]`, `[0,1]` et `[2,2]` refusés pour
`step`. Couvrir l’auxiliaire simple, l’appel de fermeture, le résultat partagé
et un dispatch omettant la production sur une alternative. M06c et M06d doivent
être rejetés pour leurs deux appels effectifs après retrait du contrôle direct.

### C3. Limite à conserver

Ces bornes concernent une entrée ou un dépliage explicitement défini du C
généré. Elles ne constituent pas une preuve de coût total, de temps ou de heap.
Les limites sur les callbacks dynamiques et l’optimiseur restent explicites.
Rejouer aussi les contrôles de l’unification, puisque le parseur est partagé.

## 8. Lot D — Fermer les refus attendus et leurs imports

Fichiers : [politique diagnostique](../../scripts/expected_failure_diagnostics.py),
[tests des gates](../../scripts/test-expected-failure-gates.py),
[inventaire](../../scripts/expected-failures.tsv) et les deux wrappers existants.

### D1. Refuser le contournement M20e

Intégrer la politique étudiée : imports de fixtures limités à un module local
`RelationalPerimeter` par ligne ; refus des en-têtes/modificateurs non admis,
des attributs, des élaborateurs enregistrés, des API de diagnostic et des
interpolations de messages. Garder le traitement des commentaires imbriqués,
caractères, chaînes et identifiants quotés, ainsi que les positions originales.

Le contrôle JSON reste cumulatif : statut exactement un, diagnostic de la
bonne classe, fichier/ligne/colonne figés, motif attendu et absence d’erreur
ou avertissement supplémentaire. Le refus de la source ne remplace pas ces
vérifications pour les fixtures admises.

Ajouter le M20e exact et ses variantes. Son contrôle compilateur doit d’abord
montrer que, sans la politique, le diagnostic fabriqué reproduit bien le site
attendu. Ensuite seulement vérifier le refus avant compilation par les wrappers.
Une erreur indépendante ne peut pas faire réussir ce contrôle.

Conserver les 23 fixtures initiales et leurs attentes byte pour byte. Ajouter
`PrivateAgentSession`, `PrivateAgentCertificate` et `PrivateAgentAnswerTarget`.
L’inventaire attendu du correctif devient 26 fixtures et 28 sites, à recompter.
Ces trois ajouts protègent la confidentialité des constructeurs, non la
nécessité mathématique de cette confidentialité.

### D2. Contrôler la fermeture réelle des imports de production

Ajouter `scripts/check-fixture-import-closure.py`. Son périmètre est l’ensemble
des modules de production que les fixtures peuvent importer, pas seulement
la fixture ni le préfixe textuel de son import.

1. Recouper l’inventaire de stratification avec les sources de production
   effectives, y compris les ajouts locaux ; aucun module admissible aux fixtures
   ne doit échapper au contrôle.
2. Utiliser le résolveur de la toolchain inchangée, notamment
   `lake env lean --deps`, sur les sources examinées. Cette commande a été
   vérifiée sur chacun des 159 modules actuels. Elle donne les imports directs,
   pas à elle seule leur fermeture transitive. Normaliser les chemins sans
   confondre un module du projet et un module extérieur homonyme.
3. Autoriser exactement les modules locaux inventoriés et les deux dépendances
   de toolchain déjà identifiées, `Init` et `Init.Omega`. Vérifier leurs chemins
   dans le répertoire de bibliothèque rendu par `lake env lean --print-libdir`,
   sous la version épinglée. Leur fermeture interne relève de cette toolchain
   reçue et figée ; cela n’autorise pas tout le préfixe `Init.*`. Tout autre
   import extérieur explicite exige un examen séparé : il n’est pas admis par
   ressemblance de nom. Refuser aussi l’homonyme local d’un module de toolchain.
4. Parcourir les dépendances locales : aucun import direct ou indirect de
   `Lean`, `Lean.Elab.*`, `Std`, `Lake` ou d’un autre module extérieur non
   autorisé ne doit exposer une API à la fixture. Ne pas changer la toolchain
   ni ajouter Mathlib pour contourner le contrôle.
5. Refuser un résultat de résolution manquant, invalide, ambigu ou interrompu.
   Ne pas traiter une erreur de résolution comme une absence de dépendance.
6. Garder `Tests/AllConstantsAudit.lean` hors des imports admis aux fixtures.
   Ses outils d’audit ne deviennent pas une dépendance de production.
7. Vérifier ensuite que les artefacts importés correspondent aux sources
   examinées. `lean --deps` ne vérifie pas leur fraîcheur. Utiliser Lake avec
   `--rehash --no-build --no-cache` sur les facettes `olean` des modules admis,
   en lots si nécessaire. La commande sur `+RelationalPerimeter:olean` a été
   exécutée avec succès pendant cette revue. Tout artefact manquant ou périmé
   bloque les fixtures et demande un build explicite ; le contrôleur ne doit
   ni le reconstruire ni télécharger un cache pour poursuivre silencieusement.
8. Figer l’état examiné : empreintes des sources, inventaire, configuration,
   toolchain et artefacts résolus. Vérifier qu’il ne change pas pendant le
   contrôle et la compilation des fixtures. Une modification concurrente
   invalide le run ; elle ne peut pas réutiliser son verdict partiel.

Le contrôle doit être appelé par l’entrée partagée
`expected_failure_diagnostics.py`, avant la compilation des fixtures. Les deux
wrappers l’imposent ainsi même lorsqu’ils sont lancés seuls ; les deux `verify`
l’imposent par cette même route. Ne pas créer un drapeau client permettant de
le sauter ou une validation persistante indépendante de l’état des sources.

La résolution est un contrôle de frontière logicielle, pas une nouvelle
propriété constitutive de l’agent. Elle doit renforcer les règles existantes,
sans modifier les données du calcul.

### D3. Tests du contrôle d’imports et adaptation du harnais

Ajouter les cas suivants à la suite réelle des deux wrappers :

- production normale : les fixtures initiales et nouvelles restent vérifiées ;
- import de l’élaborateur directement dans un module de production ;
- exposition indirecte par un autre module local ;
- import extérieur placé après commentaires ou réparti sur des lignes,
  pour les syntaxes effectivement acceptées par Lean ;
- module local admissible mais absent de l’inventaire ;
- homonyme ou chemin de bibliothèque extérieur non autorisé ;
- production normale avec l’import existant `Init.Omega` ;
- dépendance non résolue, interruption et réponse de résolution malformée ;
- artefact absent ou périmé, ou changement de source pendant le contrôle ;
- échec forcé de ce contrôle empêchant le verdict de réussite des fixtures.

Pour chaque refus, exiger la raison propre au nouveau contrôle, et vérifier
qu’aucune fixture n’a été compilée après son échec. Un statut non nul sans
diagnostic identifié ne suffit pas. Tester également l’absence de compilation
ou téléchargement automatique dans le contrôle de fraîcheur.

Le harnais actuel copie les fixtures et quelques scripts, puis partage les
artefacts de build. Adapter cette préparation : fournir les sources locales
et le manifeste de stratification nécessaires au nouveau contrôle, avec le
contrôleur lui-même et les configurations Lake. Chaque cas réel reçoit aussi
une copie indépendante des artefacts et métadonnées de build nécessaires.
Ne pas conserver une jonction mutable vers le cache de référence ni un chemin
spécial moins strict pour les tests. Le harnais doit fonctionner hors d’un
checkout Git : l’inventaire physique des sources ne repose pas seulement sur
`git ls-files`.

Les variations de source restent dans des copies jetables. Les commandes de
résolution et de fraîcheur ne doivent ni reconstruire ni écraser les caches
de référence. Toute mutation nécessitant un build utilise exclusivement ses
propres artefacts. Contrôler les empreintes de la référence après la campagne.

Les autotests lexicaux purs restent exécutables avec `--policy-only`, sans
exécution de Lean ou d’un shell. Les cas réels du résolveur et des wrappers
sont exécutés séparément dans la suite complète. Ne pas confondre ces preuves
de fonctionnement limitées avec une preuve de sécurité de Lean arbitraire.

## 9. Lot E — Préserver les dépendances riches et la fidélité documentaire

Ne pas remplacer `MaterialReading.values` par une liste indépendante, même
égale. Conserver formation, ports et références typées, interprète riche
indépendant, accords de lecture et contrôle compilé `AGENT_RICH_READ`.

Le constat F3 demeure précis : l’accord rend les valeurs égales au registre,
donc une équation de valeurs ne distingue pas tous les chemins de calcul.
Ne pas fabriquer une divergence de valeurs pour rendre un témoin nécessaire,
ni annoncer un nouveau théorème de nécessité. La garantie porte sur la
formation effective, ses consommateurs et le chemin compilé protégé.

Actualiser ensemble [README](../../README.md),
[document français](../agent-constitutif-et-persistance.fr.md) et
[document anglais](../constitutive-agent-and-persistence.en.md) :

- raccords fermés du certificat et des étapes internes ;
- confidentialité et nombre réel des fixtures ;
- périmètre exact des bornes compilées ;
- politique restreinte des fixtures et fermeture d’imports désormais contrôlée ;
- distinction entre résultats démontrés, contrôles logiciels et plateformes testées.

Ne pas réécrire les conclusions scientifiques antérieures, modifier les
figures ou publier le correctif brut. Ne pas présenter le réaudit du commit
ancien comme un verdict sur la nouvelle version.

## 10. Ordre d’exécution et validation

Exécuter dans l’ordre A, B, C, D, E. Les consommateurs scientifiques précèdent
les contrôles de leur protection ; les mesures et tests ne créent pas leurs
objets à leur place.

### 10.1. Preuves et absence de régression

- Compiler `Persistence` et `Tests/ConstitutiveAgentPersistence`, puis leurs
  importeurs et l’ensemble des tests ; vérifier l’unique audit final de chaque
  fichier modifié, tous ses noms et l’absence d’axiomes.
- Scanner toutes les sources Lean : aucun construit interdit et aucune
  déclaration `noncomputable`.
- Exécuter le sweep exhaustif des constantes et établir l’origine effective
  des exceptions générées ; aucune déclaration manuscrite n’en dépend.
- Comparer les énoncés et l’inventaire avec le commit audité, son parent et les
  acquis antérieurs. Aucun résultat ne doit être supprimé ou affaibli.
  Isoler les renforcements hérités de `924bc6c` et le changement explicite
  d’arité de `Followed.cons` : ne pas les masquer sous un bilan de signatures
  « inchangées », ni les confondre avec une perte de théorème.
- Comparer les empreintes des quatre fondations, licence, toolchain, manifeste,
  sources scientifiques antérieures, figures et fixtures initiales.
- Vérifier chaque module, les rangs A10–A17, les sorties de build et les liens
  documentaires. Recompter les fichiers et les diagnostics depuis l’arbre final.

### 10.2. Cas négatifs et cas inoffensifs

Réutiliser les 52 mutations gelées du réaudit uniquement dans des copies
extérieures. Lorsqu’une mutation ne s’applique plus, préparer et figer une
adaptation cohérente avant exécution ; conserver ancien et nouveau résultats.
Les adaptations proposées M14b et M15c restent des remplacements documentés
des scénarios M14 et M15b, pas des essais dont on pourrait changer l’attente
après observation.

| Cas | Résultat requis et raison |
| --- | --- |
| M03a, M04a | Rejet du remplacement des indices/origines exacts, et non erreur adventice. |
| M08d | Rejet d’une lecture inversée par l’accord avec la continuation. |
| M14 adapté | Détection de la perte du suivi interne annoncé et consommé. |
| M15b adapté | Détection de la perte d’acceptation dans le contrat certifié. |
| M16b | Détection de la suppression d’un retour exact annoncé. |
| M19a, M19b | La fixture de confidentialité compile après ouverture du constructeur : le wrapper doit donc échouer. |
| M06c, M06d, M06e, M06g, M06h | Rejet de productions supplémentaires réellement présentes dans le C régénéré ; aucun rejet de M06c/M06d par le contrôle direct retiré. |
| M06f | Acceptation de l’auxiliaire correct avec une seule production effective. |
| M20e | Diagnostic fabriqué reproduit au contrôle compilateur, puis source refusée par les deux wrappers. |
| Exposition directe/indirecte de l’élaborateur | Rejet par le nouveau contrôle des dépendances, pas par un échec scientifique sans rapport. |
| M11c | Rejet du remplacement de la lecture du support par le contrôle compilé existant ; ne pas prétendre une différence de valeurs. |
| Duplication supprimée par compilation, métadonnées inertes, reconstruction des mêmes garanties | Classer comme inoffensif si les mêmes données et garanties subsistent ; ne pas exiger un faux rejet. |

Le rapport distingue aussi des familles non exécutées comme mutations séparées :
M11a, M16a/c/d, M18a–c et M19c. Pour chacune, indiquer le probe qui la couvre,
ou préparer un cas cohérent manquant et le figer avant exécution. Ne pas
présenter le rejeu des 52 patches comme l’exécution de ces familles supplémentaires.
Tout cas critique non couvert reste une obligation ouverte.

Séparer une corruption de l’objet, une suppression de garantie, une perte de
confidentialité et une refactorisation correcte. Certains tests protègent une
garantie en la consommant : cela détecte sa suppression, pas sa nécessité
causale universelle. Une suppression simultanée des tests est un changement
visible à examiner, non une preuve que la garantie originale était fausse.

### 10.3. Campagne finale sur un arbre identifié

Avant le run confirmatoire, figer scripts, empreintes, commandes, paramètres,
toolchain et attentes. Écrire les résultats dans un répertoire extérieur neuf,
sans écraser ceux du réaudit. Distinguer les essais préparatoires du run final.

Commandes de base :

```text
git status --porcelain
git rev-parse HEAD
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
python scripts/test-expected-failure-gates.py --policy-only
git diff --check
git diff d52f3c0311d9572f84863481d508d38db2e5613c --check
lake update
```

Ajouter la suite complète des wrappers avec son argument `--output` dirigé
vers un répertoire extérieur neuf, les probes clients indépendants et les
mutations ciblées. Employer le Python réellement disponible, sans modifier
le vérificateur pour contourner un échec d’environnement.

Comparer le manifeste avant/après `lake update`, les empreintes avant/après
les vérifications et les sorties sélectionnées par les deux verifiers.
Exécuter les deux routes sur Windows disponible. Un run PowerShell sous Linux
reste un run Linux ; une plateforme ou un cas non exécuté est noté `NOT RUN`.

Enregistrer le diff complet et les hashes des sources : HEAD seul ne désigne
pas les modifications non commitées. Après une publication explicitement
autorisée, le SHA exact doit désigner le contenu réellement vérifié.

## 11. Critères de clôture

Les cases suivantes sont fermées par les exécutions sur la version intégrée
localement. Elles ne constituent pas un verdict d’audit indépendant sur un
nouveau commit, et ne clôturent pas la publication ou l’intégration dans `main`.

- [x] Cible et méthode inchangées ; même instance et mêmes fondations.
- [x] Origines, lectures et acceptation raccordées et consommées par le certificat.
- [x] Étapes internes, références exactes et deux retours d’admission consommés.
- [x] Zéro production supplémentaire hors de `step` sur tous les chemins visés.
- [x] Auxiliaire correct M06f accepté, doublons vivants toujours rejetés.
- [x] Contournement M20e refusé sans abaisser les diagnostics gelés.
- [x] Fermeture d’imports effectivement contrôlée par les deux wrappers, y
  compris hors de la suite globale ; tests directs et indirects exécutés.
- [x] Lecture riche et strates préservées, sans archive dans la reprise runtime.
- [x] Builds propres, constructivité, calculabilité et sweep sans défaut manuscrit.
- [x] Acquis, fichiers protégés, fixtures initiales et liens vérifiés sans régression.
- [x] Documentation française/anglaise fidèle aux preuves et aux limites des outils.
- [x] Campagne complète reproductible, avec plateformes et cas non exécutés explicites.

Une case n’est pas fermée par une intention, un contrôle de nom ou une
modification de l’énoncé demandé. Si une obligation échoue, indiquer le raccord
précis manquant ; ne pas déplacer la cible ni annoncer la réussite.

### 11.1. Résultats de la campagne locale

Les scripts, commandes, paramètres, attentes et empreintes ont été enregistrés
avant les runs confirmatoires, dans un répertoire extérieur neuf. Les essais
préparatoires et leurs échecs sont conservés séparément. Les sources sont
restées byte-identiques pendant la campagne ; seule cette clôture documentaire
du plan est rédigée ensuite. La campagne a été exécutée sous HEAD
`27546b9db4aa72769772d9253050e92fcfb0974d`, avec les modifications identifiées
dans ce plan avant leur commit de publication. Le protocole de réaudit publié
séparément désigne le SHA exact de ce commit scientifique.

| Contrôle | Résultat exécuté |
| --- | --- |
| `lake clean`, build public puis build complet | Succès ; 160 puis 183 jobs, sans erreur ni avertissement Lean. |
| `verify.sh` et `verify.ps1` | Succès sur les mêmes 181 fichiers Lean ; Bash et PowerShell 7 exécutés sur Windows. |
| Politique des diagnostics | Succès ; matrice de 288 diagnostics positifs et 576 négatifs, plus les contrôles unitaires. |
| Suite complète des deux wrappers | 34 scénarios sur chaque route, soit 68 résultats conformes aux attentes ; copies physiques indépendantes. |
| Fermeture de production | 159 modules, 290 dépendances locales ; seuls `Init` et `Init.Omega` admis depuis la toolchain épinglée. |
| Fixtures gelées | 26 fichiers et 28 sites ; les 23 fichiers initiaux sont byte-identiques. |
| Probes clients du réaudit | Les 66 déclarations positives compilent ; les 15 probes négatifs échouent pour leur raison attendue. |
| Audit des constantes | 18 255 constantes ; 360 exceptions générées, aucune déclaration écrite à la main dépendante d’un axiome. |
| Inventaire et intégrité | Aucun fichier Lean ni déclaration retiré par rapport aux références auditées ; 36 fichiers protégés inchangés. |
| Diff, manifeste, liens | Les deux contrôles de diff passent ; `lake update` ne change pas le manifeste ; aucun lien local cassé. |

Les quatre fondations, la licence, la toolchain, les figures et les anciens
fichiers scientifiques protégés restent inchangés. Seuls `Persistence.lean`
et son test Lean sont modifiés pour ce lot. Le renforcement explicite de
`Followed.cons` ajoute le raccord des références ; le certificat reçoit six
accords fermés : acceptation des cibles, lecture des cibles, origine reprise,
étapes suivies, références suivies et étapes internes. Il ne s’agit donc pas
d’une affirmation de signatures intégralement inchangées.

Le sweep indépendant brut classe deux déclarations de `Repr` comme
« manuscrites » et une déclaration `congr_simp` comme « non classée ». Leurs
origines ont été vérifiées dans les sources : les deux premières proviennent
du `deriving Repr` de `CandidateExtractionRun`, la troisième est la congruence
générée pour `firstIndexOf`. Le journal brut est conservé sans modification.
Ces trois cas expliquent la différence avec le classement exhaustif de
production : 357 exceptions déjà reconnues, plus ces trois cas générés, soit
360 ; aucun défaut manuscrit n’est dissimulé par ce reclassement.

### 11.2. Mutations et limites de leur interprétation

Le rejeu contient 55 entrées : les 52 patches gelés du réaudit, deux adaptations
gelées et un cas supplémentaire de confidentialité `AnswerTarget`. Résultat :
49 rejets, quatre acceptations inoffensives et deux anciens patches non
applicables, chacun remplacé par une adaptation exécutée et rejetée. Aucun
résultat de timeout n’est utilisé comme rejet.

- M06c/M06d/M06e révèlent deux productions effectives ; M06g/M06h révèlent
  une production supplémentaire sur un chemin extérieur à `step`. Le rejet
  vient des bornes du C compilé, sans le pin syntaxique direct retiré.
- M06f, auxiliaire correct, est accepté. M06a, partage éliminant une duplication,
  M07b, métadonnées inertes, et M07c, réécriture pure préservant la dépendance
  effective, sont également acceptés ; aucune perte de garantie n’est exigée
  artificiellement pour ces refactorisations.
- M14b et M15c remplacent les patches devenus non applicables M14 et M15b.
  Leurs suppressions de suivi interne et d’acceptation sont détectées par les
  consommateurs correspondants. M19c complète M19a/M19b : ouvrir le constructeur
  fait compiler la fixture privée, ce qui fait échouer le wrapper.
- M20e reproduit d’abord le faux diagnostic avec le compilateur, puis est
  refusé par la politique de source sur les deux routes. Les imports interdits
  directs, commentés, multilignes et indirects sont contrôlés sur des copies
  dont les artefacts mutants ont été reconstruits.
- M11c est rejeté par le contrôle compilé de lecture du support. Cela ne prouve
  pas une différence de valeurs entre lecture riche et projection runtime.

Les familles M11a, M16a/c/d et M18a–c ne sont pas annoncées comme des mutations
supplémentaires exécutées. Leur couverture est distincte : construction
historique et fixture `PrivateRegisterRealization` pour M11a ; permission,
pont et deux retours exacts pour M16a ; probes et accords universels sur les
événements et refus pour M16c/d ; variantes réellement exécutées de rejeu
direct, auxiliaire et fermeture M18d/e/f, ainsi que les pins de type et du
runtime, pour M18a–c. M19c, lui, a été ajouté et exécuté séparément.

Un rejet par confidentialité ou consommation d’une garantie protège cette
interface ; il n’établit pas sa nécessité mathématique universelle. De même,
un pin définitionnel de critère ne démontre pas qu’une reformulation du même
critère serait fausse. Les journaux distinguent ces raisons des rejets
substantifs et des cas inoffensifs.

### 11.3. Portée de la clôture

Cette campagne ferme les corrections locales prévues, sur les sources et
artefacts identifiés. Elle ne transforme pas un contrôle logiciel en preuve
de sécurité de tout Lean, ne prouve ni une complexité générale ni une mesure
de mémoire, et n’attribue pas au sweep brut une classification qu’il n’a pas
faite. Linux n’a pas été exécuté dans cette campagne ; aucun résultat Linux
n’est revendiqué. Un nouvel audit indépendant et toute publication restent
les étapes séparées de la section suivante.

## 12. Publication et audit indépendant ultérieurs

Seulement après les validations locales et une autorisation explicite :

1. Préparer le commit scientifique autonome et le pousser sur la branche
   autorisée, sans intégrer les travaux parallèles.
2. Vérifier le SHA distant exact. Préparer ensuite un prompt complet en anglais,
   sans placeholder, citant la cible inchangée, les révisions, la récupération
   autonome sur GitHub et les corrections effectivement incluses.
3. Demander une revue complète de la chaîne de l’agent, de F1–F7, des nouvelles
   frontières d’imports et de l’absence de régression. Ne pas limiter l’audit
   aux tests qui viennent d’être ajoutés ni demander un verdict positif.
4. Garder distincts le verdict mathématique, la fermeture concrète, la
   protection des interfaces, l’assurance de l’outillage et les plateformes.
5. Une fusion exige une demande séparée. Avant l’ouverture de la PR/MR,
   retirer les plans et documents de chantier de son arbre final ; si ces
   fichiers ont été committés, leur suppression appartient à la même PR/MR.
   Conserver les documents scientifiques et les instructions de reproduction
   pérennes.
6. Après une fusion autorisée, vérifier le commit de `main`, ses contenus,
   son manifeste et ses builds. La préparation d’un audit ou d’une PR ne
   clôt pas cette intégration.
