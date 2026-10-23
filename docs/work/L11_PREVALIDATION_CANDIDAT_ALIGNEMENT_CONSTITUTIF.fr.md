# L11 — Prévalidation du candidat d’alignement constitutif neuronal

## 1. Statut et règle de verdict

Ce document est un rapport temporaire de chantier. Il ne remplace ni la cible
C1–C18, ni les garanties G1–G10, ni le raccord RC1–RC6, ni la livraison
scientifique de L12.

Verdict de L11 : **le noyau formel C1–C16, G1–G10 et RC1–RC6 est
prévalidé ; C17 n’est pas encore fermé sur l’arbre courant parce que les deux
portails officiels s’arrêtent honnêtement sur `STALE_SOURCE: TARGET_1`.** Cette
empreinte ne doit pas être actualisée dans L11. Sa révision contrôlée appartient
à L12, après gel d’un commit source stable et relecture du claim.

Deux productions scientifiques restent également absentes : le run
confirmatoire v10 et le gel puis run confirmatoire v11. Leur absence ne rend
pas faux le noyau Lean, mais maintient P8, S6, la comparaison confirmatoire et
C18 ouverts. Aucun essai exploratoire n’est présenté ici comme résultat.

## 2. Méthode de prévalidation

Chaque obligation a été relue selon la chaîne suivante :

1. énoncé normatif complet ;
2. producteur exécuté ou constructeur positif ;
3. indices et dépendances du témoin ;
4. transport ou recalcul éventuel ;
5. consommateur dans le certificat ou le runtime ;
6. fixture qui interdit la substitution correspondante ;
7. audit axiomatique et exécution des gates.

Un nom présent dans un fichier de régression n’a jamais été traité comme une
preuve suffisante. Les planchers C et G ont été confrontés aux objets dépendants
qu’ils exposent. Un resserrement a été apporté pendant cette passe : le témoin
G3 du contexte est désormais prélevé depuis
`learnedConstitutiveAlignmentClosure.alignedCausal.contextRole`, et non depuis
un nom global parallèle.

## 3. Prévalidation C1–C17

| Critère | Statut L11 | Producteur, consommation et frontière vérifiés |
| --- | --- | --- |
| C1 | Prévalidé | `ConstitutiveAlignmentCertificate` et `assembleConstitutiveAlignment` restent génériques ; `constitutive_alignment` et la décomposition publique sont des spécialisations. `checkUpdates_complete` conserve la quantification sur toute trace finie exécutée. |
| C2 | Prévalidé | Les exigences et contextes distincts de l’instance publique et de l’instance apprise alimentent les runs ; les rôles `contextRole` sont indexés par l’état exécuté. Les propositions produites changent avec le contexte. |
| C3 | Prévalidé | Les transformations locales sont dérivées d’arêtes effectives et composées. `learnedAlignedComposedSourceTransformation_nonidentity` et son analogue étendu ferment deux cas positifs non identitaires. Les fixtures post-hoc et arête nulle sont refusées. |
| C4 | Prévalidé | Les propositions reconfigurées sont dérivées par `learnedAlignedReconfiguredProposalDerivation` et `learnedExtendedReconfiguredProposalDerivation`. L’égalité terminale n’est pas un champ reçu par la mise à jour sérialisée. |
| C5 | Prévalidé | `CertifiedReconfiguration.transport` fournit séparément les rôles causaux de la source, de l’exigence et de l’autorisation. Les témoins sont consommés par les productions de transition ; les fixtures interdisent l’omission de la source, le contournement de l’exigence et la substitution d’une arête nulle. |
| C6 | Prévalidé | `LearnedExecutedCausalWitness` contient exigence, contexte et autorisation pour les états initial, aligné et étendu. La deuxième production est indexée par le successeur de la première dans `LearnedArtifactExecutionLineage`. |
| C7 | Prévalidé | L’autorisation est décodée, admise, incorporée à la reconfiguration et consommée par `executeLearnedAction`. La mise à jour de contournement est refusée par `missingConstitutiveDependency` avant installation. |
| C8 | Prévalidé | `LearnedHistoricalPreActionState` porte encore l’origine ; `executeLearnedHistoricalPreActionState` puis `executeHistoricalForgetting` produisent la mémoire réduite. Les deux sorties ne deviennent égales qu’après exécution. Les fixtures refusent l’entrée déjà oubliée et la projection constante. |
| C9 | Prévalidé | La sortie oubliée est `IndependentLearnedOperationalMemory`, structurellement plus pauvre que l’état historique. `learnedExecutedFutureForgetting_origin_not_recoverable` exclut toute reconstruction satisfaisant les deux lois de retour. |
| C10 | Prévalidé | `independentLearnedFutureContract` possède admission et refus exécutés. `learnedAlignedBypassFutureSeparator` est non vide et `learnedEveryExactRealizationSeparatesAlignedFromBypass` quantifie sur toute réalisation exacte. |
| C11 | Prévalidé | `LearnedActionWitness` est construit par `executeLearnedAction` depuis la préservation, les rôles causaux et l’autorisation ; l’effet est produit par `produceLearnedEffect` depuis cette occurrence exacte de l’action. Les substitutions d’action et d’effet sont refusées. |
| C12 | Prévalidé | `learnedConstitutiveAlignmentClosure` rassemble l’artefact appris indépendant, deux reconfigurations non identitaires, trois états causalement certifiés, deux installations, réutilisation, futurs, oubli et rejet du contournement sur une même lignée. |
| C13 | Prévalidé | Les noms d’admission/refus sont réservés aux décisions effectivement calculées ; les mises à jour alignée, étendue, renommée et de contournement ont des comportements typés correspondants. Aucun écart de vocabulaire nouveau n’a été trouvé. |
| C14 | Prévalidé | Les 165 fixtures échouent avec une classe, un site et un diagnostic exacts, sans erreur additionnelle. Les 14 blocs neuronaux possèdent des fixtures distinctes. Les nouveaux contrôles atteignent notamment source, exigence, autorisation, effet, oubli, recheck et obligation de scaling. |
| C15 | Prévalidé | La décomposition conserve séparément reçu, produit, dérivé, autorisé, transporté, recalculé, oublié et irrécupérable. Les textes canoniques FR/EN ont été remis en accord avec les statuts réels de v10 et v11. |
| C16 | Prévalidé | Le même run, la même action, le même effet et le successeur produit sont reliés dans les types et dans le code généré. Le diff des arbres Gödel, Tarski et Heyting Arithmetic contre `8a945f2` est vide. |
| C17 | **En attente de L12** | Build, audit exhaustif, fixtures, imports, stratification, code généré, manifeste et diff passent. Les portails complets restent rouges uniquement parce que `TARGET_1` est périmé. Il est interdit de déclarer C17 fermé avant révision contrôlée du registre puis repassage des deux portails. |

## 4. Prévalidation G1–G10

| Garantie | Statut L11 | Raccord vérifié |
| --- | --- | --- |
| G1 | Prévalidé | Le méta-contrat est fixé avant la trace. Les décisions de transition produisent les permissions consommées ; `EveryCheckedStepPreservesContracts` accompagne la lignée. |
| G2 | Prévalidé | Les deux `ExecutedTransitionProduction` partagent décodage, run, proposition, action, effet et successeur. L’action est construite une fois par branche matérielle et l’effet la consomme, ce que confirme le contrôle du code généré. |
| G3 | Prévalidé | Exigence, contexte, source antérieure et autorisation ont des rôles causaux effectifs. Le plancher G3 lit désormais le contexte depuis le certificat conjoint lui-même. |
| G4 | Prévalidé | `checkUpdates_complete` porte sur tout `ExecutedCheckedUpdateProgram`, sans borne de longueur. La trace apprise de deux étapes est seulement le témoin positif de non-vacuité. |
| G5 | Prévalidé | `submitUpdate` n’installe que le `CheckedUpdate` produit. `CertifiedRuntimeAccessibility` accompagne tout état accessible ; le contournement refusé n’a aucun successeur installable. |
| G6 | Prévalidé | Deux historiques distincts alimentent l’oubli exécuté ; la sortie commune préserve toute liste finie couverte et ne permet pas de reconstruire l’origine. |
| G7 | Prévalidé | Les entrées sérialisées ne portent pas le certificat cible. Les conditions locales sont définies avant le succès du checker. Les checkers incrémental et complet reconstruisent séparément leurs preuves et possèdent des théorèmes de complétude relative. |
| G8 | Prévalidé | Le graphe hétérogène couvre réseau, décodeur, action, effet, successeur, mémoire et contrat. Les fragments hors cône proviennent du certificat source, les fragments affectés sont recalculés, puis l’assemblage est installé et comparé au recheck indépendant. |
| G9 | Prévalidé | L’artefact appris est décodable, lié à ses empreintes de protocole/données/générateur, et la lignée positive contient deux reconfigurations non identitaires effectivement acceptées. |
| G10 | Prévalidé | Les candidats partagent source, intention et table courante. La même API installe l’aligné et refuse le contournement ; un futur non vide du contrat exact produit la divergence normative. |

## 5. Prévalidation RC1–RC6

| Raccord | Statut L11 | Vérification de dépendance |
| --- | --- | --- |
| RC1 | Prévalidé | `ConstitutiveMetaContract`, contrats, exigences, contextes, autorisations et schémas sont reçus. Les décisions exécutées produisent admission et témoins sans prétendre produire leur justification normative. |
| RC2 | Prévalidé | `ContractObligationsAt` indexe chaque témoin par l’état exact. Les producteurs de transition, certificats installés et sources futures sont reliés au même run et au même successeur par les indices et champs d’exactitude. |
| RC3 | Prévalidé | `ContractFutureObservationAt` est construit avant toute réalisation ; ni projection candidate ni succès global du checker n’entre dans son type. Les conditions locales autonomes ne sont pas définies par l’acceptation qu’elles caractérisent. |
| RC4 | Prévalidé | `ContractFutureObservationAt.outcome_exact` et `learnedEveryExactRealizationSeparatesAlignedFromBypass` quantifient sur tout type mémoire et toute réalisation exacte du contrat fixé ; le séparateur vient de la production neuronale raccordée. |
| RC5 | Prévalidé | Les obligations persistantes sont transportées, les obligations invalidées revérifiées, les fragments transportés/recalculés assemblés, puis ce certificat exact est consommé par l’installation et les étapes successives. |
| RC6 | Prévalidé | Transformations non identitaires, deux reconfigurations, réalisation exacte, oubli non trivial, continuation après oubli, installation alignée et refus du contournement coexistent sur la lignée apprise fermée. |

## 6. Fixtures et contrôles anti-substitution

La campagne complète rapporte :

- 165 fixtures attendues en échec ;
- exactement un diagnostic attendu par fixture ;
- ligne, colonne, classe et fragment JSON contrôlés ;
- aucune erreur additionnelle tolérée ;
- 14 blocs neuronaux associés à 14 fixtures distinctes ;
- 25 frontières négatives explicitement reliées au plancher G1–G10 ;
- 6 frontières négatives reliées au plancher C1–C17.

Les substitutions couvertes comprennent les cas critiques de L1–L10 :
autorisation étrangère, source ou exigence omise, transformateur post-hoc,
action ou effet reconstruit, historique déjà oublié, récupération de l’origine,
verdict incrémental donné au recheck, fragment d’une autre version, seconde
production substituée et obligation unitaire substituée à la famille de
scaling.

## 7. Constructivité, calculabilité et couverture

État vérifié sur l’arbre L11 :

- 466 fichiers Lean, chacun avec exactement un bloc `AXIOM_AUDIT` final ;
- aucun `axiom`, `sorry`, `admit`, `unsafe`, `noncomputable`, `Classical`,
  `propext`, `Quot.sound`, `native_decide` ou `implemented_by` dans les sources ;
- build exhaustif : 42 465 constantes, 460 modules, 478 exceptions générées,
  zéro exception manuscrite ;
- union des exécutables : 466 modules atteints depuis cinq racines compilées ;
- 366 modules de production inventoriés par la stratification, tous contraints,
  aucun orphelin ;
- dix-huit frontières d’import passent avec leur auto-test ;
- les cinq contrôles de code généré passent : instance unifiée, agent,
  signatures de continuation, maître variable et machine intégrée ;
- `lake update` conserve exactement le SHA-256 du manifeste
  `558A6999B82D0FAC6C385DA1A5CABEB50A594D6ECC7996F0BE33014CFB68AFA8` ;
- les liens locaux des 70 fichiers Markdown présents sont valides ;
- `git diff --check` ne rapporte aucun défaut ; les avertissements affichés ne
  concernent que la conversion future LF/CRLF par Git.

## 8. Non-régression historique

La comparaison contre `8a945f2` ne montre aucune modification sous :

- `RelationalPerimeter/Constitution/Godel/` ;
- `RelationalPerimeter/Constitution/Tarski/` ;
- `RelationalPerimeter/Instances/HeytingArithmetic/`.

Les frontières d’import Gödel, Tarski, HA et continuations passent toutes. Les
anciens résultats restent élaborés dans le build exhaustif. Leur registre
scientifique ne doit cependant pas être déclaré frais : l’échec
`STALE_SOURCE: TARGET_1` signifie qu’un claim enregistré consomme maintenant
des sources modifiées ailleurs dans sa fermeture. L12 doit relire ce claim,
fixer une révision probatoire et recalculer l’empreinte seulement après cette
revue ; remplacer l’empreinte mécaniquement serait une falsification de
l’évidence.

## 9. Relecture séparée des textes FR et EN

Les deux passages canoniques ont été relus séparément contre les preuves. Ils
conservent les mêmes limites : résultat relatif au méta-contrat reçu, domaine
local fini pour les décisions, quantification sur les traces acceptées et les
futurs couverts, aucune universalité morale, aucune borne générale de
complexité et aucune nouveauté comparative déjà acquise.

Leur dossier comparatif est maintenant conforme à l’arbre :

- v10 possède neuf méthodes et un protocole figé, mais aucun résultat
  confirmatoire ;
- la combinaison de référence et le recheck complet sont reconnus comme des
  succès locaux, donc aucun gain discriminant propre P1 n’est revendiqué ;
- v11 préenregistre la propriété complète et les coûts, mais reste un brouillon
  sans commit gelé ni résultat ;
- P8, S6, C18 et les conclusions de nouveauté restent ouverts.

## 10. Contrôles exécutés et résultats

| Contrôle | Résultat |
| --- | --- |
| `lake build +RelationalPerimeter` | Réussi après les ajustements L11 : 367 tâches, aucun avertissement ni axiome manuscrit |
| `lake build` | Réussi après les ajustements L11 : 468 tâches, 42 465 constantes, 460 modules, zéro exception manuscrite |
| plancher C1–C17 | `NEURAL_C1_C17_REGRESSION_FLOOR_OK lean=15 portals=2 negative=6` |
| plancher G1–G10 | `NEURAL_G1_G10_REGRESSION_FLOOR_OK lean=28 portals=2 negative=25 joint_learned=connected c1_c17=connected` |
| fixtures par bloc | `NEURAL_BLOCK_NEGATIVE_FIXTURES_OK blocks=14 fixtures=14 portals=2` |
| fixtures Lean | 165/165, diagnostics et sites exacts |
| stratification | 366 modules, tous imposés, aucun orphelin |
| imports | auto-test et 18 manifestes réussis |
| code généré | cinq contrôles réussis |
| union des exécutables | 466 modules, cinq racines |
| protocole v10 | Valide : 9 méthodes, 63 cellules, 7 ablations, résultats absents |
| protocole v11 | Valide comme brouillon : 5 mutations d’auto-test, résultats absents |
| manifeste | inchangé après `lake update` |
| liens Markdown | 70 fichiers contrôlés, aucun lien local invalide |
| docs `--lean` | Échec unique attendu : `STALE_SOURCE: TARGET_1` |
| portail PowerShell | Bloqué au même contrôle documentaire avant build |
| portail Bash | Exécuté sous Git Bash ; bloqué au même `STALE_SOURCE: TARGET_1` |

## 11. Conclusion de L11

L11 ne détecte plus de rupture conceptuelle dans la chaîne C1–C16, G1–G10 ou
RC1–RC6. Le resserrement G3 et la correction des statuts FR/EN ont été intégrés.
La prévalidation n’autorise toutefois pas le verdict terminal : C17 attend le
raccord scientifique de `TARGET_1`, v10 et v11 n’ont pas leurs productions
confirmatoires, C18 et les deux audits indépendants restent ouverts.

L’ordre obligatoire suivant est donc L12 : gel d’un commit source stable,
revue et raccord de `TARGET_1`, exécution intégrale des deux portails sur cette
révision, gel/exécution des protocoles autorisés, puis préparation des deux
audits indépendants sans promettre leur verdict.
