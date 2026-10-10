# Calcul entier et formation documentaire sous carburant

Cet incrément poursuit D2 de la [spécification v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md),
sur `codex/align-persist-recovery`, depuis
`d61fac4aa81fbfe58be6a1fd1887c91049fb5a3d`. Il prolonge la
[construction du producteur](controle-producteur-documentaire.fr.md). Les anciens
rapports et relevés restent historiques. A conserve la priorité sur B.

Les deux opérations du catalogue, somme et différence orientée `droite − gauche`,
sont maintenant exécutées par un calcul instrumenté. La formation conserve
le résultat effectivement obtenu, le producteur effectivement construit et
la formation antérieure. Les égalités démontrées portent sur l'action, la
décision et l'étape documentaires entières.

Ce passage traite le calcul entier et la formation d'une déduction.
**D2 entier reste ouvert** : le maître de citation, la formation des citations,
les assemblages et les coûts de composition, de trace et d'allocation de
l'interprète ne sont pas encore tous décomposés.

## Même opération, interprétation explicite

Le [paquet du producteur](../../Tests/LocalAlignment/DocumentaryControlProducer.lean)
conserve désormais son code de catalogue, issu de la même règle que sa
fonction d'opération. `Packet.operation_agrees` prouve, pour toutes les
valeurs des deux arguments, que l'interprétation de ce code est celle de
l'opération du producteur conservé.

[ControlArithmetic.code](../../Tests/LocalAlignment/DocumentaryControlArithmetic.lean)
reçoit ce code et les valeurs issues des deux lectures payées. Il retourne
le résultat et une égalité avec `Deduction.evaluate` pour ces mêmes données.
Cette égalité est effacée à l'exécution. Le calcul instrumenté n'appelle
pas ensuite l'ancienne opération pour produire ou vérifier son résultat.

Le producteur demeure dans le témoin de formation. Son ancienne fermeture
d'opération demeure donc une donnée conservée ; elle n'est plus invoquée
sur le chemin instrumenté de cette déduction. Ce changement est un
raffinement du catalogue reçu, avec preuve d'accord, et non un ajout d'une
nouvelle opération ou d'une tâche différente.

## Réalisation constructive et coût

La première réalisation emploie une récursion structurelle sur les naturels.
La somme positive parcourt le second naturel, puis produit les successeurs
au retour. La différence naturelle annule ensemble les deux naturels
jusqu'au premier zéro. L'analyse des signes raccorde ces calculs aux quatre
cas de l'addition entière. La différence orientée utilise la négation
effectivement produite avant cette addition.

Toutes ces constructions et leurs bornes sont compilables. Les preuves
n'utilisent pas les lemmes arithmétiques automatiques dont les dépendances
sortiraient des restrictions du dépôt. Les 21 audits explicites du nouveau
module arithmétique sont sans axiome.

| Étiquette | Donnée effectivement examinée ou construite après paiement |
| --- | --- |
| `integerOperation` | Cas de l'opération reçue |
| `integerSign` | Signes et naturels des deux valeurs reçues |
| `integerNaturalCell` | Cas naturel et descente sur les arguments effectifs |
| `integerNaturalReturn` | Successeur du résultat récursif effectif |
| `integerSignReturn` | Entier positif ou négatif issu du résultat naturel |
| `integerNegate` | Négation de l'entier reçu |

Les bornes `addBound`, `sumBound` et `bound` dépendent des valeurs reçues.
Les théorèmes `add_bounded`, `difference_bounded`, `sum_bounded`,
`negate_bounded` et `bounded` couvrent tous les naturels et entiers typés,
sans plafond ajouté aux opérandes. La borne de la différence naturelle,
`droite + 1`, peut être conservatrice lorsque l'autre naturel s'annule tôt.

Cette réalisation est **unaire** : une somme dont le second naturel est grand
peut nécessiter beaucoup de transitions. Elle donne une décomposition et une
preuve de terminaison bornée, sans revendiquer une optimisation du calcul.
Une réalisation binaire demanderait ses propres preuves constructives et
un nouveau raccord d'interprétation.

Les conversions natives, successeurs, prédécesseurs, comparaisons à zéro et
constructions natives d'entiers restent des primitives de la réalisation.
Une transition sémantique ne constitue pas une borne physique uniforme de
ces primitives sur les grands entiers. Le calcul de la borne et la
réservation de ses moyens restent dans D3 ; ils ne deviennent pas gratuits
parce qu'une formule de borne a été définie.

## Formation effectivement assemblée

[ControlFormation.code](../../Tests/LocalAlignment/DocumentaryControlFormation.lean)
ouvre les quatre constructions qui suivaient auparavant une unique étiquette
d'entrée dans la formation :

| Étiquette | Production partagée |
| --- | --- |
| `formationValues` | Couple du résultat calculé et des anciennes valeurs |
| `formationWitness` | `Formation.produced`, avec l'ancienne formation et le producteur reçu |
| `formationResources` | Support portant ces valeurs et ce témoin |
| `deductionProducer` | Action portant ce support effectivement assemblé |

Une égalité de types aligne les indices du témoin déjà construit.
Elle ne reconstruit ni le producteur ni le résultat. `formFromSupport`
emballe le support reçu ; `FormationAction.eq_form` établit son égalité
avec l'action documentaire d'origine.

`ControlFormation.bounded` prouve la borne de quatre transitions.
`ControlDeduction.bounded` compose permission, lectures des prémisses,
construction du producteur, calcul arithmétique et formation. La permission
absente refuse avant toute lecture de prémisse, tout calcul arithmétique
et toute formation.

`ControlDeduction.actual_decision` et `ControlStep.actual_step` conservent
la décision et l'étape d'origine. Le certificat d'accomplissement consomme
l'action et la trace effectivement obtenues.

## Contrôles exécutés

Le [relevé de cet incrément](controle-calcul-formation-documentaire-verification.json)
porte les empreintes LF, la clôture des imports, les commandes, les résultats
et les obligations ouvertes. Il conserve une révision d'évidence nulle tant
que cet arbre de développement n'a pas une nouvelle révision Git.

La gate complète `scripts/verify.ps1` a réussi sur 309 fichiers Lean :
25 949 constantes, aucune exception écrite, 23 fixtures de refus attendu.
Les sources Lean et les scripts de contrôle sont restés identiques aux
empreintes figées avant cette exécution. Les 156 audits explicites des onze
modules de contrôle et les 60 audits de déduction sont sans axiome.

Le [contrôle du C](../../scripts/check-documentary-arithmetic-codegen.py)
vérifie les continuations différées, le code de catalogue reçu, les valeurs
lues et le partage du résultat, du producteur, de l'ancienne formation et
du support. Il interdit les appels de recalcul d'origine dans ces corps.
Les certificats ne doivent pas entrer dans le calcul ni dans la formation.

Les fixtures textuelles du contrôle compilé sont des tests des gardes du
checker. Elles ne sont pas des binaires mutants exécutés, un audit complet
du graphe d'appels ou une mesure physique du tas.
Les trois contrôles rejettent ensemble 136 mutations : 56 de l'interprète,
33 du producteur et 47 du calcul et de la formation.

Le [smoke arithmétique](../../scripts/run-documentary-arithmetic-smoke.py)
compare les valeurs à un oracle Python indépendant, avec des valeurs
attendues littérales dans le client Lean généré. Il couvre les deux opérations
sur les opérandes de −4 à 4, ainsi que quatre cas sur de grands entiers.
Ses 166 cas sont vérifiés à chacun des 32 carburants : 5 312 verdicts de
valeur, trace et seuil, avec sept audits runtime sans axiome.

Le [smoke documentaire](../../scripts/run-documentary-interpreter-smoke.py)
couvre 800 verdicts documentaires, 234 de permission, 72 de position,
32 de ressources et neuf d'intégration. Les nouveaux seuils sont :

| Parcours documentaire | Seuil exact | Résultat conservé |
| --- | ---: | --- |
| Citation du maître | 2 | Paquet existant ; coûts internes encore ouverts |
| Différence de 43 et 42 | 74 | Valeur 1, origines [1, 2] |
| Somme de deux occurrences de valeur 1 | 44 | Valeur 2, origines [1, 2, 1, 2] |
| Règle interdite | 19 | Refus sans lecture des prémisses ni calcul |
| Prémisse gauche absente | 3 | Événement manquant |
| Prémisse droite absente | 5 | Événement manquant |

La somme échoue à 43 transitions et conserve sa sortie à 49.
Les occurrences et leurs références restent distinctes, y compris lorsque
leurs valeurs sont égales.

## Obligations encore ouvertes

Cet incrément ne ferme pas la ligne entière demandée :

- Ouvrir le maître de citation et sa formation, en conservant son unique
  tête, sa recherche, son ouverture, sa réduction, sa continuation et sa sortie.
  `VariableMaster.MasterHead` possède un constructeur privé ; son entrée
  publique actuelle `masterHead` effectue ensemble quatre extensions puis
  la continuation. La décomposition devra fournir une entrée de construction
  contrôlée conservant ses mêmes égalités, et rouvrir la qualification du
  module maître concerné au registre. Les empreintes historiques ne doivent
  pas être rafraîchies automatiquement.
- Instrumenter les assemblages de citation, déduction et entrée manquante,
  y compris l'incorporation, les extensions et les liaisons différées.
  Le transport actuel d'une action de déduction construit encore une extension
  depuis le producteur d'origine ; ce passage doit être examiné et raccordé
  avant de revendiquer le partage de toute la chaîne.
- Couvrir le travail de composition des continuations, la construction des
  traces et des paquets de l'interprète, puis le modèle d'allocation déclaré.
- Fermer D3 et D4 : bootstrap borné, moyens protégés, fermeture des successeurs
  et secours effectivement achevé dans son enveloppe.

CONT-03 et P15 restent donc ouverts, ainsi que les autres étapes A et B.
Aucun nouvel essai du modèle ni audit indépendant n'est annoncé.
