# Constitution affirmative et mécanisme d'incomplétude de Gödel

## Conclusion canonique à portée explicite

Pour toute instance de `SemanticallyDefinedProofArithmeticTheory`, sur le
langage objet arithmétique fixé, satisfaisant les contrats explicites de
codage, substitution des numéraux, diagonalisation, vérification des
dérivations, relation de preuve représentée, correction sémantique et preuve
de la réflexivité de l'égalité, la formalisation exécute une chaîne qui
construit sa phrase diagonale, certifie que cette même phrase est vraie et non
prouvable en partageant le point fixe de la production reçue, et démontre
qu'elle n'est aucune égalité réflexive. La chaîne fixe ensuite exactement
l'issue consommée, inscrit le témoin dans un périmètre ordonné à plusieurs
étapes, réalise ses occurrences dans la continuation stricte et positive
produite par le turning, préserve leur ordre et distingue l'occurrence
résiduelle. La fermeture spécifiée est équivalente à une fermeture causale qui
lit son candidat dans l'interprétation finale et doit consommer la provenance
historique pour l'identifier au témoin produit. Elle se factorise alors par
`Truth(G) -> Proof(G)` ; la collision est redérivée du point fixe exact, de la
correction et des deux lois de représentation. Cette correspondance est un
théorème conditionnel pour les contrats affichés : aucune instance de PA, Q ou
d'une autre théorie arithmétique nommée n'est revendiquée, et aucune autre
notion de fermeture n'est rejetée.

## Formulation standard retenue

La variante retenue est la forme sémantique, fondée sur la correction, du
premier théorème d'incomplétude. Un système formel possède une syntaxe et des
dérivations effectivement codées, une substitution diagonale correcte et une
formule qui représente l'absence de dérivation. Si ses dérivations sont
correctes pour la sémantique externe considérée, le point fixe
`G <-> non-prouvable(G)` ne peut pas avoir de preuve : une telle preuve donne
sa vérité par correction, donc sa non-prouvabilité par le point fixe et la
représentation, en contradiction avec la preuve reçue. Cette non-prouvabilité
redonne positivement la vérité de `G` par l'autre direction de la
représentation et du point fixe.

Cette formulation est plus forte dans ses prémisses que la version seulement
fondée sur la cohérence, et elle n'est pas la variante de Rosser. Sa conclusion
formalisée est exactement : une phrase diagonale construite, un témoin
externe de sa vérité et une fonction qui transforme toute preuve supposée de
cette phrase en `Empty`. Aucune non-prouvabilité de la négation de `G` n'est
affirmée ici.

## Correspondance formelle

| Composant de l'argument standard | Composant formel | Loi utilisée |
| --- | --- | --- |
| Présentation abstraite de compatibilité | `EffectivelyPresentedSoundGodelSystem` | Codes naturels, décodeurs exécutables et vérificateurs booléens ; cette interface accepte des modèles dégénérés et ne constitue pas la cible arithmétique |
| Présentation arithmétique retenue | `SemanticallyDefinedProofArithmeticTheory` | Langage arithmétique fixé, substitution sémantiquement correcte, relation de preuve explicite, correction et preuve vérifiée de `t = t` |
| Syntaxe et numérotation | `encodeUnary`, `encodeSentence`, `decodeUnary`, `decodeSentence` | Les deux lois de décodage impliquent l'injectivité des codages |
| Substitution et lemme diagonal | `substitute`, `diagonalize`, `diagonalizeExact` | Le certificat vérifié relie l'auto-substitution à la substitution de la phrase codée |
| Dérivations | `CheckedSentenceProof` et `proofCheck` | Une preuve est un code naturel dont le vérificateur renvoie `true` |
| Relation de preuve explicite | `SemanticallyDefinedProofArithmeticTheory.proofRelationFormula` | Sous l'affectation exacte `0 -> proofCode`, `1 -> sentenceCode`, sa vérité est transportée dans les deux sens avec le résultat du même vérificateur booléen |
| Provabilité et non-prouvabilité construites | `provabilityFormula` et `unprovabilityFormula` | `Prov(n)` est l'existentielle constructive sur le code de preuve ; `Unprov(n)` est sa négation |
| Équivalence prouvable | `CheckedSentenceEquivalence` et `equivalenceCheck` | Les transports de preuve et de vérité sont reçus séparément |
| Correction | `proofSound` | Toute preuve vérifiée fournit un témoin de vérité |
| Représentation de la non-prouvabilité | `representsUnprovabilityForward` et `representsUnprovabilityBackward` | Reçue par l'interface historique ; dérivée par le nouvel accès depuis la relation de preuve explicite et les transports sémantiques de substitution |
| Phrase produite | `executeGodelDiagonalProduction` puis `executeGodelSentenceProduction` | La formule diagonalisée est produite avant son auto-application |
| Conclusion d'incomplétude | `certifyExecutedGodelWitness` | Le point fixe est transporté depuis la production reçue ; il produit la non-prouvabilité, puis la vérité du même résultat |
| Constitution et continuation | `ArithmeticExecutedGodelCausalParticipation` | Le témoin issu de l'issue exécutée devient la différence du périmètre ; le certificat de turning produit la continuation, ses occurrences intérieures et son occurrence résiduelle |
| Fermeture spécifiée et provenance | `ArithmeticExecutedGodelCausalClosureMeaning` | La forme causale est équivalente à `CircularClosureMeaning` sur la même continuation ; son candidat est lu dans `recordedDifference` et aligné au témoin produit par `recordedProvenance` |

Les adaptateurs `toGodelSyntax` et `toGodelInterpretation` transportent les
contrats vers le noyau diagonal sans fournir la conclusion. L'interface
générique `EffectivelyPresentedSoundGodelSystem` est conservée comme couche de
compatibilité abstraite : le contre-test permanent `abstractDegenerateSystem`
montre qu'elle accepte un univers singleton sans preuve. Elle n'est donc plus
utilisée seule comme évidence de la correspondance arithmétique. La cible
publique renforcée est
`semanticallyDefinedArithmeticGodelPerimetralConclusion`. Elle ajoute au
raccord R1 la conséquence vérifiée que la phrase produite ne peut être aucune
égalité réflexive, puisque ces égalités possèdent une dérivation vérifiée.

Le module
[`ArithmeticGodelCorrespondence`](../RelationalPerimeter/Constitution/ArithmeticGodelCorrespondence.lean)
fixe en outre un langage objet arithmétique avec zéro, successeur, addition,
multiplication, égalité, implication, conjonction et quantification
universelle et existentielle. Son interface historique
`EffectivelyPresentedSoundArithmeticTheory` exige que `diagonalIffProof` soit
une dérivation vérifiée du biconditionnel dans ce langage objet et reçoit les
deux lois sémantiques de non-prouvabilité. Le nouvel accès
`SemanticallyDefinedProofArithmeticTheory` reçoit à leur place une formule
binaire de preuve, sa correction sémantique point par point relativement au
même vérificateur booléen, et la correction sémantique de la substitution des
numéraux. Il exige aussi une dérivation vérifiée de chaque égalité réflexive,
construit `Prov` et `Unprov`, puis dérive les deux lois historiques avant
d'appliquer la chaîne existante par
`semanticallyDefinedArithmeticGodelPerimetralConclusion`.

Le certificat diagonal objet, les transports de preuves et la correction
restent des prémisses. Le nouvel accès n'établit donc ni la représentabilité
arithmétique interne complète du vérificateur ni une instance pour PA, Q ou une
autre théorie nommée. Sa portée exacte est le théorème abstrait fondé sur la
correction et le point fixe dans le langage arithmétique affiché.

## Ordre constitutif et identité de ressource

L'histoire `ExecutedGodelConstitutiveStep` impose successivement les passages
`received`, `diagonalize`, `selfApply`, `certify` et `continue`. La
certification consomme la production de phrase issue de l'étape précédente.
Elle construit le point fixe de cette production exacte, utilise ce même point
fixe pour dériver la non-prouvabilité, puis utilise cette non-prouvabilité et
ce point fixe pour dériver la vérité ; les trois champs ne sont plus obtenus
par des appels indépendants reconstruisant la phrase canonique.
La présentation circulaire prend ensuite ce témoin certifié comme type de sa
différence et exige, par sa provenance, l'égalité au témoin transmis. La
présentation historique de `StrongPerimetralTurning.lean` reste inchangée et
n'est pas citée comme preuve de cette participation globale. La présentation
renforcée `arithmeticExecutedGodelCircularPresentation`, définie dans le module
de constitution arithmétique, distingue les étapes `produced`, `certified` et
`continued` ; les
porteurs correspondants contiennent respectivement la production exacte et le
témoin certifié puis retenu, et leurs compatibilités imposent ces mêmes
ressources. Ses deux positions non fermantes sont réalisées par deux
occurrences distinctes et ordonnées dans la continuation.
`arithmeticHistoryPinsExit` démontre en outre que
toute histoire allant de `received` à `regimeExited` fixe exactement l'issue
canonique produite par les quatre transitions. Ces lois sont regroupées dans
`ArithmeticExecutedGodelGlobalParticipation` pour la compatibilité historique.
La nouvelle `ArithmeticExecutedGodelCausalParticipation` ajoute le certificat
de turning qui engendre la continuation utilisée, l'extension étiquetée, sa
positivité, l'occurrence résiduelle distincte des deux occurrences intérieures
et l'interprétation finale contenant l'enregistrement de provenance.
`strictTurningContinuation` construit en particulier le préfixe strict depuis
le déploiement et le pas libre fournis par ce certificat ; c'est ce préfixe que
la factorisation terminale remet à la fermeture. L'interprétation finale est
elle aussi obtenue par `finalInterpretationFromPositive` du même certificat.

Le turning ne fabrique donc pas tardivement un autre témoin : la production
diagonale et sa certification précèdent la continuation, et la continuation
consomme le témoin ainsi produit. L'apport constitutif supplémentaire par
rapport au seul lemme terminal de non-prouvabilité est l'histoire typée de ces
producteurs et consommateurs, l'inscription du témoin dans le tout, la
conservation des occurrences intérieures et la construction de la nouvelle
occurrence résiduelle.

## Obstruction exacte et contre-tests

`ExecutedGodelProducedCompleteness` isole l'obligation dirigée
`Truth(G) -> Proof(G)`. `ExecutedGodelTotalLoop` demande l'identification plus
forte `Truth(G) = Proof(G)`. Sur la continuation causale,
`circularClosureToCausalClosure` transforme exactement la fermeture spécifiée
en une contraction portant le candidat lu dans le `recordedDifference` de
l'interprétation finale. `recordedSourceProvenance` extrait ensuite du
`recordedProvenance` la preuve `PLift (candidate = witness)` ; cette preuve est
consommée avant tout transport de la contraction au témoin produit.
`causalClosureToCircularClosure` établit la direction inverse sur la même
présentation et la même continuation : la cible n'est donc pas remplacée par
une fermeture plus forte.

`causalClosureToProducedCompleteness` effectue la factorisation dirigée après
ce transport historique. `rejectCausalClosure` ne réutilise pas seulement la
paire `trueWitness`/`unprovable` stockée :
`fixedPoint_rejectsProducedCompleteness` redérive la non-prouvabilité et la
vérité depuis le point fixe exact, `proofSound` et les deux directions de
représentation. Le résultat public sur l'ancienne continuation est transporté
vers cette même continuation canonique et passe par cette voie causale. Aucun
de ces théorèmes n'appelle `rejectInitialContraction`. L'ancien rejet générique
reste disponible comme résultat de compatibilité ; il n'est pas l'évidence
citée pour la dépendance gödelienne. C'est cette fermeture définie qui est
rejetée, et non toute fermeture concevable.

Les contre-tests séparent deux causes. `UniformTotalSeed` admet aussi une
fausseté universelle non diagonale : son incohérence ne peut donc pas expliquer
le mécanisme. `UniformGodelOnlySeed`, au contraire, n'admet au niveau de sa
graine que la phrase diagonale commune. Cette phrase est bien admise, et
l'hypothèse de correction de cette graine est impossible par le théorème
diagonal. Par ailleurs, `UniformKernelSeed` est corrigé et admet une autre
application de la même famille syntaxique ; l'absence de preuve de `G` n'est
donc ni une exclusion de toute la famille, ni une propriété du seul squelette
du vérificateur.

Deux échecs attendus permanents contrôlent en plus que ni une contradiction
arbitraire `Unit -> Empty`, ni une présentation dont `TotalLoop` est stipulé
égal à `Empty`, ne peuvent être passées à la fermeture causale exécutée. Un
probe séparé vérifie que le point fixe produit ne se transporte pas à
l'application non diagonale, et qu'un témoin étranger ne peut pas réutiliser
l'enregistrement historique sans fournir l'égalité de provenance manquante.

## Limite ouverte distincte

Le dépôt ne construit pas encore une instance de
`SemanticallyDefinedProofArithmeticTheory` pour PA, Q ou une autre théorie
arithmétique nommée, avec l'arithmétisation interne complète de son prédicat de
preuve. Cette instanciation renforcerait la portée par un exemple standard
particulier ; elle n'est pas cachée dans la conclusion conditionnelle et reste
un travail à faire. Elle ne doit pas être confondue avec la correspondance
formelle générique déjà établie ni avec la réalisation uniforme exécutable du
dépôt.
