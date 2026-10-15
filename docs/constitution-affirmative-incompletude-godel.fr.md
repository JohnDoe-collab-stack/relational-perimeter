# Constitution affirmative et mécanisme d'incomplétude de Gödel

## Conclusion canonique à portée explicite

Pour toute instance de `SemanticallyDefinedProofArithmeticTheory`, sur le
langage objet arithmétique fixé, satisfaisant les contrats explicites de
codage, substitution des numéraux, diagonalisation, vérification des
dérivations, relation de preuve sémantiquement définie, correction sémantique et preuve
de la réflexivité de l'égalité, la formalisation exécute une chaîne qui
construit sa phrase diagonale, certifie que cette même phrase est vraie et non
prouvable en partageant le point fixe de la production reçue, démontre que sa
négation n'est pas davantage prouvable et qu'elle n'est aucune égalité
réflexive. La chaîne fixe ensuite exactement
l'issue consommée, inscrit le témoin dans un périmètre ordonné à plusieurs
étapes, réalise ses occurrences dans la continuation stricte et positive
produite par le turning, préserve leur ordre et distingue l'occurrence
résiduelle. La fermeture dirigée causale lit son candidat dans
l'interprétation finale, doit consommer la provenance historique pour
l'identifier au témoin produit et demande exactement `Truth(G) -> Proof(G)`.
La fermeture spécifiée historique, plus forte, se factorise vers cette
fermeture dirigée par son identification `Truth(G) = Proof(G)` ; la collision
est redérivée du point fixe exact, de la correction et des deux lois de
représentation. Cette correspondance reste un théorème conditionnel pour toute
instance abstraite reçue. Le dépôt en donne désormais une réalisation nommée
pour l'arithmétique de Heyting (HA) : calcul intuitionniste, postulats
arithmétiques usuels, codages et décodeurs, vérificateur numérique exécutable,
prédicat interne de preuve, diagonalisation interne et correction sont fermés
dans `heytingArithmeticEffectiveGodelSystem`. La conclusion correspondante est
`heytingArithmeticGodelPerimetralCorrespondence`. Aucune autre notion de
fermeture n'est rejetée.

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
cette phrase en `Empty`. La correction transforme aussi toute preuve supposée
de la négation de cette phrase en `Empty`, en appliquant sa vérité au témoin de
vérité déjà produit.

## Correspondance formelle

| Composant de l'argument standard | Composant formel | Loi utilisée |
| --- | --- | --- |
| Présentation abstraite de compatibilité | `EffectivelyPresentedSoundGodelSystem` | Codes naturels, décodeurs exécutables et vérificateurs booléens ; cette interface accepte des modèles dégénérés et ne constitue pas la cible arithmétique |
| Présentation arithmétique retenue | `SemanticallyDefinedProofArithmeticTheory` | Langage arithmétique fixé, substitution sémantiquement correcte, relation de preuve explicite, correction et preuve vérifiée de `t = t` |
| Réalisation nommée | `heytingArithmeticEffectiveGodelSystem` | Syntaxe du premier ordre arithmétique, dérivations HA, vérificateur primitif récursif, représentabilité interne de ce vérificateur, point fixe paramétrique et correction standard sont construits dans le dépôt |
| Réalisation sémantique HA | `heytingArithmeticSemanticallyDefinedProofArithmeticTheory` | Le langage arithmétique fixé est traduit vers HA, le même `haProofCheck` est représenté dans les deux sens par une formule binaire et la correction informative reconstruit les témoins existentiels dans `Type` |
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
| Indécidabilité sous correction | `producedNegationHasNoCheckedDerivation` | Une preuve vérifiée de `¬G` serait correcte et consommerait le témoin de vérité de `G` |
| Constitution et continuation | `ArithmeticExecutedGodelCausalParticipation` | Le témoin issu de l'issue exécutée devient la différence du périmètre ; le certificat de turning produit la continuation, ses occurrences intérieures et son occurrence résiduelle |
| Fermeture dirigée et provenance | `ArithmeticExecutedGodelDirectedClosureMeaning` | Son candidat est lu dans `recordedDifference`, aligné au témoin produit par `recordedProvenance`, puis sa conversion `Truth(G) -> Proof(G)` rencontre le point fixe |
| Fermeture spécifiée historique | `ArithmeticExecutedGodelCausalClosureMeaning` | La forme à égalité de types est équivalente à `CircularClosureMeaning` sur la même continuation et se factorise vers la fermeture dirigée ; elle n'est pas utilisée comme critère caractéristique de l'incomplétude |
| Contraste diagnostique dans un même système | `SemanticallyDefinedArithmeticGodelDiagnostic` | Le même prédicat `DirectedSemanticCompletenessAt` est satisfait en `0 = 0`, rejeté en `G`, et la continuation produite reste stricte |
| Frontière sélective effective | `EffectiveGodelSelectiveBoundary` | Un certificat accepté d'une phrase d'ancrage construit sa vérité et sa complétude dirigée locale ; la correspondance canonique rejette séparément cette complétude en `G`, impose que les deux phrases diffèrent et conserve la continuation stricte |
| Conclusion HA nommée | `heytingArithmeticGodelPerimetralCorrespondence` | La phrase HA produite est vraie dans le modèle standard et n'a pas de certificat HA accepté ; sa négation n'en a pas davantage, la continuation est stricte et les fermetures causale et dirigée sont rejetées |

Les adaptateurs `toGodelSyntax` et `toGodelInterpretation` transportent les
contrats vers le noyau diagonal sans fournir la conclusion. L'interface
générique `EffectivelyPresentedSoundGodelSystem` est conservée comme couche de
compatibilité abstraite : le contre-test permanent `abstractDegenerateSystem`
montre qu'elle accepte un univers singleton sans preuve. Elle n'est donc plus
utilisée seule comme évidence de la correspondance arithmétique. La cible
publique renforcée abstraite est
`semanticallyDefinedArithmeticGodelDiagnostic`. Elle ajoute au raccord R1 la
conséquence vérifiée que la phrase produite ne peut être aucune égalité
réflexive, puisque ces égalités possèdent une dérivation vérifiée, exclut
formellement tout vérificateur constamment faux, et compare dans le même
système la fermeture dirigée satisfaite en `0 = 0` à son rejet en `G`.

La réalisation nommée est distincte de ce diagnostic abstrait. Le module
[`HeytingArithmeticGodelInstance`](../RelationalPerimeter/Constitution/HeytingArithmeticGodelInstance.lean)
instancie directement `EffectivelyPresentedSoundGodelSystem`. Son
`haProofCheck` exécute le vérificateur numérique de l'histoire racine HA ; la
correction reconstruit une dérivation intuitionniste exacte depuis tout code
accepté. Le dispatcher n'énumère que les règles `0` à `21` et rejette le tag
`22` de l'élimination de la double négation. `provHA` est la formule
arithmétique obtenue à partir du graphe primitif récursif de ce même
vérificateur, et `provHA_spec` en donne la correspondance. Le point fixe
paramétrique est une dérivation HA interne, non une équivalence sémantique
supposée. Ces données construisent les deux directions de représentation de
la non-prouvabilité, puis alimentent sans hypothèse supplémentaire la chaîne
générique.

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

Dans l'accès abstrait `SemanticallyDefinedProofArithmeticTheory`, le certificat
diagonal objet, les transports de preuves et la correction restent des
prémisses. La réalisation HA ne les suppose pas : elle les construit dans ses
modules de syntaxe, de vérification, de représentabilité, de point fixe et de
correction. Le simple champ booléen d'une instance abstraite ne suffirait
toujours pas à établir cette portée ; c'est la fermeture concrète de ces
obligations, et non le seul nom de l'interface, qui justifie ici la portée HA.

Le module
[`HeytingArithmeticSemanticArithmeticInstance`](../RelationalPerimeter/Constitution/HeytingArithmeticSemanticArithmeticInstance.lean)
ferme concrètement ce raccord E2. Il construit les deux décodages exacts du
langage fixé, la substitution et la diagonalisation depuis les opérations HA,
et instancie `SemanticallyDefinedProofArithmeticTheory` avec exactement
`haProofCheck`. Les modules `InformativeSemantics` et
`InformativeRepresentability` transportent des témoins calculatoires dans
`Type` : une existentielle conserve son entier témoin, et l'exécution du graphe
primitif récursif construit le réalisateur de la formule de preuve. La formule
binaire utilisée par l'instance est la traduction certifiée de
`historyProofFormula TheoryHistory.root`; ses deux directions sont donc
dérivées du même vérificateur, pas reçues comme nouvelle hypothèse. Les
déclarations
`heytingArithmeticSemanticallyDefinedArithmeticGodelConclusion` et
`heytingArithmeticSemanticallyDefinedArithmeticGodelDiagnostic` en dérivent
sans prémisse supplémentaire la conclusion et le contraste annoncés.

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
`arithmeticHistoryOccurrences` élimine directement l'histoire reçue par le
lien exécuté et en extrait deux occurrences conservées comme données : le pas
`selfApply` et le pas `certify`. Leurs `LocatedStep` identifient les producteurs
exécutés, et `OccurrenceNext` établit que la certification suit immédiatement
l'auto-application. `executedOccurrenceCorrespondence` raccorde ensuite ces
occurrences aux deux occurrences périmétrales exactes sans les identifier entre
elles : seule la ressource produite est égalée. La sortie de `selfApply` est la
production portée par la première position, et la sortie de `certify` est le
témoin porté par la seconde. La réalisation nommée
`heytingArithmeticExecutedOccurrenceCorrespondence` applique ce raccord à la
même chaîne HA.
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

`directedClosureToProducedCompleteness` effectue la factorisation dirigée après
ce transport historique. `rejectDirectedClosure` ne réutilise pas seulement la
paire `trueWitness`/`unprovable` stockée :
`fixedPoint_rejectsProducedCompleteness` redérive la non-prouvabilité et la
vérité depuis le point fixe exact, `proofSound` et les deux directions de
représentation. `causalClosureToDirectedClosure` montre séparément comment
l'ancienne égalité de types induit cette obligation dirigée ;
`rejectCausalClosure` passe désormais par cette conversion. Le résultat public
sur l'ancienne continuation est transporté vers cette même continuation
canonique et passe par cette voie causale. Aucun de ces théorèmes n'appelle
`rejectInitialContraction`. L'ancien rejet générique reste disponible comme
résultat de compatibilité ; il n'est pas l'évidence citée pour la dépendance
gödelienne. C'est cette fermeture dirigée au témoin produit qui porte le
diagnostic d'incomplétude, et non l'égalité de types prise isolément.

Les contre-tests séparent deux causes. `UniformTotalSeed` admet aussi une
fausseté universelle non diagonale : son incohérence ne peut donc pas expliquer
le mécanisme. `UniformGodelOnlySeed`, au contraire, n'admet au niveau de sa
graine que la phrase diagonale commune. Cette phrase est bien admise, et
l'hypothèse de correction de cette graine est impossible par le théorème
diagonal. Par ailleurs, `UniformKernelSeed` est corrigé et admet une autre
application de la même famille syntaxique ; l'absence de preuve de `G` n'est
donc ni une exclusion de toute la famille, ni une propriété du seul squelette
du vérificateur.

Le contre-test permanent `kernelDecidedSentenceSupportsDirectedCompleteness`
exhibe en sens inverse une phrase du noyau qui est vraie et prouvable et porte
le même prédicat `DirectedSemanticCompletenessAt`. Plus fortement,
`SemanticallyDefinedArithmeticGodelDiagnostic` réalise ce contraste dans une
seule instance arithmétique reçue : `reflexiveZeroCompleteness` satisfait le
prédicat en `0 = 0`, tandis que la phrase diagonale produite le rejette et que
sa continuation reste stricte. `rejectProoflessChecker` démontre que le modèle
abstrait `Proof := Empty` du contre-probe ne peut pas fournir cette interface,
car la réflexivité donne déjà une preuve vérifiée. La notion dirigée n'est donc
pas contradictoire par construction. L'égalité de types historique peut encore
échouer sur une phrase vraie et prouvable à cause de la pluralité de ses
preuves ; elle reste une spécification de compatibilité plus forte, et non le
diagnostic primaire.

Deux échecs attendus permanents contrôlent en plus que ni une contradiction
arbitraire `Unit -> Empty`, ni une présentation dont `TotalLoop` est stipulé
égal à `Empty`, ne peuvent être passées à la fermeture causale exécutée. Un
probe séparé vérifie que le point fixe produit ne se transporte pas à
l'application non diagonale, et qu'un témoin étranger ne peut pas réutiliser
l'enregistrement historique sans fournir l'égalité de provenance manquante.

## Séparation explicative E1

Le module
[`GodelExplanatorySeparation`](../RelationalPerimeter/Constitution/GodelExplanatorySeparation.lean)
isole une propriété positive qui n'est pas la complétude interdite en `G`.
`EffectiveGodelSelectiveBoundary` contient exactement une phrase du système
reçu et un certificat accepté par son vérificateur. Sa vérité est obtenue par
la correction du même système, et sa complétude dirigée locale retourne ce
certificat déjà construit. Aucun rejet, aucune non-prouvabilité et aucune
conclusion sur `G` ne figurent parmi ses champs.

Dans HA, `heytingArithmeticGodelSelectiveBoundary` réalise cette propriété
avec la dérivation objet explicite de `0 = 0`, encodée puis acceptée par
`haProofCheck`. La correspondance canonique existante rejette en parallèle
`Truth(G) -> Proof(G)`. Les deux portées ne sont pas seulement distinguées par
leurs types : `heytingArithmeticReflexiveZeroDiffersFromProduced` démontre que
`0 = 0` n'est pas la phrase produite, car une égalité supposée transporterait
le certificat accepté jusqu'à `G` et contredirait sa non-prouvabilité.
`heytingArithmeticBoundaryDoesNotReduceToProducedCompleteness` exclut aussi
constructivement qu'une production de cette frontière fournisse la
complétude interdite en `G`.

Le contre-modèle permanent `abstractDegenerateSystem` conserve sa
correspondance gödelienne, sa participation causale et son rejet de la
fermeture spécifiée, mais son vérificateur constamment faux interdit toute
`EffectiveGodelSelectiveBoundary`. Il sépare donc cette nouvelle propriété de
l'ancien paquet abstrait sans modifier celui-ci. La fermeture dirigée causale
reste exactement équivalente à `Truth(G) -> Proof(G)` ; aucune nouvelle notion
de fermeture n'est introduite. Ce résultat constitue un candidat formel local
pour E1, et non un verdict d'audit extérieur.

## Limites restantes distinctes

La réalisation HA ferme dans le dépôt les obligations de codage, substitution,
vérification, représentabilité du prédicat de preuve, diagonalisation et
correction nécessaires à la conclusion nommée. Elle ne transforme pas le
résultat en variante de Rosser ni en théorème fondé sur la seule cohérence : la
portée demeure la forme sémantique fondée sur la correction annoncée plus haut.
Elle ne prétend pas non plus identifier définitionnellement ce calcul à toute
autre présentation éditoriale de HA ; une telle comparaison exigerait un
théorème de traduction séparé. Enfin, le statut de revue indépendante reste
`not_recorded` tant qu'un rapport extérieur portant sur le commit exact n'a pas
été reçu, lu et enregistré.

E2 est désormais fermée dans le dépôt par l'instance HA nommée de
`SemanticallyDefinedProofArithmeticTheory`, avec le même vérificateur et une
relation de preuve représentée dans les deux sens. E3 est fermée localement par
le raccord direct des étapes exécutées `selfApply` et `certify` aux occurrences
périmétrales exactes qui portent leurs sorties. Cette fermeture formelle ne
change pas la portée sémantique annoncée et ne vaut pas verdict d'audit
indépendant.
