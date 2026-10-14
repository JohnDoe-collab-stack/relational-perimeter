# Constitution affirmative et mécanisme d'incomplétude de Gödel

## Conclusion canonique à portée explicite

Pour tout système effectivement présenté satisfaisant les hypothèses
explicites de codage, substitution diagonale, vérification des dérivations,
transport des équivalences, correction sémantique et représentation de la
non-prouvabilité, la formalisation exécute une chaîne qui construit sa phrase
diagonale, certifie que cette même phrase est vraie et non prouvable, l'inscrit
comme ressource d'un tout relationnel exactement réalisé, puis construit une
continuation stricte et positive qui conserve ce tout. Sur cette même
ressource, toute complétude sémantique locale `Truth(G) -> Proof(G)` est
impossible ; la fermeture totalisante spécifiée, plus forte parce qu'elle
identifie les types `Truth(G)` et `Proof(G)`, se factorise par cette
complétude et échoue donc. Le résultat explique ainsi le mécanisme
d'incomplétude visé par une constitution et une continuation affirmatives,
dans cette portée conditionnelle exacte ; il ne prétend ni avoir déjà
instancié ces hypothèses pour une théorie arithmétique particulière, ni
rejeter toute notion possible de fermeture.

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
| Présentation effective | `EffectivelyPresentedSoundGodelSystem` | Codes naturels, décodeurs exécutables et vérificateurs booléens |
| Syntaxe et numérotation | `encodeUnary`, `encodeSentence`, `decodeUnary`, `decodeSentence` | Les deux lois de décodage impliquent l'injectivité des codages |
| Substitution et lemme diagonal | `substitute`, `diagonalize`, `diagonalizeExact` | Le certificat vérifié relie l'auto-substitution à la substitution de la phrase codée |
| Dérivations | `CheckedSentenceProof` et `proofCheck` | Une preuve est un code naturel dont le vérificateur renvoie `true` |
| Équivalence prouvable | `CheckedSentenceEquivalence` et `equivalenceCheck` | Les transports de preuve et de vérité sont reçus séparément |
| Correction | `proofSound` | Toute preuve vérifiée fournit un témoin de vérité |
| Représentation de la non-prouvabilité | `representsUnprovabilityForward` et `representsUnprovabilityBackward` | La vérité de la formule substituée est équivalente, par deux fonctions, à l'absence de preuve |
| Phrase produite | `executeGodelDiagonalProduction` puis `executeGodelSentenceProduction` | La formule diagonalisée est produite avant son auto-application |
| Conclusion d'incomplétude | `certifyExecutedGodelWitness` | `trueWitness` et `unprovable` sont dérivés du point fixe et de la correction |
| Constitution et continuation | `executeGodelRegimeExit` | Le même témoin devient la différence du tout, puis la continuation canonique est construite |

Les adaptateurs `toGodelSyntax` et `toGodelInterpretation` montrent la
direction essentielle de la correspondance : les hypothèses standard
effectives fournissent les interfaces du dépôt sans fournir la conclusion.
`effectiveGodelPerimetralCorrespondence` montre la direction inverse utile :
ces interfaces produisent la phrase vraie non prouvable, l'obstruction de
complétude et les données constitutives supplémentaires. La réalisation
uniforme fermée du dépôt demeure un modèle exécutable distinct ; elle ne sert
pas, à elle seule, à revendiquer la portée arithmétique générale.

Le module
[`ArithmeticGodelCorrespondence`](../RelationalPerimeter/Constitution/ArithmeticGodelCorrespondence.lean)
fixe en outre un langage objet arithmétique avec zéro, successeur, addition,
multiplication, égalité, implication, conjonction et quantification
universelle. Son interface `EffectivelyPresentedSoundArithmeticTheory` exige
que `diagonalIffProof` soit une dérivation vérifiée du biconditionnel dans ce
langage objet. L’adaptateur `toEffectiveGodelSystem` fournit alors l’interface
générique, et `arithmeticGodelPerimetralCorrespondence` dérive la vérité, la
non-prouvabilité, la continuation affirmative et le rejet de la totalisation ;
aucune de ces conclusions n’est un champ reçu. Cette spécialisation demeure
conditionnelle : elle ne construit pas encore les données de l’interface pour
PA, Q ou une autre théorie arithmétique nommée.

## Ordre constitutif et identité de ressource

L'histoire `ExecutedGodelConstitutiveStep` impose successivement les passages
`received`, `diagonalize`, `selfApply`, `certify` et `continue`. La
certification consomme la production de phrase issue de l'étape précédente.
La présentation circulaire prend ensuite ce témoin certifié comme type de sa
différence et exige, par sa provenance, l'égalité au témoin transmis. La
continuation est `oneStepAfterPerimeter` de cette présentation précise ; son
extension stricte et sa réalisation locale exacte sont des données positives,
pas les conséquences d'une simple proposition d'existence.

Le turning ne fabrique donc pas tardivement un autre témoin : la production
diagonale et sa certification précèdent la continuation, et la continuation
consomme le témoin ainsi produit. L'apport constitutif supplémentaire par
rapport au seul lemme terminal de non-prouvabilité est l'histoire typée de ces
producteurs et consommateurs, l'inscription du témoin dans le tout, la
conservation des occurrences intérieures et la construction de la nouvelle
occurrence résiduelle.

## Obstruction exacte et contre-tests

`ExecutedGodelProducedCompleteness` isole l'obligation dirigée
`Truth(G) -> Proof(G)`. La vérité produite suivie de cette fonction contredit
directement le certificat `unprovable`. `ExecutedGodelTotalLoop` demande
l'identification plus forte `Truth(G) = Proof(G)` ;
`toProducedCompleteness` montre formellement sa factorisation par l'obligation
dirigée. Enfin, la spécification globale appliquée à la continuation stricte
produit ce total loop. C'est cette fermeture définie qui est rejetée, et non
toute fermeture concevable.

Les contre-tests séparent deux causes. `UniformTotalSeed` admet aussi une
fausseté universelle non diagonale : son incohérence ne peut donc pas expliquer
le mécanisme. `UniformGodelOnlySeed`, au contraire, n'admet au niveau de sa
graine que la phrase diagonale commune. Cette phrase est bien admise, et
l'hypothèse de correction de cette graine est impossible par le théorème
diagonal. Par ailleurs, `UniformKernelSeed` est corrigé et admet une autre
application de la même famille syntaxique ; l'absence de preuve de `G` n'est
donc ni une exclusion de toute la famille, ni une propriété du seul squelette
du vérificateur.

## Limite ouverte distincte

Le dépôt ne construit pas encore une instance de
`EffectivelyPresentedSoundGodelSystem` pour PA, Q ou une autre théorie
arithmétique nommée, avec l'arithmétisation interne complète de son prédicat de
preuve. Cette instanciation renforcerait la portée par un exemple standard
particulier ; elle n'est pas cachée dans la conclusion conditionnelle et reste
un travail à faire. Elle ne doit pas être confondue avec la correspondance
formelle générique déjà établie ni avec la réalisation uniforme exécutable du
dépôt.
