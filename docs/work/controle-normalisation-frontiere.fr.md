# Normalisation contrôlée de la frontière reçue

Cette tranche poursuit D2 du [plan v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md), après
l’[ouverture contrôlée](controle-ouverture-frontiere.fr.md). Elle vise le calcul
entier de `normalizeGeneratedStructuralFrontierByFlip` depuis la frontière
effectivement produite. L’implémentation et sa qualification locale sont
terminées ; cette tranche conserve les obligations suivantes de D2.

## La relation recherchée décide la réduction

Les contextes reçus portent leur formule résiduelle et leur histoire de
décisions, avec leur provenance de génération. Le
[calcul syntaxique](../../Tests/LocalAlignment/DocumentaryControlFrontierNormalizationSyntax.lean)
transforme les littéraux et les décisions de la variable sélectionnée. Les
comparaisons lisent ces productions : d’abord la formule, puis l’histoire si
la première comparaison réussit. Le contrôle paie les cellules et les
comparaisons de variables parcourues.

La [recherche](../../Tests/LocalAlignment/DocumentaryControlFrontierNormalizationSearch.lean)
produit la même option de relation que le finder original. Une réussite forme
un témoin de `GeneratedStructuralFlipAtRelation` en `Type`. Une classification
exécute les deux directions et conserve leurs résultats et les équations de
recherche. Un échec reste un échec de ce finder précis.

La [normalisation](../../Tests/LocalAlignment/DocumentaryControlFrontierNormalization.lean)
normalise d’abord la queue reçue, puis insère la tête dans la frontière
effectivement retenue par cette première opération. Un témoin dirigé autorise
l’absorption correspondante. Une comparaison non résolue conserve le contexte
courant devant la sortie récursive. Cette disposition peut modifier l’ordre
des contextes ; elle est celle du moteur original.

## Conserver la construction entière

Le résultat construit est le paquet `AcceptedIrreducibleFrontierReduction` original
entier : la liste retenue, son `AcceptedFrontierCode` et la preuve
d’irréductibilité relative à la recherche. Une lecture de largeur seule ne
constitue pas ce résultat.

Chaque formation `identity`, `swap`, `absorbFirst`, `absorbSecond`, `prepend`
ou `compose` a une étape payée distincte. Les compositions utilisent les codes
réellement produits par la queue et l’insertion. Les indices et les listes
conservent les contextes reçus et leurs provenances ; une absorption ne
remplace pas les identités sources par l’égalité d’une valeur observée.

L’évaluation ultérieure de ce code construit les transports de préservation.
Son exécution et celle des fonctions de transport ont leurs propres coûts,
distincts de la formation de la syntaxe de routage.

`ControlMaster.expandedSearchCode` consomme la frontière de l’ouverture réelle,
puis cette réduction. `stageFromParts` conserve cette même réduction dans le
`Master.Stage` original entier. L’égalité du paquet est démontrée ; les
preuves propositionnelles sont effacées par la compilation, tandis que les
contextes et le code produit constituent les données transmises.

## Borne locale fermée

`bounded` démontre `Within (code formula selected frontier)
(bound formula selected frontier)` pour toute formule, variable et frontière
de contextes engendrés reçues. Sa réalisation concrète ne suppose pas le
succès d’une recherche ou d’un secours. Les interfaces génériques de listes
et de transformations sont instanciées avec leurs bornes démontrées.

La borne utilise la longueur de la frontière source et la somme `q` des poids
de sa syntaxe : transformation et comparaison des formules et des histoires.
Les preuves établissent que chaque contexte retenu provient de cette source
et que sa longueur ne croît pas. Elles permettent de majorer les insertions
sur les sorties réelles, sans calculer la normalisation pour choisir la borne.
Ses récurrences sont :

```text
I(q, 0)     = 3
I(q, n + 1) = (pairQuota(q) + (I(q, n) + 4)) + 1
pairQuota(q) = (q + q) + ((q + q) + 2)
B(q, 0)     = 3
B(q, n + 1) = (B(q, n) + (I(q, n) + 3)) + 1
bound       = B(q, longueur de la frontière source)
```

Ce majorant porte sur les pas du contrôle abstrait. Le calcul de `q`, de la
longueur et des récurrences est effectif ; le paiement et le majorant
indépendant de ce bootstrap restent à établir. La compilation emploie un
test natif de zéro pour les récurrences `Nat` de ce bootstrap. Ce site n’est
pas présenté comme une comparaison payée du normaliseur.

## Superviser les preuves et l’exécution

L’implémentation Lean est déléguée ; la relecture des définitions, des
hypothèses et des sources originales, les gardes C, les protocoles et la
qualification sont effectués par l’agent principal. Une compilation
intermédiaire a révélé des dépendances à `propext` et `Quot.sound` dans une
preuve arithmétique automatisée. Cette version a été refusée. Les bornes de
recherche ont ensuite été réécrites avec des lois constructives explicites
sur `Nat` ; leurs quinze audits sont sans axiome.

Le [protocole du composant](../../scripts/run-documentary-frontier-normalization-smoke.py)
fixe onze cas de normalisation, cinq cas de recherche et trois observations de
transport. Les sorties attendues précisent les formules, les décisions
ordonnées, la profondeur de provenance et les comptes de chaque constructeur
du code. Elles ne sont pas calculées par le normaliseur natif. Les observations
de transport utilisent le code retourné ; elles ne sont pas incluses dans le
coût local annoncé pour sa formation.

Les essais du composant utilisent la borne locale, le combustible exact de la trace,
une unité insuffisante et un surplus. Les anciens critères de livraison,
d’origine, de refus, de progression et de restauration restent ceux du
[protocole d’intégration](../../scripts/run-documentary-expanded-control-smoke.py).
Sa normalisation de deux enfants doit parcourir trois cellules de frontière,
deux recherches dirigées et une classification.

La [garde C](../../scripts/check-documentary-frontier-normalization-codegen.py)
contrôle les corps et fermetures nommés : absence de replay des moteurs natifs,
utilisation des flips produits, consommation des deux recherches et raccord
unique du normaliseur contrôlé. Ses mutations sont des entrées textuelles du
checker, pas des programmes corrompus compilés ni un audit externe.

La vérification complète réussit sur 347 fichiers Lean et 346 modules :
27 930 constantes, 364 exceptions de génération du compilateur et aucune
exception pour une déclaration écrite. Les 680 audits explicites des 48
modules de contrôle sont sans axiome, dont les 67 nouveaux noms de syntaxe,
de recherche et de normalisation. Les 23 fixtures d’échec attendu conservent
leurs diagnostics et leurs sites exacts.

Les dix-neuf contrôles du composant et leurs vingt-six audits runtime passent,
y compris l’égalité entre les étapes payées de routage et la somme des comptes
fixés de ses constructeurs. Les 31 contrôles d’intégration et leurs seize
audits passent avec les nouveaux comptes de normalisation. Les onze contrôles
de l’ouverture et les quatre histoires du bootstrap de génération restent
valides. Les gardes rejettent 1 735 mutations textuelles de normalisation et
2 279 mutations de la voie étendue. Les cellules de calcul, leurs sorties
et les sous-codes réellement produits sont conservés dans les corps C examinés.

La [qualification locale](controle-normalisation-frontiere-verification.json)
enregistre les 418 empreintes de sources et scripts figées avant la gate,
inchangées jusqu’à sa sortie. Les journaux des essais de développement et les
réparations restent distincts du run final. Cette qualification porte sur
l’arbre de travail ; `evidence_revision` reste `null`. Les qualifications
historiques et le registre scientifique restent inchangés.

## Portée et suite

La tranche conserve la cible, le contrat, l’instance maître et les qualifications
historiques. D2 reste ouvert pour l’évaluation du routage, les préservations et
les assignations exécutées ensuite, le paiement des bootstraps de bornes, les
autres indices, les frames et codecs, l’administration, les traces et les
allocations complètes. Les enveloppes globales de D3 et le secours sur le
présent conservé et rechargé de D4 restent à fermer. A conserve sa priorité
sur B.

Le raccord suivant est `ControlCompletion.decideCode`. Sous
`citationPreservation`, il doit évaluer le `stage.reduction.code` effectivement
reçu et composer les préservations réellement formées avec
`stage.opening.preservation`. Sous `citationRouting`, il doit ouvrir leur
application à la continuation réelle. `citationAssignment` doit ensuite ouvrir
la lecture de l’affectation transformée qui décide le candidat documentaire.
La taille du code peut majorer sa formation en transports ; elle ne majore
pas à elle seule l’invocation d’une affectation arbitraire.
