# Le cadre constitutif : relations, calcul et mémoire

Dans ce cadre, la constitution relationnelle des dépendances est primitive.
Le calcul travaille sur des objets dont la formation, la position et la
provenance sont déjà déterminées. Il recherche des transformations sur ces
objets, les applique et produit ainsi les obligations qui seront effectivement
poursuivies. La machine reprend depuis cette production. Sa mémoire conserve
les distinctions nécessaires aux futurs permis par son contrat.

La notation employée ici permet de suivre cette chaîne sans confondre un
objet constitué, sa production et les propriétés qu'on démontre à son sujet.
Elle rend les définitions existantes plus lisibles ; elle ne remplace pas les
types dépendants ni leurs témoins par une nouvelle fondation.

## Lire un objet et ses propriétés

Prenons une étape qui reçoit un curseur `c`, une formule `F` et des contextes
sources `S`. Trois écritures répondent à trois questions différentes :

```text
p : Step(c, F, S)       sur quelles données cette étape est-elle formée ?
p := step(c, F, S)      quelle production exécutée la détermine ?
p |= PreserveSAT       quelle garantie possède cette même étape ?
```

La première conserve les indices et les témoins de formation. La deuxième
désigne le résultat du producteur, pas un objet quelconque qui aurait les
bonnes propriétés. La troisième signifie que `PreserveSAT(p)` est vrai.

Dans ce document, `e |= P` se lit « l'objet `e` satisfait la propriété `P` ».
C'est une convention d'écriture pour `P(e)`, pas une commande Lean. Elle
permet une lecture des propriétés d'un même objet :

```text
e |= (A & B)     A(e) et B(e)
e |= (A | B)     A(e) ou B(e)
e |= (not A)     A(e) conduit à une contradiction
```

L'intersection ne demande pas deux objets ni deux exécutions : c'est le même
objet qui satisfait les deux propriétés. La disjonction propositionnelle ne
remplace pas un résultat calculé portant son constructeur et ses données.
La négation ne fournit pas, à elle seule, un algorithme décidant la propriété.

Nous écrirons aussi `(+entrées ; -sortie)` pour rendre visible ce qui est
reçu et ce qui est produit. Les signes n'établissent pas la production :
celle-ci doit être construite dans le code.

## Les relations primitives portent des témoins

Une compatibilité n'est pas seulement une annotation ajoutée à deux valeurs.
La fondation reçoit une famille de types relationnels et un témoin de la
compatibilité considérée :

```text
Compatible : Implicit -> Explicit -> Type
k : Compatible(i, e)
```

`k` est le témoin positif du rapport entre cet implicite `i` et cet explicite
`e`. Le remplacer par « il existe une compatibilité » ferait disparaître le
témoin précis dont une construction peut avoir besoin.

Un nœud local réunit un explicite, un implicite, une différence, sa provenance
et ce témoin de compatibilité. Le périmètre raccorde ensuite les nœuds par
des témoins supplémentaires : l'implicite du nœud courant est compatible avec
l'explicite du suivant. Ces raccords constituent une structure ; une liste de
valeurs lues dans les nœuds ne la remplace pas.

La distinction entre constitution et propriété est donc :

```text
k : Compatible(i, e)       témoin reçu et utilisable
objet := construire(k)    objet formé en utilisant ce témoin
objet |= P                propriété démontrée de cet objet
```

Cette règle ne dit pas que toute relation du cadre doit être non triviale.
Elle dit ce qu'une construction reçoit et ce qu'elle doit effectivement
utiliser. La non-trivialité d'une instance se vérifie dans cette instance.

## Une frontière peut être exactement déterminée sans être une clôture

Le premier fichier de fondation sépare les rôles internes déjà réalisés du
rôle résiduel. Sous les hypothèses de réalisation exacte, d'extension fidèle,
de séparation entre ancien et nouveau et de résidu contractile, une partie
nouvelle positivement donnée détermine une unique occurrence résiduelle.

« Contractile » signifie ici qu'un centre est fourni et que tout rôle
résiduel lui est égal. « Fidèle » impose notamment que les étiquettes
distinguent les occurrences. L'unicité vient de ces hypothèses précises,
pas d'un principe disant que toute nouveauté serait unique.

Le retournement abstrait distingue ensuite la frontière canonique de sa
continuation stricte. Dans les interfaces concernées, une admission qui
tenterait la totalisation interdite est réfutée. La continuation existe,
mais reste hors de ce régime exactement classifié.

```text
continuation : Extension(frontière, suivante)
continuation |= Strict

régimeAdmis(x) -> x = frontière
suivante != frontière
```

Cette présentation résume des constructions conditionnelles dont les
hypothèses sont explicites. Elle ne transforme pas une interface générique
en instance réalisée. Elle sépare aussi la compatibilité d'une jonction et
l'identification de ses extrémités : la première n'autorise pas automatiquement
la seconde.

## L'histoire constitue les occurrences

Dans la génération libre, la nouvelle constitution incorpore la précédente,
la formation courante et les accords de provenance. La production fournit
ensemble la cible et le pas qui la relie à la source :

```text
(+source ; -cible, -pas)

(cible, pas) := generate(source)
pas : GeneratedStep(source, cible)
```

L'histoire assemble ces pas. Pour prolonger une histoire, le nouveau pas
doit partir de sa cible actuelle :

```text
h   : History(Step, origine, courant)
pas : Step(courant, suivant)
-----------------------------------------
extend(h, pas) : History(Step, origine, suivant)
```

Une occurrence désigne un pas dans cette histoire précise. Sa source, sa
cible et son ordre se retrouvent par la structure de l'histoire. Une ancienne
occurrence prolongée et l'occurrence fraîche ne deviennent pas la même
occurrence parce qu'une lecture leur attribue la même valeur.

À ce niveau, une lecture est seulement :

```text
lecture : Occurrence(h) -> Valeur
```

Elle attribue des valeurs aux occurrences constituées. Elle ne les constitue
pas et n'est pas supposée injective. Une égalité de lectures ne permet donc
pas de remonter à une égalité d'occurrences sans une garantie supplémentaire.

La provenance historique reste, elle, indexée par l'origine constituée
complète. La conserver au travers d'une formation est autre chose que
conserver seulement sa valeur observable.

## Un transport exact possède deux lois de retour

Lorsqu'on change de représentation, le cadre exige de préciser ce qui passe
et comment on le retrouve. Pour un transport exact entre deux types :

```text
t : ExactTypeTransport(Source, Cible)

t.forward  : Source -> Cible
t.backward : Cible -> Source

t.backward(t.forward(s)) = s
t.forward(t.backward(c)) = c
```

Les deux lois conservent exactement les éléments transportés. Elles
permettent, par exemple, de reconnaître dans une histoire prolongée chacune
des occurrences anciennes et son occurrence fraîche.

Une implication entre propriétés n'est pas ce transport. Une application
qui préserve l'acceptation n'est pas nécessairement inversible. Et un
transport exact de types ne préserve pas automatiquement toute structure
supplémentaire : l'ordre, la provenance ou la participation doivent être
raccordés par les lois qui les concernent.

L'écriture `e |= A & B` décrit les garanties d'un objet ; elle ne dispense
jamais de fournir les applications et les lois de retour lorsqu'un passage
entre strates les exige.

## Le calcul produit sa décomposition avant de continuer

La couche computationnelle lit d'abord la matière issue de la génération
constitutive : histoire, état produit, occurrences anciennes et fraîches.
Cette génération ne décide pas encore quelles branches doivent être
poursuivies indépendamment.

Une étape reçoit cette matière, exécute la recherche, applique la relation
trouvée et produit sa décomposition. Ses résultats partagés alimentent les
producteurs suivants. La continuation reçoit l'état et la frontière ainsi
obtenus :

```text
(+c, +F, +S ; -p)
p := VariableMaster.step(c, F, S)

p |= Raccord & PreserveSAT

suite : History(j, p.next, F, p.frontier)
------------------------------------------------------
cons(p, suite) : History(j + 1, c, F, S)
```

`Raccord` et `PreserveSAT` sont ici les noms explicatifs des propriétés
exposées dans l'[essai de notation](ESSAI_NOTATION_PRESENT_PRODUCTION_CONTINUATION.fr.md).
La première épingle le curseur suivant et la frontière au résultat utilisé.
La seconde garantit que la viabilité SAT de la frontière est conservée.

La tête n'a pas la suite future parmi ses entrées. L'exécuteur construit
`p`, puis poursuit sur `p.next` et `p.frontier`. L'indépendance envers
l'horizon restant est prouvée pour cette production. « Pendant l'exécution »
désigne cet ordre des dépendances et des primitives, pas une durée physique
ni l'imprévisibilité du résultat.

La succession n'est donc pas une juxtaposition d'états compatibles : l'état
suivant est une sortie de la production présente, et cette sortie devient
l'entrée effective de la continuation.

## Regrouper des obligations n'identifie pas leurs sources

Deux alternatives structurelles distinctes peuvent devenir une seule
obligation opérationnelle si la transformation trouvée et sa préservation
autorisent à ne plus les poursuivre séparément pour le critère considéré.

La transformation agit sur les continuations typées de la source. La preuve
séparée garantit la préservation de l'acceptation. On ne choisit donc pas
après coup une seule continuation acceptée pour fabriquer le regroupement.
Inversement, un chercheur qui ne fournit aucun transport maintient les
alternatives concernées ; cet échec ne prouve pas l'impossibilité de tout
transport.

Sur les profils de l'histoire de rôles exécutée, le régime enregistre les
cibles effectivement produites :

```text
carry : Profil(h) -> Obligation

carry(p) = carry(q)
  iff cibleProduite(p) = cibleProduite(q)

p != q reste possible
```

L'égalité à droite vient de la normalisation exécutée et de ses traces.
Le régime est une réalisation exacte de l'image des cibles : il n'ajoute
pas un regroupement indépendant. Ses lois de retour concernent les
représentations d'obligations, pas la récupération de chaque profil source.

Pour la machine SAT, la différence se voit sur des contextes reçus. Avec la
même formule `[[positive 12, positive 1, positive 2]]`, la même profondeur,
la même variable sélectionnée et le même chercheur, une décision antérieure
vraie sur la variable 1 conduit à une branche retenue ; une décision fausse
conduit à deux. La formule demande qu'au moins une de ces trois variables
soit vraie. Les continuations viables et la distinction des enfants sont
construites dans les deux cas.

Ce scénario montre le rôle des histoires reçues dans la recherche. Ce ne
sont pas deux préfixes déclarés atteignables d'une même course canonique.

## La relation trouvée devient une capacité réutilisable

La machine reçoit le même maître public, une formule, des contextes
constitués et des permissions de lecture. Lors d'une reprise, la production
vivante retourne le sélecteur utilisé pour ouvrir les contextes SAT. La
recherche SAT fournit le code de réduction, sa frontière retenue et le
programme à configurer.

```text
production vivante
  -> sélecteur retourné
  -> ouverture et recherche SAT
  -> code de réduction
  -> programme configuré et frontière retenue
```

Le programme configuré agit ensuite sur de nouvelles entrées sans refaire
cette recherche. Pour chaque continuation typée concernée, son action donne
exactement la lecture de la continuation transportée. La préservation de SAT
est une autre garantie. L'admission d'un paquet brut vérifie sa position et
sa taille ; elle ne certifie pas que ce paquet satisfait SAT.

La prochaine recherche SAT reçoit la frontière laissée par la précédente.
Le raccord est orienté : le moteur vivant fournit son sélecteur à SAT ;
la frontière SAT alimente la recherche SAT suivante. Ce montage ne prétend
pas que SAT pilote en retour le moteur vivant.

À chaque demande, le runner actif lie une seule paire produite :

```text
(suivant, événement) := perform(mémoire, demande)
émettre(événement)
poursuivre(suivant, demandesRestantes)
```

Il ne relance pas `perform` pour obtenir séparément l'événement et l'état
suivant. Cette propriété d'exécution est contrôlée dans le code compilé ;
elle ne découle pas de la seule écriture d'une intersection de propriétés.

## La mémoire répond d'un contrat de futurs

La mémoire n'a pas à conserver toute différence passée. Elle doit conserver
les distinctions qu'une demande future autorisée peut encore révéler.
Le contrat fixe ces demandes et les réponses exigées avant la réduction.

Deux mémoires sont équivalentes sous un contrat `C` lorsque toutes les
listes finies de demandes ont les mêmes résultats observables, y compris
les événements et les refus. Les demandes conduisant à un refus restent
donc dans la quantification :

```text
FutursEgaux_C(m1, m2)
  iff pour toute liste finie q de demandes de C,
      outcome_C(m1, q) = outcome_C(m2, q)
```

Ces futurs caractérisent ce qui doit rester distinguable. Ils ne sont pas
des données causant rétroactivement le présent, ni une archive à stocker.
La transition présente reçoit seulement la mémoire et la demande courantes.
Le contrat intervient dans la justification de ce qu'on peut éliminer.

Pour le noyau cohérent de la machine, la projection réduite satisfait une
caractérisation exacte :

```text
project(m1) = project(m2) iff FutursEgaux_C(m1, m2)
```

Toute autre réalisation exacte de ce contrat qui fusionne les deux mémoires
doit respecter cette équivalence future. La nécessité porte sur leur
distinguabilité comportementale, pas sur la conservation de champs ou
d'encodages particuliers. Une impulsion future peut, par exemple, révéler
une différence entre connexions qui n'apparaît pas dans l'observation présente.

Deux sources peuvent donc rester distinctes dans leur histoire tout en
ayant la même mémoire réduite : aucune demande du contrat ne réclame alors
de les distinguer. Ce n'est pas une preuve que leurs histoires sont égales.
Changer les permissions peut rendre la distinction de nouveau nécessaire.

Le contrat intégré ajoute les demandes de routage et de lecture SAT.
Tous ses futurs finis sont préservés par la réalisation actuelle. Sa
minimalité complète reste distincte de la minimalité établie pour le noyau.
Les contrats de continuation des profils ont également leur propre domaine ;
ils ne sont pas substitués au contrat de la machine.

## L'extensivité lit ce qui a déjà été constitué

Les profils sont formés à partir de l'histoire dépendante des rôles et de
leurs occurrences réalisées. Leurs témoins de source, de formation, de cible
et de provenance restent attachés à ces occurrences. L'extensivité en donne
ensuite une lecture quantitative. Elle n'est pas une nouvelle constitution.

Dans la sous-classe binaire, cette lecture compte `2^n` profils, où `n` est
le nombre de rôles de l'histoire ; dans le maître public, `n = input + 1`.
Un régime surjectif vers ses obligations conserve exactement cette pleine largeur
si et seulement si `carry` conserve séparément chaque identité source :

```text
nombreProfils(h) = 2^n

largeur(régime) = 2^n iff Injective(carry)

profil -> obligation -> adresse
```

L'adressage séparé est construit à partir de l'injectivité et passe par les
obligations du régime. Il ne contourne pas le régime pour adresser directement
les profils. Le fait fini sur une surjection est général ; le contenu
constitutif et exécuté est porté par la construction de l'histoire et de
son régime, pas par la nouveauté supposée de ce fait combinatoire.

Le même carrier de profils reçoit aussi le régime public exécuté de largeur
un, sans égaliser les profils sources. Des politiques comparatives sur les
rôles déjà produits donnent des largeurs `2^k`. Ce résultat ne dit pas que
toute non-injectivité supprime toute croissance exponentielle : une largeur
`2^(n-1)` peut subsister. Il caractérise exactement la conservation de la
pleine largeur extensive `2^n` comme largeur opérationnelle.

Le nombre de profils, le nombre de branches SAT retenues, la mémoire et le
coût du calcul restent des grandeurs différentes. Aucun coût total ni aucune
borne polynomiale générale pour SAT ne se déduit de la seule largeur un.

## La chaîne complète

```text
relations primitives et témoins positifs
  -> constitution, histoire et occurrences
  -> contextes reçus et recherche exécutée
  -> transformation trouvée et préservation
  -> décomposition opérationnelle produite
  -> action configurée et continuation effective
  -> mémoire exacte sous contrat
  -> observations et lectures quantitatives
```

Une même production peut satisfaire plusieurs propriétés. Ce qui assure la
continuité de la détermination entre les strates n'est toutefois pas le fait
de lui attribuer plusieurs prédicats : ce sont les raccords exacts, les
témoins positifs et les lois de transport construits à chaque passage.

La notation sert à voir simultanément cette production et ses garanties.
Elle laisse visibles les différences entre constitution, réalisation,
admission, acceptation, obligation et observation. Les normes et l'adéquation
d'un régime restent elles aussi distinctes. `NormativeAdequacy` reçoit une
spécification et une famille de témoins d'adéquation indexée par les
occurrences concernées ; l'admission seule ne construit pas ces témoins.

Cette explication porte sur le cadre et sa machine logicielle construite.
Elle ne fournit pas encore un modèle physique relativiste ni une incarnation
matérielle. La temporalité établie ici est celle de la production et de la
continuation typées.

## Correspondance avec les sources

| Passage expliqué | Définitions et garanties à consulter |
| --- | --- |
| Rôles internes, résidu et extension fidèle | [SegmentedResidualRole](../../SegmentedResidualRole.lean) : `ExactInternalRealization`, `FaithfulExtension`, `positiveExtension_hasUniqueResidualOccurrence`. |
| Frontière, continuation stricte et régime | [AbstractSegmentedTurning](../../AbstractSegmentedTurning.lean) : `BoundaryGenerator`, `CoreCoupledObstructedRegime`, `coreCoupledTurning`. |
| Deux applications et leurs lois de retour | [ExactTypeTransport](../../ExactTypeTransport.lean) : `ExactTypeTransport`. |
| Relations primitives et constitution libre | [StrongPerimetralTurning](../../StrongPerimetralTurning.lean) : `LocalNode`, `PerimeterSpine`, `FreeConstitutionCore`, `generate`. |
| Occurrences, lectures et provenance | [StrongPerimetralTurning](../../StrongPerimetralTurning.lean) : `History.Occurrence`, `History.OccurrenceReadout`, `HistoricalProvenanceRecord`, `NormativeAdequacy`. |
| Génération avant la recherche | [ConstitutiveGeneration](../../RelationalPerimeter/Computation/ConstitutiveGeneration.lean) : `iteratedHistory`, `successorOccurrenceSplit`. |
| Profils de rôles constitués | [RelationalProfileConstitution](../../RelationalPerimeter/Computation/ConstitutiveSearch/RelationalProfileConstitution.lean) : `RelationallyConstitutedOccurrence`, `DependentRelationalRoleHistory`, `RelationalOccurrenceProfile`. |
| Production et continuation du maître | [MasterResourceExecution](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MasterResourceExecution.lean) et [VariableMasterExecution](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/VariableMasterExecution.lean) : `VariableMaster.step`, `History`, `head_horizon_independent`. |
| Cibles produites et obligations | [ExecutedOutputObligations](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExecutedOutputObligations.lean) et [UnifiedPublicCertificate](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean). |
| Action sur les continuations SAT et préservation | [StructuralGlobalContextRelation](../../RelationalPerimeter/Computation/ConstitutiveSearch/SAT/StructuralGlobalContextRelation.lean) : `mapContinuation`, `mapContinuation_accept`. |
| Machine et transition partagée | [MasterRuntime](../../RelationalPerimeter/Computation/Machine/MasterRuntime.lean) et [MasterContract](../../RelationalPerimeter/Computation/Machine/MasterContract.lean) : `MasterMachine.receive_exact`, `run_shared_transition`, `all_futures_exact`. |
| Distinctions nécessaires du noyau | [ConstitutiveLiveExecution](../../RelationalPerimeter/Computation/Machine/ConstitutiveLiveExecution.lean) : `ConstitutiveExecution.minimality`, `any_realization`. [Minimality](../../RelationalPerimeter/Constitution/Continuation/Minimality.lean) expose l'interface générale des réalisations exactes. |
| Théorème de pleine largeur | [RelationalRoleExtensiveFamily](../../RelationalPerimeter/Computation/ConstitutiveSearch/RelationalRoleExtensiveFamily.lean) : `BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_preservesConstitutedIdentities`. |

La [chaîne scientifique canonique](../science/chaine-constitutive-machine.fr.md)
et sa [table d'évidence](../science/preuves-chaine-constitutive-machine.fr.md)
précisent les contrats et les résultats cités. La
[cible canonique](../conclusion-largeur-exponentielle-conservation-identites.fr.md)
reste inchangée par ce document.

Document explicatif de travail, confronté à la branche `relativite` au commit
`466abaa877a7cec778853621e6d677f655895f55`. Les règles en blocs `text` sont
une notation documentaire, non un nouveau calcul formel. Le client Lean de
l'essai précédent vérifie la règle de production et son raccord à la
continuation ; il n'est pas présenté comme une formalisation indépendante
de tout ce document.

La vérification locale du document a résolu 34 déclarations citées ou utilisées
comme ancrages dans un client important seulement `RelationalPerimeter`.
Les trois petites preuves du client sur les propriétés d'un même objet et
les retours du transport, ainsi que les neuf déclarations de production
auditées, n'affichent aucun axiome. Les liens locaux et le contrôle documentaire
statique passent. Ces contrôles ne constituent pas un nouvel audit indépendant.
