# Essai de notation : présent, production, continuation

Document de travail sur la branche `relativite`, confronté aux sources du
commit `466abaa877a7cec778853621e6d677f655895f55`.
Il ne modifie ni les fondations, ni le code, ni la cible scientifique
[canonique](../conclusion-largeur-exponentielle-conservation-identites.fr.md).

## Ce que la notation doit rendre lisible

Une étape reçoit un état et des contextes déjà constitués. Elle exécute la
recherche, produit une action avec sa préservation, puis détermine la frontière
qui sera effectivement poursuivie. La continuation reçoit cet état suivant et
cette frontière, pas des remplaçants choisis indépendamment.

Nous voulons pouvoir lire simultanément **ce qui produit le résultat** et
**quelles propriétés ce même résultat possède**. La lecture des types comme
prédicats aide pour le second point. Elle ne remplace pas la constitution
relationnelle nécessaire au premier.

La chaîne reste celle du projet :

```text
relations et témoins constitutifs
  -> histoire, occurrences et contextes reçus
  -> recherche exécutée
  -> action et préservation séparée
  -> décomposition produite
  -> continuation effective
  -> mémoire sous contrat
  -> observations et lectures quantitatives
```

Cet essai développe les passages centraux. Il ne reconstruit pas les relations
primitives à partir de leurs propriétés aval. La
[chaîne scientifique](../science/chaine-constitutive-machine.fr.md) reste la
référence pour l'ensemble.

## Trois écritures qui ne doivent pas se confondre

| Écriture | Sens dans cet essai |
| --- | --- |
| `p : Step(c, F, S)` | La production est formée sur ce curseur `c`, cette formule `F` et ces contextes sources `S`. Ses indices et ses témoins restent présents. |
| `p |= P` | La propriété `P` est vraie de cette production précise. Cela ne constitue pas à nouveau `p`. |
| `p := step(c, F, S)` | Le producteur exécuté détermine `p`. Ce n'est pas le choix d'un objet quelconque satisfaisant `P`. |

`p |= P` est ici une convention documentaire pour `P p`. Lean conserve sa
distinction entre données et preuves ; aucun nouveau jugement n'est ajouté à
son langage. L'essai ne met pas en place un calcul de types intersection : il
vérifie une notation de propriétés sur les objets déjà définis dans le projet.

Nous écrirons aussi `(+c, +F, +S ; -p)` pour indiquer les entrées reçues et la
sortie produite. Les signes ne prouvent ni terminaison, ni existence, ni partage
d'une exécution. Dans cet exemple, l'existence vient de la définition Lean
`step`, pas des signes.

## Une production avant sa continuation

Fixons les entrées réelles :

- `c : MasterResources.Cursor`, le curseur du maître avec ses ressources
  constituées ;
- `F : SAT.Cnf`, la formule reçue ;
- `S : VariableMaster.States F`, les contextes constitués sur cette formule.

La règle de production est :

```text
entrées : (+c, +F, +S)
producteur : VariableMaster.step

p := step(c, F, S)
-------------------------------------------
sortie : -p : Step(c, F, S)
```

La définition exécute les producteurs suivants dans un support de références
typées. Chaque producteur lit les ressources déjà présentes dans ce support :

```text
curseur reçu
  -> tête du maître produite
  -> ouverture des contextes avec la variable découverte dans cette tête
  -> recherche et réduction de la frontière ouverte
  -> frontière retenue lue dans cette réduction
  -> curseur suivant lu dans cette même tête
```

À l'intérieur de la tête, l'ordre est lui aussi explicite : découverte, application,
décomposition, assemblage, puis continuation par références. L'ouverture SAT
n'est pas une partition fournie comme entrée. Une recherche locale qui ne trouve
pas la transformation considérée maintient les obligations concernées ; elle ne
prouve pas l'inexistence de toute transformation possible.

La règle de continuation est ensuite :

```text
p := step(c, F, S)
suite : History(j, p.next, F, p.frontier)
------------------------------------------------------
History.cons(p, suite) : History(j + 1, c, F, S)
```

Les indices de la suite sont les sorties de `p`. Le futur n'est pas une prémisse
de `step`. Il devient une continuation possible seulement après ce raccord.
L'exécuteur lie une fois `p`, puis appelle la suite avec `p.next` et `p.frontier`.

Ce n'est pas une preuve que le futur serait imprévisible. C'est une contrainte
précise sur les dépendances de la production présente : elle ne reçoit ni la
suite terminée, ni l'horizon restant. `head_horizon_independent` exprime ce
point pour l'exécuteur existant. Il ne mesure pas un temps physique.

Toutes ces définitions sont dans
[VariableMasterExecution.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/VariableMasterExecution.lean).

## Plusieurs propriétés du même résultat, sans deuxième production

Sur une production déjà formée, définissons deux propriétés :

```text
Raccord(p) :
  p.next est le successeur du maître
  et p.frontier est la frontière effectivement retenue par p.reduction

PreserveSAT(p) :
  la frontière source admet une continuation acceptée
  si et seulement si la frontière produite en admet une
```

L'intersection signifie :

```text
p |= Raccord & PreserveSAT
```

**Une seule production possède les deux propriétés.** Cela ne signifie pas
produire un objet pour le raccord et un autre pour SAT. En Lean, les preuves des
deux propriétés peuvent être réunies par `And` ; cette paire de preuves n'est
pas une paire d'exécutions.

Voici une traduction vérifiable sur les types existants. Les deux prédicats
sont des lectures de `p`, pas une nouvelle représentation de son état :

```lean
import RelationalPerimeter

set_option autoImplicit false

namespace EssaiNotation
open ConstitutiveSearch
open ConstitutiveSearch.EndogenousDecomposition

def Raccord {c : MasterResources.Cursor} {F : SAT.Cnf}
    {S : VariableMaster.States F} (p : VariableMaster.Step c F S) : Prop :=
  And (p.next = VariableMaster.nextCursor c) (p.frontier = p.reduction.retained)

def PreserveSAT {c : MasterResources.Cursor} {F : SAT.Cnf}
    {S : VariableMaster.States F} (p : VariableMaster.Step c F S) : Prop :=
  Iff (FrontierViable (SAT.generatedStructuralBranchSystem F) S)
    (FrontierViable (SAT.generatedStructuralBranchSystem F) p.frontier)

theorem meme_production (c : MasterResources.Cursor) (F : SAT.Cnf)
    (S : VariableMaster.States F) :
    let p := VariableMaster.step c F S
    And (Raccord p) (PreserveSAT p) := by
  dsimp only
  exact And.intro (And.intro (VariableMaster.step_next_exact c F S)
    (VariableMaster.step c F S).frontierExact)
    (VariableMaster.step_viable_iff c F S)

def continuer {j : Nat} {c : MasterResources.Cursor} {F : SAT.Cnf}
    {S : VariableMaster.States F} (p : VariableMaster.Step c F S)
    (suite : VariableMaster.History j p.next F p.frontier) :
    VariableMaster.History (j + 1) c F S :=
  VariableMaster.History.cons p suite

end EssaiNotation
/- AXIOM_AUDIT_BEGIN -/
#print axioms EssaiNotation.Raccord
#print axioms EssaiNotation.PreserveSAT
#print axioms EssaiNotation.meme_production
#print axioms EssaiNotation.continuer
/- AXIOM_AUDIT_END -/
```

Les occurrences répétées de `step` dans les énoncés et leurs preuves ne sont
pas un nouveau programme runtime. Le partage réel se lit dans les `let` et les
références du producteur et de l'exécuteur ; l'intersection seule ne le garantit
pas. La préservation transporte des continuations acceptées et établit
l'équivalence de viabilité. Elle ne donne pas, par elle-même, un transport
réversible de tous les objets ni l'identité des sources regroupées.

## Le consommateur machine reçoit les productions, pas seulement leurs propriétés

Dans [MasterRuntime.lean](../../RelationalPerimeter/Computation/Machine/MasterRuntime.lean),
`receive` initialise la machine depuis l'instance maître existante. Une reprise
`advance(m)` suit ensuite cette règle, avec `scope` et `F` fixés :

```text
u := ConstitutiveExecution.produce(m.core.live)
v := produceProblem(scope, F, u.action.selected, m.problem.frontier)
m' := (installProduced(u).state, v.next)
```

La même production `u` fournit le sélecteur à la recherche SAT et l'état installé
au noyau. La production `v` fournit la frontière poursuivie et le programme de
routage. `advance_frontier_is_produced` et `advance_preserves_SAT` raccordent
ces sorties au résultat effectif de la recherche et à sa préservation.
`ScopedProblemProduction.route_exact` relie ensuite le routage aux lectures de
la continuation transportée, pas seulement à une largeur identique.

Pour une requête de la machine, nous pouvons lire les modes ainsi :

```text
entrées : (+m, +requete)
t := perform(m, requete)
sorties : (-t.event, -t.state)
suite exécutée depuis t.state
```

Dans [MasterContract.lean](../../RelationalPerimeter/Computation/Machine/MasterContract.lean),
`run` lie une transition `t`, utilise son événement et poursuit depuis son état.
`run_shared_transition` expose ce raccord ; `run_exact` relie ce chemin actif à
la spécification. Le contrat à fonctions séparées `next` et `event` sert de
spécification : l'appeler séparément pour chaque lecture ne serait pas une
justification de l'exécution unique. Celle-ci repose sur le chemin apparié et
ses contrôles compilés existants, non sur la notation `(+m ; -t)`.

## Le futur caractérise la mémoire ; il ne produit pas rétroactivement le présent

Le contrat machine est fixé avant la comparaison des mémoires. Il comprend les
reprises, lectures, impulsions, routages et refus décrits par ses requêtes.
`all_futures_exact` quantifie sur toute liste finie de ces requêtes, avec leurs
entrelacements. Il préserve les observations, événements et admissions du
contrat riche sous la projection et l'exécution réduite.

Nous notons :

```text
m |= RepondExactement(C, source)
```

Cette propriété compare les réponses de `m` à celles de `source`, pour tous les
futurs finis du contrat `C`. Elle n'ajoute pas une archive de ces futurs à `m`.
Les témoins d'admission et leurs transports restent ceux de
[ExactRealization](../../RelationalPerimeter/Constitution/Continuation/Minimality.lean) :
ils ne sont pas remplacés par un simple booléen.

La production présente utilise ses entrées déjà constituées. La quantification
sur les futurs sert à établir quelles différences doivent rester distinguables.
Ce sont deux dépendances différentes. Une équivalence de futurs sous contrat
ne prouve pas l'identité des histoires sources.

L'essai ne transfère pas la minimalité du noyau à toute la mémoire SAT intégrée.
Cette dernière garde ses contextes, lus par les recherches suivantes. Il ne
confond pas non plus le contrat machine avec un accès arbitraire à toute
l'histoire.

## Où cette notation aide, et où elle ne suffit pas

Elle aide à écrire une règle dont les entrées, le producteur et le raccord à la
suite sont immédiatement visibles ; puis à regrouper les garanties portant sur
ce même résultat, sans inventer une autre instance.

Elle ne permet pas de remplacer les indices `Step(c, F, S)` par une étiquette
générale « production correcte ». Deux objets satisfaisant les mêmes propriétés
ne deviennent pas la même occurrence. De même :

- `A` implique `B` ne fournit pas les deux transports avec leurs lois de retour ;
- « le chercheur n'a rien trouvé » ne signifie pas « aucun témoin possible » ;
- nier une propriété exige sa réfutation constructive, pas un complément
  automatiquement décidable ;
- une intersection de garanties ne prouve ni une borne de coût, ni une
  exécution unique, ni une incarnation matérielle.

La lecture par propriétés est donc utile pour **les propriétés d'un objet déjà
constitué**. Dans la traduction testée, les prédicats portent encore sur des
objets indexés : nous n'avons pas démontré qu'un langage de types non dépendants
remplacerait cette formalisation. Les dépendances constitutives entre sources,
productions et continuations restent les indices et témoins Lean existants.
Les effacer pour tout exprimer par prédicats serait changer la méthode.

Sur `relativite`, cet essai précise l'ordre causal actuellement formalisé. Il
ne définit encore ni métrique, ni temps propre, ni équation physique. Un modèle
physique devra fournir ses propres objets et lois sans confondre cet ordre avec
une mesure temporelle.

## Vérification de l'essai

Contrôles effectués sur le checkout indiqué en tête du document :

- build ciblé de `VariableMasterExecution` et `MasterContract`, avec leurs
  dépendances : succès, 172 jobs ;
- bloc Lean ci-dessus placé hors du dépôt et élaboré avec `lake env lean` :
  succès ; ses quatre déclarations ne dépendent d'aucun axiome ;
- comparaison du bloc documentaire et du client élaboré : contenus identiques,
  à la seule normalisation des fins de ligne près ;
- `scripts/check-scientific-docs.py --static` : succès, y compris les liens du
  nouveau document ;
- `scripts/check-scientific-docs.py --self-test` : sept tests réussis ;
- contrôle du diff et des espaces de fin de ligne : succès. Aucun fichier
  suivi n'est modifié ; seul ce document de travail est ajouté.

Les deux contrôles Python utilisent Python 3 disponible dans l'environnement.
Pour reproduire le contrôle Lean, extraire le bloc tel quel dans un fichier
hors du dépôt et l'élaborer depuis ce checkout. Le build ciblé n'est pas une
nouvelle reproduction complète de toutes les gates du projet.

Ces contrôles vérifient la traduction de la notation et ses références. Ils ne
constituent ni un nouvel audit indépendant ni une nouvelle preuve de la cible.
Les sources Lean, documents canoniques et fondations restent inchangés. Ce
document de travail doit être retiré avant une intégration dans `main`, sauf
décision explicite d'en faire une documentation canonique revue.
