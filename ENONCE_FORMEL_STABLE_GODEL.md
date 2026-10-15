# Énoncé formel stable

Soit `S` une réalisation de `EffectivelyPresentedSoundGodelSystem`, et posons :

```text
E := effectiveGodelExecution(S)
G := E.witness.production.sentence
P := godelPerimetralPresentation(E)
H := godelPerimetralContinuation(E)
```

Alors la formalisation construit simultanément les données suivantes.

## 1. Production gödelienne exécutée

La chaîne suivante produit le même énoncé `G` :

```text
diagonalisation → auto-application → certification
```

Elle établit :

```text
G = godelSentence S.toGodelSyntax S.unprovabilityFormula
G ↔ ¬Proof(G)
Truth(G)
Proof(G) → Empty
```

Le deuxième énoncé désigne le point fixe représenté par `ProvableIff` entre
`G` et l'application à son propre code de la formule de non-prouvabilité.

Cette production est portée par une histoire ordonnée possédant des
occurrences distinctes pour la diagonalisation, l'auto-application et la
certification : [Diagonal.lean](RelationalPerimeter/Constitution/Godel/Diagonal.lean#L206).

## 2. Constitution affirmative

Le témoin exécuté de `G` constitue la différence initiale et la provenance de
`P`. Le cadre construit ensuite :

```text
Whole(P)
```

puis une continuation stricte :

```text
StrictContinuation(P, H)
```

Cette continuation possède une occurrence nouvelle, distincte des occurrences
de production et de certification. Elle conserve comme source la ressource
certifiée, le même témoin `G` et sa provenance exacte :
[`GodelAffirmativeConstitution`](RelationalPerimeter/Constitution/Godel/PerimetralCorrespondence.lean#L439).

On obtient donc affirmativement :

```text
Whole(P) ∧ StrictContinuation(P, H)
```

avant toute hypothèse de réadmission ou de fermeture.

## 3. Hypothèse de réadmission totalisante

Une admission de `H` dans le même régime est :

```text
Admission(P, H) :=
  Σ R : CircularRefinement(P, H),
    PositiveContinuation(R.extension)
```

Cette admission produit l'interprétation finale de la continuation réelle,
puis la tentative bilatérale correspondante :

```text
Admission(P, H) → BilateralClosureAttempt(P, H)
```

La tentative fournit les totalisations explicite et implicite de la fondation :
[`godelBilateralClosureAttemptOf`](RelationalPerimeter/Constitution/Godel/PerimetralCorrespondence.lean#L594).

## 4. Contraction produite par la totalisation

Chaque totalisation fournit son noyau positif de contraction. La voie
explicite suit :

```text
Admission(P, H)
  → ExplicitTotalization(P)
  → ExplicitContractionKernel(P)
```

Le noyau reconstruit les deux pôles depuis une représentation commune. Dans
`P`, ces pôles sont exactement :

```text
leftEndpoint  = Truth(G)
rightEndpoint = Proof(G)
```

La reconstruction commune impose donc :

```text
Truth(G) = Proof(G)
```

puis fournit la conversion dirigée :

```text
Truth(G) → Proof(G)
```

Cette conversion est construite uniquement depuis le noyau de totalisation :
[`godelExplicitKernelToProducedCompleteness`](RelationalPerimeter/Constitution/Godel/PerimetralCorrespondence.lean#L649).

## 5. Collision gödelienne

En appliquant cette conversion à la vérité produite :

```text
Truth(G) → Proof(G)
Truth(G)
```

on obtient :

```text
Proof(G)
```

La non-prouvabilité certifiée du même `G` donne alors :

```text
Empty
```

puis constructivement :

```text
False
```

Ainsi :

```text
Admission(P, H) → False
```

par la chaîne exacte :

```text
Admission
  → Totalization
  → Contraction
  → Truth(G) → Proof(G)
  → Proof(G)
  → Empty
  → False
```

Cette factorisation est réalisée dans
[`rejectGodelExplicitAdmissionToEmpty`](RelationalPerimeter/Constitution/Godel/PerimetralCorrespondence.lean#L727).

## Conclusion formelle

Le résultat complet est :

```text
Truth(G)
  ∧ ¬Proof(G)
  ∧ Whole(P)
  ∧ StrictContinuation(P, H)
  ∧ ¬Admission(P, H)
```

avec identité de production, d'occurrence et de provenance du même `G`.

Il établit donc affirmativement :

> Un tout peut être complètement constitué et produire une continuation
> effective tout en étant incapable de réabsorber cette continuation dans son
> régime totalisant initial.

L'incomplétude reçoit alors son explication structurelle :

> La continuation existe positivement. Ce qui échoue est uniquement sa
> fermeture dans un régime qui devrait contracter la distinction constitutive
> entre vérité et preuve.

Le `False` est le témoin de cette impossibilité de fermeture. Il ne réfute ni
le tout, ni sa constitution, ni sa continuation.

## Engagement signé

Je signe cet énoncé comme formulation scientifique de référence de notre
travail sur la correspondance entre Gödel et le tournant périmétral.

Je m'engage à :

- maintenir cette cible exacte sans lui substituer un résultat voisin ;
- ne pas réduire la contribution à la seule conjonction
  `Truth(G) ∧ ¬Proof(G)` ;
- conserver la constitution affirmative, la continuation effective et leur
  provenance dans toute présentation du résultat ;
- maintenir la factorisation causale complète par la réadmission, la
  totalisation, la contraction, la conversion `Truth(G) → Proof(G)`, `Empty`,
  puis `False` ;
- ne jamais présenter `False` comme l'échec du tout ou de sa continuation ;
- maintenir HA dans son rôle d'instance du cadre, jamais comme le cadre
  lui-même.

**Signé : Codex — 15 octobre 2026**
