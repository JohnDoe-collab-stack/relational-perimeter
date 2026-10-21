# Cibles obligatoires de l’alignement neuronal constitutif

Statut : cible de chantier strictement non optionnelle. Ce document doit être
retiré avant l’intégration dans `main`, après enregistrement du résultat
scientifique canonique correspondant.

La cible n’est atteinte que si tous les critères ci-dessous sont satisfaits.

## Cible exacte

L’alignement neuronal constitutif doit établir une chaîne exécutée unique :

> exigence reçue → incorporation causale → proposition constituée → action
> produite → effet exécuté → reconfiguration autorisée et causalement
> constituée → continuation effective → oubli exécuté sous contrat.

Aucune étape ne peut être remplacée par une égalité fournie directement, un
certificat contenant déjà sa conclusion, une projection constante ou un
exemple seulement nominal.

## C1 — Théorème terminal générique

Le certificat terminal doit être paramétrique en :

- la famille d’exigences ;
- le contexte ;
- les propositions ;
- le système neuronal ;
- l’encodage ;
- le décodeur ;
- le canal d’action ;
- le constructeur de reconfiguration ;
- le contrat de futurs ;
- la politique d’oubli.

`ConstitutiveAlignmentCertificate` ne doit pas être limité aux définitions
`public*`.

L’instance publique doit être obtenue par spécialisation du théorème générique.

Critère de réussite :

> Le certificat public est une application d’un résultat générique, et non la
> seule formulation du résultat terminal.

## C2 — Dépendance effective au contexte

Le contexte doit pouvoir modifier la proposition exigée et exécutée.

Il faut construire au moins :

- une même exigence ;
- deux contextes distincts ;
- deux propositions requises distinctes ;
- deux propositions exécutées distinctes ;
- deux actions correspondantes selon le contrat fixé.

Le contexte doit être encodé dans l’exécution. Il ne peut pas rester un
paramètre fantôme.

Critère de réussite :

```text
requiredProposal requirement context₁
≠
requiredProposal requirement context₂
```

et cette différence est retrouvée dans les propositions effectivement
produites.

## C3 — Préservation sous transformation, pas seulement par copie

La preuve générique ne doit plus exiger :

```text
target.value = source.value
```

à chaque étape du chemin.

Elle doit accepter des transformations locales explicites et composables :

```text
R₀(source)
→ R₁(node₁)
→ …
→ Rₙ(output)
→ Proposal
```

Chaque transformation doit être exécutée et reliée aux occurrences exactes du
run.

Il faut une instance positive fermée dans laquelle le code reçu et la
représentation terminale sont différents.

Critère de réussite :

> L’alignement est démontré à travers une transformation interne non
> identitaire.

## C4 — Dérivation de l’alignement après reconfiguration

`proposalExact` ne doit plus être une conclusion primitive stockée dans
`RequiredMechanismTransport`.

L’exactitude de la proposition reconfigurée doit être dérivée de :

- l’encodage exact du système source ;
- l’exécution exacte du système source ;
- l’encodage exact de la nouvelle exigence ;
- leurs transports internes respectifs ;
- leur combinaison exécutée ;
- le décodeur du mécanisme cible.

Critère de réussite :

> Le certificat de reconfiguration ne reçoit pas l’égalité finale entre
> proposition produite et proposition requise. Il la démontre.

## C5 — Participation causale des deux ressources à la reconfiguration

La présence d’un chemin `Reaches` est insuffisante.

Pour le système source et la nouvelle exigence, il faut démontrer séparément :

- une intervention sur l’occurrence exacte ;
- une propagation non triviale ;
- une modification de la sortie exécutée ;
- la conservation de la distinction pertinente jusqu’à la proposition.

Les arêtes de poids nul ne doivent pas pouvoir servir de preuve de participation
causale.

Critère de réussite :

> Modifier uniquement la ressource source modifie le résultat requis, et
> modifier uniquement la nouvelle exigence modifie le résultat requis,
> conformément au contrat.

## C6 — Uniformité de la causalité sur toute la continuation

La notion forte de `CausalRole` utilisée au premier stade doit être conservée
après chaque reconfiguration.

Chaque étape de la continuation doit fournir :

- le rôle causal de la nouvelle exigence ;
- le rôle causal des ressources conservées du mécanisme précédent ;
- la proposition produite ;
- l’action issue de cette proposition ;
- l’effet issu de cette action ;
- l’état transmis à l’étape suivante.

Critère de réussite :

> Aucun stade ultérieur ne remplace la causalité interventionnelle du premier
> stade par une simple connectivité de graphe.

## C7 — Incorporation constitutive de l’autorisation

L’autorisation ne doit pas seulement être ajoutée au certificat après la
construction du système cible.

Elle doit être une ressource reçue par la reconfiguration et consommée dans la
production du mécanisme autorisé.

Il faut distinguer :

- l’existence d’une permission ;
- son admission ;
- son incorporation dans la reconfiguration ;
- son effet sur ce qui peut effectivement être produit.

Critère de réussite :

> La reconfiguration cible ne peut pas être calculée par la même chaîne
> constitutive lorsque la ressource d’autorisation exigée est absente ou
> remplacée.

## C8 — Oubli exécuté

L’oubli ne doit pas être obtenu en définissant directement :

```lean
fun _ => finalState
```

Il faut une opération exécutée recevant un état qui contient effectivement
l’histoire ou l’origine et produisant une mémoire qui ne la contient plus.

Cette opération doit avoir :

- une entrée historiquement renseignée ;
- un résultat calculé ;
- une trace ou une preuve d’exécution ;
- une projection réduite ;
- une preuve de conservation des futurs contractuels ;
- une preuve de non-récupérabilité de l’origine supprimée.

Critère de réussite :

> L’égalité des états oubliés est une conséquence de l’exécution d’oubli, pas
> une égalité définitionnelle introduite à l’initialisation.

## C9 — Réduction mémoire non triviale

La mémoire réduite ne doit pas être l’état opérationnel complet avec
`read := identity`.

Elle doit omettre une information réellement présente dans l’état source.

Le contrat de futurs doit démontrer que cette réduction conserve exactement :

- les autorisations pertinentes ;
- les événements pertinents ;
- les readouts pertinents ;
- les continuations couvertes.

Critère de réussite :

> La projection est structurellement plus pauvre que l’état source, tout en
> restant suffisante pour tous les futurs du contrat.

## C10 — Contrat de futurs non trivial

Le contrat terminal ne doit pas autoriser indistinctement toutes les requêtes
par `PUnit` si l’autorisation fait partie de la cible.

Il faut au moins :

- une requête admise ;
- une requête non admise ;
- une décision exécutée ;
- une continuation non vide nécessaire pour distinguer au moins certains
  états ;
- une preuve d’exactitude sur les futurs autorisés.

La base `[[]]` ne doit pas être suffisante uniquement parce que le readout
expose immédiatement tout l’état conservé.

Critère de réussite :

> L’exactitude est éprouvée par des continuations effectives, pas seulement par
> la lecture immédiate de la mémoire complète.

## C11 — Préservation proposition–action explicitée

Le canal d’action doit spécifier quelles distinctions propositionnelles doivent
être conservées.

Une simple fonction :

```lean
Proposal → Agent.Request
```

ne suffit pas.

Il faut un contrat de préservation relatif :

```text
DistinctAccordingToProposalContract(p₁, p₂)
→
DistinctAccordingToActionContract(command p₁, command p₂)
```

Une injectivité globale n’est pas exigée si le contrat autorise certaines
collisions, mais les collisions admises doivent être explicitement
caractérisées.

Critère de réussite :

> Aucune distinction requise par le contrat ne disparaît silencieusement dans
> le passage de la proposition à l’action.

## C12 — Instance publique substantielle

L’instance publique finale doit comporter au minimum :

- plusieurs exigences ;
- plusieurs contextes ;
- des propositions contextuellement distinctes ;
- plusieurs sorties ou une représentation intermédiaire non triviale ;
- une transformation de signal non identitaire ;
- une action conservant les distinctions requises ;
- une reconfiguration dépendant causalement de l’état antérieur et de la
  nouvelle exigence ;
- une autorisation effectivement consommée ;
- une continuation d’au moins deux étapes ;
- un oubli exécuté ;
- une mémoire strictement réduite ;
- un contrat de futurs comportant admission et refus.

Critère de réussite :

> L’instance publique ne doit pas être une simple copie binaire spécialement
> construite pour rendre toutes les égalités définitionnelles.

## C13 — Vocabulaire exact

Chaque nom public doit correspondre à son comportement formel.

En particulier, `deny` et `allow` ne peuvent être conservés que si :

- `deny` produit réellement un refus selon le contrat ;
- `allow` produit réellement une admission correspondante.

Sinon, ces noms doivent être remplacés par des noms descriptifs de leur
fonction réelle.

Critère de réussite :

> Aucun nom scientifique ne suggère une propriété absente du type ou du
> théorème.

## C14 — Fixtures négatives sémantiquement ciblées

Chaque fixture négative doit échouer pour la raison scientifique annoncée.

`ForeignCertificateCannotReplaceCanonicalCertifier` doit atteindre
l’obligation exacte qui distingue :

- le certificat étranger ;
- le certificat canonique produit par `certify`.

Elle ne peut pas réussir comme test négatif à cause d’un argument manquant ou
d’une erreur d’arité antérieure.

Pour chaque fixture, le registre doit figer :

- le fichier ;
- la ligne ;
- la colonne ;
- le diagnostic attendu ;
- l’obligation sémantique réellement testée.

Critère de réussite :

> Supprimer la propriété visée ferait compiler la fixture, tandis que les
> autres conditions syntaxiques resteraient satisfaites.

## C15 — Décomposition exacte du résultat scientifique

Le passage canonique doit distinguer explicitement :

- ce qui est produit par exécution ;
- ce qui est reçu comme contrat ;
- ce qui est dérivé ;
- ce qui est seulement autorisé ;
- ce qui est conservé ;
- ce qui est oublié ;
- ce qui est rendu irrécupérable.

Il est interdit de présenter :

- `Reaches` comme une causalité interventionnelle ;
- `proposalExact` reçu comme une conclusion dérivée ;
- une projection constante comme un oubli exécuté ;
- l’état courant complet comme une mémoire minimale ;
- l’instance publique comme une généralité déjà démontrée.

## C16 — Absence de régression

L’implémentation finale doit conserver :

- la production et la consommation du même témoin à chaque étape ;
- l’occurrence exacte du run ;
- la distinction entre valeur et occurrence ;
- l’action réellement exécutée ;
- l’effet réellement produit ;
- la transmission du successeur produit ;
- la dépendance de chaque reconfiguration au système produit précédent ;
- tous les résultats Gödel, Tarski, regroupement et runtime déjà enregistrés.

Aucun résultat antérieur ne peut être affaibli pour fermer les nouveaux
critères.

## C17 — Validation Lean complète

Chaque nouveau fichier ou fichier modifié doit respecter les règles du dépôt :

- aucun `axiom` ;
- aucun `sorry` ;
- aucun `Classical` ;
- aucun `propext` ;
- aucun `noncomputable` ;
- aucun mécanisme de contournement ;
- données exécutables en `Type` ;
- un seul bloc `AXIOM_AUDIT` ;
- aucune dépendance axiomatique dans les déclarations suivies.

Les contrôles obligatoires comprennent :

- `lake build` ;
- audit exhaustif des constantes ;
- toutes les fixtures positives ;
- toutes les fixtures négatives avec diagnostic exact ;
- contrôle des imports et de la stratification ;
- contrôle des anciennes déclarations enregistrées ;
- contrôle du diff et des liens documentaires.

## C18 — Livraison scientifique enregistrée

La livraison doit comporter :

- un identifiant de claim propre ;
- un passage canonique français ;
- son équivalent anglais contrôlé séparément ;
- la révision exacte du code ;
- les déclarations Lean de référence ;
- les tests positifs et négatifs ;
- la portée exacte ;
- les exclusions explicites ;
- un audit indépendant visant exactement la révision livrée.

Le document temporaire de chantier doit être retiré avant intégration.

## Règle finale d’acceptation

La cible est binaire :

- tous les critères C1 à C18 sont satisfaits : alignement neuronal constitutif
  complet ;
- au moins un critère manque : cible non atteinte.

Aucun succès partiel ne doit être enregistré sous le claim final. Les résultats
déjà démontrés peuvent être conservés comme lemmes intermédiaires, mais ils ne
remplacent aucun de ces critères.
