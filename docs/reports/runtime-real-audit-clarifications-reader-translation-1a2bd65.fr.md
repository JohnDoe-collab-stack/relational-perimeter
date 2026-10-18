# Revue des clarifications d'audit runtime–réels

Responsable : Codex (OpenAI), lectures autonomes puis confrontation formelle.

Date : 18 octobre 2026.

Révision examinée : `1a2bd65b080fc9eefca60bd91dbb175a9a458862`.

## Périmètre

La lecture française autonome a porté intégralement sur
`docs/runtime-real-cauchy-effective-correspondence.fr.md`. La lecture anglaise
a ensuite porté intégralement, séparément, sur
`docs/runtime-effective-cauchy-real-correspondence.en.md`. La confrontation
FR/EN et la lecture des définitions Lean concernées ont été effectuées après
ces deux lectures.

Le diff de la révision examinée ne modifie aucun fichier Lean, script, manifeste
ou toolchain. Il précise deux limites déjà relevées par l'audit indépendant,
ajoute une note factuelle séparée au rapport reçu et remet le plan à l'état
exact de la gate 6. Il ne change ni le contrat, ni les quantifications, ni la
portée effective de l'affirmation.

## Lecture française

Le texte conserve la direction constitutive : les comportements, archives,
banques, pas exécutés, actions et continuations sont formés avant leurs readouts.
La présentation dyadique et le carrier restent des projections aval ; aucun
aller-retour numérique ne reconstruit une occurrence, une histoire ou un témoin
Cauchy riche.

La clarification native distingue désormais exactement trois faits. Le calcul
riche part de la banque courante, produit le `Step` diagonal, le fait consommer
par le regroupement, installe la cible puis continue banque et journal.
`nativeLiveStep`, séparément, ignore la mémoire live courante et exécute le
kernel sélectionné depuis son champ `initial`. Pour la fabrique `ofTerms`, ce
champ est la projection de l'archive initiale riche ; pour une famille générique
reçue, seule la loi `kernelExact` garantit l'accord avec tout `Step` riche
courant du même terme et de la même précision. Le texte n'invente donc pas une
origine projetée pour une donnée générique reçue.

La phrase sur `private` est également bornée correctement. Elle décrit la
frontière d'élaboration de l'interface Lean ordinaire et la portée des fixtures
négatives. Elle n'affirme plus une inforgeabilité contre un métaprogramme qui
viserait volontairement un nom interne compilé.

Verdict de lecture française : **reviewed** pour
`RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE` sur la révision indiquée.

## Lecture et confrontation anglaises

La version anglaise conserve les mêmes sujets, quantifications et directions.
`current live memory`, `initial field`, `generic received family` et
`kernelExact` correspondent respectivement à la mémoire live courante, au champ
initial reçu, à la famille générique reçue et à la loi d'uniformité du texte
français. `Elaboration boundary` et `ordinary Lean interface` bornent la portée
de `private` de la même manière que « frontière d'élaboration » et « interface
Lean ordinaire ».

Aucune version ne transforme cette uniformité numérique en identité d'archives,
ne fait du kernel live un rejeu du producteur riche, ni ne reconstruit une
histoire à partir du readout. Les deux textes conservent les mêmes exclusions :
pas de couverture de tous les réels classiques, pas de complétude par borne
supérieure, pas d'ordre global décidable, pas de coût physique, pas de résultat
sur `AC`, `CH` ou l'originalité.

Verdict de traduction : **reviewed** pour
`RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE` sur la révision indiquée.

## Confrontation aux définitions

`NativeTermKernel` contient un `LiveEnvironment` et un champ `initial`.
`nativeLiveStep` nomme son argument de mémoire `_memory`, sélectionne
`kernels (modulus p)`, puis appelle exactement
`kernel.environment.step kernel.initial p`. `nativeTermKernel real` construit
le champ initial par
`(environment real).project (environment real).initialArchive`, et
`NativeCauchyFamily.ofTerms` utilise ce constructeur. Pour l'interface générique,
`NativeCauchyFamily.kernelExact` reçoit tout archive et tout `Step` courant et
relie son code à la réponse du kernel démarré depuis `initial`.

Les fixtures `PrivateAdditionArchive`, `PrivateMultiplicationArchive`,
`PrivateNegationArchive`, `PrivateReciprocalArchive`, `PrivateNativeArchive`,
`PrivateAdditionArchiveUpdate` et `PrivateNativeArchiveUpdate` contrôlent le
refus par l'interface ordinaire. Elles ne deviennent pas une preuve contre les
métaprogrammes, limite désormais explicite dans les deux langues.

La note de rectification vérifie directement le snapshot Git : le bloc terminal
`AXIOM_AUDIT` de `Tests/RelationalRealEffectiveCorrespondence.lean` occupe les
lignes 156 à 220 et contient soixante-trois commandes `#print axioms`. Elle ne
réécrit pas le rapport indépendant et ne lui attribue pas cette correction.

## Contrôles mécaniques déjà rejoués sur le contenu examiné

La gate PowerShell complète a été rejouée après les dernières modifications
documentaires et a réussi : 398 jobs Lean ; 37 092 constantes dans 395 modules ;
737 exceptions générées et aucune exception écrite ; 329 modules de production
stratifiés ; 189 fixtures négatives avec diagnostics et sites exacts ; 396
fichiers Lean conformes. Les contrôles statiques, références publiques et de
tests, frontières d'import, code généré, liens et `git diff --check` ont réussi.

Ces résultats établissent la cohérence mécanique de l'arbre, pas le verdict de
lecture à eux seuls. La présente revue n'est pas indépendante. Le champ
`independent` doit rester `not_recorded` jusqu'à réception et lecture d'un
rapport extérieur visant exactement la révision indiquée.
