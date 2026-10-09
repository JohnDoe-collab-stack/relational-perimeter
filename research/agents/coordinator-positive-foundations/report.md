# Relecture du contre-modèle de provenance

Coordinateur `/root`, 9 octobre 2026. Le modèle `swapProvenanceOnly` est un ajout original du referee `/root/positive_foundation_referee` ; sa relecture indépendante de l’auteur est donc effectuée ici par le coordinateur. Résultat T2 établi dans le périmètre sélectionné ; vérification humaine en attente.

Lecture directe des définitions dans `research/agents/referee-positive-foundations/IndependentProbes.lean.in:49–137` : `boolBoundary false` sélectionne `false` pour les trois indices, la jonction et la provenance. Le transport proposé est l’identité sur les sortes explicite, implicite, différence et la fibre de jonction. Il conserve donc les trois indices et la jonction. Sa seule application non identitaire est `Bool.not` sur la fibre de provenance ; les deux lois de retour se calculent par cas sur `Bool`.

Si un `BoundaryTransport` possédait exactement ces applications, son champ `provenanceExact` imposerait `Bool.not false = false`, soit `true = false`. Le théorème `provenanceSwapCannotEnrich` projette ce champ, réécrit l’accord avec le transport proposé, puis utilise la disjonction des constructeurs de `Bool`. Cette contradiction ne touche pas les autres morphismes riches, dont l’identité. Elle établit que l’accord de jonction ne remplace pas l’accord de provenance pour ce transport spécifié.

Le coordinateur a recompilé toute la sonde après lecture, avec succès et 22 déclarations auditées sans axiomes. Journal : `labyrinth/evidence/positive-referee-probes.log`. Le build complet et le script global ont également réussi ; ces contrôles de compilation sont distincts de cette vérification de l’énoncé et de sa portée.
