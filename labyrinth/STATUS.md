# Labyrinth status

Generated 2026-10-09T06:55:37Z by `labyrinth/lab.py build`. Do not edit by hand.


## Conjectures (0)


## Open doors (questions) (9)

- **Circularité positive autonome** [`q.positive-circle`, answered] La séparation de la présentation positive et de l’obstruction, ainsi que le retour exact à la présentation historique, sont réalisés. La génération positive générale reste une question distincte.
- **Rôle final équipé de sa frontière** [`q.equipped-final-role`, partial] La frontière avant choix, le rôle final par choix et la grammaire des rôles intérieurs/finals sont réalisés. La classification est exhaustive dans cette grammaire, avec retours et conservation des données par transport. La minimalité universelle et la rigidité générale restent ouvertes.
- **Transport de la constitution relationnelle** [`q.rich-transport`, partial] Toutes les fibres ont des transports exacts avec calcul dépendant et restriction choisie. Les épines, positions et ordre sont transportés ; une formation reconstruite sur les mêmes états et pas conserve exactement ses histoires et commute avec déploiement, composition et clôture.
- **Réalisation choisie et rigidité** [`q.rigidity`, open] Comment séparer une réalisation exacte distinguée de la propriété selon laquelle toute réalisation admissible impose la même classification ?
- **Plusieurs témoins ou successeurs** [`q.multiple-generation`, open] Le mécanisme du tournant peut-il être formulé sur une génération générale à plusieurs successeurs tout en conservant la continuation choisie ?
- **Quantité structurelle générale** [`q.quantity`, open] Quelle signature et quel critère d’équivalence constituent une quantité structurelle au-delà de la seule correspondance de porteurs ?
- **Converse d’une reconstruction de trace** [`q.converse-traces`, open] Sous quelles hypothèses supplémentaires une trace localement exacte, ordonnée et contiguë se reconstruit-elle en histoire enracinée composable ?
- **Fidélité des cibles sous interprétation** [`q.concrete-faithfulness`, open] Quelles hypothèses sur ConcreteContinuationAlgebra préservent la distinction de la cible fermante et de la continuation libre ?
- **Algèbre de génération positive générale** [`q.positive-generation`, answered] Une PositiveFormation reçue engendre des histoires finies composables et leur épine, avec nœuds, positions et lectures de compatibilité exacts. Une jonction distincte ferme la chaîne positive ; elle ne se déduit pas de la positivité seule.

## Hunches (speculation, not claims) (2)

- **Comparer les frontières par des morphismes équipés** [`h.equipped-morphisms`, tested] La piste est réalisée T2 pour la frontière sélectionnée, les familles complètes et les opérations de la formation reconstruite. Les comparaisons entre formations arbitraires restent spéculatives.
- **Propriété universelle des histoires** [`h.free-paths`, live] Une propriété universelle de chemins libres pourrait clarifier la reconstruction et le transport de la génération ; elle n’est pas établie ici.

## Dead ends (refuted) (14)

- **L’exactitude locale imposerait l’ordre sur toute trace** [`x.local-order`, refuted] Réfuté sur SemanticTrace par l’exemple permuté.
- **L’ordre suffirait à la participation composable** [`x.order-bridge`, refuted] Réfuté sur SemanticTrace par l’exemple intercalé.
- **Contractibilité et exclusion suffiraient à l’unicité** [`x.weak-unique`, refuted] Réfuté par deux occurrences Bool portant le même label final.
- **Le transport exact entre types conserverait toute relation** [`x.exact-order`, refuted] Réfuté par le transport Bool.not sur Before.
- **La positivité du noyau suffirait à reconstruire l’intérieur exact** [`x.positive-old-completion`, refuted] Réfuté par deux anciens Bool fusionnés dans un noyau pourtant positif et fidèlement étiqueté sur son porteur étendu.
- **La bijection exacte conserverait le témoin choisi** [`x.carrier-junction`, refuted] Réfuté par Bool.not sur la fibre de compatibilité fermante, avec trois indices inchangés.
- **Conserver la jonction suffirait à conserver la provenance** [`x.junction-provenance`, refuted] Réfuté par un échange de provenance indépendant, sans changement des indices ni de la jonction.
- **La positivité circulaire interdirait tout retour du nœud brut** [`x.positive-no-recurrence`, refuted] Réfuté par une chaîne positive d’un pas sur le même nœud.
- **L’unicité du rôle par choix imposerait une jonction unique** [`x.role-unique-choice`, refuted] Réfuté par une même forme Bool avec deux pointages distincts et un rôle unique sur chaque pointage.
- **Une chaîne positive fournirait sa propre jonction** [`x.generation-forces-closure`, refuted] Réfuté par une histoire dirigée positive dont la fibre fermante est Empty.
- **La formation admissible déterminerait un successeur unique** [`x.positive-unique-successor`, refuted] Réfuté par deux pas depuis le même état vers deux cibles différentes, et deux continuations choisies différentes.
- **Deux lectures du même nœud seraient la même occurrence** [`x.repeated-nodes-merge-positions`, refuted] Réfuté par deux pas sur le même nœud avec here et later here distincts.
- **Les bijections de sortes suffiraient pour toutes les familles** [`x.sort-transport-fibres`, refuted] Réfuté par mêmes sortes Bool et fibres de compatibilité Unit/Empty.
- **Une grammaire exhaustive couvrirait tout rôle extérieur possible** [`x.universal-role-exhaustiveness`, refuted] Réfuté : CircularRole P est classifié exactement, tandis que son extension CircularRole P ⊕ Unit possède un élément extérieur à l’image de cette grammaire.

## Recent events (36 total)

- 2026-10-09T05:17 · computed · Build complet 104 tâches et script global 107 fichiers Lean : succès, audits sans axiomes et git diff --check propre.
- 2026-10-09T05:20 · documented · Extension positive validée : build104, gate107, referee clôturé et tableau de bord38/54/18 sans erreur ; limites de génération et transport général maintenues.
- 2026-10-09T05:35 · proposed · Lot 1 : frontière sans jonction choisie, enrichissement par témoin, retours exacts et modèles vide/Unit/Bool ; résultats sous revue avant intégration.
- 2026-10-09T05:38 · computed · Lot 1 compilé sous revue : oubli/reconstruction de frontière, enrichissement exact, modèles Empty/Unit/Bool et import public ; audits sans axiomes.
- 2026-10-09T05:44 · proved · Lot 1 achevé : forme sans jonction, transport exact témoin/pointage, trois retours, vide impossible et rôle unique par choix ; cinq T2 sous revue IA clôturée.
- 2026-10-09T05:44 · documented · Lot 1 clôturé : build 106, vérification de 109 fichiers Lean, 26 empreintes, 85 ancres ; tableau de bord 43 lignes/61 nœuds/19 cartes sans erreur ; plan actualisé.
- 2026-10-09T05:44 · refuted · Un rôle unique pour chaque choix ne force pas une jonction unique : deux pointages Bool distincts sur une même forme.
- 2026-10-09T05:50 · proposed · Lot 2 : formation positive, chemins finis composables, déploiement exact des positions et témoins de compatibilité, puis clôture explicite ; quatre modèles séparateurs.
- 2026-10-09T05:59 · computed · Lot 2 compilé sous revue : formation/histoires, composition réindexée, positions exactes et témoins de compatibilité ; modèles sans clôture, à deux successeurs et à nœud répété, imports publics.
- 2026-10-09T06:09 · refuted · Lot 2 : une chaîne positive peut manquer de clôture, deux successeurs peuvent être distincts et des nœuds bruts répétés ne fusionnent pas les positions.
- 2026-10-09T06:10 · reviewed · Revue finale du lot 2 clôturée sans correction restante : huit T2, 32 ancres nouvelles et 30 empreintes relus ; données Step supplémentaires et retours bruts explicitement hors garantie.
- 2026-10-09T06:10 · proved · Lot 2 achevé : formation, histoires composables, déploiement, positions et compatibilités exactes ; clôture avec témoin reçu et pont historique ; continuation choisie supplémentaire.
- 2026-10-09T06:10 · documented · Lot 2 clôturé : build 109, contrôle global de 112 fichiers Lean, 79 audits nouveaux, 38 sondes indépendantes, 117 ancres et 30 empreintes ; tableau de bord 51 lignes/73 nœuds/21 cartes sans erreur ; plan actualisé.
- 2026-10-09T06:12 · proposed · Lot 3A et 3B : transports exacts de toutes les fibres relationnelles, restriction aux témoins sélectionnés, puis formation reconstruite, épines, histoires, positions et ordre structurel.
- 2026-10-09T06:28 · computed · Lot 3 compilé et relu dans sa portée : 162 déclarations nouvelles, imports publics, build 116 et contrôle de 119 fichiers Lean ; 62 sondes indépendantes sans axiomes. Carte et documents sous dernière revue.
- 2026-10-09T06:31 · refuted · Les bijections des sortes ne suffisent pas à transporter les relations : mêmes sortes Bool, fibres de compatibilité Unit et Empty. Les swaps de familles restent distincts des accords sur témoins choisis.
- 2026-10-09T06:31 · proved · Lot 3 achevé dans sa signature : neuf T2 sur fibres complètes, calcul dépendant, restriction, épines, positions et ordre, formation reconstruite, opérations commutantes et clôture reçue transportée.
- 2026-10-09T06:32 · reviewed · Revue du lot 3 clôturée sans correction restante : 62 sondes sans axiomes, neuf T2 et 37 ancres nouvelles, 38 empreintes, README et documents cohérents ; humain en attente.
- 2026-10-09T06:32 · documented · Lot 3 clôturé : 116 tâches, 119 fichiers Lean, 162 audits nouveaux, 154 ancres et 38 empreintes ; tableau de bord 60 lignes/84 nœuds/22 cartes sans erreur ; plan actualisé, lot 4 suivant.
- 2026-10-09T06:35 · proposed · Lot 4 : grammaire intérieure/finale équipée, classification relative, raccord historique, données choisies conservées par transports ; commit et push demandés après validation.
- 2026-10-09T06:55 · computed · Lot 4 compilé : 109 audits nouveaux, imports publics, build 121 et contrôle de 124 fichiers Lean ; 49 sondes indépendantes sans axiomes et 17 diagnostics de provenance réussis.
- 2026-10-09T06:55 · refuted · Une exhaustivité universelle des rôles ne découle pas de la classification déclarée : une branche extérieure ajoutée reste hors de son image. Deux jonctions donnent aussi deux choix distincts avec un rôle unique par choix.
- 2026-10-09T06:55 · proved · Lot 4 achevé relativement à la grammaire intérieure/finale : classification exacte, absence de nouvelle position intérieure finale, raccord historique, données complètes conservées et carrés de classification commutants.
- 2026-10-09T06:55 · reviewed · Revue indépendante clôturée sans correction restante : sept T2 et 30 ancres nouvelles, 47 empreintes, 109 audits et scopes cohérents. Hashing CRLF→LF seul ; ancestry et sources exactes couplées, contrôle réel des blobs après commit restant au coordinateur. Humain en attente.
- 2026-10-09T06:55 · documented · Quatre constructions principales réalisées et intégrées : carte 93 nœuds, 67 lignes, 184 ancres, 47 sources ; tableau de bord 67/93/23 sans erreur. Journal de six sessions, plan et documents actualisés ; livraison Git explicitement demandée.
