# Labyrinth status

Generated 2026-10-09T05:20:37Z by `labyrinth/lab.py build`. Do not edit by hand.


## Conjectures (0)


## Open doors (questions) (9)

- **Circularité positive autonome** [`q.positive-circle`, answered] La séparation de la présentation positive et de l’obstruction, ainsi que le retour exact à la présentation historique, sont réalisés. La génération positive générale reste une question distincte.
- **Rôle final équipé de sa frontière** [`q.equipped-final-role`, partial] Un rôle équipé de la frontière de clôture et de sa jonction est implémenté avec conservation par morphismes riches. La minimalité de la signature et la grammaire circulaire complète restent ouvertes.
- **Transport de la constitution relationnelle** [`q.rich-transport`, partial] Identité, inversion et composition sont réalisées pour la frontière sélectionnée, avec accords source/cible/différence et témoins de jonction/provenance. Le transport des familles complètes reste ouvert.
- **Réalisation choisie et rigidité** [`q.rigidity`, open] Comment séparer une réalisation exacte distinguée de la propriété selon laquelle toute réalisation admissible impose la même classification ?
- **Plusieurs témoins ou successeurs** [`q.multiple-generation`, open] Le mécanisme du tournant peut-il être formulé sur une génération générale à plusieurs successeurs tout en conservant la continuation choisie ?
- **Quantité structurelle générale** [`q.quantity`, open] Quelle signature et quel critère d’équivalence constituent une quantité structurelle au-delà de la seule correspondance de porteurs ?
- **Converse d’une reconstruction de trace** [`q.converse-traces`, open] Sous quelles hypothèses supplémentaires une trace localement exacte, ordonnée et contiguë se reconstruit-elle en histoire enracinée composable ?
- **Fidélité des cibles sous interprétation** [`q.concrete-faithfulness`, open] Quelles hypothèses sur ConcreteContinuationAlgebra préservent la distinction de la cible fermante et de la continuation libre ?
- **Algèbre de génération positive générale** [`q.positive-generation`, open] Comment engendrer une chaîne positive et sa jonction depuis une algèbre constructive indépendante de l’obstruction ?

## Hunches (speculation, not claims) (2)

- **Comparer les frontières par des morphismes équipés** [`h.equipped-morphisms`, tested] La piste a une réalisation T2 pour la signature de clôture sélectionnée. Son extension à toute la constitution relationnelle reste spéculative.
- **Propriété universelle des histoires** [`h.free-paths`, live] Une propriété universelle de chemins libres pourrait clarifier la reconstruction et le transport de la génération ; elle n’est pas établie ici.

## Dead ends (refuted) (8)

- **L’exactitude locale imposerait l’ordre sur toute trace** [`x.local-order`, refuted] Réfuté sur SemanticTrace par l’exemple permuté.
- **L’ordre suffirait à la participation composable** [`x.order-bridge`, refuted] Réfuté sur SemanticTrace par l’exemple intercalé.
- **Contractibilité et exclusion suffiraient à l’unicité** [`x.weak-unique`, refuted] Réfuté par deux occurrences Bool portant le même label final.
- **Le transport exact entre types conserverait toute relation** [`x.exact-order`, refuted] Réfuté par le transport Bool.not sur Before.
- **La positivité du noyau suffirait à reconstruire l’intérieur exact** [`x.positive-old-completion`, refuted] Réfuté par deux anciens Bool fusionnés dans un noyau pourtant positif et fidèlement étiqueté sur son porteur étendu.
- **La bijection exacte conserverait le témoin choisi** [`x.carrier-junction`, refuted] Réfuté par Bool.not sur la fibre de compatibilité fermante, avec trois indices inchangés.
- **Conserver la jonction suffirait à conserver la provenance** [`x.junction-provenance`, refuted] Réfuté par un échange de provenance indépendant, sans changement des indices ni de la jonction.
- **La positivité circulaire interdirait tout retour du nœud brut** [`x.positive-no-recurrence`, refuted] Réfuté par une chaîne positive d’un pas sur le même nœud.

## Recent events (13 total)

- 2026-10-09T04:51 · milestone · Carte initiale des fondations sur main ; provenance figée et plan distingué des résultats.
- 2026-10-09T04:51 · computed · Construction des quatre modules réussie ; audits sans dépendance axiomatique signalée.
- 2026-10-09T04:51 · proved · Deux contre-modèles et un diagnostic du rôle final compilés dans Lean (adéquation en relecture).
- 2026-10-09T04:55 · reviewed · Relecture indépendante des résultats T2 : hypothèses, suffixe éventuellement vide et liens de dépendance corrigés. Contrôle humain en attente.
- 2026-10-09T04:55 · refuted · Positivité du noyau sans injectivité ancienne : reconstruction intérieure exacte réfutée par deux contre-modèles Lean.
- 2026-10-09T04:58 · documented · Carte fondationnelle et tableau de bord générés et vérifiés : 21 T2, 5 voies réfutées, 8 questions ; sources de référence inchangées.
- 2026-10-09T05:00 · documented · Sondes archivées en .lean.in et recompilées ; alias historiques et empreintes conservés ; 33 références de la carte vérifiées.
- 2026-10-09T05:17 · proved · Couche positive autonome et pont historique exact implémentés sur une nouvelle branche ; modèles de pôles identifiés et obstrués.
- 2026-10-09T05:17 · proved · Transports riches de frontière sélectionnée : cinq accords, inversion/composition et rôle équipé avec retours exacts.
- 2026-10-09T05:17 · refuted · Bijection sans conservation de jonction, jonction sans conservation de provenance, positivité sans interdiction de retour brut : trois contre-modèles distincts.
- 2026-10-09T05:17 · reviewed · Referee IA indépendant : établi dans le périmètre sélectionné, addendum des deux lois finales accepté ; vérification humaine en attente.
- 2026-10-09T05:17 · computed · Build complet 104 tâches et script global 107 fichiers Lean : succès, audits sans axiomes et git diff --check propre.
- 2026-10-09T05:20 · documented · Extension positive validée : build104, gate107, referee clôturé et tableau de bord38/54/18 sans erreur ; limites de génération et transport général maintenues.
