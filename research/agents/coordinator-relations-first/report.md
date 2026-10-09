# Intégration de la reprise constitutive

La livraison `bf13840` sert de référence ; la branche reste `codex/positive-circular-foundations`. Le choix exprimé par l’utilisateur est traité comme principe de constitution du projet. Il ne devient pas un théorème sur toutes les mathématiques ni un argument tiré du seul ordre des déclarations Lean.

L’ancienne carte est conservée. Les 93 nœuds ont chacun une lecture des données reçues, des constructions, des lectures et de leur portée. Les 58 claims T2 et leur revue formelle sont conservés ; une revue indépendante distincte examine leur adéquation constitutive. Les 184 ancres et les 47 empreintes formelles sont vérifiées. Le garde nouveau refuse une omission de nœud, un changement de claim formel ou une clôture sans referee distinct ; ses contrôles restent des contrôles de provenance.

Le coordinateur a recoupé dans les sources les deux retours de `PositiveHistory.positionTransport`, `deploy_link_exact`, le seul champ reçu de `RequirementOccurrenceAgreement` et ses producteurs `sourceStateExact`, `locatedStepExact`, `targetStateExact`, ainsi que les deux branches et retours de `CircularRole`. Les ajustements de signature/portée ne créent aucun nouveau théorème. La carte met l’intérieur exact au premier plan et reformule la question générale de quantité depuis les acquis existants.

La génération documentaire a d’abord révélé un champ `result` mal nommé dans la nouvelle histoire SOTA ; il a été remplacé par le champ attendu `was`. Les entrées d’histoire ajoutées pour un simple changement de groupe ont été retirées : la réorganisation ne constitue pas une amélioration mathématique. Le replay des sources et métadonnées a ensuite réussi.

Le contrôle visuel utilise Chrome headless et Playwright du runtime local, avec le script `DashboardCheck.cjs`. Il vérifie les onglets, les 67 lignes, les 93 nœuds, les 23 cartes et l’affichage des distinctions reçu/dérivé dans une fiche centrale. Une attente de libellés a été corrigée pour tenir compte de `text-transform` ; le produit affichait déjà les cinq champs. Les captures sont inspectées par le coordinateur, sans erreur de page.

La seconde phase du referee porte sur l’ensemble intégré et les documents. La provenance de cette interprétation sera figée séparément après son acceptation. Les sources Lean inchangées ne sont pas recompilées inutilement ; aucune nouvelle validation computationnelle n’est revendiquée.

La seconde phase accepte le candidat avec le verdict `ACCEPTED-RELATIVE`, après les corrections exactes demandées. L’auteur conserve les originaux de ses propositions ; les pièces de revue restent distinctes. Le coordinateur met à jour uniquement les états/evidence de revue et enregistre un snapshot séparé de 16 entrées. Les généralités restent ouvertes et la vérification humaine reste en attente. Aucun commit ni push nouveau n’est réalisé dans cette reprise locale.
