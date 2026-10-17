# Revue de lecture et de traduction — runtime réel et provenance du témoin

Responsable : Codex (OpenAI), lectures autonomes puis confrontation formelle.

Date : 17 octobre 2026.

Révision examinée : `ffeae501f4425e80705a1b23903dadaf3a3b7937`.

## Périmètre et ordre de lecture

La lecture française autonome a porté, dans cet ordre, sur
`godel-regroupement-completude-reels.fr.md` puis
`runtime-real-cauchy-effective-correspondence.fr.md`. La lecture anglaise
autonome a ensuite porté sur `godel-grouping-relational-real-completeness.en.md`
puis `runtime-effective-cauchy-real-correspondence.en.md`. La confrontation aux
preuves n'a eu lieu qu'après ces lectures séparées.

La confrontation formelle a couvert les types et les corps complets qui
forment, exécutent, prouvent et transportent la chaîne : production
gödelienne, famille de Cauchy exécutée, charge historique normalisée,
regroupement fini, cible produite, action et admission, runtime commun,
correspondance des readouts et réalisation au périmètre `H1`. Le code C généré
pour la fenêtre de `LimitGrouping.program.act` a également été inspecté.

## Revue de lecture française

Pour `GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS`, la quantification canonique
porte bien sur une exécution gödelienne effective et sur une famille de Cauchy
exécutée reçue. Les cinq composantes de cette famille — producteur, cohérence
intraterme, module, monotonie du module et loi de Cauchy — restent des données
reçues. Le maître commun contient l'environnement exécutable et la mémoire ; il
ne reconstruit pas la famille à partir d'un readout extensif. Le texte parle
d'un paquet `Result` commun, et non d'unicité mathématique de tout objet
possible.

Les chaînes positive et négative restent séparées. La première construit les
regroupements finis, la cible installée, la continuation, l'archive et le réel
relationnel. La seconde conserve le même témoin gödelien pour rejeter la boucle
totale et la fermeture globale du même régime. Le passage canonique exclut
toujours l'identification à tous les réels classiques, la complétude d'ordre,
la densité, AC, CH et toute revendication d'originalité.

La correction de provenance ferme précisément le défaut qui subsistait dans
la cible produite. `ProducedTarget` ne stocke plus un second témoin
source–cible. `sourceNearTarget` transporte le témoin
`NormalizedHistory.nearSourceTarget`, et
`sourceNearTarget_is_normalized` établit l'identité hétérogène entre
l'accesseur exposé et ce témoin normalisé. `Action` expose le même témoin ;
`Accepted` conserve le type historique attendu par ses consommateurs tout en
prouvant, par `preservation_is_normalized`, qu'il s'agit du transport du témoin
normalisé. Dans `program.act`, `normalizedCharge` est lié une fois, puis partagé
entre la cible, l'action et l'admission. Aucun rejeu indépendant de
`receivedNear` n'est présent dans cette fenêtre exécutée.

Verdict de lecture : **reviewed** pour la portée française des deux affirmations
sur la révision indiquée. Ce verdict ne vaut ni audit indépendant, ni verdict
d'originalité.

## Revue de traduction anglaise

Les passages anglais conservent les mêmes quantifications, les mêmes entrées
reçues et les mêmes exclusions. `same-term coherence` traduit la cohérence
intraterme sans la renforcer en cohérence globale arbitraire ; `common Result
package` traduit le paquet commun sans introduire une unicité. Les expressions
relatives au runtime, au regroupement, à la cible installée et au readout
gardent l'orientation constitutive : les relations, histoires et ressources
produisent le résultat ; la lecture numérique est aval.

La version anglaise de la correspondance runtime–réel effectif n'identifie ni
environnements, ni états, ni journaux, ni ressources, ni occurrences. Elle
conserve l'aller-retour numérique positif et les futurs limites finis sans
prétendre reconstruire l'histoire riche depuis les valeurs.

Verdict de traduction : **reviewed** pour les deux affirmations sur la révision
indiquée. Aucune extension ou réduction de portée n'a été relevée entre les
passages canoniques français et anglais.

## Contrôles techniques de la révision

La révision a passé le build Lean complet (`359/359`), l'audit global des
constantes (`32602` constantes, `356` modules, aucune exception écrite), les
`57` échecs attendus, les frontières d'import, la stratification, la politique
source et les contrôles de génération. L'inspection du C généré pour la fenêtre
de l'action a compté un appel à `normalizedCharge` et aucun appel à
`receivedNear`.

Ces contrôles confirment la cohérence mécanique de la révision ; ils ne
remplacent pas la lecture sémantique ci-dessus et ne constituent pas un audit
extérieur. Le statut indépendant demeure `not_recorded`.
