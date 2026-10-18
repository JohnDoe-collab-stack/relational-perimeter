# Note de rectification du rapport indépendant runtime–réels

Date de vérification locale : 18 octobre 2026.

Rapport concerné :
[audit structurel runtime–réels](aristotle-runtime-real-structural-audit-5e69b1b.md).

Révision auditée : `5e69b1bae964bd2aa2de0a6c53a2cebea959f6fc`.

## Rectification factuelle

La suggestion n° 4 de la section 9 du rapport affirme que le bloc
`AXIOM_AUDIT` de `Tests/RelationalRealEffectiveCorrespondence.lean` serait
vide. Cette affirmation est factuellement incorrecte sur la révision auditée.

La lecture directe du fichier dans le snapshot Git de cette révision montre
un unique bloc terminal compris entre les lignes 156 et 220. Il contient
soixante-trois commandes `#print axioms`, de
`RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.terminal` à
`RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.boundedLimitRealized`.
Le build et l'audit exhaustif consignés dans le même rapport n'y signalent
aucun axiome.

## Portée de la note

Cette note ne modifie pas le rapport reçu, ne se substitue pas à son auteur et
ne transforme pas une revue locale en audit indépendant. Elle corrige seulement
ce constat vérifiable sur le snapshot exact. Les autres observations, limites
et le verdict `VALIDATED` du rapport restent attribués au rapport original.

Elle n'ajoute aucune conclusion sur tous les réels classiques, la complétude
par borne supérieure, `AC`, `CH`, le coût physique ou l'originalité.
