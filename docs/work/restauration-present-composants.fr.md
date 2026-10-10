# Restauration des composants du présent documentaire

Le présent complet peut désormais être capturé et restauré comme données
typées en conservant le curseur maître, ses formations et tous ses producteurs.
La mémoire du dossier possède aussi un codec depuis des octets, avec égalité
de ses citations et de ses lecteurs de justification. **La reprise du présent
complet depuis un fichier reste à réaliser.** Les deux résultats ci-dessus
ne ferment pas cette dernière obligation du lot 6.

## Ce que la restauration conserve

Un curseur maître ne se réduit pas à son étape courante. Son support conserve
les occurrences de source, de préfixe, de fraîcheur, de découverte,
d'application, de décomposition et de tête produites dans son histoire.
Les producteurs portent leurs ports, leurs fonctions et leurs dépendances.
La lecture d'une frontière opérationnelle ne remplace pas ces données.

Le nouveau payload parcourt la formation reçue et conserve les valeurs déjà
produites. Chaque nœud contient le producteur, la formation antérieure, la
valeur matérielle et sa preuve d'accord avec cette production. La capture
lit les valeurs du support reçu. La restauration construit la formation
avec ces champs ; elle n'applique pas l'opération historique du producteur.
Les trois références du curseur sont conservées avec leurs indices dépendants.

`MasterPayload.resources_exact` établit l'égalité du support entier.
`MasterPayload.cursor_exact` établit l'égalité du curseur entier pour tout
curseur reçu, sans supposer une égalité de frontière ou un nombre fixé
d'étapes. Cette construction couvre aussi le producteur non canonique qui
copie une occurrence antérieure : le contre-exemple aux seules valeurs ne
disparaît pas dans ce payload.

## Le présent entier et ses futurs

Le raccord assemble ce payload maître avec la mémoire documentaire, le
stockage, les liaisons finies, la file typée restante, le contexte de politique,
le compteur et le dernier résumé. Toutes ces données proviennent du même
présent reçu. Aucun de ces composants n'est remplacé par un état initial.

`MaterializedPresent.present_exact` prouve l'égalité avec le présent reçu.
`MaterializedPresent.all_futures` en déduit l'accord de toute suite finie de
requêtes du langage mémoire, y compris sa trace positive. Les nouvelles
citations, les déductions, les lectures, le statut et les resets en font partie.
L'accomplissabilité se transporte également. La reprise du préfixe réel après
trois tours accomplit la citation et la somme restantes, avec la valeur deux
et les origines `[1, 2, 1, 2]`.

Ces énoncés consomment le **payload typé**. Ils ne décrivent pas un chargement
de ces données maître et de contrôle depuis des octets.

## La mémoire documentaire depuis des octets

Le schéma 3 encode la suite ordonnée des positions sources des citations du
dossier. Les sources et le contrat sont reçus inchangés par le chargeur.
Chaque position est résolue en sa référence typée exacte, puis sa permission
est vérifiée. Le lecteur de justification est construit directement à partir
de ces références. Aucun producteur d'extraction ni aucune incorporation
historique n'est exécuté pendant ce chargement.

La classe `PortableMemory.Formed` est positive et indexée par la mémoire
réellement constituée. Les paquets d'incorporation effectifs ferment cette
formation. Les preuves couvrent les programmes finis, toutes les politiques
adaptatives totales et toutes les suites finies de requêtes mémoire à partir
d'une mémoire initiale formée. Elles comprennent les refus, les sorties qui
manquent leur but et les productions supplémentaires retenues.

`PortableMemory.byte_roundtrip` restitue la mémoire entière, y compris son
lecteur de justification ; l'égalité ne porte pas seulement sur les positions.
Deux citations de même contenu restent deux occurrences à positions distinctes
dans le dossier. Une position source interdite de même contenu est refusée.
La fidélité exige la même configuration reçue. Ce schéma n'encode pas le
stockage de déductions, dont le schéma 2 a ses propres lois.

## Vérifications réalisées

Les quatre modules nouveaux comportent 81 références sélectionnées sans
axiome. Les cas instancient les preuves générales sur les traces existantes,
y compris les cas inadéquats et refusés ; ils ne rejouent pas une trace
favorable pour remplacer ces exécutions.

Le smoke exécute 45 processus : 16 sauvegardes du dossier de l'exécution
adaptative effective, leurs 16 chargements dans de nouveaux processus,
12 refus de fichiers altérés et une continuation du présent typé matérialisé.
Chaque chargement documentaire restitue les octets exacts et les trois textes
sources attendus, puis exécute une nouvelle extraction certifiée. Ce test de
composant n'effectue pas une citation par le moteur maître après reprise
physique. La nouvelle citation maître et la somme sont exécutées dans le cas
distinct de continuation du présent typé. Aucun appel Qwen n'est effectué.

Le contrôle du C examine cinq chemins de capture et de restauration et refuse
quatre injections de rejeu. Les chemins maître et présent ne comportent aucun
appel indirect de fermeture. Pour le chargeur de dossier, cette interdiction
porte sur ses appels directs : le lecteur de justification construit pourra
ensuite appeler le lecteur des citations antérieures. Les fonctions et
fermetures statiquement nommées sont parcourues pour rechercher les producteurs
historiques. L'initialisation globale du processus et l'identité physique du
tas restent hors de ce contrôle.

```text
lake build Tests.LocalAlignment.DocumentaryRestorationComponentsCases
python -B scripts/check-restoration-components-codegen.py
python -B scripts/run-restoration-components-smoke.py
```

Le [relevé de vérification](restauration-present-composants-verification.json)
conserve les commandes, les empreintes et la gate de cet incrément.
La gate complète passe sur 274 fichiers Lean et 24 072 constantes, avec zéro
exception écrite à l'audit et les 23 fixtures de refus attendus conformes.
Le candidat `DOCUMENTARY_RESTORATION_COMPONENTS` reste non commité ; aucun
audit indépendant n'est enregistré. Les relevés précédents restent attachés
à leurs arbres respectifs.

## Obligation durable encore ouverte

Le payload maître contient encore des données typées de rang supérieur,
notamment des fonctions de producteur, d'assignation et de lecture. Il faut
leur donner une représentation portable explicite, en fermer la fidélité pour
les producteurs réellement employés, puis encoder et valider les données de
contrôle du présent. Les lois typées déjà prouvées pourront alors consommer
la loi d'égalité du présent chargé depuis les octets.

Le chargement durable devra réunir ces composants, identifier la configuration
reçue et réaliser dans un nouveau processus des citations maître et des
déductions depuis ce présent chargé. Le présent typé exact et les codecs de
composants sont désormais raccordés ; le codec complet et cette réalisation
physique manquent encore. Le lot 6 reste ouvert sur cette cible.
