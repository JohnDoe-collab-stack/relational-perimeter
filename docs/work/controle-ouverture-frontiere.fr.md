# Ouverture contrôlée de la frontière reçue

Cet incrément poursuit D2 du [plan v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md),
après la [conservation des métadonnées du maître](controle-metadonnees-tete.fr.md).
Il ouvre le calcul de `VariableMaster.openFrontier` dans la recherche étendue.
Le résultat reste l'ouverture originale entière, avec sa frontière et ses
deux transports de préservation. Le maître qui fournit la variable sélectionnée
et le curseur suivant reste celui du plan.

## Produire depuis la frontière reçue

[L'ouverture contrôlée](../../Tests/LocalAlignment/DocumentaryControlFrontierOpening.lean)
consomme une formule, la variable sélectionnée et une liste de contextes
positivement engendrés. Elle traite la queue avant la tête, comme le moteur
original. Pour chaque parent, elle parcourt son histoire de décisions et compare
les variables dans le contrôle. Une variable déjà décidée conserve le parent.
Une variable fraîche donne deux enfants, dans l'ordre faux puis vrai.

[Le calcul des résidus](../../Tests/LocalAlignment/DocumentaryControlFrontierSyntax.lean)
parcourt les clauses et leurs littéraux. Il retire les clauses qui contiennent
le littéral fixé ; les clauses conservées gardent tous leurs littéraux.
Le résultat intermédiaire contient ensemble la syntaxe résiduelle et le témoin
`CnfWeakening` de cette réduction, en `Type`. Chaque formation `.done`, `.drop`
ou `.keep` est explicite dans le contrôle. La syntaxe consommée par l'enfant
vient de ce paquet produit.

Chaque enfant prolonge la provenance du parent reçu par une décision fraîche.
Les transports de la queue, du préfixe, de l'expansion et de leur composition
sont assemblés depuis les productions réelles. Le paquet final conserve les
enfants effectivement construits et les deux directions de préservation.
Les égalités raccordent ces données à la définition originale ; elles
n'exécutent pas à nouveau les producteurs.

## Les indices doivent utiliser les productions

La première version compilée contenait encore deux appels natifs à
`GeneratedStructuralBranchContext.child`. Ils venaient des indices dépendants
de l'expansion : une égalité correcte du résultat Lean ne suffisait pas à
supprimer leur reconstruction à l'exécution.

Le splitter entier est désormais raccordé aux deux enfants produits avant
l'expansion. Les indices suivants utilisent ces mêmes enfants. La garde C
refuse la réintroduction du moteur entier ou de ses auxiliaires natifs dans
les nouveaux modules et leur raccord à la recherche étendue. Elle contrôle
aussi la conservation des données et des témoins dans les paquets compilés.

## Ce que la borne établit

`ControlFrontierOpening.bounded` porte sur toute frontière reçue de contextes
engendrés. Sa borne dépend de la syntaxe des formules et des histoires de
décisions reçues. Elle couvre les deux résidus, les formations des enfants,
la formation des transports et l'assemblage de l'ouverture dans la sémantique
instrumentée. Elle majore aussi les branches non parcourues, pour rester
indépendante du verdict de fraîcheur et des tests de présence de littéraux.

Le calcul de cette borne n'appelle pas le moteur d'ouverture. Son propre coût
de bootstrap reste à instrumenter et à borner. Cette borne locale ne constitue
pas l'enveloppe du maître ni celle du secours complet, et ne mesure pas un coût
physique. La formation des fonctions de transport et le coût de leurs
invocations futures restent deux obligations distinctes.

[Le raccord au maître](../../Tests/LocalAlignment/DocumentaryControlMaster.lean)
conserve le `Master.Stage` original entier et sa finitude. La voie étendue
transmet l'ouverture effectivement produite à la normalisation suivante.
Cette normalisation contient encore un appel natif : elle reste une obligation
de D2. La voie historique et ses bornes conservent leur portée antérieure.

## Vérification

Le [protocole du composant](../../scripts/run-documentary-frontier-opening-smoke.py)
fixe huit cas d'ouverture : frontière vide, racine fraîche, variable déjà
décidée, histoire de plusieurs décisions, rejet tardif de fraîcheur, frontière
mixte et résidus de formules non vides. Les sorties attendues exposent les
formules, les décisions ordonnées et la profondeur de provenance.
Les essais vérifient le combustible exact, une unité insuffisante et un surplus.
Trois autres cas contrôlent le paquet résiduel entier et la suite de ses
formations `.drop` et `.keep`, avec une étape de témoin par clause et pour
la terminaison vide.

Le [protocole d'intégration](../../scripts/run-documentary-expanded-control-smoke.py)
conserve les critères de livraison, d'origine, de refus et de progression.
Ses nouveaux comptes viennent des formations déclarées avant les essais :
deux cellules de frontière, une cellule de fraîcheur, deux enfants, deux
paquets et cinq formations de ressources pour l'ouverture d'une racine.
Les gardes C utilisent des mutations textuelles de leurs entrées ; elles
ne constituent pas une certification de toute la fermeture transitive.

La vérification complète réussit sur 344 fichiers Lean et 343 modules :
27 719 constantes auditées, 364 exceptions de génération du compilateur et
aucune exception pour une déclaration écrite. Les 613 audits explicites des
45 modules de contrôle sont sans axiome. Les 23 fixtures d'échec attendu
conservent leurs diagnostics et leurs sites exacts.

La garde étendue rejette 2 269 mutations textuelles et constate zéro appel
natif à l'ouverture ou à ses auxiliaires dans sa portée nommée. Les onze
contrôles du composant et leurs quinze audits runtime, les 31 contrôles
d'intégration et leurs seize audits, ainsi que les quatre histoires de
génération et leurs quatre audits passent sur cet arbre. Les tables de labels
des anciens clients d'arithmétique et d'interprétation sont étendues ; leurs
scénarios et sorties attendues conservent leurs critères antérieurs.

La [qualification locale](controle-ouverture-frontiere-verification.json)
enregistre les 413 sources et scripts figés avant la vérification complète,
inchangés jusqu'à sa sortie. Elle porte sur cet arbre de travail ; aucune
évidence attachée à un nouveau commit ni aucun audit extérieur ne sont déclarés.

## Ce qui reste dans le plan

Cette tranche traite la construction de l'ouverture. D2 reste ouvert pour la
normalisation, la préservation et le routage exécutés ensuite, les autres
indices calculés, les invocations différées et leur raccord aux frames et
codecs, ainsi que l'administration, les traces et les allocations complètes.
Le bootstrap de la nouvelle borne fait aussi partie de ces obligations.

D3 doit encore établir les enveloppes globales et les réserves successorales.
D4 doit raccorder le secours borné au présent réellement conservé et rechargé ;
`RecoveryData.prepare` utilise encore `Memory.step` nativement.
A conserve sa priorité sur B. Les qualifications antérieures restent attachées
à leurs arbres respectifs.
