# Recettes exactes des producteurs du maître

**Date :** 10 octobre 2026.

**Branche :** codex/ai-alignment-under-contract.

**Candidat scientifique :** DOCUMENTARY_MASTER_RECIPES.

**Référence de départ :** f30196e4a8ae2b77b0d061c1e03cccd236265013.

## Le passage fermé

Les sept producteurs employés par le moteur maître ont maintenant des recettes
explicites : découverte, application, décomposition, assemblage, puis production
du préfixe, de la source et de la fraîcheur suivants. Chaque recette désigne
les ports réellement lus, dans leur ordre, avec son environnement dépendant.

Une formation positive relie ces recettes au support effectivement produit.
Pour toute formation de cette classe, la capture lit les valeurs conservées.
Le payload contient la formation antérieure, la recette, la valeur déjà produite
et son accord avec cette production. La restauration reconstruit le même
producteur et la même formation. Elle restitue le **support entier**, puis le
**curseur entier**, avec ses trois références dépendantes.

L'égalité porte donc sur les producteurs et les formations, pas seulement sur
les valeurs ou la profondeur. Tout consommateur du curseur, et toute continuation
finie du moteur maître, retrouve la même entrée depuis ce payload restauré.
Ces lois sont des preuves Lean constructives.

La classe est fermée par les sept productions de chaque tête effectivement
exécutée. Les preuves d'appartenance couvrent aussi tout programme documentaire
fini, toute politique adaptative totale et toute suite finie du langage mémoire,
à partir d'un maître initialement formé dans cette classe. Elles consomment
les étapes partagées de la trace reçue et leur accord avec l'exécuteur.
Elles n'exigent ni réussite des buts ni admissibilité de toutes les propositions.

## Ce qui est portable à ce stade

Deux données doivent être distinguées.

Le **payload de recettes typées** conserve aussi les valeurs maître et les
environnements dépendants. Il n'a plus un champ libre de type Producer
pour chaque étape : le producteur est reconstruit par la recette correspondante.
Cependant, les indices de ces recettes et les valeurs maître contiennent
encore des états, assignations et données de rang supérieur. Ce payload
n'est pas une représentation entière en données de premier ordre.

L'**enregistrement de recette** contient seulement le code de l'opération et
les positions de ses ports. Cet enregistrement a son codec exact depuis des
octets. Les positions sont une lecture des références typées ; leur ordre,
leurs répétitions et leurs distinctions sont conservés. Le chargeur vérifie
le code, l'arité, les naturels et la consommation entière des octets.

Cet enregistrement ne suffit pas à reconstituer la recette typée ni son
environnement. Il n'est pas un checkpoint maître. Il n'identifie pas, à lui
seul, les sources et la configuration de tout le présent. Ses octets ne sont
pas présentés comme le schéma versionné du futur checkpoint complet.

La restriction à la classe formée est positive : une histoire emploie ces
sept producteurs avec leurs ports. Elle ne transforme pas un producteur
arbitraire de même valeur en producteur canonique. La restauration générale
du [payload maître antérieur](restauration-present-composants.fr.md) garde
sa portée propre ; ce nouveau résultat prépare la représentation des producteurs
réellement employés par l'application.

## Les données que la capture consomme

Le constructeur de capture reçoit le support actuel et un témoin positif
de sa classe de formation. Il lit les valeurs matérielles de ce support.
Les lois de retour ne remplacent pas une sortie par l'application nouvelle
d'une ancienne opération.

Les preuves d'appartenance aux classes de traces sont logiques : elles
établissent l'existence du témoin à partir de l'exécution reçue. Elles ne sont
pas annoncées comme un constructeur de certificats à exécuter après coup
sans coût ni rejeu. Les fonctions qui construisent des témoins de continuation
ne sont pas incluses dans le contrôle du chargement.

Une lecture séparée parcourt directement la formation conservée et relève
les ports de chaque producteur. Elle n'a pas besoin de reconstruire un témoin
de classe. Pour un support formé, une preuve établit son accord avec les ports
des enregistrements de recettes. Cela relie les enregistrements à la
constitution reçue, plutôt qu'à une liste d'indices prescrite indépendamment.

## Chaîne formelle

| Module | Résultat |
| --- | --- |
| [DocumentaryMasterOperations.lean](../../Tests/LocalAlignment/DocumentaryMasterOperations.lean) | Sept recettes typées, reconstruction des producteurs existants, ports ordonnés exacts et codec des enregistrements |
| [DocumentaryMasterFormation.lean](../../Tests/LocalAlignment/DocumentaryMasterFormation.lean) | Classe positive, capture des valeurs conservées, égalité du support et du curseur, fermeture de toute continuation maître finie |
| [DocumentaryMasterFormationExecution.lean](../../Tests/LocalAlignment/DocumentaryMasterFormationExecution.lean) | Appartenance des programmes, des politiques adaptatives et des requêtes mémoire ; existence du payload exact pour leur maître final |
| [DocumentaryMasterObservation.lean](../../Tests/LocalAlignment/DocumentaryMasterObservation.lean) | Lecture directe de la formation et accord avec les ports des recettes |
| [DocumentaryMasterFormationCases.lean](../../Tests/LocalAlignment/DocumentaryMasterFormationCases.lean) | Instanciations sur les traces reçues, cas inadéquats et bloqués, futurs finis et refus de formats invalides |

resources_exact restitue tout le support. cursor_exact restitue tout le
curseur, assignation et références comprises. all_cursor_consumers et
future_heads consomment cette égalité exacte.

Les théorèmes program_formed, adaptive_formed et memory_formed couvrent
les productions supplémentaires, les inversions de sources, les refus et les
dépendances absentes. Une déduction conserve le curseur maître. Une tentative
de citation consomme son successeur réel, même si elle est refusée.
Une proposition détournée peut donc ajouter des productions ; la preuve
conserve ce passage au lieu de le remplacer par la seule tâche requise.

## Vérifications exécutées

Les cinq modules portent 76 déclarations sélectionnées sans axiome.
Le build avec l'audit exhaustif est passé : 24 604 constantes dans 281 modules,
364 exceptions générées historiques inchangées et aucune exception écrite.

Le contrôle du code généré examine sept graphes d'appels directs : capture,
arbre de formation, ressources, curseur, restauration et lecture des ports.
Il rejette 14 injections d'une production historique ou d'une application
indirecte. Les sept fabriques de producteurs peuvent construire les fermetures
qui serviront lors de futurs calculs ; elles ne les appliquent pas dans ces
graphes de capture et de restauration.

Cette portée n'inclut pas l'exécution ultérieure des fermetures construites,
la construction des témoins de classe, l'initialisation globale du processus,
ni l'identité physique des allocations. Elle ne constitue pas un contrôle
d'un chargeur maître depuis des octets.

Un processus Lean audité exécute les trois programmes existants depuis le
même cadre initial reçu : le programme complet, celui qui produit une sortie
inadéquate et celui qui contient un refus puis une dépendance absente.
Les ports sont lus dans leurs formations réellement produites, écrits et
comparés à des oracles littéraux indépendants. Ils comptent respectivement
trois, deux et deux têtes maître ; le support initial n'a aucun producteur.

Huit enregistrements, dont un cas de ports répétés, produisent les octets
attendus par un oracle séparé. Douze formats invalides sont rejetés : code
inconnu, naturel négatif, arité incorrecte, troncature, octet hors alphabet
ou données supplémentaires. Les huit fonctions du client runtime ont leur
audit sans axiome. Aucun modèle local n'est appelé.

    lake build Tests.LocalAlignment.DocumentaryMasterFormationCases Tests.AllConstantsAudit
    python -B scripts/check-master-recipes-codegen.py
    python -B scripts/run-master-recipes-smoke.py

La vérification complète de cet incrément est passée : 282 fichiers Lean,
284 jobs de build, audit exhaustif et 23 fixtures de refus attendu.
Le [relevé de développement](recettes-producteurs-maitre-verification.json)
conserve les commandes, les portées et les empreintes de cet arbre.
Les anciennes évidences et le registre scientifique restent inchangés.
Cet incrément reste un candidat de développement ; aucun audit indépendant
nouveau n'est enregistré.

## Prochaine obligation du lot 6

Il reste à représenter en données portables les valeurs maître et les
environnements que les recettes consomment, avec leurs formations. Il faudra
résoudre les ports depuis ces données chargées, restituer la recette typée,
puis réunir le maître avec les codecs du stockage, du dossier et du contrôle.

Le chargement conjoint devra identifier la configuration reçue et fournir
l'égalité du présent entier. Un nouveau processus devra ensuite réaliser
de nouvelles citations et déductions depuis ce présent chargé. La restauration
des recettes typées et les octets des enregistrements ne ferment pas cette
reprise physique complète. Le lot 6 demeure ouvert sur cette obligation et
sur l'interface documentaire du modèle local.
