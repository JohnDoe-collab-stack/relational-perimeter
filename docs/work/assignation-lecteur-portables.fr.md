# Reprise portable de l’assignation et de son lecteur mesuré

**Date :** 10 octobre 2026.

**Branche :** codex/ai-alignment-under-contract.

**Candidat scientifique :** DOCUMENTARY_ASSIGNMENT_READER_BYTES.

**Référence de départ :** f30196e4a8ae2b77b0d061c1e03cccd236265013,
avec l’incrément de recettes maître déjà présent dans l’arbre de développement.

## Le composant fermé

Le maître conserve une assignation fonctionnelle et le lecteur qui mesure
ses opérations. Ce composant possède maintenant une représentation de premier
ordre et un codec exact depuis des octets. La restauration retrouve le
**couple entier : assignation et lecteur mesuré**. Elle ne conserve donc pas
seulement les réponses à quelques questions déjà posées.

Le point de départ déclaré est la primitive alternante existante et son
lecteur existant. Les commandes enregistrent ensuite les retournements et
les visites du code de transport réellement retourné. Une identité ajoute
sa visite ; une composition conserve les visites des deux sous-codes puis
celle de leur composition. Les commandes sont stockées de la plus récente
à la plus ancienne. Leur interprétation construit les fonctions latentes
qui traiteront de futures lectures.

Deux recettes peuvent donner les mêmes bits et avoir des compteurs différents.
Un séparateur Lean le montre pour la recette initiale et celle qui ajoute
une visite : les bits sont identiques pour toute variable, tandis qu’une
lecture de la variable zéro compte respectivement trois et quatre nœuds.
Le codec conserve cette distinction.

## La capture consomme les ressources conservées

La capture parcourt les valeurs du support maître reçu. Chaque tête conservée
fournit sa variable de découverte et son propre code de transport exécuté.
Les autres ressources ne sont pas remplacées par des têtes recalculées.
La liste des commandes n’est pas une liste de variables attendues prescrite
indépendamment de l’exécution.

Une première lecture employait la variable du champ de schedule dérivé.
L’inspection du code compilé a montré qu’elle reconstruisait le contexte de
génération. La version finale lit directement la variable de découverte
conservée. Une preuve établit son accord avec celle du schedule. Le contrôle
compilé rejette aussi l’injection de cette reconstruction.

La capture ne construit pas un nouveau témoin de la trace. Son résultat est
une donnée exécutable lue dans les valeurs actuelles. Les théorèmes établissent
séparément son exactitude pour les traces couvertes.

## Quantifications et preuves

La loi du codec vaut pour **toute recette finie** du langage déclaré. La
fidélité du lecteur vaut pour toute donnée positivement représentée par ce
langage. La primitive initiale est fixée ; aucun codec pour une fonction
arbitraire n’est annoncé.

La réflexion est exacte pour tout code de transport de la relation de
retournement existante, avec ses cas identité, atome et composition, à partir
d’un lecteur représenté. Elle conserve aussi le lecteur produit par toute
étape séquentielle reçue, en consommant les accords de l’entrée, du code,
de la sortie et du lecteur inscrits dans cette étape.

Pour les ressources maître, la condition initiale est l’accord exact entre
la recette lue dans le support et le couple assignation/lecteur courant.
Elle est prouvée pour les curseurs initiaux de l’assignation alternante.
Elle est ensuite conservée par toute continuation maître finie et par toute
trace finie du programme documentaire, de la politique adaptative totale
ou du langage mémoire déclaré. Ces preuves couvrent les propositions
détournées, les refus, les déductions, les dépendances absentes et les remises
à zéro du contexte. Elles ne supposent pas que la tâche réussisse.

L’égalité obtenue porte sur les fonctions elles-mêmes, avec le lecteur
dépendant. Elle est établie constructivement par la constitution du code
et les accords des étapes. Toute lecture finie de variables retrouve les
mêmes bits et les mêmes compteurs. Tout consommateur du couple restauré
consomme exactement la même donnée dans ce cadre.

| Module | Passage établi |
| --- | --- |
| [DocumentaryPortableAssignment.lean](../../Tests/LocalAlignment/DocumentaryPortableAssignment.lean) | Couple assignation/lecteur, primitive alternante, commandes, réflexion du code exécuté et exactitude d’une étape reçue |
| [DocumentaryAssignmentCodec.lean](../../Tests/LocalAlignment/DocumentaryAssignmentCodec.lean) | Enveloppe versionnée, codec des commandes, retour exact du couple et de ses consommateurs |
| [DocumentaryAssignmentCapture.lean](../../Tests/LocalAlignment/DocumentaryAssignmentCapture.lean) | Capture des valeurs conservées et fidélité sur les traces maître, documentaires, adaptatives et mémoire |
| [DocumentaryAssignmentCases.lean](../../Tests/LocalAlignment/DocumentaryAssignmentCases.lean) | Traces concrètes reçues, futurs finis, identité, composition et séparateur du coût de lecture |

## Octets et reprise physique

Le schéma de composant porte l’identifiant 88 et la version 1. Il contient
le nombre de commandes, puis chaque code et son port optionnel. Une visite
n’a pas de variable ; un retournement en exige une. Le lecteur vérifie le
schéma, la version, les naturels, les arités et la consommation entière
des mots et des octets.

Une recette syntaxiquement valide modifiée désigne un autre lecteur.
Le chargeur ne compare pas ses octets à une histoire externe et n’offre
pas une authentification du checkpoint. La loi de fidélité concerne les
octets sauvegardés depuis la donnée représentée.

Un processus exécute les trois programmes existants depuis le même cadre
initial reçu : complet, inadéquat, puis refus avec dépendance absente.
Il écrit la recette de leur support effectivement produit et les lectures
de leur assignation réelle. Trois nouveaux processus chargent uniquement
les octets de recette et effectuent de nouvelles lectures. Les résultats
retrouvent exactement les bits et compteurs des lectures de référence.

Les codes et sorties écrits sont aussi confrontés à des oracles indépendants :
les variables littérales des trois traces et un calcul séparé des bits,
visites et comparaisons unaires pour dix questions. Quatre reprises
supplémentaires traitent la primitive seule, une visite, deux retournements
de la même variable et la forme identité-atome-composition. Quinze formats
invalides sont refusés dans un client séparé.

Ce smoke emploie neuf processus physiques. Les clients de départ, de reprise
et de refus auditent respectivement sept, six et trois déclarations sans
axiome. Aucun modèle local n’est appelé.

## Vérifications de cet incrément

Les quatre modules portent 84 déclarations sélectionnées sans axiome.
L’audit exhaustif passe sur 24 772 constantes dans 285 modules, avec les
364 exceptions générées historiques inchangées et aucune exception écrite.

Huit graphes d’appels directs contrôlent la capture, la réflexion, la
construction des fonctions latentes et le chargement du composant. Dix-huit
injections de production historique, reconstruction de génération ou lecture
prématurée sont rejetées. Les callbacks du codec ne portent que sur les mots
de premier ordre. Les chemins de capture et de construction ne font aucune
application indirecte de fermeture.

Ce contrôle porte sur les appels nommés directs. L’exécution ultérieure
du lecteur, l’initialisation globale, le runtime, le compilateur et le système
gardent leurs frontières propres. Une future lecture exécute effectivement
la chaîne de lecteur conservée ; aucune borne de coût constant ou d’énergie
physique ne découle de cette restauration.

    lake build Tests.LocalAlignment.DocumentaryAssignmentCases Tests.AllConstantsAudit
    python -B scripts/check-assignment-codegen.py
    python -B scripts/run-assignment-restart-smoke.py

La vérification complète de cet incrément est passée : 286 fichiers Lean,
288 jobs de build et 23 fixtures de refus attendu, avec l’audit exhaustif
et les contrôles du code compilé et des reprises physiques.
Le [relevé de développement](assignation-lecteur-portables-verification.json)
conserve les commandes, les portées, les reçus et les empreintes de cet arbre.
Les évidences historiques et le registre scientifique restent inchangés. Cet incrément
est un candidat de développement ; aucune nouvelle revue indépendante
n’est enregistrée.

## Ce qui reste au lot 6

Le couple restauré ne constitue pas tout le SequentialAssignment : ses
invariants dépendants et sa place dans le maître restent à raccorder.
Les états de génération, décisions et provenance, contextes opérationnels,
résultats de découverte et d’application et environnements des producteurs
doivent encore recevoir leur représentation portable fidèle.

Ce composant prépare le chargement des valeurs et environnements des
[recettes maître](recettes-producteurs-maitre.fr.md). Il reste ensuite à
résoudre leurs ports depuis les données chargées et à réunir le maître,
le stockage, la mémoire documentaire et le contrôle en identifiant la
configuration reçue. La reprise physique devra réaliser de nouvelles
citations et déductions depuis ce présent entier chargé. Le lot 6 demeure
ouvert sur ces passages et sur l’interface documentaire du modèle local.
