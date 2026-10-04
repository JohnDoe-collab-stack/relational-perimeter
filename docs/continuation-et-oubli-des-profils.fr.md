# Continuation et oubli des profils normalisés

Le résultat de largeur et sa cible scientifique restent inchangés. Cette
extension précise ce qui peut rester disponible après une normalisation réelle,
sans conserver son entrée historique dans la mémoire de reprise.

## Une même exécution, deux interfaces

`UnifiedMaster.publicInstance` initialise puis appelle une fois l'exécuteur par
ressources typées. Ses rôles, son programme, sa normalisation, son régime et son
curseur sont des projections de ce résultat commun. `UnifiedMaster.certificate`
réunit cette instance et les preuves portant sur elle ; il n'est pas conservé
dans la mémoire de reprise.

Le certificat fermé fixe le régime d'image effectif, le curseur de reprise,
les lecteurs produits, l'accord des têtes entre horizons, le prolongement
historique et les lectures des références. L'admission d'une inspection
équivaut à la borne des rôles produits ; son événement est la lecture
correspondante de la sortie produite, pas seulement un accord entre deux
implémentations. Le contrôle des chemins compilés interdit séparément la
réexécution d'un calcul égal : l'égalité des résultats ne prouve pas, à elle
seule, qu'un exécuteur n'a été appelé qu'une fois.

Ces lois fixent le contrôle de borne et la lecture déterministes définis par
l'interface d'inspection ; elles ne décrivent pas une découverte supplémentaire.

`ProducedContinuation.publicStart` utilise cette même exécution par ressources.
Cette exécution fournit à la fois les rôles et les relations de la normalisation,
et le curseur atteint depuis lequel la recherche reprend. Elle est prouvée égale
à l'exécution publique auditée par `public_execution_exact`.

L'interface historique conserve le profil source, le résultat exécuté et sa
trace. L'interface de reprise conserve uniquement l'état vivant, la sortie
normalisée et les lecteurs des continuations effectivement produites. Elle ne
stocke ni le profil source, ni le résultat historique, ni le support de ressources,
ni le préfixe opérationnel. Les preuves d'accord restent séparées du moteur.

L'état vivant conserve notamment l'affectation, la génération, la graine et la
provenance encore consommées par la découverte. Il n'est pas présenté comme une
mémoire minimale ou comme l'effacement de toute histoire reconstructible.

## Regroupement et transports sur les mêmes rôles

Les règles locales sont construites à partir des licences retournées par les
étapes exécutées. Les actions sur les continuations arbitraires préservent
l'acceptation, et deux traces normalisantes transportent la même donnée vers
la même sortie. L'égalité des obligations correspond exactement à l'égalité
des cibles produites, sans identification des profils sources.

Le théorème de la classe binaire s'applique directement au régime maître : son
carrier est définitionnellement celui des mêmes profils de rôles. La largeur
complète est `2^(input+1)`, la largeur exécutée est un. Les politiques de
regroupement partiel sur ces mêmes rôles ont largeur `2^k`, où `k` compte les
rôles conservés séparément. Ces politiques ne sont pas présentées comme des
exécutions supplémentaires de découverte.

Les transports de codage et d'image ont leurs deux lois de retour. L'image
des positions normales est aussi raccordée aux obligations de valeurs
effectivement produites, avec accord de `carry`. Ce transport est établi après
la réduction et sa convergence ; son inverse restitue une position normale,
pas le profil source ni la continuation d'origine.

Une extension de la recherche conserve les têtes déjà produites et utilise le
profil effectivement produit du nouveau suffixe. Son plongement préserve la
distinction des anciens profils, respecte la renormalisation et se compose
sur les profils comme sur les obligations. Cette extension historique reste
une interface scientifique distincte de la mémoire de reprise.

`Instance.grow` reçoit l'instance conservée, exécute uniquement les pas nouveaux
depuis son curseur terminal et raccorde le suffixe à l'histoire conservée.
`Growth.resume` prolonge ce résultat à son tour. Les références typées aux
ressources anciennes sont transportées dans le support étendu ; leurs lectures,
leurs distinctions et leur composition sont prouvées. Le transport de l'instance
est fixé au résultat de son producteur, pas fourni indépendamment. Ces références
historiques ne sont pas ajoutées à la mémoire de reprise : son contrat n'autorise
que les opérations et lectures futures décrites ci-dessous.

Le prolongement générique exige aussi un `ProducedPrefix` construit
positivement : le curseur complet doit être celui retourné par l'exécuteur
de ressources, pas un support étranger ayant la même frontière. Le raccord
conservé est prouvé égal à une exécution ininterrompue ; cette preuve ne lance
pas une seconde exécution.

## Le contrat futur exact

Deux opérations sont autorisées :

- demander un nombre de pas supplémentaires du moteur réel ;
- lire une variable d'une continuation produite, à un rôle existant.

Les adresses des rôles sont une lecture ordinale dérivée de l'histoire
constituée. L'admission d'une lecture vérifie sa borne. Les opérations de reprise
ne reçoivent ni l'ancien profil ni l'archive scientifique. La préparation extrait
les lecteurs une fois ; les lectures futures ne retraversent pas l'histoire.

L'entrée runtime `ProducedContinuation.executeRequests` calcule ensemble le
successeur et les événements de chaque requête. Chaque pas partage sa production
entre l'événement et le prochain état. Les fonctions séparées `next` et `event`
servent aux lois du contrat ; elles ne sont pas deux passages à lancer pour
obtenir ces résultats runtime.

Le contrat préserve les événements de découverte, application et décomposition,
les lectures de l'état vivant et les observations des continuations produites.
Ces accords valent pour toutes les suites finies de requêtes. L'admission est
transportée dans les deux directions. Une lecture concrète du premier rôle est
construite et sa réponse est prouvée existante : le contrat n'est pas vide.

Le nombre de pas est l'entrée de l'exécuteur déjà présent. Cette construction
ne prétend pas ajouter une classe générale d'entrées interactives ou résoudre
des instances SAT arbitraires.

## Ce qui est effectivement oublié

Les profils publics transformé et retenu sont distincts. Leurs normalisations
réellement exécutées donnent la même mémoire de reprise. Toutes les requêtes
du contrat donnent alors les mêmes événements futurs. Aucun décodeur Lean ne
peut retrouver uniformément le profil d'origine depuis cette mémoire.

Ce n'est pas une identification des profils constitués : leurs identités et
leur distinction restent établies dans l'interface historique. C'est la perte
de leur entrée historique depuis la mémoire de reprise, sous le contrat annoncé.

Il faut distinguer ces parcours de normalisation des préfixes chronologiques
canoniques de la recherche. Le théorème de reconstruction sous conservation
exacte de la profondeur et de toute la provenance reste vrai sur ces derniers.
Il ne prouve pas l'impossibilité de l'oubli des profils normalisés.

## Repères dans le code

Les interfaces de regroupement sont des reconstructions locales autonomes,
informées par le matériau de comparaison sous Apache-2.0. Elles utilisent les
interfaces locales de rôles, traces, images finies et continuation ; aucune
fondation extérieure ni dépendance par chemin n'est requise. La licence du
dépôt reste Apache-2.0.

- [Instance et certificat maître](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean) : `publicInstance`, `certificate`, `class_iff_on_executed_regime`, `publicGrowth`, `public_obligations_compose`.
- [Clients de la façade maître](../Tests/UnifiedMasterInstance.lean) : application directe du théorème de classe, transports, admission et perte du profil.
- [Moteur vivant](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/LiveResourceContinuation.lean) : exactitude des productions, des reprises et des événements.
- [Contrat et séparateur](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ProducedProfileContinuation.lean) : `memory_fibres`, `public_profile_irrecoverable`, `public_all_future_events`, `publicContractCertificate`.
- [Clients et calcul concret](../Tests/ProducedContinuation.lean).

Ces preuves ne donnent ni une borne de coût total, ni une borne physique de
mémoire, ni l'oubli de toute provenance. Elles n'affaiblissent pas le résultat
de largeur opérationnelle déjà établi.

## Reproduction locale

Depuis la racine du dépôt :

Python 3 est requis par les vérificateurs. `RELATIONAL_PERIMETER_PYTHON` permet
de sélectionner son exécutable si `python3` n'est pas disponible dans le chemin.

```sh
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
```

Les clients publics incluent des calculs concrets du checkpoint, en plus des
preuves générales. Ces contrôles locaux ne sont pas un audit indépendant.
