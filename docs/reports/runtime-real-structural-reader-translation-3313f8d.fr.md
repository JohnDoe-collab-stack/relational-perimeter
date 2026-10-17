# Revue de lecture et de traduction — correspondance structurelle effective

Responsable : Codex (OpenAI), lectures autonomes puis confrontation formelle.

Date : 18 octobre 2026.

Révision examinée : `3313f8db67b84aa67d79a9d6f5721066d5cfbe67`.

## Périmètre et ordre de lecture

La lecture française autonome a porté intégralement, dans cet ordre, sur
`godel-regroupement-completude-reels.fr.md` puis
`runtime-real-cauchy-effective-correspondence.fr.md`. La lecture anglaise a
ensuite porté intégralement sur
`godel-grouping-relational-real-completeness.en.md` puis
`runtime-effective-cauchy-real-correspondence.en.md`. La confrontation aux
types et aux corps Lean a été effectuée après ces lectures séparées.

La confrontation formelle a suivi quatre lectures distinctes : formation des
objets et indices ; exécution des producteurs et actions ; obligations
réellement consommées par les preuves ; transports et pertes autorisées. Elle a
couvert la chaîne gödelienne et son runtime commun, les cinq constructeurs du
porteur réel fermé, les opérations additives et multiplicatives, l'inverse sous
apartness, l'ordre positif, la densité et les bornes finies, les transports de
familles, la production native de limites, leur unicité et le paquet terminal
`effectiveCorrespondence`.

## Revue de lecture française

Le passage gödelien conserve sa portée propre. Il quantifie sur une exécution
gödelienne effective et une famille de Cauchy exécutée reçue sur la présentation
produite. Le maître commun exécute les sources, construit et consomme les
regroupements historiques, installe la cible et permet sa continuation. La
branche négative réutilise le même témoin diagonal pour rejeter la boucle totale
et la fermeture globale du même régime. Ce passage ne prétend toujours pas, à
lui seul, fournir les opérations de corps, la densité ou tous les réels
classiques. Leur construction séparée dans le passage structurel n'est donc pas
une contradiction de portée.

Le passage structurel place correctement le runtime avant son readout. Le type
`Real P baseDepth` est fermé par `leaf`, `add`, `neg`, `mul` et `certified` ;
les opérations composées exécutent leurs enfants depuis les archives courantes,
retiennent les productions et actions exactes, puis seulement projettent leurs
codes. Les fonctions `toPresentation` et `toCarrier` sont utilisées comme vues
numériques aval, jamais comme constituants des runtimes.

L'inverse n'est pas totalisé : sa construction exige une `Apartness` orientée à
zéro. L'ordre n'est pas rendu décidable ; ses preuves transportent des témoins
positifs et exécutent les comparaisons depuis les archives reçues. La densité et
les bornes naturelles exposent les mêmes cibles que leurs actions constitutives.
Le texte ne transforme ni ces témoins finis en complétude d'ordre, ni les
contrôles du code compilé en borne de coût physique.

Pour les familles natives, le terme diagonal est exécuté depuis l'entrée
courante de la banque, et le regroupement consomme le `Step` appartenant à cette
même production. La mémoire suivante installe cette cible et remplace seulement
l'entrée visitée. Le runtime live est constitué par les kernels reçus et le
module ; le raccord propositionnel au readout canonique intervient dans la
preuve, sans introduire un rejeu riche dans la fermeture compilée.

La complétude native construit donc un candidat, sa convergence et sa
réutilisation. L'unicité produit un seul pas médiateur du terme et le partage
entre deux convergences. Sa conclusion est numérique et comportementale : elle
n'identifie ni les constructeurs, ni les archives, ni les occurrences. Le test
qui oppose un candidat `certified` à un candidat `add` confirme explicitement
cette séparation tout en conservant leur accord numérique.

Verdict de lecture française : **reviewed** pour
`GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS` et
`RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE` sur la révision indiquée. Ce
verdict ne vaut ni audit indépendant, ni couverture de tous les réels
classiques, ni verdict d'originalité.

## Revue de traduction anglaise

La version anglaise conserve les quantifications, les entrées reçues, les
directions de dépendance et les exclusions du français. `closed carrier`
désigne le même type inductif fermé par cinq constructeurs ; il n'introduit pas
une clôture totalisante gödelienne. `downstream readout` conserve l'orientation
runtime-vers-présentation. `reflection` s'applique aux relations numériques sur
les images des applications et ne signifie jamais reconstruction des histoires
riches.

Les formulations de l'inverse partiel, de l'ordre non globalement décidable,
des témoins finis de densité et de bornes, du `Step` diagonal consommé par le
regroupement, de la banque mise à jour localement et de l'unicité sans identité
d'occurrences correspondent au texte français. Les deux versions séparent de
la même manière `Equivalent`, `NumericalFutureEquivalent` et l'égalité des
objets riches.

Verdict de traduction : **reviewed** pour les deux affirmations sur la révision
indiquée. Aucune extension ou réduction de portée n'a été relevée entre les
passages canoniques français et anglais.

## Contrôles techniques de la révision

La révision a passé le build Lean complet (`398` travaux), l'audit global des
constantes (`37002` constantes, `395` modules, `735` exceptions générées et
aucune exception écrite), les frontières d'import, la stratification de `329`
modules de production et les seize contrôles du code compilé.

Le harnais indépendant des façades de fixtures a passé ses vingt cas : les deux
baselines ont chacune exécuté `182` fixtures, puis les dix-huit mutations ont
été rejetées avec le statut et le diagnostic attendus. Aucun timeout n'a été
accepté. Le fichier temporaire `results.json`, conservé hors dépôt, porte
l'empreinte SHA-256
`33686DCADB50DB81F71B7CACD64915B37A7BC82B20595E4F39929155A02A9BB2`.

Les sept autotests documentaires passent. Après enregistrement de la nouvelle
révision, des empreintes et de la présente évidence dans le registre, les
contrôles `--static` et `--lean` passent, puis les deux façades complètes
`verify.ps1` et `verify.sh` passent sur le même contenu scientifique. La façade
Bash a été exécutée sous Git Bash ; une tentative préalable avec le binaire WSL,
qui ne résolvait pas le chemin Windows du Python figé, n'est pas comptée comme
une vérification du dépôt.

Ces contrôles ne remplacent pas la lecture sémantique ci-dessus et ne
constituent pas un audit extérieur. Le statut indépendant reste
`not_recorded` tant qu'un rapport extérieur visant exactement la révision
indiquée n'a pas été reçu et lu.
