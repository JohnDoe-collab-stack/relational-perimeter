# Analyse confirmatoire du passage à l’échelle du checker compilé — v8

## Verdict

La campagne établit une réutilisation structurelle réelle des fragments pour
les transitions dont le cône affecté reste local. Elle **n’établit aucun gain
pratique de temps** : sur cette famille et cette implémentation, le checker
incrémental compilé est beaucoup plus lent que le recheck complet apparié. Le
critère de gain fixé avant le run est donc `false`.

Ce résultat défavorable ne modifie ni les théorèmes Lean de correction et
d’équivalence, ni l’existence de la réutilisation transportée. Il montre que
leur implémentation actuelle n’offre pas encore l’économie physique attendue.

## Protocole effectivement exécuté

- Sept tailles : 0, 2, 5, 10, 20, 40 et 80.
- Une initialisation, puis six mises à jour successives par processus.
- Une répétition d’échauffement et cinq répétitions mesurées par taille.
- 35 traces mesurées et 210 mises à jour acceptées.
- Une seule instance maître par processus.
- À chaque étape, le checker incrémental et le recheck complet reçoivent le
  même état source et le même artefact cible ; Lean identifie leurs successeurs.
- Aucun run mesuré n’a été retiré.

La v7 antérieure est conservée comme échec de protocole : son échauffement à la
taille 160 a dépassé le budget de 120 secondes. Aucun résultat v7 partiel n’a
été promu.

## Croissance structurelle observée

| taille | neurones | largeur du profil | graphe nœuds/arêtes | certificat initial |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 2 | 4 | 17 / 20 | 4 |
| 2 | 4 | 6 | 19 / 26 | 6 |
| 5 | 7 | 9 | 22 / 35 | 9 |
| 10 | 12 | 14 | 27 / 50 | 14 |
| 20 | 22 | 24 | 37 / 80 | 24 |
| 40 | 42 | 44 | 57 / 140 | 44 |
| 80 | 82 | 84 | 97 / 260 | 84 |

La famille n’est pas une répétition d’un graphe fixe : le réseau, le profil,
le graphe causal, le certificat et les unités de vérification croissent tous
avec la taille.

| taille | unités d’exécution | unités de vérification | delta de certificat |
| ---: | ---: | ---: | ---: |
| 0 | 2 | 37 | 4 |
| 2 | 4 | 45 | 6 |
| 5 | 7 | 57 | 9 |
| 10 | 12 | 77 | 14 |
| 20 | 22 | 117 | 24 |
| 40 | 42 | 197 | 44 |
| 80 | 82 | 357 | 84 |

Pour une transition source vers locale ou locale vers source, le cône mesuré
reste à 14 nœuds. À la taille 80, 83 fragments sont transportés et un seul est
recalculé. Pour une transition source vers étendue, le cône atteint 96 nœuds :
un fragment est transporté et 83 sont recalculés. La transition étendue vers
locale est elle aussi étendue, car le delta est relatif à l’état effectivement
installé, et non au seul nom de la version cible. Le protocole distingue donc
bien les changements locaux des changements étendus dans une trace réelle.

## Coûts temporels observés

Les valeurs ci-dessous sont les médianes de cinq répétitions. Les temps de
trace couvrent six mises à jour. Le ratio utilise le coût total, initialisation
comprise.

| taille | initialisation (ms) | incrémental, trace (ms) | recheck complet, trace (ms) | ratio total incrémental/complet | pic RSS médian (MiB) |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 0,0216 | 0,1671 | 0,0201 | 4,49 | 8,95 |
| 2 | 0,0251 | 0,4296 | 0,0284 | 8,44 | 10,88 |
| 5 | 0,0291 | 1,7476 | 0,0491 | 22,74 | 10,69 |
| 10 | 0,0412 | 11,4767 | 0,1099 | 76,53 | 11,50 |
| 20 | 0,0875 | 131,2957 | 0,3632 | 291,51 | 11,85 |
| 40 | 0,2948 | 2 808,0782 | 1,5250 | 1 559,36 | 13,25 |
| 80 | 1,6847 | 70 777,6260 | 10,5220 | 5 779,31 | 23,39 |

Le critère préenregistré exigeait, pour chaque taille au moins égale à 20, un
coût total incrémental médian inférieur ou égal à 80 % du coût complet médian.
Il échoue à toutes ces tailles. La campagne ne permet donc pas de revendiquer
une économie pratique.

Les points finis indiquent également une croissance très défavorable du
chemin incrémental actuel. Ils ne suffisent toutefois pas à établir une loi
asymptotique : aucune qualification polynomiale ou exponentielle n’est tirée
de ces sept tailles.

## Ce qui est établi et ce qui reste ouvert

Établi par le code et les observations appariées :

- le même checker compilé accepte plusieurs adaptations successives ;
- l’incrémental et le complet visent exactement le même artefact et la même
  propriété depuis le même état ;
- leurs successeurs sont égaux dans le type Lean ;
- des fragments sont réellement transportés lors des changements locaux ;
- le graphe pertinent et les certificats grandissent avec la famille ;
- la mémoire résidente observée reste sous 24 MiB jusqu’à la taille 80 ;
- aucun gain temporel n’est observé ; le résultat préenregistré est négatif.

Non établi :

- une borne asymptotique de temps ou de mémoire ;
- un gain pratique de l’incrémental ;
- une généralisation à d’autres familles de réseaux ou contrats ;
- une explication théorique du coût élevé de l’implémentation incrémentale ;
- une attribution physique séparée du temps à la conversion, à l’assemblage du
  certificat et à l’installation. Le binaire chronomètre l’initialisation, le
  chemin incrémental et le recheck complet ; ses colonnes `execution_units` et
  `verification_units` sont des comptages déterministes, pas des chronomètres
  de phases internes.

La prochaine optimisation éventuelle doit être une nouvelle étude. Elle ne
peut pas réinterpréter cette campagne ni remplacer ses résultats défavorables.
