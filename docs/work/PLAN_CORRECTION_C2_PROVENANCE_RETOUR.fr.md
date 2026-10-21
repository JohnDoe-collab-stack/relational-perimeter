# C2 — Plan de correction de la provenance des résultats du pont

Préparé le 21 octobre 2026 après lecture du rapport, du patch C2e, des
producteurs Lean, des contrôleurs Python et du C effectivement généré.

**Statut : correction implémentée et vérifiée localement de bout en bout.**
Aucun nouveau verdict d'audit indépendant n'est annoncé par ce document.

## 1. Référence et problème exact

| Référence | Valeur |
| --- | --- |
| Dépôt | `JohnDoe-collab-stack/relational-perimeter` |
| Branche étudiée | `codex/constitutive-agent-corrections-audit` |
| HEAD lors de cette étude | `e7348c069ec92f8e10f1c55098d41c0f25c59f7a` |
| Commit scientifique audité | `8e56638bfeae56de64ef766b6030de16bb43ca1c` |
| Arbre scientifique audité | `ed1aa61bee925d3e0b652ebd4d28751845766554` |
| Rapport étudié, conservé hors dépôt | `CONSTITUTIVE_AGENT_THREE_LINKS_AUDIT.md`, notamment §§ 12, 15, 16, 19 et 20 |
| SHA-256 du rapport | `44f0742d0f5eeb9bd742814f1ee3e4a9b77df9387cbe28f177679c3e9c374a00` |
| Verdict de l'agent | `AGENT TARGET REQUIRES CORRECTIONS` |
| Verdict de conservation | `NO REGRESSION VERIFIED` |
| Toolchain | `leanprover/lean4:v4.33.1` |

Le rapport valide les clauses mathématiques centrales, l'instance publique,
C1 et C3. Le défaut restant concerne la protection du chemin compilé C2 :
une substitution partielle passe le build et le vérificateur Bash.

Dans C2e, le vrai champ `bridge.sourceEvent` appelle `sourcePerform`, mais
ne conserve de son événement que `productions`. Pour `inspect` et `propose`,
le message est recalculé par `decideReply` depuis `source.history.targets`,
sans utiliser la lecture matérielle de l'opération riche. Les autres demandes
retournent l'événement riche entier.

Ce message projeté a la même valeur que le message riche. Le patch rétablit
constructivement `eventLaw`, `bridge_source_event` et `bridgeRichResult`.
Il ne contredit donc aucun théorème d'égalité. Il contredit l'assurance que
le contrôleur donne sur la provenance du résultat retourné.

La correction doit fermer **ce défaut de consommation**, sans transformer
l'égalité de valeurs en une preuve de provenance qu'elle ne fournit pas.
L'ancien succès de la campagne à cinq cas reste un fait historique ; il ne
constitue pas une validation contre C2e.

## 2. Cible et méthode inchangées

### 2.1. Exigence reçue

> Poursuivre le moteur autorisé depuis ses productions réelles ; ne restituer
> une valeur que pour une production effectivement formée et une variable du
> périmètre reçu ; restituer la valeur de cette production, non une valeur
> choisie par le contrôleur ; préserver les garanties d’acceptation annoncées
> par les actions utilisées ; conserver ces droits et ces accords après reprise.

### 2.2. Critère d'achèvement conservé

> La première instance est achevée lorsque l’exigence concrète gouverne ses
> autorisations, que sa production opérationnelle est celle du moteur réel,
> que ses réponses et refus satisfont la spécification indépendante, et que
> le suivi de ces garanties se compose sur toutes ses interactions finies.
>
> La mémoire complète doit permettre cette continuation tout en ne permettant
> pas de reconstruire uniformément le profil initial oublié. Cette propriété
> doit être réalisée sur des sources distinctes effectivement construites.
>
> L’ensemble doit être livré comme une instance construite et exécutable, non
> comme une liste d’interfaces abstraites supposées satisfaites. Le résultat
> scientifique sera ce paquet fermé ; la transposition à d’autres exigences ou
> à d’autres agents restera une nouvelle tâche de preuve.

Cette correction ne modifie ni la
[conclusion computationnelle antérieure](../conclusion-largeur-exponentielle-conservation-identites.fr.md),
ni la [méthode constitutive](../constitution-calcul-et-persistance-pour-ia.fr.md),
ni le domaine d'interaction de l'agent.

### 2.3. Raccord à suivre de bout en bout

```text
exigence reçue et histoire constituée
  → référence sur le support et MaterialReading
  → décision de la même RichOperation
  → résultat de cette opération par sourcePerform
  → projection effectivement retournée par le champ riche du pont
  → accords locaux puis accords sur toutes les interactions finies
  → certificat fermé et client public
```

Les constructions et les lois de cette chaîne existent déjà. Le présent lot
renforce le contrôle logiciel de son quatrième raccord ; il ne substitue
pas ce contrôle aux autres raccords, ni aux témoins dans `Type`.

Invariants de méthode :

- L'égalité d'une valeur recalculée ne remplace pas sa production depuis le
  rôle, la lecture et la décision suivis.
- Le support historique et le support du moteur restent distincts, avec
  leurs véritables transports. Aucun registre projeté ne devient un support
  constitutif par simple renommage.
- Une référence conservée, un événement produit et une preuve d'admission
  ne sont pas interchangeables.
- L'archive scientifique reste séparée de la mémoire runtime ; on ne répare
  pas C2 en réintroduisant l'archive dans cette mémoire.
- L'extensivité reste un readout aval. Aucun parcours de profils, nouveau
  régime d'obligations ou modèle de coût n'entre dans cette correction.
- Les quatre fondations, le maître, les producteurs scientifiques, C1 et C3
  ne sont ni affaiblis ni remplacés.

## 3. Diagnostic technique vérifié

Dans [le contrôleur actuel](../../scripts/check-agent-codegen.py),
`bridge_fields` :

1. reconstruit le record retourné par le vrai `bridge` ;
2. sélectionne les fermetures de `sourceNext` et `sourceEvent` ;
3. exige un appel à `sourcePerform` par chemin ;
4. interdit quatre entrées runtime nommées.

La sélection du vrai record est utile et doit rester. Le défaut vient de
l'étape suivante : le contrôleur compte l'appel, mais ne vérifie pas
l'origine de la valeur qui sort de la fermeture. `decideReply` et la lecture
de `History.targets` permettent C2e sans appeler les quatre entrées interdites.

Le moteur partagé [d'analyse C](../../scripts/unified_codegen_analysis.py)
ne fournit pas déjà cette garantie :

- atteindre sa frontière `target` retourne une valeur abstraite vide et un
  compteur, pas un résultat dont les projections ont une origine précise ;
- `join` réunit des étiquettes, ce qui ne prouve pas que tous les retours ont
  la même origine autorisée ;
- les clés de mémoïsation fondées sur `retained()` ne distinguent pas toutes
  les structures de champs, origines et captures nécessaires ici ;
- l'appel au compteur des fermetures sélectionnées ne réinjecte pas leurs
  véritables captures dans une analyse d'origine des arguments.

Il serait donc incorrect de renommer les étiquettes existantes « provenance »
ou de rechercher simplement `sourcePerform` dans un graphe de dépendances.

Le C actuel de `Agreement` confirme le raccord attendu :

| Élément | Forme observée sous Lean 4.33.1 |
| --- | --- |
| Record runtime de `Continuation.Exact` | Neuf champs ; `sourceNext` à l'indice 1, `sourceEvent` à l'indice 5 |
| Captures des deux fermetures riches | `input` et `master` |
| Arguments restants | `source` et `request` |
| Opération | `sourcePerform(input, master, source, request)` |
| Retour de `sourceNext` | Projection 0 du résultat de cet appel |
| Retour de `sourceEvent` | Projection 1 du résultat de cet appel |
| `Event` | `productions` et `message`, deux champs distincts |

Ces observations ne sont pas des indices à supposer immuables. Le schéma Lean,
l'effacement et la forme compilée doivent être vérifiés avant leur usage.
Les numéros des lambdas et des variables C ne sont pas des identifiants stables.

## 4. Propriété exacte à contrôler

Pour **chaque invocation de chaque fermeture riche sélectionnée** :

1. appliquer les captures réellement installées dans le record et les
   arguments symboliques distincts `source` et `request` ;
2. identifier exactement un appel exécuté à la déclaration propriétaire
   `ConstitutiveSearch.Agent.sourcePerform`, avec ces mêmes arguments ;
3. suivre le résultat particulier de cet appel ;
4. exiger que chaque chemin retournant une valeur fournisse sa projection 0
   pour `sourceNext`, ou sa projection 1 entière pour `sourceEvent`.

« Un appel » signifie ici un appel dans une invocation du champ, pas un appel
global partagé entre les deux fonctions du pont. Il ne faut pas modifier
l'architecture pour fabriquer ce partage supplémentaire.

Une reconstruction transparente de record est admissible si chacun de ses
champs provient exactement de la projection correspondante du même résultat,
avec le même constructeur. En particulier, reconstruire un `Event` à partir
de ses deux champs riches doit réussir. Conserver seulement `productions`
et recalculer `message` doit échouer.

Ce contrôle ne décide pas l'égalité mathématique de programmes arbitraires.
Il vérifie une propriété d'origine des retours sur un fragment explicite du
C généré par la toolchain épinglée. Toute forme nécessaire non résolue donne
un échec explicite, jamais un succès par défaut.

## 5. Architecture retenue pour la correction

### 5.1. Séparer l'analyse d'origine de l'analyse de multiplicité

Créer un module local d'outillage, par exemple
`scripts/agent_codegen_provenance.py`, appelé par `bridge_fields`.
Conserver le moteur partagé de multiplicité et de capture sans modification.
Réutiliser son découpage syntaxique seulement là où ses règles conviennent.

Cette séparation évite de changer silencieusement le sens de `Value`, de
`join` ou des frontières des autres contrôles de reprise. Le nouveau module
ne crée aucun import scientifique, dépendance externe ou hypothèse Lean.

Le nouveau domaine s'applique dès la factory `bridge`, avec deux paramètres
symboliques distincts pour `input` et `master`. Ne pas convertir après coup
un record abstrait dont l'ancien domaine aurait déjà effacé les origines des
captures. Les autres champs sont identifiés mais leurs fermetures réduites
ne sont pas exécutées par cette analyse des deux champs riches.

### 5.2. Domaine abstrait : des origines structurées, pas une contamination

Représenter explicitement :

- les paramètres d'entrée et les captures, avec des identités distinctes ;
- les fermetures, leur cible, leur arité et leurs arguments fixés ;
- les objets et leurs champs, avec leur constructeur ;
- le résultat `R` d'un appel identifié à `sourcePerform` et ses chemins de
  projection, par exemple `R.1`, `R.2.productions`, `R.2.message` ;
- une valeur étrangère, une constante et une valeur non résolue, sans les
  confondre avec une origine riche établie.

Chaque valeur suivie possède une expression d'origine normalisée : paramètre,
résultat d'appel identifié, projection de champ ou construction dont les
champs portent eux-mêmes de telles expressions. La validation finale compare
cette expression à la forme attendue ; elle ne cherche pas seulement une
étiquette présente quelque part dans son arbre. Une valeur étrangère ou
inconnue est absorbante pour l'exactitude du champ qui la contient, jamais
convertie en origine riche par une jonction ou une égalité de valeurs.

L'origine de `R` est liée à l'appel effectif et à ses arguments, pas au nom
d'une variable ni à une égalité prouvée après coup. Deux appels produisent
deux origines ; leurs champs ne deviennent pas interchangeables parce que
les sorties sont prouvées égales.

La reconnaissance d'une reconstruction transparente est structurelle :
même constructeur runtime épinglé, tous les champs runtime requis, mêmes
projections correspondantes du même `R`, aucun champ supplémentaire ni champ
scalaire oublié. Le retour direct de `R.2` et la reconstruction complète de
la représentation runtime épinglée de `R.2` sont les deux formes normales
admises pour l'événement. Une seule étiquette riche présente dans le record
n'est jamais suffisante.

### 5.3. Exécuter symboliquement le bon périmètre

1. Résoudre le vrai `bridge` et son artefact propriétaire, puis son record
   retourné, pas un observateur supplémentaire laissé intact.
2. Extraire les fermetures des champs riches et leurs captures réelles.
   Vérifier leur saturation avec les deux arguments de l'interface.
3. Suivre auxiliaires, alias, fermetures statiques et applications indirectes
   résolues. Ne pas imposer l'écriture d'une lambda particulière.
4. À l'appel riche exact, créer `R` et vérifier l'identité de tous les
   arguments compilés attendus, y compris les indices conservés à l'exécution.
5. Propager les projections et les constructions jusqu'à chaque `return`.
6. Vérifier l'origine du retour et le nombre d'appels sur chaque chemin.

L'opération riche constitue une frontière **nommée, possédée et explicitée**,
pas une exemption accordée à tout auxiliaire contenant un nom ressemblant.
Ses définitions et ses lois restent celles examinées dans ce lot. L'analyse
du pont ne suffit pas à certifier une réécriture ultérieure de l'interpréteur
lui-même ; une telle réécriture demanderait sa propre vérification.

### 5.4. Conditions de justesse de cette analyse

- **Branches :** explorer toutes les alternatives pertinentes. Accepter un
  retour seulement si chaque alternative vérifiée respecte la propriété ;
  ne pas réunir un bon et un mauvais résultat en une étiquette commune.
- **Alias :** représenter les objets mutables du C par des identités de tas
  abstraites. Une écriture par un alias modifie tous les accès au même objet.
  Copier indépendamment un record à chaque affectation serait incorrect.
- **Mises à jour :** modéliser `lean_ctor_set`, `lean_closure_set` et toute
  mise à jour effectivement rencontrée. Une mutation d'un objet marqué comme
  projection riche ne doit pas conserver aveuglément son ancienne origine.
- **Appels :** un auxiliaire qui ne rappelle pas `sourcePerform` peut néanmoins
  transporter son résultat reçu en argument. Il faut donc suivre ce retour,
  pas classer l'auxiliaire comme inutile à partir du seul graphe d'appels.
- **Calcul étranger :** suivre ou résumer conservativement le calcul projeté.
  Un résumé ne peut ni lui attribuer une origine riche ni ignorer un appel,
  une capture ou un effet susceptible d'altérer un objet suivi. À défaut de
  résumé justifié dans ce fragment, refuser explicitement l'analyse.
- **Runtime Lean :** les incréments et décréments de références connus ne
  créent pas d'origine ; les allocations, lectures, écritures et applications
  ont des règles distinctes. Ne pas traiter tout `lean_*` comme une identité.
- **Mémoïsation :** commencer sans cache interprocédural dans ce périmètre
  borné. Une éventuelle optimisation ultérieure devra inclure origines,
  champs, captures et état pertinent du tas dans une clé correcte. Ne pas
  réutiliser les clés actuelles fondées seulement sur `retained()`.
- **Cycles et limites :** refuser les cycles auxiliaires, boucles ou limites
  d'analyse non résolus ; aucun élargissement ne doit créer une origine exacte.
- **Identité des symboles :** conserver les contrôles de propriétaire, refuser
  une définition ambiguë dans le périmètre sensible et résoudre les objets
  statiques. Un prototype ou un suffixe de nom ne suffit pas.
- **Formes C :** casts autorisés, tags, champs scalaires et arités sont
  explicitement contrôlés. Un cast ou une forme non prise en charge n'autorise
  pas à effacer les différences entre deux origines.

Le premier jalon technique doit traiter le C canonique et le C de C2e avec
ces règles. Si cela échoue, corriger l'analyse ou signaler l'obligation
ouverte ; ne pas réduire la correction à une interdiction du nom choisi
dans C2e.

### 5.5. Conserver les autres gardes et préciser leurs messages

Maintenir les contrôles existants d'absence du runtime dans l'interpréteur
riche, de lecture effective du support, de multiplicité et d'absence de
production supplémentaire. Ils ne deviennent pas inutiles avec cette analyse.

Le côté réduit du pont peut toujours appeler légitimement `executeInput`.
Ne pas lui appliquer les contraintes du côté riche.

Remplacer le succès excessif « no projected responder » par un succès qui
indique ce qui a été vérifié : champ sélectionné, origine attendue du retour,
arguments de l'appel, chemins analysés et borne d'applications `[1,1]`.
Conserver un préfixe d'échec compatible `AGENT_BRIDGE_FAILED: sourceEvent:`
ou `sourceNext:`, suivi du chemin de champ fautif et de l'origine trouvée.

Pour C2e, le diagnostic doit porter sur le message projeté retourné, non
sur le nom de son auxiliaire, une preuve devenue introuvable, un avertissement
ou une limite de temps.

## 6. Fichiers et périmètre de modification

| Fichier | Intervention prévue |
| --- | --- |
| `scripts/agent_codegen_provenance.py` | Nouveau domaine d'origine et analyse bornée des retours |
| `scripts/check-agent-codegen.py` | Raccorder cette analyse aux vrais champs du pont ; conserver les autres contrôles |
| `scripts/test-agent-codegen-provenance.py` | Autotests positifs et négatifs de l'analyse, exécutés par le contrôleur normal |
| `Tests/AllConstantsAudit.lean` | Étendre l'outillage de schémas utilisé pour les reconstructions : `Event`, `Source`, type du résultat produit et effacement ; conserver l'audit final unique |
| `scripts/test-agent-contract-links-v2.py` | Nouveau protocole version 2, avec C2e et un contrôle positif de reconstruction exacte |
| `scripts/test-agent-contract-links.py` | Conserver la version 1 byte-identique comme protocole historique reproductible ; ne plus la présenter comme fermeture de C2e |
| Documents canoniques français et anglais de l'agent | Décrire la propriété réellement contrôlée et ses frontières |
| Ancien plan des trois raccords | Ajouter une note datée sur C2e et l'état du nouveau lot, sans réécrire les anciens résultats |

Le nom définitif des nouveaux modules peut être ajusté avant le gel ; leurs
responsabilités ne doivent pas être fusionnées avec le code scientifique.

Par défaut, **aucun fichier Lean de production ne change**, notamment
`State`, `Execution`, `Agreement`, `Persistence`, `PublicInstance` et les
fondations. Les deux verifiers appellent déjà le même contrôleur : conserver
ces routes, et vérifier qu'un échec nouveau est bien propagé par chacune.
Ne les modifier que si un raccord effectif le nécessite.

Ne pas ajouter une lecture, un champ de mémoire, une hypothèse client ou
une seconde décision pour rendre le contrôle plus facile. Si une modification
scientifique paraît nécessaire, arrêter ce lot pour l'expliquer et réviser
explicitement le plan avant de toucher au producteur concerné.

### Ordre d'implémentation

1. Enregistrer l'état de départ et les empreintes des fichiers protégés ;
   préparer les espaces de travail et d'évidence extérieurs.
2. Vérifier les schémas et construire le domaine d'origine avec les autotests
   de projection, reconstruction, alias et arguments distincts.
3. Analyser la factory puis les deux fermetures réelles. Obtenir l'acceptation
   du C canonique et le rejet motivé de C2e, sans changer les producteurs Lean.
4. Raccorder l'analyse au contrôleur normal et conserver tous ses contrôles
   antérieurs ; compléter les cas positifs et négatifs de la matrice.
5. Préparer et figer la campagne version 2 ; exécuter ses neuf cas dans les
   copies indépendantes, puis toute la validation finale de non-régression.
6. Consigner les résultats effectifs et corriger la documentation bilingue.
   Contrôler le diff final ; toute modification ultérieure du code testé
   impose une nouvelle validation de cet état, pas la reprise des anciens logs.

Ne pas passer du jalon 3 à une annonce de clôture : l'acceptation des formes
légitimes, l'intégration aux deux routes et la conservation font partie du lot.

## 7. Matrice des vérifications du contrôleur

Ces contrôles rapides portent sur le fragment C analysé. Ils complètent,
mais ne remplacent pas, les mutations compilées de la section suivante.

| Cas | Attendu | Ce qui doit être établi |
| --- | --- | --- |
| Projections canoniques des deux champs | Accepter | Retours `R.1` et `R.2`, arguments et captures corrects |
| Auxiliaires de projection et alias | Accepter | Même origine après plusieurs appels résolus |
| Fermeture statique et fermeture capturée | Accepter | Arguments fixés puis arguments de l'interface effectivement transmis |
| Reconstruction exacte de `Event` | Accepter | Ses deux champs viennent du même `R.2` |
| Branches ayant chacune un retour riche exact | Accepter | Propriété vérifiée dans toutes les alternatives |
| Runtime seulement dans les champs réduits | Accepter | Absence de confusion entre les deux côtés |
| Appel riche inutilisé, retour runtime | Rejeter | Le compteur seul ne suffit pas |
| Productions riches, message projeté, même via un auxiliaire | Rejeter | Origine incorrecte de `return.message` |
| Message riche, productions étrangères | Rejeter | Origine incorrecte de `return.productions` |
| Une branche riche, une branche projetée | Rejeter | Aucun `join` permissif |
| Champs issus de deux appels riches distincts | Rejeter | Identité d'origine et multiplicité |
| Bonne fonction, mauvaise source ou mauvaise demande | Rejeter | Arguments distingués, pas seulement callee identifié |
| Résultat ou sous-champ réécrit à travers un alias | Rejeter | Mise à jour du tas réellement suivie |
| Échange de champs, constructeur ou schéma altéré | Rejeter | Correspondance source/C vérifiée avant les indices |
| Fermeture capturant un ancien résultat au lieu de l'opération courante | Rejeter | Origine propre à cette invocation |
| Chemin sans appel, double appel caché | Rejeter | Bornes par chemin conservées |
| Appel indirect, objet global ou expression nécessaires non résolus | Rejeter explicitement | Aucun succès à partir d'une valeur inconnue |
| Faux symbole ressemblant au producteur | Rejeter | Résolution exacte et artefact propriétaire |

Inclure un test où l'appel auxiliaire reçoit le résultat riche en argument
sans rappeler le producteur : ce cas protège précisément contre le raccourci
« pas de nouveau producteur dans le graphe, donc pas de donnée pertinente ».

Les anciens autotests de partage, de dispatch, de limites `[1,1]` et de
sélection du record restent exécutés. Un succès des nouveaux cas ne doit pas
masquer un échec dans les contrôles antérieurs.

## 8. Campagne compilée version 2

### 8.1. Versionner avant le run confirmatoire

Créer `test-agent-contract-links-v2.py` et laisser
`test-agent-contract-links.py` byte-identique. Les documents canoniques et
la validation courante appellent explicitement v2. La version 1 reste
reproductible avec son propre fichier, son commit et ses empreintes ; elle
n'est ni remplacée, ni réinterprétée, ni utilisée pour affirmer la fermeture
de C2e.

Avant le run final, figer le script, toutes les transformations, leurs
attentes et diagnostics, les sources et les paramètres. Enregistrer leurs
SHA-256, le commit et l'arbre, la toolchain, Python, l'OS et les commandes.
Toute correction après observation produit une nouvelle révision du protocole
et un nouveau répertoire d'exécution, sans écraser l'essai précédent.

### 8.2. Cas obligatoires

Conserver les cinq cas v1 :

1. effacement du contenu d'exactitude C1 : échec de preuve substantiel ;
2. effacement du fait d'absence C3 : échec de preuve substantiel ;
3. remplacement du champ riche par le runtime avec égalités rétablies :
   build réussi, contrôle compilé rejeté ;
4. même remplacement avec observateur riche inutilisé : même rejet ;
5. auxiliaire riche légitime : build et contrôle acceptés.

Ajouter trois cas compilés :

6. **C2e** : productions riches et message projeté pour `inspect` et `propose`,
   avec les égalités et le certificat rétablis constructivement ;
7. même mélange avec le calcul du message caché dans un auxiliaire résolu ;
8. reconstruction légitime de l'événement depuis les deux projections de
   son unique résultat riche ;
9. appel riche conservé, mais successeur reconstruit indépendamment avec la
   même valeur et les égalités rétablies : rejet de la provenance de
   `sourceNext`. Si la construction Lean complète de ce cas révèle une
   impossibilité substantielle due au type de `Source`, consigner cet échec
   de construction et conserver obligatoirement son analogue C dans les
   autotests du contrôleur ; ne pas annoncer qu'un cas non exécuté a réussi.

Pour 6 et 7 : le build complet doit réussir sans avertissement Lean ni axiome,
puis le contrôleur doit rejeter la provenance du message. Pour 8 : tout doit
réussir. Pour 9, si la variante est constructible, elle doit compiler avant le
rejet d'origine. Une mutation qui ne compile pas n'a pas testé la nouvelle
protection.

Reconstituer ces variantes dans le vocabulaire local et les espaces de test.
Les matériaux bruts de l'audit restent hors dépôt ; leur projet ne devient
pas une dépendance scientifique ou technique.

### 8.3. Isolation et rejet valide

- Préserver une empreinte complète des sources de référence avant/après.
- Préparer les patches avant le run, dans un répertoire neuf extérieur.
- Utiliser des copies jetables détachées et des artefacts physiquement
  indépendants ; aucun cache scientifique partagé modifiable.
- Restaurer et revalider le témoin canonique entre les variantes ; ne pas
  cumuler des mutations ou récupérer du C d'un cas antérieur.
- Rejouer C2e à travers **`verify.sh` et `verify.ps1`**, en plus du contrôleur
  direct. Exiger le même rejet d'origine dans les deux routes.
- Séparer erreur de protocole, erreur Lean et rejet attendu du contrôleur.
  Un timeout, un parseur cassé avant le site pertinent, un nom absent, un
  import manquant ou un lint ne compte pas comme fermeture de C2e.
- Ne pas rejeter une variante parce que tout son fichier a changé d'empreinte :
  cela éviterait de vérifier la provenance au lieu de la vérifier.

## 9. Non-régression et validation finale

### 9.1. Conservation scientifique

Comparer au commit scientifique `8e56638bfeae56de64ef766b6030de16bb43ca1c` :

- toutes les sources Lean de production et les quatre fondations doivent
  rester byte-identiques ; aucune déclaration ni hypothèse n'est remplacée ;
- C1 garde le suivi des références de chaque nœud et des vrais suffixes ;
- C3 garde les faits précis de refus consommés depuis les mêmes témoins ;
- les accords riches locaux et finis, la reprise sans archive, l'oubli
  démontré et les constructions publiques restent inchangés ;
- le calcul antérieur, les largeurs `2^n` et partielles, les autorisations de
  regroupement et les lois des transports ne changent pas ;
- licence, toolchain, manifeste, figures et documents scientifiques hors du
  périmètre documentaire annoncé restent inchangés.

La modification éventuelle du seul outillage Lean de schémas est listée et
revue séparément ; elle n'est pas présentée comme une modification de la
fondation ou une nouvelle preuve du phénomène.

### 9.2. Séquence à exécuter sur le lot terminé

```text
lake clean
lake build +RelationalPerimeter
lake build
python -B scripts/check-unified-codegen.py
python -B scripts/check-agent-codegen.py
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
python -B scripts/test-agent-contract-links-v2.py --output <nouveau répertoire extérieur>
python -B scripts/test-expected-failure-gates.py --output <autre répertoire neuf extérieur>
git diff --check
lake update
```

Ce sont des commandes du futur protocole, pas des exécutions déjà réussies.
Le protocole figera les chemins absolus des exécutables et des répertoires
de sortie. Un environnement manquant est déclaré non exécuté, pas validé.

Exiger ensuite :

- zéro avertissement Lean, zéro trou et zéro dépendance axiomatique manuscrite ;
- exactement un bloc d'audit final par fichier Lean et aucun terme interdit ;
- inventaire exhaustif, stratification et absence d'orphelins inchangés ;
- conservation des fixtures, diagnostics exacts, contrôles d'artefacts et
  résultats de la suite complète des deux wrappers ;
- nouveaux autotests effectivement appelés par le contrôleur des deux routes ;
- liens locaux valides et documentation française/anglaise cohérente ;
- `lake-manifest.json` byte-identique après `lake update` ;
- association des résultats au hash des sources, contrôleurs et artefacts C
  effectivement utilisés, sans modification pendant le run confirmatoire.

Les 181 fichiers Lean et les 26 fixtures à 28 sites étaient les nombres de
l'état audité. Recalculer l'inventaire final au lieu de reprendre ces chiffres
par habitude ; expliquer toute différence.

## 10. Documentation, fermeture et livraison

### 10.1. Documentation exacte

Les versions française et anglaise doivent distinguer :

1. l'accord sémantique riche/runtime, démontré constructivement et composé
   sur toutes les suites finies ;
2. le contrôle d'origine du retour des champs sélectionnés, sur le fragment
   compilé annoncé ;
3. les autres contrôles du producteur, du support, des artefacts et des
   fixtures, qui restent nécessaires séparément.

Décrire la version 2 et le contre-exemple qu'elle rejette. Ne pas annoncer
une protection contre tout programme C ou Lean arbitraire, une preuve de
coût total, ni un nouveau verdict indépendant avant de l'avoir reçu.

### 10.2. Jalons de fermeture

- [x] **G1 — Origine :** le C canonique est accepté et C2e est rejeté parce
  que son message ne vient pas du résultat riche suivi.
- [x] **G2 — Complétude du retour :** successeur, événement entier, captures,
  arguments, champs et branches sont contrôlés ; pas seulement un sous-champ.
- [x] **G3 — Formes légitimes :** auxiliaires, fermetures et reconstruction
  exacte passent sans imposer une syntaxe scientifique particulière.
- [x] **G4 — Campagne :** les neuf cas prévus donnent les résultats figés ou
  le statut explicitement autorisé du cas 9 ; tous ses analogues C passent,
  et les deux verifiers rejettent C2e au bon endroit.
- [x] **G5 — Conservation :** production Lean inchangée, C1/C3 et toutes les
  suites antérieures conservées, manifeste et sources de référence intacts.
- [x] **G6 — Portée :** messages et documents décrivent exactement l'analyse
  réalisée, ses frontières et ses cas non pris en charge.
- [x] **G7 — Reproductibilité :** empreintes, commandes, patches et journaux
  sont associés au même état final, avec les limites de plateforme explicites.

La correction n'est déclarée localement terminée que lorsque ces sept jalons
sont documentés par leurs résultats effectifs. Si l'analyse ne permet pas de
fermer un jalon sans affaiblir la cible ou la méthode, le signaler comme
obligation ouverte ; ne pas remplacer la propriété par une recherche de noms
ou une égalité de sorties.

### 10.2.1. Résultats locaux de l'implémentation

L'analyse reconstruite suit le vrai record retourné par `bridge`, sélectionne
les fermetures réellement installées, puis interprète leurs chemins C jusqu'au
retour. Elle exige exactement le successeur et l'événement produits par le même
appel à `sourcePerform`, avec les captures et arguments attendus. Une
reconstruction locale de `Event` n'est transparente que si ses deux champs
proviennent, dans le bon ordre, du même événement riche. Les branches
d'allocation générées par Lean sont corrélées ; tout chemin sensible inconnu,
toute mutation du résultat riche et toute origine concurrente échouent fermés.

Les résultats exécutés sont :

| Contrôle | Résultat |
| --- | --- |
| Autotests unitaires d'origine | Succès : retour direct, reconstruction exacte, alias, auxiliaire statique, branches d'allocation, captures et deux champs riches ; toutes les substitutions prévues sont rejetées. |
| Contrôleur canonique | Succès : `sourceNext` et `sourceEvent` ont chacun une origine exacte dans le retour de `sourcePerform`, avec arguments préservés. |
| Builds propres | `lake build +RelationalPerimeter` : 160 tâches ; `lake build` : 183 tâches ; zéro avertissement. |
| Constructivité exhaustive | 18 333 constantes, 360 exceptions générées par le compilateur, zéro dépendance axiomatique manuscrite. |
| Verifiers complets | Git Bash et PowerShell réussissent sur les mêmes 181 fichiers Lean, 159 modules de production et 26 fixtures ; aucun orphelin. |
| Matrice des wrappers | 68 résultats attendus sur les deux surfaces, tous conformes. |
| Campagne C2 v2 | Neuf cas conformes ; C2e direct et caché sont rejetés sur `sourceEvent`, la reconstruction exacte est acceptée et le successeur indépendant est rejeté sur `sourceNext`. C2e est également rejeté par les deux verifiers complets. |
| Manifeste et diff | `lake update` laisse le SHA-256 du manifeste inchangé (`558a6999b82d0fac6c385da1a5cabeb50a594d6ecc7996f0be33014cfb68afa8`) ; `git diff --check` réussit. |

La première campagne confirmatoire v2, conservée hors dépôt dans
`C:/Users/frederick/c2v2-final-46bddd46`, associe les résultats suivants :

| Matériau | SHA-256 |
| --- | --- |
| Protocole figé v2 | `779b0f6c211a2ca25aa7237aead4edfa64a9f9c1b54130a61b8c49fcc5136a6c` |
| Résultats des neuf cas | `36e3f5a08355fc87a125e7d6b2fc8cf97f66c9dd08f2897fd657244efa6f4513` |
| Journal des commandes | `419ed923473e24b8b4bdc5b94c6609acddf2f59e9464573a06e9e4639da50f0a` |
| Script v1 conservé | `fb48ed7d682fced66a7e6d09d61c77b9e3d589dd747c9fd658fb8d093a97d36d` |
| Script v2 | `b8f2b3dcf32f2f67706131132c9277f881ae72eb888d262e29dc677f74ce652a` |
| Contrôleur raccordé | `12435bc57d0bdc3a62a4e667058a3be7b476f7af5514025d3daa323ca7108b6f` |
| Analyse d'origine | `00076f377475654f1b7383d7fff849a89b3e71736324f3d3f172ca11bf68a960` |
| Autotests d'origine | `eae917bc30d3446a5a3a1e0df4700811b27a237119e5c71d55ba0af64a7cdd48` |

La seconde exécution confirmatoire v2 est conservée hors dépôt dans
`C:/Users/frederick/c2v2-final-tree-20261021-r2`. Son protocole figé inventorie
l'arbre documentaire final, les exécutables effectivement employés et toutes
les empreintes de cette seconde exécution. Elle ne modifie pas la référence.

### 10.3. Livrables et autorisations

Livrer le contrôleur corrigé, ses tests, le protocole v2, les mises à jour
documentaires et un bilan distinguant preuves conservées et contrôles exécutés.
Conserver les logs et extractions bruts hors du dépôt.

Le présent plan est temporaire : le retirer de l'arbre final lors d'une future
PR d'intégration dans `main`, comme les autres documents de chantier concernés.
Les rapports finaux et instructions de reproduction restent des livrables.

La demande ultérieure de l'utilisateur a explicitement autorisé
l'implémentation. Le commit, le push, une nouvelle soumission à Aristotle et la
fusion ne sont ni effectués ni annoncés ici ; ils restent des étapes distinctes.
