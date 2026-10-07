# Signatures exactes de continuation : rôles et contrat complet de l’agent

Une source peut rester historiquement distincte d’une autre tout en donnant
les mêmes réponses pour un contrat futur déterminé. Cet ajout calcule les
distinctions à conserver pour un contrat de lecture explicite. Il construit
aussi une source dont la différence doit rester visible, et une continuation
qui la distingue.

Le résultat porte sur les distinctions comportementales, pas sur un minimum
d’octets ou un coût polynomial. Le volet quantique et la preuve du coût total
ne sont pas établis par ces modules.

## Contrat fixé indépendamment de la signature

`FutureContract` spécifie la transition, l’événement, la lecture, les témoins
d’admission et une décision constructive d’admission ou de refus. `Outcome`
enregistre les lectures, les événements et les possibilités d’admission sur
toute suite finie, y compris la lecture finale. Le contrat spécifie également
la transition totale utilisée en cas de refus.

`FutureEquivalent` signifie l’égalité de ces résultats sur **toutes** les suites
finies. Sa définition ne mentionne pas la signature. Elle compare les
possibilités d’admission, non une identité automatique de leurs témoins.
Lorsqu’une réalisation doit transporter les témoins eux-mêmes,
`ExactRealization` exige les deux fonctions de transport et leurs lois de retour.

Une `FiniteFutureBasis` contient des suites réellement testées et une preuve
que leur accord implique l’accord sur tous les futurs. L’interface générique
est conditionnelle : elle ne promet pas de trouver une base finie pour tout
contrat. Dans l’instance de lecture ci-dessous, la base est construite et sa
complétude est démontrée.

Le noyau prouve :

- `signature_exact` : même signature exactement lorsque tous les futurs
  autorisés par le contrat sont indiscernables ;
- `separate` : une différence produit une suite concrète et une preuve que
  ses réponses diffèrent ;
- `minimal_distinctions` : toute réalisation exacte conserve ces distinctions ;
- `recoverSignature_exact` : la signature se récupère depuis toute réalisation
  exacte munie d’une couverture positive de son domaine de mémoire ;
- `SignatureDynamics.run_exact` : une mise à jour construite avec son accord
  de transition reste exacte sur toutes les suites finies.

La couverture utilisée dans la preuve de factorisation n’est pas une archive
des sources dans la mémoire runtime. La congruence comportementale seule
n’est pas présentée comme un algorithme gratuit de mise à jour.

## Sources effectivement constituées

`AcceptedRoleSource role` contient une occurrence constituée du rôle réel, son
payload dépendant et sa preuve d’acceptation. Le rôle provient de l’exécution
existante. `producedOutput` applique `interpretRoleStageAtom` avec l’accord de
formation de cette occurrence. La préservation de l’acceptation est une preuve
séparée, consommée par le producteur de cible acceptée.

Trois sources sont construites :

1. Le payload gauche accepté de l’exécution.
2. Le payload droit obtenu en appliquant l’action réelle à ce payload gauche.
3. Un payload gauche variant sur une variable calculée depuis la formule et
   les décisions déjà présentes, puis son output effectivement produit.

La variable choisie est démontrée absente de la formule et des décisions ; la
variante est donc acceptée positivement. Les deux premières sources ont des
occurrences distinctes et le même output. La troisième est distinguée par la
lecture de cette variable.

## Portée exacte de la nouvelle réalisation

Pour un rôle et une variable de lecture reçue avant la classification,
`roleReadContract` promet uniquement des lectures répétées de l’output produit
à cette variable. Ses transitions sont identitaires, ses admissions ont un
témoin unitaire et son domaine est fermé sous toutes ses demandes.

Sa base complète est la lecture initiale : toutes les lectures ultérieures
répètent cette valeur. La mémoire réduite est un booléen. Les transports des
témoins d’admission sont construits et satisfont leurs deux lois de retour.

Les producteurs suivent cet ordre dans un support typé :

```text
source acceptée + variable de lecture
  -> action réelle et cible acceptée
  -> évaluation de la base indépendante
  -> signature finie
```

`localCertificate` ferme l’exactitude, le regroupement de deux sources
distinctes, le séparateur positif et la nécessité de la distinction restante
pour toute autre réalisation exacte du même contrat.

`resources_change_partition` compare le **même domaine de sources** sous deux
ressources de lecture : à la variable sélectionnée, les sources gauche et
variante s’accordent ; à la variable libre construite, elles se distinguent.
Les ressources sont des variables à lire, pas une partition ou un masque de
regroupement. Elles restent des paramètres reçus du contrat : ce théorème
n’est pas une recherche autonome d’un contrat optimal.

## Composition et exécution

`AcceptedRoleHistory` compose ces sources dans l’histoire dépendante des rôles.
`produceHistoryReadings` produit un vecteur de lectures pour un nombre arbitraire
de rôles. Le contrat composé promet des lectures répétées de ce vecteur ; sa
base et sa réalisation sont fermées sur tout ce domaine.

`executeSigned` produit la signature de la tête avant son appel récursif sur
la suite. Son effacement redonne exactement `MasterResources.execute`.
La tête est indépendante de la longueur future, et les lectures sont celles
des sources attachées aux rôles de **la même exécution**.

La signature est ici un consommateur des outputs réels. Elle ne remplace pas
la graine qui commande la recherche suivante et n’est pas présentée comme
une découverte nouvelle de la décomposition de l’agent.

`publicSignatureMemory` exécute le consommateur data-only `executeReadings`.
Sa sortie ne possède que le type `List Bool`, sans champ d’histoire, de support,
de payload source ou de curseur. Son égalité avec les lectures de l’exécution
riche est prouvée. `publicSignatureCertificate` conserve séparément le témoin
scientifique épinglé et les accords de tête et d’horizon.

Le code compilé de la signature locale ne dépend pas d’une image de profils.
Le maître réutilisé construit toujours son image **locale à deux occurrences**.
Le contrôle des dépendances nommées ne trouve pas d’énumération globale des
profils sur ce chemin. Il ne certifie pas les callbacks arbitraires d’un client,
le ramasse-miettes ou la mémoire transitoire physique.

## Signatures de tous les états atteignables de l’agent

`ExistingAgent.initialSignature_exact` réemploie le résultat antérieur sur les
profils initiaux d’un maître et d’une exigence fixés. Leur signature initiale
est unitaire parce que leurs exécutions futures existantes sont déjà égales.
La mémoire, les droits, les registres et l’interprète de l’agent ne sont pas
remplacés par `Unit`.

`ReachableAgent` ferme séparément le contrat complet sur tous les états
atteignables, à maître et exigence reçue fixés. Il réemploie les vraies demandes
`advance`, `inspect`, `obtain` et `propose`, leurs événements, leurs refus et
leurs admissions positives. Les témoins d’admission sont transportés avec les
deux lois de retour ; aucune observation de l’agent n’est retirée.

La signature est le nombre de productions déjà exécutées. Deux sources ont
la même signature si et seulement si toutes leurs continuations donnent les
mêmes lectures, événements et possibilités d’admission. La preuve ne pose pas
cette équivalence : l’égalité de lecture du contrat existant permet de retrouver
le nombre de productions grâce à la longueur du registre et au périmètre reçu
non vide. Ce nombre détermine ensuite la mémoire effective pour ce maître et
cette exigence. La base composée de la seule lecture initiale est donc complète
sur ce domaine fermé, pour toutes les suites de demandes, sans horizon borné.

Tous les nombres de productions sont positivement atteignables. Deux nombres
différents produisent un séparateur ; toute réalisation exacte doit conserver
cette distinction. `update_exact` et `dynamics_exact` ferment les mises à jour
sur une demande et sur une suite arbitraire. `executeSignedInput` obtient sa
signature depuis le résultat de la véritable production de l’agent ; son
effacement redonne cette production.

`countRealization` réalise également ce contrat avec un état dynamique de type
`ULift Nat`, avec couverture positive et lois de retour des droits. Son
interprète **reconstruit** les réponses depuis le maître, l’exigence et le
nombre de productions, par le moteur runtime existant. Il ne garde pas
l’archive personnelle du profil dans cet état, mais cette reconstruction a
un coût réel : elle ne prouve ni un temps constant ni un minimum d’octets pour
le programme complet et ses ressources initiales. La mémoire et l’interprète
de l’agent existant n’ont pas été modifiés.

`no_singleton_realization` prouve qu’un état `Unit` ne peut pas réaliser ce
contrat complet : les lectures distinguent déjà zéro production d’une production.
`recoverCount_exact` construit la factorisation par toute autre réalisation
exacte avec couverture positive. `publicCertificate` ferme ces garanties sur
le maître public et une exigence singleton réellement reçue, sans hypothèse
scientifique ouverte.

## Coût : limite restante

`CostModel` compte les lectures, décisions, événements et transitions à la
frontière de l’API du contrat. L’effacement et les comptes non nuls sont
prouvés. Le coût interne de ces primitives, la recherche, la construction des
ressources, les allocations et l’arithmétique ne sont pas couverts par cette
comptabilité. Aucun théorème de coût total n’en est déduit.

## Points d’entrée et vérification

- [Certificat et mémoire publics](../RelationalPerimeter/Agents/ContinuationSignatures/PublicCertificate.lean).
- [Exécution fusionnée et consommateur data-only](../RelationalPerimeter/Agents/ContinuationSignatures/FusedExecution.lean).
- [Contrat indépendant](../RelationalPerimeter/Constitution/Continuation/Behavior.lean).
- [Minimalité et transports](../RelationalPerimeter/Constitution/Continuation/Minimality.lean).
- [Balayage complet du lot](../Tests/ContinuationSignatureAxiomCoverage.lean).
- [Signatures et réalisation du contrat complet de l’agent](../RelationalPerimeter/Agents/ContinuationSignatures/ReachableAgent.lean).
- [Vérifications clientes du raccord complet](../Tests/ContinuationSignatureReachableAgent.lean).

```text
lake build +Tests.ContinuationSignatureAxiomCoverage
python scripts/check-continuation-signature-codegen.py
```

Les petits `#eval` sont des smoke tests, non des mesures confirmatoires de coût.
La vérification globale du dépôt reste distincte du balayage de ce lot.

Voir aussi la [version anglaise](continuation-signatures.en.md).
