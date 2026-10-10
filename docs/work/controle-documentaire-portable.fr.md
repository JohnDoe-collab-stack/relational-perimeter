# Restaurer exactement le contrôle documentaire depuis des octets

**Date :** 10 octobre 2026.

**Branche :** `codex/ai-alignment-under-contract`.

**Candidat scientifique :** `DOCUMENTARY_CONTROL_BYTES`.
Cet incrément de développement prolonge le
[raccord des composants du présent](restauration-present-composants.fr.md),
sur la référence `6575de4a219301cb42c93c842de7814145b013ff`.
Les anciennes preuves et leurs relevés restent sur leurs snapshots propres.

## Ce qui est maintenant fermé

Les données de contrôle d'un présent documentaire peuvent être écrites en octets
et restituées exactement : les spécifications des slots, leurs liaisons aux
occurrences, la file typée restante, le contexte de politique, le compteur et
le dernier résumé. La preuve porte sur toute donnée de contrôle typée du langage
déclaré, avec le stockage reçu fixé et un codec exact du type de contexte.

Elle n'exige ni que les slots soient tous réalisés, ni que leurs sorties
satisfassent leurs buts, ni que les instructions restantes soient admissibles.
Une liaison absente reste absente. Une sortie autorisée mais inadéquate garde
sa référence. Une règle interdite encore en attente revient comme cette même
instruction : son admission sera décidée par l'exécuteur lorsqu'elle sera
proposée à l'effectuation.

Cela ferme la partie du checkpoint qui détermine le travail encore à faire.
À stockage et dossier maître identiques, le contrôle chargé restitue exactement
le présent antérieur. Toute suite finie du langage mémoire produit alors la
même exécution, sa trace positive, ses événements et ses réponses. Le témoin
d'accomplissabilité se transporte également.

La condition sur les autres composants fait partie de cet énoncé : ce codec
ne sérialise ni le stockage documentaire ni le dossier avec son curseur maître.
Le stockage a déjà son codec canonique ; le dossier et le maître doivent encore
être réunis avec le contrôle dans un chargement physique complet.

## Constitution et chargement

Le schéma 4 distingue deux couches. La couche de mots conserve les nombres
signés, les listes, les options, les spécifications, les instructions et les
résumés. La couche physique emploie les véritables octets 0, 1 et 2 du codec
de référence, avec signes et longueurs explicites. L'encodage unaire sert ici
la simplicité de la loi d'aller-retour ; aucun gain de taille n'est revendiqué.

Chaque citation en attente conserve sa demande et les deux positions de ses
sources reçues. Chaque déduction conserve l'occurrence de règle et les deux
ports des slots antérieurs. Le chargeur retrouve ces références dans les
contextes reçus, puis construit la file typée dans son ordre. Sa liste finale
doit être exactement celle reçue par le chargeur.

Les liaisons des slots conservent une option de position dans le stockage.
Le chargeur retrouve cette occurrence précise ; il ne cherche pas une autre
sortie de même valeur, et ne filtre pas les liaisons selon la satisfaction
du but. Deux occurrences de même valeur peuvent donc rester deux liaisons
distinctes. Les absences, les sorties supplémentaires et les erreurs déjà
constatées n'obligent pas à fabriquer un présent favorable.

Le résumé conserve la route prise, les événements et l'inspection éventuelle,
avec sa position, sa valeur et ses origines. Le contexte et le compteur
proviennent du même présent. Un reset autorisé modifie le contexte ; il conserve
la file, les liaisons, le compteur et le résumé.

Les codecs de contexte `Nat` et `List Nat` sont fermés dans le dépôt,
ainsi que la composition par listes, options et produits. L'interface générale
reçoit explicitement un codec du type de contexte et sa loi exacte. Elle
n'annonce pas une sérialisation de toute fonction ou de tout type possible.

Le chargeur vérifie le format, les longueurs, les références et la cohérence
de la file avec sa cible finale. La fidélité démontrée concerne les octets
sauvegardés du présent considéré, dans la même configuration reçue. Les tests
de mutations invalides ne constituent pas une authentification de toute
modification possible d'un fichier.

## Raccord aux preuves et à l'exécution

[DocumentaryControlCodec.lean](../../Tests/LocalAlignment/DocumentaryControlCodec.lean)
construit les codecs et leurs lois avec conservation exacte de la queue de
mots non consommée. `byte_roundtrip` établit le retour depuis les octets.

[DocumentaryPortableControl.lean](../../Tests/LocalAlignment/DocumentaryPortableControl.lean)
consomme ces codecs et résout les références typées :

| Déclaration | Énoncé et données consommées |
| --- | --- |
| `binding_exact`, `bindings_exact` | Retour exact des liaisons, y compris leurs absences |
| `instruction_exact`, `script_exact` | Retour de la demande, des ports et de la file réellement reçus |
| `record_exact`, `byte_roundtrip` | Égalité de la donnée de contrôle entière |
| `present_byte_roundtrip` | Égalité du présent après réunion du contrôle chargé avec le même dossier et le même stockage fournis |
| `loaded_all_futures` | Égalité hétérogène de toute exécution mémoire finie et de sa trace positive depuis ce chargement |
| `loaded_accomplishable` | Transport positif du témoin d'accomplissabilité |

La résolution des références et la reconstruction du contrôle n'exécutent
aucune tâche, recherche maître, extraction ou déduction historique.
Le décodage du contexte est confié au codec explicitement reçu. Le code généré est
contrôlé sur six chemins et leurs dépendances nommées ; six injections de
producteur historique sont refusées. Les fermetures du codec de contexte reçu
et l'initialisation globale du processus restent les frontières explicites
de ce contrôle.

Les [cas Lean](../../Tests/LocalAlignment/DocumentaryPortableControlCases.lean)
instancient les lois sur le préfixe réel, son reset, le démarrage, des sorties
inadéquates et le présent bloqué. Les trois modules portent 93 déclarations
sélectionnées dans leurs blocs d'audit.

## Vérification physique du composant

Le smoke emploie les huit régimes de propositions déjà déclarés, avec et sans
reset du contexte à chaque tour. Il ajoute deux resets après le préfixe.
Dix-huit exécutions effectives sauvegardent leur stockage et leur contrôle ;
dix-huit nouveaux processus rechargent ces deux composants. Les octets sont
comparés à des oracles littéraux indépendants des codecs Lean.

La file chargée contient encore une nouvelle citation puis une somme dépendante.
Le processus de chargement ne reçoit pas un curseur maître restauré et
n'effectue pas cette citation. Un cas distinct charge les octets de contrôle
avec le dossier maître réel et le stockage réel encore fournis, puis exécute
ces futurs : la file s'achève au tour cinq, la conclusion vaut deux et porte
les origines `[1, 2, 1, 2]`. Il contrôle aussi les liaisons absentes du présent
bloqué, la conservation de sorties inadéquates et les ports distincts des
citations de même valeur.

Vingt fichiers invalides sont refusés avant toute écriture de résultat :
versions ou schémas inconnus, longueurs incohérentes, références manquantes,
nombres naturels négatifs, cible finale altérée, tags inconnus, troncature
et données supplémentaires. Au total, le smoke lance 57 processus. Aucun appel
au modèle local n'est effectué.

```text
lake build Tests.LocalAlignment.DocumentaryPortableControlCases
python -B scripts/check-documentary-control-codegen.py
python -B scripts/run-documentary-control-smoke.py
```

La vérification complète de cet incrément est passée : 277 fichiers Lean,
24 301 constantes auditées dans 276 modules, aucune exception écrite et les
23 fixtures historiques de rejet conformes. Le
[relevé de vérification](controle-documentaire-portable-verification.json)
conserve les empreintes des sources et du journal brut, ainsi que les conditions
des contrôles. Cet incrément reste en développement sur la branche ; ces
résultats ne constituent ni une nouvelle expérience confirmatoire ni un audit
indépendant.

## Prochaine obligation du lot 6

Le contrôle, le stockage canonique et la mémoire des citations ont maintenant
leurs codecs de composant. Le maître conserve encore des valeurs et des
producteurs de rang supérieur sans représentation portable fermée.

Il reste à encoder fidèlement les ressources et formations maître, à réunir
les composants dans un seul présent chargé sous sa configuration identifiée,
puis à réaliser de nouvelles citations et déductions dans un nouveau processus
depuis ce présent complet. Les lois de contrôle et de présent typé sont prêtes
à consommer l'égalité exacte de cette restauration. Le lot 6 demeure ouvert
sur cette reprise complète et sur l'interface documentaire du modèle local.
