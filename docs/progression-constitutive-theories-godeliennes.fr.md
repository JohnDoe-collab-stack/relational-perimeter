# Progression constitutive des théories et obstructions gödeliennes

## Portée et statut

Ce développement construit une progression finie de théories arithmétiques à
partir d’histoires positives. À chaque étage, il produit un énoncé gödelien
propre au régime de preuve courant, certifie sa vérité et sa non-prouvabilité,
ajoute exactement cet énoncé comme nouvelle occurrence, puis exécute une
nouvelle production gödelienne dans le régime étendu.

Le résultat raccorde deux transformations sans les identifier : le changement
de théorie modifie le type des preuves disponibles, tandis que le changement
de représentation détermine où les distinctions d’un étage doivent être
conservées entre mémoire, futurs et readouts.

## Histoires certifiées

Une `TheoryHistory` est une histoire finie enracinée dans l’arithmétique
standard. Une extension ne reçoit pas une totalité extensive d’axiomes. Elle
ajoute une occurrence de phrase à l’histoire déjà constituée.

`SoundTheoryHistory` certifie positivement chaque étape :

```text
histoire source certifiée
  + témoin de vérité de la phrase ajoutée
  → histoire étendue certifiée
```

La correction d’un axiome historique suit son témoin d’occurrence. La
correction d’une dérivation suit récursivement sa construction. Un certificat
de preuve vérifié pour une histoire se décode en dérivation typée, et une
dérivation typée se réencode en certificat vérifié pour la même histoire.

## Production gödelienne à un étage arbitraire

Toute histoire finie ainsi certifiée détermine un système gödelien effectif.
Son vérificateur de preuves reçoit le code de cette histoire. Son prédicat de
non-prouvabilité et sa preuve diagonale sont construits pour ce même régime.

L’exécution canonique de l’étage `T` produit une phrase `G_T` et deux témoins :

```text
Truth(G_T)
Proof_T(G_T) → Empty
```

La racine réutilise le vérificateur, le prédicat de non-prouvabilité et
l’expression diagonale publiés pour l’instance HA existante. Cette compatibilité
n’en remplace pas les déclarations publiques.

## Une étape exécutée

`executeGodelTheoryProgression` construit une étape unique :

```text
T
  → production exécutée de G_T
  → T⁺ = T + {G_T}
  → preuve de G_T dans T⁺
  → production exécutée de G_T⁺ dans T⁺
```

La provenance est conservée dans le type et dans des égalités exactes :

- l’exécution source est l’exécution canonique de l’histoire source
- l’histoire cible ajoute la phrase de cette exécution, sans phrase substituée
- sa certification consomme le témoin vrai de la même exécution
- la preuve cible provient de l’occurrence `newest` de cette phrase
- l’exécution cible est l’exécution canonique de l’histoire certifiée obtenue

Le résultat central d’une étape est :

```text
(Proof_T(G_T) → Empty) × Proof_T⁺(G_T)
```

Il n’y a pas de contradiction. Les deux composants portent sur deux familles
de preuves différentes. Le développement construit également :

```text
Truth(G_T) → Proof_T⁺(G_T)
Proof_T(φ) → Proof_T⁺(φ)
Truth(G_T⁺)
Proof_T⁺(G_T⁺) → Empty
```

La première conversion ne fabrique pas la preuve cible à partir de son
argument de vérité. Le témoin `Truth(G_T)` a déjà été consommé pour certifier
la correction de l'extension, et `Proof_T⁺(G_T)` est construit séparément par
l'occurrence exacte ajoutée à l'histoire. La fonction expose ensuite leur
composition disponible au nouvel étage sans confondre ces deux productions.

Le transport des anciennes preuves est exécuté par la chaîne complète :

```text
certificat source
  → dérivation source décodée
  → transport des axiomes vers l’extension
  → certificat cible réencodé
```

## Nouvelle phrase et irréversibilité

La nouvelle production n’est pas une copie de l’ancienne. Le dépôt démontre :

```text
G_T ≠ G_T⁺
```

Si les deux phrases étaient égales, la preuve déjà construite de `G_T` dans
`T⁺` deviendrait une preuve de `G_T⁺` dans `T⁺`, contrairement au nouveau
certificat de non-prouvabilité.

Le transport général en sens inverse est lui aussi rejeté :

```text
(∀ φ, Proof_T⁺(φ) → Proof_T(φ)) → Empty
```

Un tel transport renverrait la preuve cible de `G_T` vers `Proof_T(G_T)`, que
le certificat source exclut. Cette preuve consomme l’ancienne non-prouvabilité,
et non celle de la nouvelle phrase.

## Localisation représentationnelle aux deux étages

Les constructions runtime existantes sont réappliquées sans duplication à
l’exécution source puis à l’exécution cible.

À chaque étage :

- un regroupement opérationnel positif calcule une mémoire terminale commune
  sans imposer l’exactitude globale des readouts
- une préservation dirigée adaptée à cette collision produirait la conversion
  vérité–preuve interdite à cet étage
- un séparateur terminal fini, porté par la requête vide après les runs de
  fermeture, distingue déjà les readouts produits
- toute réalisation exacte du contrat doit donc conserver deux mémoires
  terminales distinctes

L’extension de théorie n’est pas un effet caché du runtime. Elle est l’action
constitutive explicite entre deux étages. Chaque runtime reste indexé par la
production de son propre étage.

## Itération finie

`SoundGodelTheoryStage.advance` effectue une récursion compilable sur un nombre
naturel :

```text
T₀
  → T₁ = T₀ + {G₀}
  → T₂ = T₁ + {G₁}
  → …
  → Tₙ
```

`SoundGodelTheoryStage.executedTrace` conserve en outre chaque étape exécutée
et l’étage terminal qu’elle a effectivement produit. Le cas récursif consomme
directement ce terminal pour construire la progression suivante. Un étage
retient son exécution gödelienne maîtresse avec la preuve de sa canonicité. Le
terminal transporte donc aussi l’exécution cible produite par l’étape, et la
progression suivante la consomme au lieu de la recalculer depuis la seule
histoire. `executedTrace` n’appelle pas `advance`. Le théorème
`executedTrace_target_eq_advance` établit seulement après l’exécution que le
terminal partagé coïncide avec l’itérateur simplifié.

Le transport d’une preuve ancienne suit lui aussi cette chaîne retenue. La
méthode `ExecutedGodelTheoryTrace.preserveProof` consomme récursivement chaque
étape stockée et sa traduction dirigée. Le transport public vers `advance`
est obtenu seulement ensuite, par transport le long de l’égalité entre le
terminal exécuté et le terminal simplifié.

À chaque maillon, la phrase courante est non prouvable dans son étage et
prouvable dans l’étage suivant. Les anciennes preuves se transportent vers
tout étage ultérieur fini. La phrase suivante est fraîche, et la production
courante possède son regroupement opérationnel et son obligation de séparation
exacte.

Cette itération ne construit ni limite infinie, ni union extensive de toutes
les théories, ni théorie finale complète. Elle suit une succession finie de
productions et d’extensions effectivement constituées.

## Résultat fondationnel

La progression établit deux déplacements raccordés :

```text
déplacement de la frontière de preuve
  T ⟶ T + {G_T}

localisation représentationnelle de l’obstruction
  G_T relativement à Proof_T
  puis G_T⁺ relativement à Proof_T⁺
```

La phrase précédente devient prouvable lorsque le régime de preuve est
étendu. Une nouvelle phrase, produite relativement à ce régime renforcé,
porte une nouvelle non-prouvabilité et de nouvelles contraintes de
représentation. L’incomplétude est ainsi suivie comme une progression
constitutive finie de régimes de preuve et de leurs frontières de
préservation.

Le résultat porte sur la non-prouvabilité fournie par l’interface formelle. Il
n’affirme pas automatiquement la non-réfutabilité de chaque phrase, une théorie
complète finale, un runtime transversal comparant le même `G_T` avant et après
l’extension, ni une priorité bibliographique.
