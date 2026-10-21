# Soumission de l'audit C2 sur l'origine exacte du retour

La correction C2 a été figée et transmise à une nouvelle session Aristotle,
distincte de toutes les sessions d'audit antérieures.

| Élément | Valeur |
| --- | --- |
| Dépôt | `JohnDoe-collab-stack/relational-perimeter` |
| Branche | `codex/constitutive-agent-corrections-audit` |
| Commit scientifique audité | `a75619ffc33a6d0ce62ec2c626cf243ae43edacb` |
| Arbre scientifique | `364820dab5decb29795bfea260857f17224bf0f6` |
| Commit de publication du protocole | `501efc8f217003ee3ca1d8dbc10df8c64c9632b2` |
| SHA-256 du protocole | `f77251a561f5a25eeda6e092e669a8455d4a8400bde6e1b7c89e8976044ed7e6` |
| Projet Aristotle neuf | `2129f06c-99c3-4cd6-ac06-0043b8a02b93` |
| Tâche Aristotle | `4de608d4-58d2-4b28-b770-586181962e73` |
| Statut à l'acceptation | `QUEUED` |
| Pièces transmises | 10, soit 657 708 892 octets |

Le protocole demande deux verdicts indépendants : la fermeture exacte de C2
sur la provenance du résultat retourné, puis l'absence ou la présence d'une
régression. Il conserve mot pour mot l'exigence et le critère d'achèvement de
l'agent, exige les 75 réponses annoncées et impose notamment la reproduction
de C2e avant son rejet substantiel.

Avant l'envoi, le paquet hors ligne a été reconstruit dans un répertoire Linux
neuf à partir du bundle Git et des blobs canoniques. Lean 4.33.1, les deux
builds, les vérificateurs Bash et PowerShell, `git diff --check` et
`lake update` ont réussi. Les 319 fichiers suivis ont conservé leurs empreintes.
Cette validation locale prépare l'entrée ; elle ne remplace pas le verdict
indépendant demandé.

Le commit scientifique reste la cible immuable. Le présent reçu est un document
de chantier postérieur à l'envoi et ne doit jamais lui être substitué.
