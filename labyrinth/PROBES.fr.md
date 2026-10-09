# Sources archivées des modèles séparateurs

Après la relecture, les deux sondes ont été renommées sans modifier leur contenu :

- `labyrinth/probes/FoundationalSeparators.lean` → [FoundationalSeparators.lean.in](probes/FoundationalSeparators.lean.in).
- `research/agents/referee-foundations/IndependentProbes.lean` → [IndependentProbes.lean.in](../research/agents/referee-foundations/IndependentProbes.lean.in).

Les rapports et les premiers événements conservent les chemins historiques de l’exécution. Les références de la carte, son état des questions et le script de reproduction emploient les noms actuels. Lean accepte ces fichiers comme sources :

```powershell
lake env lean labyrinth/probes/FoundationalSeparators.lean.in
lake env lean research/agents/referee-foundations/IndependentProbes.lean.in
```

Le suffixe `.lean.in` évite d’ajouter ces expériences aux modules `*.lean` examinés par les contrôles globaux de production, tout en conservant les sources et leurs audits terminaux. Les empreintes sont dans `evidence/probe-archive.json`.
