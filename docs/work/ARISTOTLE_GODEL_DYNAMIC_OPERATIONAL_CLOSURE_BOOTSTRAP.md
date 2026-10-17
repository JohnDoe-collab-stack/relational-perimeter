# Bootstrap only — fresh Gödel runtime audit project

This is the initialization task for a brand-new independent audit project. The
uploaded source archive is authoritative. Do not clone or fetch anything.

It must contain `relational-perimeter/` as a complete Git checkout, including
its `.git` history, detached at:

```text
31d9d0765298acd0d1e9715b57cc8adcfcb7cd7b
```

For this initialization task only:

1. enter `relational-perimeter/`;
2. run `git rev-parse HEAD` and `git status --short`;
3. verify locally that
   `c3a12b5114ca519aae8e8c83eec6b6d723d450d4` and
   `e2b75474c8bef91cfb9f24d6fed8d408e38d0269` are ancestors of the target;
4. verify that the files listed in
   `SOURCE_INPUT_MANIFEST.txt` are readable;
5. stop and return exactly the factual initialization results followed by
   `READY_FOR_TOOLCHAIN`.

Do not begin the mathematical audit, do not use an installed mismatched Lean
version, and do not return `VALIDATED` or `NOT VALIDATED`. The next task in this
same fresh project will upload the exact Lean `v4.33.1` toolchain parts and the
complete seven-criterion audit request.
