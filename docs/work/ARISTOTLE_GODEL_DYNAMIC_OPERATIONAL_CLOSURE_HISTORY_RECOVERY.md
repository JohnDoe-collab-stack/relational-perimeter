# History recovery only — fresh Gödel runtime audit project

The source bootstrap correctly found the uploaded files but the service removed
the nested `.git` directory while extracting the archive. That initialization
returned no mathematical verdict.

The attached file
`relational-perimeter-history-31d9d07.bundle` is a verified Git bundle:

```text
bytes: 4920351
SHA-256: 96747eb16bef8ce0bf196b514ab92ea66e38b371f6001c8817cd0a35764526e9
advertised ref: refs/heads/audit-target
target: 31d9d0765298acd0d1e9715b57cc8adcfcb7cd7b
```

For this recovery task only:

1. locate the uploaded bundle and verify its SHA-256;
2. enter the existing `relational-perimeter/` source directory;
3. initialize a nested repository there and import the bundle:

```text
git init
git fetch /path/to/relational-perimeter-history-31d9d07.bundle \
  refs/heads/audit-target:refs/heads/audit-target
git checkout --detach 31d9d0765298acd0d1e9715b57cc8adcfcb7cd7b
```

4. run `git rev-parse HEAD` and `git status --short`;
5. verify that
   `c3a12b5114ca519aae8e8c83eec6b6d723d450d4` and
   `e2b75474c8bef91cfb9f24d6fed8d408e38d0269` are ancestors of the target;
6. verify that the required files in `SOURCE_INPUT_MANIFEST.txt` remain
   readable;
7. stop and return the factual recovery results followed by
   `READY_FOR_TOOLCHAIN`.

Do not begin the mathematical audit and do not return `VALIDATED` or
`NOT VALIDATED`. The next task will upload the exact Lean `v4.33.1` toolchain
parts and the complete seven-criterion audit request.
