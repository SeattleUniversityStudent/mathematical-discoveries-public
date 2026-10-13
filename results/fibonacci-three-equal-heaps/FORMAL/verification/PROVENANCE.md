# Provenance of the verification records (publisher note)

The Lean sources in this folder were built and replayed by the formal verifier on its own machine; the publisher did not run Lean for this result. The
verifier's native records are held privately and are bound here by SHA-256. Files in this folder are either verbatim copies of verifier outputs
(`axioms_report_stdout.txt`, `claims_module_stdout.txt`, `claims_report_check.json`, `replay_stdout.txt`, `Report_Claims.lean.txt`, the axiom-report source stored with a .txt suffix so that it is not mistaken for one of the 127 submitted modules) or summaries derived by the publisher
from the verifier's records with absolute private file-system paths removed (`build_execution_summary.json`, `replay_summary.json`, `build_result.json`,
`import_graph.json`). Every numeric and hash field in a summary is copied unchanged from the source record named in it.

| Record | Bytes | SHA-256 |
| --- | --- | --- |
| Clean-build evidence archive (664 members; 127 source inputs, compiled outputs, 256 logs) | 14743028 | 0100f090534bbb6192ef7ce43e8fc7dc153548faccff3752ea6e8f9598fbf5ca |
| Native archive-verification receipt | 119572 | 0ce387bf75e17f9d46604861e851a42cee651238f439f12860b7f521fb75f6f3 |
| Native stored-declaration replay execution record | 96406 | 8bba4b741dc50aa9c186c6553484b50d5c6da48e0b371a1e462ac764b8dcebdf |
| Clean-build result (`result.json` in the archive) | 2570 | c717df81f8566d7cee2001ebb9160a30f0add507c814ba27dd2f4149141f29e6 |
| Source manifest of the 127 submitted modules | 17546 | f256ba4b274396585fdbdd1935f2f40a62429772a6ce2e8dac6382228bf72d15 |
| Typed-report check (`claims-report-check.json`) | 449 | 6da48d0813d4fcca46c17fa4f38835ab823358753b51b53a3daa2b2883c5ba70 |
| Exact claim-release receipt (replay claim; private identifier omitted) | 815 | a95027d3b347090649bd232e5f7cff55fdb86b9462ddb503e27c3237f009b173 |

The clean build compiled 127 submitted modules plus one report source (128 invocations, all exit 0, no project cache reused) on 2026-10-13. The replay ran one
`leanchecker --fresh -v Claims` command that exited 0 on 2026-10-13. Its standard output is the single line in `replay_stdout.txt`; the checker prints no
per-declaration log, so what the replay covered rests on the checker's source (hash in `replay_summary.json`) and on the import chain
Claims -> Chunk124 -> ... -> Chunk00 -> Model -> Std (see `import_graph.json`), not on individual log lines.

Limits: the clean-build archive itself (14.7 MB, mostly compiled `.olean` files) is not republished. The platform is macOS as recorded by the verifier's resource accounting; the
processor architecture is not recorded in the files the publisher holds. No second independent compilation was performed; the replay checks the stored declarations of the clean build.
