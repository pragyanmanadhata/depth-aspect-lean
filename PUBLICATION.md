# Publication preparation

This remains a **relative formalization**, with the assumption boundary in
[ASSUMPTIONS.md](ASSUMPTIONS.md) and manuscript corrections in
[AUDIT.md](AUDIT.md). Publication checks do not renew the separate mathematical
correspondence review described in [REVIEW.md](REVIEW.md).
The [scope qualifications](REVIEW.md#scope-qualifications) record the restricted
Popa input, cancellation without an explicit `H(0)` convention, and the distinct
depth ranges of some signed intermediate estimates and the final theorem.

## Preserved records and cleanup

A complete recoverable copy was made before editing. The
[cleanup checks](verification/publication-checks.json) record file preservation
and publication-file scanning. All Lean files, the pinned
configuration, verification scripts, correspondence files, and current build and
axiom-audit evidence are unchanged. The retained endpoint records also match all
65 of their recorded module hashes. The 335 source hashes in the existing
integrated certificate, the 322 proof hashes in the completed review, and its
four correspondence hashes still match. No recorded review has been regenerated
or relabeled. Documentation and CI configuration are outside those hash sets.

Unsupported claims about a release payload manifest, ZIP checksum, and archive
packaging checks were removed. Python caches and 79 superseded debugging logs
were removed; ignore rules exclude Python bytecode and common caches. The
integrated build, axiom audit, module-cache check, and both endpoint audit records
are retained. The ignored `.lake` directory is local build state and should not
be committed. During that earlier cleanup stage, no remote repository was
created and nothing was pushed or published.

The publication-file scan found no credential patterns or absolute workstation
paths in retained text files. Current local Markdown links and JSON source
references resolve. The manuscript’s author affiliation and contact address are
retained as attribution. Pattern scanning cannot prove the absence of every
possible secret. The historical workspace path in
`correspondence/completed-review.json` is provenance outside this package, as
that record explicitly states; it is not a required build input.

## Exact manuscript

[manuscript/working-draft.pdf](manuscript/working-draft.pdf) is the unchanged
supplied working draft, 483,323 bytes. Its SHA-256 is:

```text
20b71677582cf2bf04965d91c82cfb05074e3d66bc49fe9be004229743f0cc71
```

This matches the existing paper hash in all correspondence records. No different
manuscript version was substituted.

## Reproducibility

A separate source copy was created without `.lake`, project build artifacts, or
local dependency symlinks. All nine Git dependencies were fetched from the
public URLs in the lockfile and checked at their recorded revisions, with no
tracked modifications or Git object alternates. A fresh download of official
compiled dependency caches succeeded: all 8,639 files were fetched and extracted.
The complete supplied verifier, `python3 scripts/verify.py --serial`, exited
successfully on **2026-10-25 at 21:16:43 UTC** after about 4 hours 17 minutes.
The [run record](verification/clean-source/run.json) and
[fresh certificate](verification/clean-source/summary.json) record:

- All 322 individual module builds and the full umbrella build passed.
- All 2,376 requested public-theorem axiom audits passed, using only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Module/umbrella inventories and the supplied disallowed-construct source scan
  passed.
- All nine pinned Git dependencies were pristine before and after verification,
  including the verifier's checks for extra Lean sources outside caches.
- All 335 recorded source hashes remained unchanged and match both this
  repository and the original integrated certificate.
- The existing review's proof and correspondence hash bindings matched.

The raw [build output](verification/clean-source/build.log),
[axiom report](verification/clean-source/axioms.txt),
[verifier output](verification/clean-source/verifier.log),
[dependency fetch](verification/clean-source/dependency-fetch.log), and
[fresh official cache download](verification/clean-source/official-cache-fetch.log)
are retained separately from the nine original verification records. Paths in
the fresh certificate identify files relative to the repository root. The
optional `--require-current-modules` mode and standalone endpoint audit commands
were not rerun; their original evidence is retained unchanged.

The [environment record](verification/clean-source/environment.json) identifies
macOS 15.7.7 on ARM, Python 3.14.6, and the reused installed Lean 4.32.0 toolchain.
There were no Lean/Lake path overrides or local dependency checkout links.
Three relative file symlinks tracked by upstream dependencies resolve within
those same packages. This was a clean source/dependency test on this machine,
not a fresh operating-system or toolchain installation, nor a Linux test.

The new certificate's `paper_correspondence_review_passed` field means that the
existing review's source bindings matched. It does not record a new or
independent mathematical review. The correspondence record retains its original
**2026-10-25T07:27:20.384564+00:00** timestamp and unchanged contents.

## GitHub Actions

The [workflow](.github/workflows/verify.yml) uses the existing pinned Lean
toolchain and dependency manifest, pins its two actions by commit, downloads
the official mathlib cache, and runs `python3 scripts/verify.py --serial`. It has
read-only repository permissions, disables persisted checkout credentials, and
does not restore a project build cache or commit verification records.

The [local CI validation record](verification/ci-static-validation.json) reports
that actionlint 1.7.12 and `bash -n` on the run command passed.
ShellCheck and Pyflakes integrations were unavailable and disabled. That local
validation did not include a GitHub Actions run or test Linux execution, runner
resources, or the six-hour time limit. The pinned Lean action still downloads the Elan
bootstrap from a mutable upstream branch, so this is not a hermetic build.

A [static portability check](verification/linux-portability-static.json) found no import-casing or checked-path mismatches; actual Linux execution remains untested.

## License

The Lean code, scripts, and documentation are licensed under
[Apache License 2.0](LICENSE). Existing third-party attribution, including the
mathlib adaptation in `DepthAspect/EndpointAbel.lean`, is preserved in the source
and [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). The manuscript PDF and
`correspondence/paper-text.txt` remain separately copyrighted and are excluded
from the Apache license. Earlier verification records retain the licensing
status recorded at their original timestamps.
