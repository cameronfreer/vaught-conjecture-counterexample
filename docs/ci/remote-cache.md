# Remote Lake artifact cache for the cold dependency path

Status: design and inert wiring.  Nothing here is active until the repository variable
`LAKE_CACHE_ENDPOINT` is set (this repository) and the dependency repositories adopt the proposed
publishing workflows in [`proposed/`](proposed/).  Facts below are for the pinned toolchain
`leanprover/lean4:v4.35.0-rc3` (Lake 5.0.0-src+470d5ce); file references are to its Lake sources
(`src/lean/lake/Lake/...` in the toolchain).

## Problem

CI carries `.lake/packages` between runs in the `deps` GitHub cache, keyed on `lean-toolchain` and
`lake-manifest.json`.  On a new dependency pin that cache misses and the cold path runs
`lake exe cache get` (the public Mathlib cache, which covers only the modules the
`cameronfreer/mathlib4` fork shares with upstream) and then compiles the rest from source: the
Mathlib closure of InfinitaryLogic has 1,716 modules (1,728 for this workspace), InfinitaryLogic has
368 source modules, and the ComputableModelTheory modules this workspace builds come on top.  The
outputs of exactly these modules already exist, built by the dependencies' own CI at the same
revisions.  Lake's artifact cache can carry them: a publisher uploads one archive per module plus a
map from input hashes to archives; a consumer downloads the map for a package's checked-out
revision and the archives it names, and `lake build` unpacks a module instead of compiling it
whenever its input hash is in the map.

## What Lake provides (established)

### (a) Configuring an S3-compatible service

Services are declared in the *system* Lake configuration, a TOML file at `$LAKE_CONFIG` (default
`~/.lake/config.toml`; `Lake/Config/LakeConfig.lean`, `Lake/Load/Toml.lean`):

```toml
cache.defaultService = "vc-public"          # optional; Reservoir otherwise
cache.defaultUploadService = "vc-r2"        # optional
[[cache.service]]
name = "vc-public"
kind = "s3"
artifactEndpoint = "https://<public host>/artifacts"
revisionEndpoint = "https://<public host>/revisions"
```

and selected with `--service <name>`.  (The environment variables `LAKE_CACHE_ARTIFACT_ENDPOINT`
and `LAKE_CACHE_REVISION_ENDPOINT` still work but are deprecated since 2026-02-19.)  There is no
bucket or region field: the endpoints are full URL prefixes, and Lake appends the scope.

- **Uploads** (`lake cache put`, `put-staged`) run `curl --aws-sigv4 aws:amz:auto:s3 --user
  "$LAKE_CACHE_KEY" -X PUT` (`Lake/Config/Cache.lean`, `uploadS3`, `transferArtifacts`).  The key
  is `<ACCESS_KEY_ID>:<SECRET_ACCESS_KEY>`, and the SigV4 region is hard-wired to `auto`.  That is
  Cloudflare R2's region, so R2 works (the upload endpoint is the S3 API URL
  `https://<ACCOUNT_ID>.r2.cloudflarestorage.com/<bucket>`); AWS S3 itself, which requires the
  bucket's real region in the signature, is not usable.  The local experiment below confirmed the
  signature header `Credential=<ACCESS_KEY_ID>/<date>/auto/s3/aws4_request`.
- **Downloads** are plain unauthenticated `curl` GETs (`downloadArtifacts`, `getUrl?`); there is no
  way to sign them.  Reads therefore need a public host: an R2 custom domain (the `r2.dev` URL is
  rate-limited and meant for development).  So a consumer and a publisher use *different* services
  (public host versus S3 API host) over the same object layout.

### Object layout and scopes

With `--repo <owner>/<repo>` (`s3ArtifactUrl`, `s3RevisionUrl`):

```
artifacts/<owner>/<repo>/<content hash>.art
revisions/<owner>/<repo>[/pt/<target triple>][/tc/<toolchain dir>]/<commit>.jsonl
```

where `<toolchain dir>` is the toolchain with `/` → `--` and `:` → `---`
(`leanprover--lean4---v4.35.0-rc3`).  Artifacts carry no platform or toolchain (they are content
addressed, so identical archives are stored once across revisions); only the revision map does.
`--scope <s>` instead uses `<s>` verbatim for both and never adds `pt/` or `tc/`.

### (b) What `lake cache put` uploads, and which package

- The mappings file comes from `lake build <targets> -o <file> [--package <p>]`: one JSON line per
  module of package `<p>` (default: the root) covered by the build, `[input hash, "<hash>.ltar"]`.
  The `.ltar` is the module's archive (`.olean`, `.olean.server`, `.olean.private`, `.ilean`,
  `.ir`, `.c`), packed by `leantar` (`Lake/Build/Module.lean`, `packLtar`).  The archives are only
  in the Lake cache when the build ran with the cache writable (`LAKE_ARTIFACT_CACHE=true`);
  `lake cache put` then reads them from there, and `lake cache stage <file> <dir>` copies them out
  for `put-staged`.
- **One package per map.**  A map never includes a dependency's modules; each package is
  published separately under its own scope.  Mathlib's own dependencies (batteries, aesop, Qq,
  ProofWidgets, plausible, importGraph, LeanSearchClient) are unchanged upstream revisions and
  stay with `lake exe cache get`.
- **The fork can be published by whoever builds it.**  The scope is only a name: InfinitaryLogic's
  CI builds the fork, so it can record `--package mathlib` and upload under
  `--repo cameronfreer/mathlib4` for the fork commit in its manifest.  A consumer fetches it with
  `lake cache get --package mathlib --repo cameronfreer/mathlib4`, which looks up the commit checked
  out in `.lake/packages/mathlib`.  A scope must have a single publisher: a second upload for the
  same commit replaces the map.
- **Hits across workspaces.**  A module's input hash (`Lake/Build/Module.lean`, `recBuildDeps`)
  mixes the hashes of its imports, the Lean version, the source file's content, its options, the
  module name, the package's original name and the Lean arguments; no paths.  It is therefore the
  same in InfinitaryLogic's workspace and in this one exactly when the toolchain and the revisions
  of the module's package and of everything it imports agree.  For InfinitaryLogic `e460cb6` they
  do: its manifest pins the same Mathlib (`346a4bd`), LeanArchitect, checkdecls and Mathlib
  dependencies as this workspace's.  ComputableModelTheory `a1fe761` pins InfinitaryLogic
  `6480603`, not `e460cb6`, so its modules that import InfinitaryLogic modules changed in between
  will miss here; its Mathlib-only classical modules (`ComputableModelTheory.Classical`) hit.

### (c) What a consumer's `lake cache get` does

- With a custom service, `lake cache get` handles **one package per call** (the root, or
  `--package <p>`) and requires `--repo` or `--scope`.  Only Reservoir has a multi-package mode.
- It reads the package's `HEAD`, requests the map for that commit, and on a 404 walks back through
  the history, up to `--max-revs` commits (default 100).  It writes the map into the local cache
  (`$LAKE_CACHE_DIR/outputs/<package>/<input hash>.json`), then downloads every archive the map
  names (all of them, used or not), each verified against its content hash.
- Exit codes and leftovers: no map found gives "no outputs found …", exit 1, nothing written.  A
  failed or corrupt download gives exit 1, but the map has already been written, so mappings can
  name archives that are missing (observed in the experiment below).  A build that meets such a
  mapping logs it at verbose level only and compiles the module (`getArtifactsUsingCache?`), so a
  partial fetch is not fatal; the script below still removes the package's mappings so that the
  fallback is exactly the uncached build.
- During `lake build`, a module whose trace is up to date (for example from `lake exe cache get`)
  is taken as is.  Otherwise, since the cache is readable by default, Lake looks the input hash up
  in the local cache and, on a hit, unpacks the archive into the package's build directory; on a
  miss it compiles.  The `deps` GitHub cache saved afterwards is therefore complete without the
  Lake cache.
- `lake build --try-cache` is unrelated: it controls Reservoir and GitHub-release build archives of
  whole packages (`Lake/Build/Package.lean`), offered only for `leanprover`/`leanprover-community`
  packages or packages with `preferReleaseBuild`.  None of ours qualify.

### (d) Platform and toolchain in the scope

`put` and `get` add `pt/<target>` unless the package sets `platformIndependent = true`, and
`tc/<toolchain>` unless it sets `fixedToolchain` (or is Lean itself) (`Lake/CLI/Main.lean`,
`cachePlatform`, `cacheToolchain`).  The setting read is that of the package being published or
fetched, not the root's, so this repository's own `platformIndependent = true` plays no role here.

| Package | `platformIndependent` | `fixedToolchain` | Revision map path |
|---|---|---|---|
| mathlib (fork) | true | true | `revisions/cameronfreer/mathlib4/<commit>.jsonl` |
| InfinitaryLogic | unset | unset | `revisions/cameronfreer/infinitary-logic/pt/x86_64-unknown-linux-gnu/tc/leanprover--lean4---v4.35.0-rc3/<commit>.jsonl` |
| ComputableModelTheory | unset | unset | `revisions/cameronfreer/computable-model-theory/pt/x86_64-unknown-linux-gnu/tc/leanprover--lean4---v4.35.0-rc3/<commit>.jsonl` |

`put-staged` loads no workspace, so the publisher passes `--platform` and `--toolchain` itself
(and omits both for the fork).  The scope is computed from the configuration at the consumer's
current revision, so a package that changes `platformIndependent` misses the maps published
before the change (observed in the experiment).

A known defect in this toolchain: for a `platformIndependent` package, a module whose `.ltar` was
already present when `-o` recorded it is entered as platform-dependent and then left out of the
map (`trackOutputsIfEnabled`; fixed upstream by lean4#15231, after v4.35.0-rc3).  The proposed
staging step deletes stale archives first and refuses to stage a fork map with fewer than 1,000
lines.

### (e) Precedent

TauCeti publishes its root package's Lake artifacts to an R2 bucket (`tauceti-cache`) behind a
custom domain with anonymous reads, from a separate key-holding job that runs only
`lake cache put-staged` on a staged directory; Mathlib there stays on `lake exe cache get` (with a
GitHub Actions snapshot of the `.ltar` download store).  The design below follows the same split,
extended to the fork and to two dependency repositories.

## Design

### Who publishes what

| Publisher (CI, on push to the default branch, after a green build) | Package | Scope (`--repo`) | When |
|---|---|---|---|
| `cameronfreer/infinitary-logic` (`master`) | InfinitaryLogic | `cameronfreer/infinitary-logic` | every push |
| `cameronfreer/infinitary-logic` (`master`) | mathlib (the fork) | `cameronfreer/mathlib4` | once per fork commit (skipped if its map is already public) |
| `cameronfreer/computable-model-theory` (`main`) | ComputableModelTheory | `cameronfreer/computable-model-theory` | every push |

This repository only reads.  One R2 bucket holds everything under the prefixes `artifacts/` and
`revisions/`; one custom domain serves it read-only.

### Consumer (this repository)

[`scripts/ci/lake-cache-get.sh`](../../scripts/ci/lake-cache-get.sh), run by the new step in
`.github/workflows/ci.yml` before "Fetch Mathlib cache and build dependencies", only when the
`deps` cache missed and `vars.LAKE_CACHE_ENDPOINT` is non-empty, with `continue-on-error`.  It
writes a read-only service definition into a temporary `LAKE_CONFIG` and runs, with
`LAKE_CACHE_DIR=$RUNNER_TEMP/lake-cache`:

```sh
lake cache get --service vc-public --package mathlib \
  --repo cameronfreer/mathlib4 --max-revs=1
lake cache get --service vc-public --package InfinitaryLogic \
  --repo cameronfreer/infinitary-logic --max-revs=20
lake cache get --service vc-public --package ComputableModelTheory \
  --repo cameronfreer/computable-model-theory --max-revs=20
```

(The first call also clones the dependencies at their manifest revisions, as
`lake exe cache get` would.)  Each package gets two attempts (the second downloads only what the
first did not verify), none after "no outputs found".  A package that does not complete has its
mappings removed.  If any package completed, `LAKE_CACHE_DIR` is exported to the later steps; if
none did, the directory is deleted and nothing is exported.  The existing cold step then runs
unchanged: `lake exe cache get` fills in the upstream Mathlib modules, and the two `lake build`
calls unpack the cached modules and compile only the misses.  `LAKE_ARTIFACT_CACHE` stays unset
(read-only cache), and no service is configured during the builds, so they make no network
requests.  The project's own modules are never fetched.

The fork's map is looked up for the exact pinned commit only (`--max-revs=1`): an older fork
commit's map would download about 1,700 archives for few hits.  InfinitaryLogic and
ComputableModelTheory may walk back 20 commits, which turns a pin to an unpublished commit (for
example a branch head) into a partial hit at small cost (their maps name about 30 and 16 MiB).

### Publishers (proposed, not active)

- [`proposed/infinitary-logic/build.yml`](proposed/infinitary-logic/build.yml) and
  [`proposed/infinitary-logic/publish-lake-cache.yml`](proposed/infinitary-logic/publish-lake-cache.yml)
- [`proposed/computable-model-theory/lean_action_ci.yml`](proposed/computable-model-theory/lean_action_ci.yml)
  and [`proposed/computable-model-theory/publish-lake-cache.yml`](proposed/computable-model-theory/publish-lake-cache.yml)

The build job, after its existing checks and only on a push to the default branch with the upload
variable set, stages:

```sh
export LAKE_ARTIFACT_CACHE=true LAKE_CACHE_DIR=$RUNNER_TEMP/lake-cache
find .lake/build .lake/packages/mathlib/.lake/build \( -name '*.ltar' -o -name '*.ltar.hash' \) -delete
lake build $TARGETS > /dev/null                      # nothing compiles; outputs enter the cache
lake build $TARGETS --no-build --rehash -o il.jsonl
lake build $TARGETS --no-build --rehash -o mathlib.jsonl --package mathlib   # InfinitaryLogic only
lake cache stage il.jsonl      "$STAGING/InfinitaryLogic"
lake cache stage mathlib.jsonl "$STAGING/mathlib"
```

and uploads the staging directory as a workflow artifact.  A separate `publish` job (a reusable
workflow, the only place the key exists) checks out only `lean-toolchain`, `lake-manifest.json`
and `lakefile.toml` at the published commit, validates the staged tree (flat directories of
regular files, plain `<hash>.<ext>` names, only the expected packages), installs the pinned
toolchain, and runs

```sh
lake cache put-staged "$STAGING/InfinitaryLogic" --service vc-r2 \
  --repo cameronfreer/infinitary-logic --rev "$GITHUB_SHA" \
  --platform x86_64-unknown-linux-gnu --toolchain "$(cat lean-toolchain)"
lake cache put-staged "$STAGING/mathlib" --service vc-r2 \
  --repo cameronfreer/mathlib4 --rev "<fork commit from lake-manifest.json>"
```

(`put-staged` uploads the archives first and the map last, so a map that is visible names
archives that are present.)  A last step, without the key, fetches each published map from the
public host and compares it byte for byte with the staged one.

## Security model

- **Publisher keys only in the publishing repositories**, as the secret `LAKE_CACHE_KEY`, exposed
  only to the `publish` job.  That job runs no code from the repository or its dependencies:
  `lake cache put-staged` loads no workspace, and the scope inputs come from files checked out at
  the commit (and, for the fork's options, from the fork's `lakefile.lean` at the pinned commit),
  not from the build job.  The build job, which elaborates Lean code from the default branch and
  can therefore tamper with anything later in the same job, never sees the key.  Pull requests
  never publish.
- **Two credentials**: one R2 API token per publishing repository, each restricted to Object Read
  & Write on this bucket.  R2 tokens are scoped to buckets, not prefixes, so either token can
  overwrite the other's objects; if that matters, use one bucket per publisher (two custom
  domains, and two services in the consumer script).  Rotate by installing the new token, letting
  one publication succeed, then revoking the old one.
- **Consumers hold no credential.**  Reads are anonymous over HTTPS, and this repository needs only
  a repository variable.  A fork's pull request that cannot see the variable runs the cold path as
  today.
- **Integrity.**  Downloads are checked against Lake's content hashes, which are 64-bit and not
  cryptographic: they detect corruption, not forgery.  Trust in a fetched module is trust in the
  publishing CI and in whoever can write to the bucket, the same kind of trust as in the public
  Mathlib cache today.  The project's own modules, and every audit, are still compiled and run
  from source on every run.  A run with the variable unset (and the `deps` cache deleted)
  rebuilds everything from source if a full check is wanted.

## Failure modes

| Situation | Effect |
|---|---|
| `LAKE_CACHE_ENDPOINT` unset (or not visible to the run) | Step skipped; today's cold path. |
| `deps` cache hit | Step skipped; today's warm path. |
| No map for a package's commit (not yet published, other toolchain, platform setting changed) | "no outputs found", mappings absent; that package compiles from source. |
| Host unreachable, HTTP error, corrupt archive | Retried once; then that package's mappings are removed and it compiles. |
| Map found but some input hashes differ (older revision, different dependency pins) | Those modules compile; the rest unpack. |
| Script or Lake error not covered above | `continue-on-error`; if `LAKE_CACHE_DIR` was not yet exported, the builds run uncached; if it was, a mapping without an archive only makes Lake compile that module. |
| Publisher fails | Nothing (or only archives) uploaded; consumers miss. |

## Cost and benefit

Measured on the main checkout's `.lake/packages` (read-only; zstd level 3 on the files a module
archive contains):

| Package | Modules | Outputs, uncompressed | Compressed (estimate) |
|---|---|---|---|
| Mathlib fork, InfinitaryLogic's closure | 1,716 | about 0.67 MiB per module (300-module sample), so about 1.1 GiB | about 0.2 MiB per module, so about 340 MiB per fork commit |
| InfinitaryLogic (built modules) | 339 | 97 MiB | 28 MiB |
| ComputableModelTheory (built modules) | 137 | 58 MiB | 16 MiB |

- **Bucket size.**  About 0.4 GiB per fork commit plus at most 30 MiB per InfinitaryLogic commit
  and 16 MiB per ComputableModelTheory commit; archives are content addressed, so a new commit adds
  only the archives of modules whose outputs changed.  A year of activity stays near R2's 10 GB free
  storage; no lifecycle rule is needed at first (an age-based rule would also delete archives
  still named by a map of a long-lived fork pin).
- **Requests and egress.**  A cold run makes about 2,100–2,300 GETs (one per archive, plus a few
  map lookups) for about 0.4 GiB.  R2 egress is free; Class B reads are free up to 10 million a
  month, and Class A writes (one per archive per publication, about 2,400 for a new fork pin and
  about 400 per later push) up to one million.  Expected cost: nothing.
- **Time.**  Today's cold path compiles roughly 2,100 modules (20 minutes or more).  With all three
  maps present it downloads about 0.4 GiB (well under a minute from a Cloudflare custom domain to
  a GitHub runner) and unpacks the archives during the two dependency builds (a few minutes), so a
  cold run should take about as long as a warm run plus three to five minutes.  This is an
  estimate to be confirmed on the first cold run.  Warm runs are unaffected.  The publishing
  repositories pay about two minutes per push for packing and staging, plus about one more for
  the fork map when the fork pin changes.

## Provisioning checklist (owner)

1. **Bucket.**  A Cloudflare R2 bucket, for example `vc-lake-cache`, in an account the owner
   controls.  Public access through `r2.dev` off.
2. **Custom domain.**  Attach a hostname (for example `lake-cache.<your domain>`) to the bucket as
   an R2 custom domain; the zone must be in the same Cloudflare account.  Optionally add a Cache
   Rule making `/artifacts/*` cacheable with a long edge TTL (artifact keys are immutable); leave
   `/revisions/*` uncached so that a 404 for a not-yet-published commit is not cached.
3. **Two credentials.**  Two R2 API tokens with Object Read & Write restricted to this bucket, one
   for InfinitaryLogic and one for ComputableModelTheory.  Each gives an access key id and a secret.
4. **Repository settings.**

   | Repository | Kind | Name | Value |
   |---|---|---|---|
   | `cameronfreer/vaught-conjecture-counterexample` | variable | `LAKE_CACHE_ENDPOINT` | `https://lake-cache.<your domain>` |
   | `cameronfreer/infinitary-logic` | variable | `LAKE_CACHE_ENDPOINT` | the same public URL |
   | `cameronfreer/infinitary-logic` | variable | `LAKE_CACHE_UPLOAD_ENDPOINT` | `https://<ACCOUNT_ID>.r2.cloudflarestorage.com/vc-lake-cache` |
   | `cameronfreer/infinitary-logic` | secret | `LAKE_CACHE_KEY` | `<ACCESS_KEY_ID>:<SECRET_ACCESS_KEY>` of the first token |
   | `cameronfreer/computable-model-theory` | variable | `LAKE_CACHE_ENDPOINT` | the same public URL |
   | `cameronfreer/computable-model-theory` | variable | `LAKE_CACHE_UPLOAD_ENDPOINT` | as above |
   | `cameronfreer/computable-model-theory` | secret | `LAKE_CACHE_KEY` | the second token's pair |

   The endpoint values carry no trailing `/artifacts` or `/revisions`; the workflows append them.
5. **Adopt the publishing workflows** from [`proposed/`](proposed/) in the two dependency
   repositories (each by its own pull request), then push to their default branches (or re-run
   the last default-branch build) so that the current pins get published.  The fork map is
   published by InfinitaryLogic's first run.
6. **First consumer run.**  Delete this repository's `deps-v6-…` cache entry for the current pins
   (`gh cache list`, `gh cache delete <key>`), re-run CI, and check the step's notice
   ("fetched [mathlib InfinitaryLogic …]") and the time of the cold step.

### Checking a publication without building

Once a map is public, the number of hits it will give here can be predicted from the trace files
already in a populated `.lake/packages`: each module's trace records its input hash as `depHash`.

```sh
curl -fsSL "$BASE/revisions/cameronfreer/mathlib4/<fork commit>.jsonl" -o fork.jsonl
python3 - fork.jsonl .lake/packages/mathlib/.lake/build/lib/lean <<'PY'
import json, pathlib, sys
keys = {json.loads(l)[0] for l in open(sys.argv[1]).read().splitlines()[1:] if l}
hashes = [json.load(open(t)).get("depHash") for t in pathlib.Path(sys.argv[2]).rglob("*.trace")]
print(f"{sum(h in keys for h in hashes)} of {len(hashes)} local modules are in the map")
PY
```

## Local experiment (no credentials, no builds)

Run on 2026-10-06 against a local HTTP server standing in for the bucket (it stored `PUT`s and
answered `GET`s), with a hand-made staging directory (one mapping naming a real module output
whose content hash came from its `.hash` file), from a scratch package and from this workspace:

- `lake cache services` lists services declared in `$LAKE_CONFIG`.
- `put-staged` uploaded the archive and then the map, with the URLs given above and an
  `AWS4-HMAC-SHA256 Credential=<id>/<date>/auto/s3/aws4_request` signature.
- `lake cache put` derived `pt/x86_64-unknown-linux-gnu/tc/leanprover--lean4---v4.35.0-rc3/`
  for a package without `platformIndependent`, and only `tc/…` after setting it.
- In this workspace, `scripts/ci/lake-cache-get.sh` derived
  `revisions/cameronfreer/mathlib4/346a4bd….jsonl` for the fork (no platform, no toolchain) and
  the `pt/…/tc/…` paths for InfinitaryLogic `e460cb6…` and ComputableModelTheory `a1fe761…`;
  fetched the published packages, reported an unpublished one as "no outputs found in 20
  revisions from HEAD" and removed its mappings; with the host unreachable it removed the cache
  directory and exported nothing.
- A corrupted archive failed the hash check (exit 1) after its mapping had been written.
- Backtracking walks `HEAD`, `HEAD~1`, … one request per commit; the local revision cache is keyed
  by package name only, so it must start empty (a fresh `LAKE_CACHE_DIR`, as in CI).

Not established without a real publication: the end-to-end unpacking during `lake build` (read from
the Lake sources, not run), the hit rate across workspaces (argued from the input-hash
definition; check it with the snippet above), and the cold-run time.
