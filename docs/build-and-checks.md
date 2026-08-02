# Build and checks

How to build the project and run the discipline checks. No mathematical content here.

## Prerequisites

The Lean toolchain is managed by [elan](https://github.com/leanprover/elan). If `lake`
is not on your `PATH`:

```bash
curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
```

elan reads `lean-toolchain` and installs the pinned Lean version automatically on first use.

### Why `lean-toolchain` pins an RC, not a stable release

`lean-toolchain` currently pins `leanprover/lean4:v4.31.0-rc2`. This is deliberate
mathlib-alignment, not a stale pin left over from bootstrap: `[[require]] mathlib` in
`lakefile.toml` tracks `rev = "master"` (a floating target, made reproducible by the explicit
commit pin in `lake-manifest.json`), and the mathlib commit currently pinned there itself
depends on `leanprover/lean4-cli` at `inputRev = "v4.31.0-rc2"`. That match is evidence — not
a formal proof — that mathlib master, as resolved, targets this same Lean release; it is the
closest signal available without querying the Lean/mathlib release calendar directly. Treat
this pin as tied to mathlib's own toolchain, not to a preference for release-candidates: moving
to a later stable release ahead of mathlib's own pin risks desyncing the build. Re-evaluate
this pin whenever `lake update` re-resolves mathlib (an explicit `lean-coder` task; see below).

## Build

```bash
lake exe cache get   # download prebuilt mathlib oleans (first time / after mathlib bump)
lake build
```

> `lake update` (bumping the mathlib revision) is an **explicit `lean-coder` task only**. The
> pinned commit in `lake-manifest.json` is the reproducibility source of truth — do not run
> `lake update` as a side effect of other work.

## Discipline checks

```bash
bash scripts/check-no-sorry.sh          # unmarked `sorry`
bash scripts/check-no-axiom.sh          # unmarked axiom/constant/opaque/unsafe
bash scripts/check-theorem-names.sh     # overclaiming declaration names
bash scripts/check-axioms.sh            # axiom-leak static pre-filter
bash scripts/check-release-cone.sh      # release cone (import LerayHopf): sorry-free, axiom-free,
                                         #   no placeholder namespaces (issues #147, #151)
bash scripts/test-check-release-cone.sh # committed regression fixtures for the check above (issue #151)
bash scripts/check-statement-cards.sh   # every ALLOW_SORRY decl has a statement card (issue #158)
```

`check-statement-cards.sh` also pins `w1pTime_continuous_in_H` at `p = q = 2` — see
`docs/statement-gates.md` for the statement-card process this enforces and
`docs/postmortems/2026-07-w1ptime-false-statement.md` for why.

## Preflight (run before and after editing)

Builds, then runs all the discipline checks above (plus the live axiom pin) in order:

```bash
bash scripts/agent-preflight.sh
```

For agent runs, do not stream full Lean build or preflight output into the chat/context.
Capture the log, inspect the exit status, and read only the relevant success tail or
error slice:

```bash
bash scripts/agent-preflight.sh >/tmp/lean-pde-preflight.log 2>&1
echo $?
tail -n 80 /tmp/lean-pde-preflight.log
```

On failure, narrow the log with `rg`, `sed`, or `tail` before quoting output.

## Markers

The checks honor same-line justification markers:

| Marker | Permits |
|---|---|
| `-- ALLOW_SORRY: <reason>` | a `sorry` on that line |
| `-- ALLOW_AXIOM: <reason>` | an `axiom`/`constant`/`opaque`/`unsafe` on that line |
| `-- ALLOW_NAME: <reason>` | a reserved term in a declaration name on that line |

Markers are per-line by design, so every exception is justified where it occurs.

**Exception — the release cone has no marker escape.** Inside the transitive import
closure of `LerayHopf.lean` (`import LerayHopf`), `check-release-cone.sh` rejects `sorry`
and `axiom`/`constant`/`opaque`/`unsafe` even when marked, and rejects the
`Scaffold`/`Placeholder`/`Stub`/`Draft` namespaces outright (see `docs/guardrails.md`).
The fix there is always to move the module behind `LerayHopf.Experimental`, never to add
a marker.

## CI

Auto full builds are **abolished** (GitHub Actions cost).

- **PRs** run the `guards` job: the seven static/textual guards above
  (`check-no-sorry.sh`, `check-no-axiom.sh`, `check-theorem-names.sh`, `check-axioms.sh`,
  `check-release-cone.sh`, `test-check-release-cone.sh`, `check-statement-cards.sh`). No
  Lean build on CI for PRs.
- **Full build + live axiom pin** (`check-axioms-live.sh`, which additionally prints the
  `LerayHopf.Experimental` axiom profile for visibility — see
  `docs/statement-gates.md`) runs **manually** via the `lean` workflow's
  `workflow_dispatch` trigger on GitHub, together with all seven guards above.
- **Release-candidate build attestation** — a separate, persisted evidence record
  for one exact SHA — runs manually via the `release-attestation` workflow (see
  below).
- **Mandatory build gate** (for the AI agent team, per `AGENTS.md`) is the
  **local incremental build**, enforced by the `scripts/hooks/pre-push` git hook.
  For a human contributor this hook is available and useful but opt-in, not
  mandatory — see `CONTRIBUTING.md`'s build-cost policy for what is actually
  expected of that audience.

### Activating the pre-push hook (once per clone)

```bash
git config core.hooksPath scripts/hooks
```

After activation, every `git push` runs the grep guards and, when `.lean` /
`lakefile` / `lean-toolchain` files changed, a flock-serialized `lake build`.
A failing build or failing guard blocks the push.

Verify activation:

```bash
git config --get core.hooksPath   # should print: scripts/hooks
```

## Release-candidate build attestation (issue #150)

The README badge links to the `release-attestation` workflow, a `workflow_dispatch`-only
job that certifies one exact commit SHA has a full `lake build` pass plus all discipline
guards, including the capstone live axiom pin (`check-axioms-live.sh`). It never runs on
push, pull request, or a schedule, and it is separate from the `lean` workflow's routine
`full-build` dispatch job (see above) — it takes an explicit SHA input and produces a
persisted attestation record, rather than only a job log.

### Producing a new attestation

```bash
gh workflow run release-attestation.yml --repo uda-lab/leray-hopf -f ref=<candidate-sha-or-tag>
```

The run resolves `<candidate-sha-or-tag>` and checks it out, records the resulting commit
SHA, the `lean-toolchain` content, and the sha256 of `lake-manifest.json`, runs the full
build and every guard script, and writes the results as:

- the workflow run's **job summary** (a Markdown table: SHA, toolchain, manifest hash,
  per-step pass/fail, guard log checksums), and
- an **artifact** named `release-attestation-<sha>` (the same Markdown file plus the raw
  guard logs), retained for 90 days (the GitHub maximum for public repositories).

### Finding the SHA of the latest attestation

Open the workflow's [runs page](https://github.com/uda-lab/leray-hopf/actions/workflows/release-attestation.yml)
(same link as the README badge) and open the most recent run — the job summary states the
attested SHA at the top. **A green badge or a green run does not mean the current branch
HEAD is attested** — it means exactly the SHA recorded in that run's summary is attested.
If commits have landed since that SHA, treat the code between the attested SHA and HEAD as
unattested (though still covered by the local pre-push build gate and, on PRs, the fast
`guards` job) until a new attestation is run against the new candidate SHA.

### Durability caveat

The job summary and artifact are bounded by GitHub's run/artifact retention window, not
stored forever. For a commit that is being cut as an actual public release, additionally
attach the attestation Markdown file as an asset on the corresponding GitHub Release — the
workflow artifacts and logs are retention-limited, but Release assets are not subject to
that Actions retention deadline (a maintainer can still delete a Release or its assets,
same as any other repository content).

**Example:** the
[`v0.1.0-rc1` Release](https://github.com/uda-lab/leray-hopf/releases/tag/v0.1.0-rc1)
archives the evidence for attested SHA `7c15710a7b9068a2aa105fc7c11b432e7685b7b5`
(run [29714844283](https://github.com/uda-lab/leray-hopf/actions/runs/29714844283)):
`attestation.md`, the full artifact zip (guard logs included), the complete raw workflow
run log, a machine-readable `release-provenance.json`, and a `SHA256SUMS` file making all
of the above mutually verifiable. This copy is not subject to the workflow run's own
artifact-retention window. As with the badge above, this certifies exactly that SHA,
not the branch HEAD at any later time.

Publishing a Release like this is not automatic — the workflow succeeding does not by
itself create a tag or Release. Adopting a candidate SHA as a release is an owner
decision, so for now this is a manual step the owner (or someone acting under explicit
owner authorization) performs after reviewing a successful run: create an annotated tag
pointing at the attested SHA, create a GitHub Release (pre-release before a first stable
tag), and attach the five files listed above (the checksum file is one of them). A future
iteration may add an explicit `workflow_dispatch` input (e.g. `publish_release_assets=true`
plus a tag name) so an owner-triggered run can create a draft/pre-release directly — if
added, it must still fail closed on tag/SHA mismatch and must never overwrite an existing
Release.

## README Star History embed (issue #189)

The README currently has **no Star History section at all** — neither a chart nor a link.
Until 2026-08-02 it carried [Star History](https://www.star-history.com/)'s
standard authenticated embed: a `sealed_token` query parameter on the
`api.star-history.com/chart` URL, generated from a fine-grained GitHub personal access
token scoped to `uda-lab/leray-hopf` only, read-only, no write/admin permissions. That
sealed token was Star History's own public embed value, generated by their service
specifically for pasting into a README's HTML — it is not the raw PAT and does not expose
the PAT's credentials. Should the embed be restored, the same applies, and the raw PAT
itself must never be committed, to this repository or anywhere else.

**Current state (2026-08-02, issue #230 §A.2): the whole section is REMOVED.** The README no
longer has a Star History section — the owner's decision was to drop it entirely rather than
keep a link or an explanatory note. Restoring the chart therefore means re-creating the
section, not merely swapping a token value — see step 3 below.

### Why it was removed

Both routes were tested and both fail; star-history.com itself was up (`200`), so this was
not a transient outage:

| Route | Result |
|---|---|
| Authenticated embed (`sealed_token=…`) | **`401`** — `The provided GitHub access token is invalid or expired` |
| Anonymous (no `sealed_token`) | **`404`** — `GitHub restricted starred-data access for uda-lab/leray-hopf.` |

The second row is the important one, and it corrects an assumption in the older version of
this runbook: **there is no anonymous fallback for this repository.** A valid sealed token is
structurally required, so "test the anonymous URL" is a diagnostic step, not a recovery path.
Regenerating the token needs an interactive owner sign-in at star-history.com and a fresh
fine-grained PAT, which no automated agent can do on the owner's behalf.

### Diagnosing

**Print the response body, not just the status.** The classification below depends on the
body text: a bare `404` cannot be distinguished from any other `404` without it. Use the raw
`&` separator, not the README's HTML-escaped `&amp;` — a `curl` command line is not HTML, so
`&amp;` there is a literal string rather than a separator and a straight copy-paste from
README markup will not work.

```bash
# authenticated (only meaningful while an embed with a token is committed)
curl -s -w '\n-- HTTP %{http_code}\n' \
  "https://api.star-history.com/chart?repos=uda-lab/leray-hopf&type=date&legend=top-left&sealed_token=<YOUR_SEALED_TOKEN>"
# anonymous
curl -s -w '\n-- HTTP %{http_code}\n' \
  "https://api.star-history.com/chart?repos=uda-lab/leray-hopf&type=date"
```

Both diagnoses come from these two responses; no third "liveness" probe is needed, and a
homepage `200` proves nothing about the chart API. Do **not** try to establish API health by
charting some large well-known repository as a control: `api.star-history.com` computes charts
on demand and returns `500 Repo <owner>/<name>: timeout of 10000ms exceeded` for repositories
with many stars, so that check reports a false outage (verified 2026-08-02 against
`star-history/star-history`). An outage shows up directly on the two commands above, as a `5xx`
or a hang rather than a `401`/`404` with a specific body.

Classification:

| Observation | Meaning | Action |
|---|---|---|
| Authenticated → `401`, body `The provided GitHub access token is invalid or expired` | The sealed token's underlying PAT expired or was revoked | Regenerate (owner-only, below) |
| Anonymous → `404`, body `GitHub restricted starred-data access for uda-lab/leray-hopf.` | No anonymous route exists for this repository; a token is structurally required | Regenerate, or leave the section out |
| Either → `5xx`, a timeout body, or a hang | The chart API is unhealthy right now | Wait and retest; do not change the README |
| Authenticated → `200` | Token is live | Embed can be restored/kept |

A `404` **without** that body text is something else and should be investigated on its own
terms rather than assumed to be the restriction case.

### Restoring the embed

1. Sign in at [star-history.com](https://www.star-history.com/) and follow the
   [authenticated embed guide](https://www.star-history.com/blog/how-to-use-github-star-history/)
   to regenerate the embed for `uda-lab/leray-hopf`, creating a new fine-grained PAT scoped
   the same way (this repository only, read-only) if the old one expired. This step requires
   the repository owner — do not attempt to delegate it to an agent, and never route a raw
   PAT through a transcript, a log, or a tool argument.
2. Confirm the new token returns `200` using the authenticated command above **before**
   committing anything.
3. Re-create a `## Star History` section in the README containing the `<picture>` block (dark
   `source`, light `source`, and `img` fallback, all carrying the same `sealed_token`). Commit
   only the sealed token, never the raw PAT. Confirm with the owner first — removing the
   section was their explicit call, so restoring it is their decision, not a maintenance
   default.

If the token cannot be restored, leave the README as it is. A broken image is worse than no
section, and star counts are not evidence of mathematical quality (see the non-goals in issue
#230).
