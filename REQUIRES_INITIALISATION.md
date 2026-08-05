<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->

# REQUIRES INITIALISATION

**This repository is not finished being set up.** 16 substitution token(s) across 18 file(s) still have no value.

## Why this is not already done

This repo was created from `hyperpolymath/rsr-template-repo`. The mint
(`just repo-init`) fills every token that has a single mechanical answer —
owner, repo, author, dates, licence, branch — and it has done so here.

The tokens below are the ones it *deliberately cannot* answer. They need a
decision or a fact that exists only in your head: what this project is for,
what command builds it, which port the service listens on, whether a PGP key
is held at all. The template's own token vocabulary says as much — you cannot
sensibly answer "required invariants" in a thirty-second bootstrap.

They were left **visibly unfilled on purpose**. The alternatives were both
worse: inventing plausible values would put confident falsehoods into a
security policy and an architecture document, and silently deleting the
sections would hide the fact that a decision is owed. A visible gap is
honest; a fabricated answer is not.

## Do not delete this file until every item below is resolved

This file is the only marker that the work is outstanding. Deleting it early
does not finish the setup, it just conceals it — and the next person or agent
to arrive will reasonably assume the repo is complete.

- **If you are a person:** delete this file yourself once the last item is done.
- **If you are an agent:** resolve what you legitimately can, leave the rest,
  and delete this file only when no token below remains anywhere in the tree.
  Do not delete it to make a gate go green.

Re-running the estate top-up tool will remove this file automatically once
nothing is outstanding, so the safest way to finish is to fix the tokens and
let the check confirm it.

## Do these first

`.github/settings.yml` is applied to the forge by a GitHub App. An
unfilled token here can be written into the repository's real name or
description. This has fired before in this estate: illegal braces were
collapsed to dashes and a repo was renamed `-REPO-`, which then read as
deleted.

- `{{DESCRIPTION}}` — One-line description used in .github/settings.yml. HIGH PRIORITY: settings.yml is applied by a GitHub App, so an unfilled token here can be written into forge metadata verbatim.

## What is needed, and where it goes

### `{{ARGS}}`

Arguments for the justfile recipe this appears in.

Appears in:

- `.machine_readable/contractiles/Justfile`
- `Justfile`

### `{{AUTHOR_EMAIL_ALT}}`

Appears in:

- `.github/.mailmap`

### `{{AUTHOR_ORG}}`

Author's organisation. NOTE: no filled instance of this exists anywhere in the estate — consider deleting the field instead.

Appears in:

- `.machine_readable/self-validating/examples/project-metadata.k9.ncl`

### `{{DESCRIPTION}}`

One-line description used in .github/settings.yml. HIGH PRIORITY: settings.yml is applied by a GitHub App, so an unfilled token here can be written into forge metadata verbatim.

Appears in:

- `.github/settings.yml`

### `{{LICENSE}}`

SPDX identifier for this repo's licence.

Appears in:

- `container/Containerfile`
- `container/manifest.toml`
- `docs/developer/ABI-FFI-README.adoc`

### `{{OPENSSF_PROJECT_ID}}`

OpenSSF project ID, same registration.

Appears in:

- `docs/archive/TEMPLATE-STANDARDS-AUDIT.adoc`

### `{{PGP_KEY_URL}}`

Public URL the PGP key can be fetched from. Same caveat as PGP_FINGERPRINT.

Appears in:

- `.well-known/security.txt`

### `{{PORT}}`

Port the container service listens on.

Appears in:

- `container/Containerfile`
- `container/compose.toml`
- `container/deploy.k9.ncl`
- `container/entrypoint.sh`
- `container/manifest.toml`
- `container/vordr.toml`

### `{{PROJECT_DESCRIPTION}}`

One-line description, matching the forge description.

Appears in:

- `container/Containerfile`
- `container/manifest.toml`

### `{{PROJECT_PURPOSE}}`

One line: what this exists to do.

Appears in:

- `guix.scm`

### `{{PROJECT_UNIQUE_STRENGTH}}`

What this does that its alternatives do not.

Appears in:

- `.machine_readable/bot_directives/methodology.a2ml`

### `{{REGISTRY}}`

Container registry to publish to.

Appears in:

- `container/compose.toml`
- `container/ct-build.sh`
- `container/deploy.k9.ncl`

### `{{SECURITY_EMAIL}}`

Address for private vulnerability reports. Two competing values exist in the estate (`6759885+hyperpolymath@users.noreply.github.com` and `security@hyperpolymath.org`) — pick one deliberately.

Appears in:

- `.well-known/security.txt`

### `{{SERVICE_NAME}}`

Container service name.

Appears in:

- `container/.gatekeeper.yaml`
- `container/Containerfile`
- `container/compose.toml`
- `container/ct-build.sh`
- `container/deploy.k9.ncl`
- `container/entrypoint.sh`
- `container/manifest.toml`
- `container/vordr.toml`

### `{{VERSION}}`

Version/tag for the container image.

Appears in:

- `container/deploy.k9.ncl`
- `container/manifest.toml`
- `container/vordr.toml`

### `{{WEBSITE}}`

Project homepage URL, or delete the field if there is none.

Appears in:

- `.well-known/security.txt`

---

Generated by the estate top-up pass. Rationale and the governing rulings are
in `hyperpolymath/standards`; the token vocabulary is
`.machine_readable/ai/PLACEHOLDERS.adoc` in `rsr-template-repo`.
