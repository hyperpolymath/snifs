# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# bag-of-actions CI manifest for snifs — runs the proof gate + ABI conformance on
# OWNED compute (a `nix`-capable estate node, e.g. mesh-server-1) with ZERO GitHub
# Actions minutes, and posts each verdict back to the PR commit as a status that
# satisfies a branch-protection required check.
#
# Run on the node, from the snifs repo root, after `git fetch`/checkout of the PR head:
#
#   GITHUB_REPOSITORY=hyperpolymath/snifs GITHUB_SHA=<head-sha> \
#     mix bag.report /path/to/snifs/ci-checks.exs
#
# (`mix bag.report` lives in bag-of-actions; run it from there with this manifest
#  path, or `cd` into bag and pass an absolute path.)
#
# `required_cap: "nix"` routes each check to a node that has the `nix` capability;
# the commands fetch the actual toolchain (idris2/lean4/agda/zig/wasm-tools/python/just)
# via `nix shell` at run time. `github_context` is the required-status-check NAME the
# verdict posts to — point branch-protection's required contexts at these.
[
  %{
    check_id: "snifs-proofs",
    command: [
      "bash",
      "-lc",
      "nix shell nixpkgs#idris2 nixpkgs#lean4 nixpkgs#agda nixpkgs#just --command bash -c 'just proof-check-all'"
    ],
    required_cap: "nix",
    github_context: "bag / Formal proofs (owned compute)"
  },
  %{
    check_id: "snifs-abi",
    command: [
      "bash",
      "-lc",
      "nix shell nixpkgs#zig nixpkgs#wasm-tools nixpkgs#python3 nixpkgs#just --command bash -c 'just abi-conformance'"
    ],
    required_cap: "nix",
    github_context: "bag / ABI conformance (owned compute)"
  }
]
