# CI definitions

Immutable reusable build definitions for approved callers. This repository contains no application source, deployment credentials or application history.

The required API compiler workflow accepts only repository ID `1201945594` with either `signalorust/signalo` (owner ID `345015266`) or `All-projects-Rust/signalo` (owner ID `348736467`). The caller checkout must match its intrinsic GitHub source SHA. Definitions remain separate from caller source.

This definition host is `All-projects-Rust/ci-definitions`, repository ID `1435776151`, owner ID `348736467`. Publication and admission tooling must independently verify those host identifiers and pin the reviewed merged commit and workflow digest. The reusable workflow cannot embed its own future commit SHA. Callers must use the published 40-character commit, never a branch, a tag or a caller-controlled local definition.

Hosted scheduling is the default. Disposable scheduling additionally requires the exact target caller identity, explicit caller opt-in and separately admitted infrastructure. Publishing this definition does not activate infrastructure, transfer repositories or change caller permissions. No secrets are accepted by the workflow.

`Definition validation` runs on pull requests targeting `main` and pushes to `main`. It checks actual pre-checkout guard behavior, immutable compiler command and environment baselines, and the validation workflow contract using Python's standard library. It does not execute the application compiler in this repository.

Run locally:

```sh
python3 -I -B -m unittest discover -s tests -p 'test_*.py' -v
```

Preserve the protected publication history and existing pinned revisions. Updates require a reviewed pull request and successful `Definition validation`; changing a compiler command or identity requires deliberate review of the corresponding contract.
