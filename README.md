# ordvec-formalization

[![Lean CI](https://github.com/Fieldnote-Echo/ordvec-formalization/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Fieldnote-Echo/ordvec-formalization/actions/workflows/lean_action_ci.yml)
[![No sorry](https://img.shields.io/badge/no%20sorry-audited-brightgreen)](https://github.com/Fieldnote-Echo/ordvec-formalization/actions/workflows/lean_action_ci.yml)

Lean 4 formalization of a finite constant-weight bitmap overlap model: under an
explicit monotone overlap signal contract, an overlap-tail admission rule is
Bayes-optimal, and its idealized uniform-null probability is exactly
hypergeometric.

The development now also packages supplied ordered-tail calibration with the
Bayes-optimal cutoff. This matters because the finite bitmap hypergeometric
calibration remains explicit, not a hidden claim about real deployment corpora.

This is a theory of **decision sufficiency through a quotient**, not
**representation completeness**. Full observations may still be essential for forming,
transforming, training, calibrating, and composing semantic representations.
They can carry margins, near-ties, residual features, confidence, and other
signals that matter for tasks beyond candidate admission. The formal result
says only that, for a binary admission decision satisfying the stated
statistical contract, the decision surface can factor through an order-like
quotient.

## Why This Matters

OrdVec-style candidate generation uses cheap overlap/popcount filters. This repo
checks the mathematical shape of that filter in a finite model:

```text
symmetry picks overlap
MLR / Bayes decision theory makes a threshold optimal
the constant-weight bitmap null calibrates that threshold event
```

The result is deliberately task-relative. It says that if relevance evidence for
a binary admission decision factors through overlap, and is monotone in that
overlap, then the optimal deterministic rule can be an overlap cutoff. It does
not say that ordinal signatures contain all semantic information, or that real
encoders automatically satisfy the model.

For implementations, the practical takeaway is narrow: under an empirically
validated monotone-overlap decision contract, candidate admission can be a
calibrated popcount threshold rather than an arbitrary accept/reject rule.

## Main Checked Result

```lean
OrdvecFormalization.exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
```

In words: for `K`-active bitmaps, when the null is uniform over all `K`-active
documents and the signal law is a finite exponential tilt by literal query
overlap, some literal overlap-tail rule has Bayes risk no larger than any
deterministic admission rule on the full constant-weight bitmap space. The same
tail event has the checked hypergeometric upper-tail probability under the
uniform bitmap null.

For the theorem-name surface, see [`docs/theorem-map.md`](docs/theorem-map.md).
For the module-by-module proof path, see [`docs/proof-spine.md`](docs/proof-spine.md).
For a reviewer-oriented summary, see [`docs/reviewer-brief.md`](docs/reviewer-brief.md).
For a developer-facing worked example, see
[`docs/rag-pipeline-guide.md`](docs/rag-pipeline-guide.md).

## Scope

This repository proves:

- finite deterministic Bayes-threshold optimality under explicit factorization
  and monotonicity assumptions;
- a group-theoretic maximal-invariant theorem explaining why bitmap overlap is
  the natural quotient under query-preserving coordinate relabelings;
- exact hypergeometric calibration for the idealized uniform constant-weight
  bitmap null.

It does not prove:

- real encoders satisfy the quotient, symmetry, or monotone-overlap contracts;
- the textbook hypergeometric null is the deployment null for real corpora;
- ordinal quotients are representation-complete for semantic tasks;
- Neyman-Pearson, UMP, Karlin-Rubin, randomized-test, asymptotic, or empirical
  calibration results.

## Build

Pinned to Lean `v4.28.0` and Mathlib `v4.28.0`.

```sh
lake update     # first run only; fetches Mathlib
make build      # runs lake build --wfail
make verify
make check-doc-names
make audit
make lint
```

GitHub Actions runs the same build, verification, documentation-name guard,
audit, and linter checks in
[`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml).
The `--wfail` build treats Lean warnings, including `sorry`, as failures; the
separate audit checks Lean sources for proof-placeholder contamination.

## License

Apache-2.0; see [`LICENSE`](LICENSE).
