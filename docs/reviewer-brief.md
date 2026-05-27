# Reviewer And Builder Brief

This repository formalizes a finite decision-theoretic claim behind OrdVec-style
candidate admission. It does not claim that every embedding model satisfies the
assumptions. It proves what follows when the assumptions hold.

## The Claim

The checked headline theorem is:

```lean
OrdvecFormalization.ordvec_bitmap_uniform_null_headline_theorem
```

It says that, for `K`-active bitmap documents in dimension `D`, if the null is
uniform over `K`-active bitmap documents and relevance is modeled as a canonical
finite exponential tilt of that law by literal query-document overlap, then:

1. some overlap-tail rule is Bayes-optimal among all deterministic rules on the
   full bitmap-document observation space;
2. under the uniform constant-composition bitmap null, that same threshold event
   has exactly the hypergeometric upper-tail probability.

The cost-sensitive version is:

```lean
OrdvecFormalization.ordvec_bitmap_uniform_null_costed_headline_theorem
```

The more general positive-base theorem is:

```lean
OrdvecFormalization.ordvec_bitmap_headline_theorem
```

There the Bayes-optimality result holds for any positive base law, while the
hypergeometric equation is a separate uniform-null tail calibration at the same
cutoff.

## Glossary

- `K`-active bitmap: a bitmap with exactly `K` active coordinates.
- Overlap-tail rule: accept a candidate iff query-document overlap is at least a
  cutoff.
- Canonical overlap tilt: a signal model that exponentially reweights a base law
  by overlap evidence.
- Uniform constant-composition null: the uniform law over all `K`-active
  bitmaps.
- Hypergeometric tail: the exact probability, under that null, of clearing an
  overlap cutoff.

## Why This Is The Right Shape

Dense retrieval usually treats the encoder score as primitive. This
formalization treats retrieval as a finite statistical experiment:

```text
full observation Z
ordinal / bitmap quotient Q(Z)
overlap evidence T(Q(Z))
retrieval decision
```

If the relevance likelihood ratio factors through the quotient evidence, then
the quotient loses no Bayes-relevant information for the retrieval decision. If
that factored evidence is monotone in overlap, the optimal deterministic rule is
a threshold.

This is a sufficiency theorem, not a representation-learning theorem.

## Assumption Checklist

- finite document space;
- fixed `D`, `K`, and query bitmap `q`;
- `q.card = K`;
- uniform `K`-active bitmap null for the strongest headline theorem;
- positive finite base law for the more general theorem;
- signal parameter strictly larger than null parameter;
- deterministic admission rules;
- idealized null calibration, not a deployment-corpus guarantee.

## What Builders Get

For an edge-deployable RAG component, the useful engineering consequence is:

```text
when the empirical retrieval contract is approximately true,
candidate admission can be a calibrated popcount threshold
instead of another dense score computation.
```

The Lean development supports the rule shape and the idealized finite null:

- threshold form: optimal under the finite monotone evidence model;
- bitmap event: the theorem is stated over literal `K`-active bitmap documents;
- null calibration: the threshold event has a checked hypergeometric tail under
  the uniform constant-composition bitmap law;
- costs: asymmetric false-accept / false-reject tradeoffs change the threshold,
  not the rule family.

## What Reviewers Should Check

The proof is intentionally decomposed:

- `FiniteExperiment.lean`: quotient no-loss theorem for finite experiments.
- `OrdinalSufficiency.lean`: quotient evidence plus monotonicity gives a
  threshold.
- `CanonicalTilt.lean`: finite exponential tilts make the likelihood ratio a
  monotone function of the evidence.
- `BitmapNull.lean`: exact hypergeometric bitmap overlap null.
- `BitmapCalibration.lean`: combines the canonical signal model with the exact
  bitmap null in the headline theorem.

Run:

```sh
make build
make verify
make audit
make lint
```

The expected axiom baseline is:

```text
[propext, Classical.choice, Quot.sound]
```

## What Is Not Claimed

- Real encoders are not proved to satisfy quotient/factorization assumptions.
- The hypergeometric null is not claimed to be the deployment null for every
  corpus or embedding model.
- Ordinal retrieval sufficiency is not representation completeness.
- Dense magnitudes are not dismissed; they may be necessary for training,
  transformation, calibration, margins, near-ties, and non-retrieval targets.

## Empirical Contract

The formalization gives the conditions. A benchmark harness should audit them:

- Does `P(relevant | overlap = t)` increase with `t`?
- Is the estimated likelihood ratio `p(t | relevant) / p(t | nonrelevant)`
  monotone?
- Do presumed negatives follow the hypergeometric tail, or a fitted effective
  null?
- Where does the contract fail: broad queries, cross-domain retrieval,
  paraphrase, sparse signatures, or near-tie top-K instability?

The theory is strongest when paired with these diagnostics: Lean proves the
decision consequences, and experiments test whether modern encoders operate in
the regime where the contract is a good approximation.
