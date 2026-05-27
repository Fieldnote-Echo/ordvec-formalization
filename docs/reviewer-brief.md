# Constant-Weight Bitmap Overlap Brief

This repository formalizes a finite decision-theoretic claim about
constant-weight bitmap overlap admission. It proves what follows when the stated
finite assumptions hold.

## The Claim

The checked theorem is:

```lean
OrdvecFormalization.exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
```

It says that, for `K`-active bitmaps in dimension `D`, if the null is uniform
over `K`-active bitmaps and the signal law is modeled as a canonical finite
exponential tilt of that law by literal bitmap overlap, then:

1. some overlap-tail rule is Bayes-optimal among all deterministic rules on the
   full constant-weight bitmap observation space;
2. under the uniform constant-weight bitmap null, that same threshold event
   has exactly the hypergeometric upper-tail probability.

The cost-sensitive version is:

```lean
OrdvecFormalization.exists_uniformBitmapOverlapTail_finiteCostedBayesRisk_le_and_hypergeomTail
```

The more general positive-base theorem is:

```lean
OrdvecFormalization.exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
```

There the Bayes-optimality result holds for any positive base law, while the
hypergeometric equation is a separate uniform-null tail calibration at the same
cutoff.

## Glossary

- `K`-active bitmap: a bitmap with exactly `K` active coordinates.
- Overlap-tail rule: accept a candidate iff bitmap overlap is at least a
  cutoff.
- Canonical overlap tilt: a signal model that exponentially reweights a base law
  by overlap evidence.
- Uniform constant-weight null: the uniform law over all `K`-active
  bitmaps.
- Hypergeometric tail: the exact probability, under that null, of clearing an
  overlap cutoff.

## Why This Is The Right Shape

The formalization treats admission as a finite statistical experiment:

```text
full observation Z
quotient Q(Z)
overlap evidence T(Q(Z))
binary admission decision
```

If the class likelihood ratio factors through the quotient evidence, then the
quotient loses no Bayes-relevant information for that decision. If that factored
evidence is monotone in overlap, the optimal deterministic rule is a threshold.

This is a quotient-sufficiency theorem, not a representation-learning theorem.

## Assumption Checklist

- finite observation space, specialized in the strongest theorem to the
  constant-weight bitmap subtype;
- fixed `D`, `K`, and query bitmap `q`;
- `q.card = K`;
- uniform `K`-active bitmap null for the strongest checked theorem;
- positive finite base law for the more general theorem;
- signal parameter strictly larger than null parameter;
- deterministic admission rules;
- idealized null calibration, not a deployment-corpus guarantee.

## What Builders Get

For an implementation that uses constant-weight overlap admission, the useful
engineering consequence is:

```text
when the empirical decision contract is approximately true,
candidate admission can be a calibrated popcount threshold
instead of a full-score computation.
```

The Lean development supports the rule shape and the idealized finite null:

- threshold form: optimal under the finite monotone evidence model;
- bitmap event: the theorem is stated over literal `K`-active bitmaps;
- null calibration: the threshold event has a checked hypergeometric tail under
  the uniform constant-weight bitmap law;
- costs: asymmetric false-accept / false-reject tradeoffs change the threshold,
  not the rule family.

## What Reviewers Should Check

The proof is intentionally decomposed:

- `FiniteExperiment.lean`: quotient-form optimality theorem for finite
  experiments.
- `FiniteDecision.lean`: monotone predicates on finite supports are thresholds.
- `MLR.lean`: monotone likelihood ratio makes Bayes admit predicates monotone.
- `BayesThreshold.lean`: Bayes thresholds minimize finite pointwise risk.
- `OrdinalSufficiency.lean`: quotient evidence plus monotonicity gives a
  threshold.
- `OverlapSufficiency.lean`: specializes the quotient bridge to actual overlap
  coordinates.
- `CanonicalTilt.lean`: finite exponential tilts make the likelihood ratio a
  monotone function of the evidence.
- `ExponentialTilt.lean`: ordered-support exponential tilts have MLR.
- `FNCH.lean`: actual-overlap FNCH weights match the shifted tilt.
- `OverlapNull.lean`: overlap-null theorem wrappers and compatibility aliases.
- `OverlapBayesOptimal.lean`: finite Bayes-risk and cost-sensitive wrappers for
  the canonical overlap-tilt theorem.
- `BitmapNull.lean`: exact hypergeometric bitmap overlap null.
- `BitmapSymmetry.lean`: query-stabilizer coordinate permutations preserve
  overlap, same-overlap equal-cardinality bitmaps lie in the same
  query-stabilizer orbit, and invariant constant-weight bitmap statistics
  factor through overlap.
- `BitmapCalibration.lean`: combines the canonical signal model with the exact
  bitmap null in the constant-weight bitmap theorem.

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
- Real encoders are not proved to satisfy the query-stabilizer symmetry
  assumption; the symmetry theorem identifies the canonical invariant when that
  assumption is appropriate.
- The hypergeometric null is not claimed to be the deployment null for every
  corpus or embedding model.
- Quotient sufficiency for one decision is not representation completeness.
- Full observations are not dismissed; they may be necessary for training,
  transformation, calibration, margins, near-ties, and targets outside the
  modeled decision.

## Empirical Contract

The formalization gives the conditions. A benchmark harness should audit them:

- Does `P(relevant | overlap = t)` increase with `t`?
- Is the estimated likelihood ratio `p(t | relevant) / p(t | nonrelevant)`
  monotone?
- Do presumed negatives follow the hypergeometric tail, or a fitted effective
  null?
- Where does the contract fail: broad queries, cross-domain admission,
  paraphrase, sparse signatures, or near-tie top-K instability?

The theory is strongest when paired with these diagnostics: Lean proves the
decision consequences, and experiments test whether modern encoders operate in
the regime where the contract is a good approximation.
