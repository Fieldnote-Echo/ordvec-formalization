# Proof Spine

This is the module-by-module path through the checked Lean development. The
front-door README stays short; this file is for reviewers who want to follow the
formal dependency story.

## Conceptual Stack

```text
Finite observations
  -> quotient by symmetry / factorization contract
  -> ordered overlap evidence
  -> monotone likelihood ratio
  -> Bayes-optimal threshold
  -> supplied calibration equality at the same cutoff
  -> exact finite bitmap-null calibration
```

The algebraic and decision-theoretic layers do different jobs:

- `BitmapSymmetry.lean` explains why literal bitmap overlap is the canonical
  invariant when the problem is invariant under query-preserving coordinate
  relabelings.
- `FiniteExperiment.lean`, `OrdinalSufficiency.lean`, `MLR.lean`, and
  `BayesThreshold.lean` explain why monotone quotient evidence gives an optimal
  deterministic threshold.
- `CalibratedEvidence.lean` packages a supplied ordered-tail calibration
  equality with the Bayes-optimal cutoff. It does not prove null adequacy or
  identify the calibrated event with a bitmap event.
- `BitmapIncidence.lean`, `BitmapNull.lean`, and `BitmapCalibration.lean`
  identify the bitmap event bridge and the exact hypergeometric tail under the
  idealized uniform constant-weight bitmap null.

## Dependency Shape

```text
BitmapSymmetry
  -> overlap is the query-stabilizer orbit classifier

FiniteExperiment
  -> FiniteBayesRisk
  -> OrdinalSufficiency / OverlapSufficiency
  -> CanonicalTilt / OverlapBayesOptimal

FiniteBayesRisk + OrdinalSufficiency
  -> CalibratedEvidence

BitmapNull
  -> BitmapIncidence

CalibratedEvidence + BitmapIncidence + OverlapBayesOptimal
  -> BitmapCalibration
  -> exact hypergeometric null calibration
```

Lean import order is not identical to conceptual dependence: `BitmapSymmetry`
imports bitmap definitions from `BitmapNull`, but it does not depend on
`BitmapCalibration`.

## Modules

1. `FiniteExperiment.lean`
   Defines finite positive laws, finite weighted risk, quotient pullbacks, and
   the quotient-form optimality theorem. If pointwise Bayes evidence or the
   likelihood ratio factors through a quotient, then some quotient-form admit
   set has no larger risk than any full-space deterministic rule. It also
   includes the finite witness that a quotient can preserve one decision target
   while discarding another.

2. `FiniteBayesRisk.lean`
   Gives Bayes-risk and cost-sensitive Bayes-risk names to the generic finite
   weighted-risk API.

3. `OrdinalSufficiency.lean`
   Adds ordered quotient evidence. If the full likelihood ratio is a monotone
   function of ordered quotient evidence, then some pulled-back ordinal
   threshold is Bayes-optimal among all deterministic full-space rules.

4. `CalibratedEvidence.lean`
   Combines the ordered threshold theorem with an externally supplied
   `OrderedTailCalibration`, returning one cutoff that is both Bayes-optimal and
   calibrated by the supplied equality. This layer is graph-neutral and does
   not prove empirical null adequacy.

5. `OverlapSufficiency.lean`
   Specializes the ordered quotient bridge to overlap coordinates, exposing the
   actual-overlap threshold set used by later theorems.

6. `CanonicalTilt.lean`
   Instantiates the factorization contract with a finite exponential family over
   arbitrary full observations. Tilting a positive base law by quotient-level
   overlap evidence makes the likelihood ratio a monotone function of that
   evidence.

7. `OverlapBayesOptimal.lean`
   Uses the finite Bayes-risk and cost-sensitive wrappers to expose the
   canonical overlap-tilt theorem in Bayes-risk form.

8. `BitmapIncidence.lean`
   Defines the constant-weight bitmap subtype, the uniform finite law on that
   subtype, literal bitmap overlap evidence, and the bridge showing pulled-back
   actual-overlap thresholds are literal bitmap overlap tail events.

9. `BitmapCalibration.lean`
   Connects the canonical overlap-tilt theorem to constant-weight bitmap
   observations. It proves that the Bayes-optimal pulled-back cutoff is the
   literal bitmap overlap tail event and that the uniform bitmap null assigns
   that event the corresponding hypergeometric upper-tail probability.

10. `BitmapSymmetry.lean`
   Defines coordinate permutations, the query stabilizer, and the induced action
   on bitmaps. It proves query-stabilizer permutations preserve overlap, that
   equal-cardinality bitmaps with equal query overlap lie in the same
   query-stabilizer orbit, and that every invariant constant-weight bitmap
   statistic factors through literal overlap.

11. `FiniteDecision.lean`
   Proves that every monotone predicate on a finite ordered support is
   represented by a threshold cut, including accept-all and reject-all boundary
   cuts.

12. `MLR.lean`
   States monotone likelihood ratio by cross multiplication and proves it makes
   weighted pointwise Bayes admission monotone. It also connects admission to
   the usual likelihood-ratio cutoff when denominators are positive.

13. `BayesThreshold.lean`
    Proves Bayes and cost-sensitive Bayes thresholds minimize finite pointwise
    risk by summing pointwise inequalities.

14. `ExponentialTilt.lean`
    Proves positive finite exponential tilts have monotone likelihood ratio as
    the tilt parameter increases.

15. `FNCH.lean`
    Connects literal actual-overlap Fisher noncentral hypergeometric weights to
    the shifted exponential-tilt implementation after normalization.

16. `OverlapNull.lean`
    Provides overlap-null theorem wrappers and compatibility aliases for the
    FNCH overlap threshold optimality surface.

17. `BitmapNull.lean`
    Defines constant-weight bitmap spaces, overlap fibers, tail events, and the
    inside/outside choice space. It proves the hypergeometric overlap-fiber
    cardinality and the exact upper-tail probability under the uniform finite
    bitmap law.

18. `Verify.lean`
    Checks the public theorem names and prints their axiom footprint.

## Reviewer Checks

Run:

```sh
make build
make verify
make check-doc-names
make audit
make lint
```

The expected axiom baseline is:

```text
[propext, Classical.choice, Quot.sound]
```
