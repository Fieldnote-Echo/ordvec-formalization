/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import OrdvecFormalization.OverlapNull

open scoped NNReal

namespace OrdvecFormalization

/-!
# Concrete theorem-shape examples

This file keeps a tiny concrete instantiation of the final paper-facing theorem
in the build so API drift is easy to spot.
-/

/-- A small feasible FNCH parameter set. -/
def toyParams : FNCHParams where
  N := 10
  k := 4
  draws := 3
  k_le_N := by norm_num
  draws_le_N := by norm_num

/-- A balanced prior for example statements. -/
noncomputable def balancedPrior : Prior where
  prob := (1 / 2 : ℝ≥0)
  le_one := by norm_num

#check overlapNull_threshold_isBayesOptimal toyParams
  (by norm_num : (0 : ℝ) < 1) balancedPrior

end OrdvecFormalization
