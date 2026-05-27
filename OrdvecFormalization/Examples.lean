/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import Mathlib.Tactic.NormNum
import OrdvecFormalization.BitmapCalibration
import OrdvecFormalization.OverlapNull

open scoped NNReal

namespace OrdvecFormalization

/-!
# Concrete theorem-shape examples

This file keeps a tiny concrete instantiation of the final bitmap theorem
in the build so API drift is easy to spot.
-/

/-- A small feasible FNCH parameter set. -/
def exampleFNCHParams : FNCHParams where
  N := 10
  k := 4
  draws := 3
  k_le_N := by norm_num
  draws_le_N := by norm_num

/-- A balanced prior for example statements. -/
noncomputable def balancedPrior : Prior where
  prob := (1 / 2 : ℝ≥0)
  le_one := by norm_num

theorem balancedPrior_pos : 0 < balancedPrior.prob := by
  norm_num [balancedPrior]

/-- Unit false-decision costs for example statements. -/
def unitDecisionCosts : DecisionCosts where
  falseAccept := 1
  falseReject := 1

theorem unitDecisionCosts_falseReject_mul_balancedPrior_pos :
    0 < unitDecisionCosts.falseReject * balancedPrior.prob := by
  norm_num [balancedPrior, unitDecisionCosts]

/-- A tiny `1`-active bitmap query in three coordinates. -/
def exampleBitmapQuery : Finset (BitmapCoord 3) :=
  {0}

@[simp]
theorem card_exampleBitmapQuery : exampleBitmapQuery.card = 1 := by
  simp [exampleBitmapQuery]

#check overlapNull_threshold_bayesRisk_optimal_of_lt exampleFNCHParams
  (by norm_num : (0 : ℝ) < 1) balancedPrior

#check overlapNull_costed_threshold_bayesRisk_optimal_of_lt exampleFNCHParams
  (by norm_num : (0 : ℝ) < 1) balancedPrior unitDecisionCosts

#check exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail (D := 3) (K := 1)
  (by norm_num) (q := exampleBitmapQuery) card_exampleBitmapQuery
  (by norm_num : (0 : ℝ) < 1) balancedPrior balancedPrior_pos

#check exists_uniformBitmapOverlapTail_finiteCostedBayesRisk_le_and_hypergeomTail (D := 3) (K := 1)
  (by norm_num) (q := exampleBitmapQuery) card_exampleBitmapQuery
  (by norm_num : (0 : ℝ) < 1) balancedPrior unitDecisionCosts
  unitDecisionCosts_falseReject_mul_balancedPrior_pos

end OrdvecFormalization
