/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import OrdvecFormalization.OverlapBayesOptimal
import OrdvecFormalization.BitmapCalibration

namespace OrdvecFormalization

/-!
# Compatibility checks for moved names

These checks ensure legacy aggregate imports still expose definitions that now
live in narrower modules.
-/

#check @finiteBayesRisk
#check @finiteCostedBayesRisk

#check @ConstantWeightBitmap
#check @constantWeightBitmapOverlapEvidence
#check @BitmapCut

end OrdvecFormalization
