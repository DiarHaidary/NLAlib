/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Column spaces of a column-partitioned matrix (deprecated names)

The two range facts about `Matrix.fromCols` moved to
`NLAlib.ForMathlib.Data.Matrix.ColumnRowPartitioned`, in the `Matrix` namespace, on 2026-10-15.
This file keeps the old names as deprecated aliases for one release; import the new file instead.
-/

@[expose] public section

namespace NLAlib

@[deprecated Matrix.range_mulVecLin_le_range_fromCols_left (since := "2026-10-15")]
alias range_mulVecLin_le_range_fromCols_left := Matrix.range_mulVecLin_le_range_fromCols_left

@[deprecated Matrix.mem_range_mulVecLin_fromCols_replicateCol (since := "2026-10-15")]
alias mem_range_mulVecLin_fromCols_replicateCol := Matrix.mem_range_mulVecLin_fromCols_replicateCol

end NLAlib
