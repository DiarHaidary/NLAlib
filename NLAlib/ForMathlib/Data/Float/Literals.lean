/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Real.Basic
import all Init.Data.OfScientific

/-!
# Exact zero and one conversions in the Float model

Upstream candidates for the logical API of core's floating-point literals. The import of
all core definitions exposes the logical body of `Float.ofNat`, which is not exposed by a
normal import in Lean 4.33. No native evaluation or extra axiom is used.

## Main results

* `Float.isFinite_ofInt_zero`: the converted integer zero is finite.
* `Float.isFinite_ofNat_one`: the converted natural one is finite.
* `Float.div_ofInt_zero_ofNat_one`: the quotient is positive zero.
-/

@[expose] public section

namespace Float

/-- Converting the integer zero yields a finite binary64 word. -/
theorem isFinite_ofInt_zero : (Float.ofInt 0).isFinite = true := by decide

/-- Converting the natural one yields a finite binary64 word. -/
theorem isFinite_ofNat_one : (Float.ofNat 1).isFinite = true := by decide

/-- Dividing converted integer zero by converted natural one gives positive zero exactly. -/
theorem div_ofInt_zero_ofNat_one :
    Float.ofInt 0 / Float.ofNat 1 = Float.ofBits 0 := by
  decide

end Float
