/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Computation.IndexBinder

/-!
# Complex kernels at index expressions

The run of a complex kernel of `NLAlib/Computation/BLAS.lean` depends on its size arguments only
through their values. The run lemmas of the kernels are stated at constant sizes (`.const n`);
inside a program the sizes may be index variables bound by loops and index binders, and these
statements bridge the two. Each follows from `NLAlib.Computation.exec_eq_of_normIdx_eq`: the two
statements have the same index normal form.

## Main results

* `NLAlib.Computation.exec_zcopy_congr`, `NLAlib.Computation.exec_zidentity_congr`,
  `NLAlib.Computation.exec_zneg_congr`, `NLAlib.Computation.exec_zconjTranspose_congr`,
  `NLAlib.Computation.exec_zhermShift_congr`, `NLAlib.Computation.exec_zhermScale_congr`,
  `NLAlib.Computation.exec_zhermAvg_congr`, `NLAlib.Computation.exec_ztraceRe_congr`: the kernels
  at index expressions.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C) (p : P)
  (st : St P K C)

/-- `zcopy` at index expressions runs as at the constants of their values. No printed source. -/
theorem exec_zcopy_congr (m n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (Y : ℕ) (yo : IExp ℕ) :
    exec I (zcopy (ι := ι) p m n X xo Y yo).run st =
      exec I (zcopy (ι := ι) p (.const m.eval) (.const n.eval) X xo Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zcopy; rfl) st

/-- `zidentity` at an index expression runs as at the constant of its value. No printed
source. -/
theorem exec_zidentity_congr (n : IExp ℕ) (Y : ℕ) (yo : IExp ℕ) :
    exec I (zidentity (ι := ι) p n Y yo).run st =
      exec I (zidentity (ι := ι) p (.const n.eval) Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zidentity; rfl) st

/-- `zneg` at index expressions runs as at the constants of their values. No printed source. -/
theorem exec_zneg_congr (m n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (Y : ℕ) (yo : IExp ℕ) :
    exec I (zneg (ι := ι) p m n X xo Y yo).run st =
      exec I (zneg (ι := ι) p (.const m.eval) (.const n.eval) X xo Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zneg; rfl) st

/-- `zconjTranspose` at index expressions runs as at the constants of their values. No printed
source. -/
theorem exec_zconjTranspose_congr (m n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (Y : ℕ) (yo : IExp ℕ) :
    exec I (zconjTranspose (ι := ι) p m n X xo Y yo).run st =
      exec I (zconjTranspose (ι := ι) p (.const m.eval) (.const n.eval) X xo Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zconjTranspose; rfl) st

/-- `zhermShift` at an index expression runs as at the constant of its value. No printed
source. -/
theorem exec_zhermShift_congr (n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (c : Cell ℕ ℕ) (Y : ℕ)
    (yo : IExp ℕ) :
    exec I (zhermShift (ι := ι) p n X xo c Y yo).run st =
      exec I (zhermShift (ι := ι) p (.const n.eval) X xo c Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zhermShift zmirror; rfl) st

/-- `zhermScale` at an index expression runs as at the constant of its value. No printed
source. -/
theorem exec_zhermScale_congr (n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (c : Cell ℕ ℕ) (Y : ℕ)
    (yo : IExp ℕ) :
    exec I (zhermScale (ι := ι) p n X xo c Y yo).run st =
      exec I (zhermScale (ι := ι) p (.const n.eval) X xo c Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zhermScale zmirror; rfl) st

/-- `zhermAvg` at an index expression runs as at the constant of its value. No printed
source. -/
theorem exec_zhermAvg_congr (n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (c : Cell ℕ ℕ) (Y : ℕ)
    (yo : IExp ℕ) :
    exec I (zhermAvg (ι := ι) p n X xo c Y yo).run st =
      exec I (zhermAvg (ι := ι) p (.const n.eval) X xo c Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zhermAvg zmirror; rfl) st

/-- `ztraceRe` at an index expression runs as at the constant of its value. No printed
source. -/
theorem exec_ztraceRe_congr (n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (dst : Cell ℕ ℕ) :
    exec I (ztraceRe (ι := ι) p n X xo dst).run st =
      exec I (ztraceRe (ι := ι) p (.const n.eval) X xo dst).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold ztraceRe; rfl) st

end NLAlib.Computation
