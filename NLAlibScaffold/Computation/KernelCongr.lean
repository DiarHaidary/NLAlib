/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Computation.FirstOrder
public import NLAlib.Matrix.Computation.NewtonSchulzSignProgramTree
public import NLAlibScaffold.Computation.IndexBinder

/-!
# Complex kernels at index expressions (scaffold)

Statements for a new file `NLAlib/Computation/BLASCongr.lean` (stage COMPDYN S2a, design note
`docs/design/Computation-EighProgram.md`, §2.4): the run of a complex kernel of
`NLAlib/Computation/BLAS.lean`, and of the test and step blocks of the Newton–Schulz program,
depends on its size arguments only through their values. The run lemmas of the S1c/S1d pilot are
stated at constant sizes (`.const n`); inside `NLAlib.eighProg` the sizes are index variables bound
by index binders, and these statements bridge the two. Each follows from
`NLAlib.Computation.exec_eq_of_normIdx_eq`: the two statements have the same index normal form.

## Main results

* `NLAlib.Computation.exec_zcopy_congr`, …, `NLAlib.Computation.exec_ztraceRe_congr`: the
  kernels.
* `NLAlib.exec_newtonSchulzTestBlock_congr`, `NLAlib.exec_newtonSchulzStepBlock_congr`: the
  Newton–Schulz blocks.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C) (p : P)
  (st : St P K C)

/-- **`zcopy` at index expressions** runs as at the constants of their values. No printed source.
Proof: `NLAlib.Computation.exec_eq_of_normIdx_eq` (scaffold); the normal forms agree by
`simp only [NLAlib.Computation.zcopy, NLAlib.Computation.Builder.named,
NLAlib.Computation.Builder.forRange, NLAlib.Computation.Builder.ins,
NLAlib.Computation.Builder.stmt, NLAlib.Computation.Builder.run, NLAlib.Computation.Stmt.normIdx,
NLAlib.Computation.Instr.normIdx, NLAlib.Computation.Cell.normIdx,
NLAlib.Computation.IExp.eval_mul,
NLAlib.Computation.IExp.eval_const]` (the value of every index expression of the tree is a
function of the values of `m` and `n`). S, 4 lines. -/
theorem exec_zcopy_congr (m n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (Y : ℕ) (yo : IExp ℕ) :
    exec I (zcopy (ι := ι) p m n X xo Y yo).run st =
      exec I (zcopy (ι := ι) p (.const m.eval) (.const n.eval) X xo Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zcopy; rfl) st

/-- **`zidentity` at an index expression** runs as at the constant of its value. No printed source.
Proof: as `NLAlib.Computation.exec_zcopy_congr`, unfolding `NLAlib.Computation.zidentity` and
`NLAlib.Computation.zidx`. S, 4 lines. -/
theorem exec_zidentity_congr (n : IExp ℕ) (Y : ℕ) (yo : IExp ℕ) :
    exec I (zidentity (ι := ι) p n Y yo).run st =
      exec I (zidentity (ι := ι) p (.const n.eval) Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zidentity; rfl) st

/-- **`zneg` at index expressions** runs as at the constants of their values. No printed source.
Proof: as `NLAlib.Computation.exec_zcopy_congr`, unfolding `NLAlib.Computation.zneg`. S, 4
lines. -/
theorem exec_zneg_congr (m n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (Y : ℕ) (yo : IExp ℕ) :
    exec I (zneg (ι := ι) p m n X xo Y yo).run st =
      exec I (zneg (ι := ι) p (.const m.eval) (.const n.eval) X xo Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zneg; rfl) st

/-- **`zconjTranspose` at index expressions** runs as at the constants of their values. No printed
source.
Proof: as `NLAlib.Computation.exec_zcopy_congr`, unfolding `NLAlib.Computation.zconjTranspose`
and `NLAlib.Computation.zidx` (two nested loops). S, 5 lines. -/
theorem exec_zconjTranspose_congr (m n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (Y : ℕ) (yo : IExp ℕ) :
    exec I (zconjTranspose (ι := ι) p m n X xo Y yo).run st =
      exec I (zconjTranspose (ι := ι) p (.const m.eval) (.const n.eval) X xo Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zconjTranspose; rfl) st

/-- **`zhermShift` at an index expression** runs as at the constant of its value. No printed
source.
Proof: as `NLAlib.Computation.exec_zcopy_congr`, unfolding `NLAlib.Computation.zhermShift`,
`NLAlib.Computation.zmirror` and `NLAlib.Computation.zidx` (the inner loops run to `.var j`,
whose value is the same on both sides). S, 6 lines. -/
theorem exec_zhermShift_congr (n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (c : Cell ℕ ℕ) (Y : ℕ)
    (yo : IExp ℕ) :
    exec I (zhermShift (ι := ι) p n X xo c Y yo).run st =
      exec I (zhermShift (ι := ι) p (.const n.eval) X xo c Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zhermShift zmirror; rfl) st

/-- **`zhermScale` at an index expression** runs as at the constant of its value. No printed
source.
Proof: as `NLAlib.Computation.exec_zhermShift_congr`, unfolding `NLAlib.Computation.zhermScale`.
S, 6 lines. -/
theorem exec_zhermScale_congr (n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (c : Cell ℕ ℕ) (Y : ℕ)
    (yo : IExp ℕ) :
    exec I (zhermScale (ι := ι) p n X xo c Y yo).run st =
      exec I (zhermScale (ι := ι) p (.const n.eval) X xo c Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zhermScale zmirror; rfl) st

/-- **`zhermAvg` at an index expression** runs as at the constant of its value. No printed source.
Proof: as `NLAlib.Computation.exec_zhermShift_congr`, unfolding `NLAlib.Computation.zhermAvg`.
S, 6 lines. -/
theorem exec_zhermAvg_congr (n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (c : Cell ℕ ℕ) (Y : ℕ)
    (yo : IExp ℕ) :
    exec I (zhermAvg (ι := ι) p n X xo c Y yo).run st =
      exec I (zhermAvg (ι := ι) p (.const n.eval) X xo c Y yo).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold zhermAvg zmirror; rfl) st

/-- **`ztraceRe` at an index expression** runs as at the constant of its value. No printed source.
Proof: as `NLAlib.Computation.exec_zcopy_congr`, unfolding `NLAlib.Computation.ztraceRe`. S, 4
lines. -/
theorem exec_ztraceRe_congr (n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (dst : Cell ℕ ℕ) :
    exec I (ztraceRe (ι := ι) p n X xo dst).run st =
      exec I (ztraceRe (ι := ι) p (.const n.eval) X xo dst).run st := by
  exact exec_eq_of_normIdx_eq I (by unfold ztraceRe; rfl) st

end NLAlib.Computation

namespace NLAlib

open Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C) (p : P) (mm : ι)
  (st : St P K C)

/-- **The Newton–Schulz test block at an index expression** runs as at the constant of its value.
No printed source.
Proof: as `NLAlib.Computation.exec_zcopy_congr`, unfolding `NLAlib.newtonSchulzTestBlock`,
`NLAlib.Computation.zhermShift`, `NLAlib.Computation.zboxTest` (whose `ifThenElse` keeps its
cells, `NLAlib.Computation.Builder.ifThenElse`) and the kernel call's dimensions
(`List.map_cons`). S, 8 lines. -/
theorem exec_newtonSchulzTestBlock_congr (n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (W V : ℕ)
    (one lo hi f : Cell ℕ ℕ) :
    exec I (newtonSchulzTestBlock p mm n X xo W V one lo hi f).run st =
      exec I (newtonSchulzTestBlock p mm (.const n.eval) X xo W V one lo hi f).run st := by
  exact exec_eq_of_normIdx_eq I
    (by unfold newtonSchulzTestBlock zhermShift zmirror zboxTest; rfl) st

/-- **The Newton–Schulz step block at an index expression** runs as at the constant of its value.
No printed source.
Proof: as `NLAlib.exec_newtonSchulzTestBlock_congr`, unfolding `NLAlib.newtonSchulzStepBlock`,
`NLAlib.Computation.zhermShift`, `NLAlib.Computation.zneg` and `NLAlib.Computation.zhermAvg`.
S, 8 lines. -/
theorem exec_newtonSchulzStepBlock_congr (n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (W V : ℕ)
    (c : Cell ℕ ℕ) :
    exec I (newtonSchulzStepBlock p mm n X xo W V c).run st =
      exec I (newtonSchulzStepBlock p mm (.const n.eval) X xo W V c).run st := by
  exact exec_eq_of_normIdx_eq I
    (by unfold newtonSchulzStepBlock zhermShift zmirror zneg zhermAvg; rfl) st

end NLAlib
