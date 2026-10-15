/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Metrizable.Basic

/-!
# Second countability and metrizability of the matrix topology

Mathlib gives `Matrix m n R` the product topology (`Mathlib.Topology.Instances.Matrix`) but no
`SecondCountableTopology` instance, so the Borel-measurability instances that need it
(`MeasurableAdd₂`, `MeasurableMul₂`, through `ContinuousAdd.measurableMul₂` and its kin) are not
found for matrices under the global topology, and `Measurable.add`, `AEMeasurable.add` and
`Measurable.mul` do not apply to matrix-valued functions unless a matrix norm scope is opened.
This file adds the instance, for countable index types and second countable entries, and the
`MetrizableSpace` instance, for finite index types and metrizable entries, which Mathlib lacks too
(so that `measurable_of_tendsto_metrizable` and the other metrizable-target results apply to
matrix-valued limits). Upstream candidate for `Mathlib.Topology.Instances.Matrix`.

## Main results

* `Matrix.instSecondCountableTopology`: matrices over a second countable space, with countable
  index types, are second countable.
* `Matrix.instMetrizableSpace`: matrices over a metrizable space, with finite index types, are
  metrizable.
-/

@[expose] public section

namespace Matrix

/-- Matrices over a second countable space, with countable index types, form a second countable
space in the product topology. -/
instance instSecondCountableTopology {m n R : Type*} [Countable m] [Countable n]
    [TopologicalSpace R] [SecondCountableTopology R] : SecondCountableTopology (Matrix m n R) :=
  inferInstanceAs (SecondCountableTopology (m → n → R))

/-- Matrices over a metrizable space, with finite index types, form a metrizable space in the
product topology. -/
instance instMetrizableSpace {m n R : Type*} [Finite m] [Finite n] [TopologicalSpace R]
    [TopologicalSpace.MetrizableSpace R] : TopologicalSpace.MetrizableSpace (Matrix m n R) :=
  inferInstanceAs (TopologicalSpace.MetrizableSpace (m → n → R))

end Matrix
