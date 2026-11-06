/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Subst

/-!
# The identity implementation of kernels (scaffold)

Statements for `NLAlib/Computation/Subst.lean` (stage COMPDYN S1a, design note
`docs/design/Computation-DynamicPrograms.md`, §4.3 and "S1 implementation status"): keeping every
kernel call is an implementation, when the two interpretations have the same kernels, so
`NLAlib.Computation.RunsWithin.subst` applies to programs with kernel calls that substitute only
instructions or oracles.

## Main results

* `NLAlib.Computation.implementsKernel_self`: the identity implementation of kernels.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K : Type} [DecidableEq P]

/-- **The identity implementation of kernels**: if two interpretations over the same kernel names
have the same kernels and shapes, the concrete one charges one per operation, and `cost` charges a
kernel call itself, then keeping every kernel call implements the kernels of `I` under `I'`, with no
scratch. No printed source.
Proof: as `NLAlib.Computation.implementsInstr_self`: take
the state `st` with store `s₁` and the charge of the kernel call under the concrete
interpretation added; the run is
`simp only [exec, hker, hksh]` after rewriting `Interp.kcallStore` (its body reads only `kernel`
and `kshape`: `simp only [Interp.kcallStore, hker, hksh]` turns the call under `I'` into the one
under `I`, then `hs₁`, `Option.map_some`); counts by `hc'` and `hcost`; peaks by `le_max_left`.
S, about 12 lines. -/
theorem implementsKernel_self {I I' : Interp P ι K (OpCount P ι)} (hker : I'.kernel = I.kernel)
    (hksh : I'.kshape = I.kshape) (hc' : ∀ k, I'.charge k = Finsupp.single k 1)
    (cost : OpKind P ι → OpCount P ι)
    (hcost : ∀ p o ds, cost (.kcall p o ds) = Finsupp.single (.kcall p o ds) 1) :
    ImplementsKernel I I' .kcall cost (fun _ => 0) 0 := by
  intro o p dims ins outs st s₁ hs₁
  have hk : ∀ o p ds ins outs s, I'.kcallStore o p ds ins outs s = I.kcallStore o p ds ins outs s :=
    fun o p ds ins outs s => by simp only [Interp.kcallStore, hker, hksh]
  refine ⟨{ st with store := s₁, cnt := st.cnt + I'.charge (.kcall p o (dims.map IExp.eval)) },
    ?_, rfl, rfl, rfl, rfl, ?_, fun q => le_max_left _ _, le_max_left _ _⟩
  · simp only [exec, hk, hs₁, Option.map_some]
  · simp only [hc', hcost, le_refl]

end NLAlib.Computation
