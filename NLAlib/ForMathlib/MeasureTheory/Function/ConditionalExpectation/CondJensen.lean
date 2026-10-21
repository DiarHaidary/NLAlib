/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Conditional Jensen's inequality on a convex set that is not closed

Mathlib's `ConcaveOn.condExp_map_le` proves
$\mathbb{E}[\varphi(f) \mid m] \le \varphi(\mathbb{E}[f \mid m])$ for $\varphi$ concave and upper
semicontinuous on a closed convex set $s$. Closedness serves only to put the conditional mean of
$f$ in $s$; when the conditional mean is known to lie in $s$ almost surely, the inequality holds on
any convex set on which $\varphi$ is continuous. This is the form needed on the cone of
positive definite matrices, which is open (conditional Lieb,
`NLAlib/Probability/MatrixConcentration/ConditionalMGFBound.lean`). The conditional form of
`ConcaveOn.le_map_integral_of_integral_mem` (`NLAlib/ForMathlib/Analysis/Convex/Integral.lean`).
Upstream candidate for `Mathlib/MeasureTheory/Function/ConditionalExpectation/CondJensen.lean`.

## Main results

* `ConcaveOn.condExp_map_le_of_condExp_mem`: conditional Jensen for a concave function, on a
  convex set containing the conditional mean.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

variable {Ω E : Type*} {m mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure Ω}

/-- **Conditional Jensen's inequality**
$\mathbb{E}[\varphi(f) \mid m] \le \varphi(\mathbb{E}[f \mid m])$ almost everywhere, for $\varphi$
concave and continuous on a convex set $s$ that need not be closed, provided $f$ and
$\varphi \circ f$ are integrable, and $f$ and its conditional mean lie in $s$ almost everywhere.
Mathlib's `ConcaveOn.condExp_map_le` needs $s$ closed.
Port of the prototype lemma of the same name
(`NLAlib/ForMathlib/MeasureTheory/ConditionalJensen.lean`). -/
theorem ConcaveOn.condExp_map_le_of_condExp_mem (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {s : Set E} {φ : E → ℝ} {f : Ω → E} (hφ : ConcaveOn ℝ s φ) (hφc : ContinuousOn φ s)
    (hfs : ∀ᵐ ω ∂μ, f ω ∈ s) (hf : Integrable f μ) (hφf : Integrable (fun ω => φ (f ω)) μ)
    (hmean : ∀ᵐ ω ∂μ, μ[f | m] ω ∈ s) :
    μ[fun ω => φ (f ω) | m] ≤ᵐ[μ] fun ω => φ (μ[f | m] ω) := by
  let S : Set (E × ℝ) := {p | p.1 ∈ s ∧ p.2 ≤ φ p.1}
  let p : Ω → E × ℝ := fun ω => (f ω, φ (f ω))
  have hp : Integrable p μ := hf.prodMk hφf
  have hmem : ∀ᵐ ω ∂μ, μ[p | m] ω ∈ closure S :=
    hφ.convex_hypograph.closure.condExp_mem hm hp isClosed_closure
      (hfs.mono fun ω hω => subset_closure ⟨hω, le_rfl⟩)
  have hfst := (ContinuousLinearMap.fst ℝ E ℝ).comp_condExp_comm (m := m) hp
  have hsnd := (ContinuousLinearMap.snd ℝ E ℝ).comp_condExp_comm (m := m) hp
  filter_upwards [hmem, hfst, hsnd, hmean] with ω hω h₁ h₂ hmean
  change (μ[p | m] ω).1 = μ[f | m] ω at h₁
  change (μ[p | m] ω).2 = μ[fun ω => φ (f ω) | m] ω at h₂
  have heq : μ[p | m] ω = (μ[f | m] ω, μ[fun ω => φ (f ω) | m] ω) := Prod.ext h₁ h₂
  rw [heq] at hω
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hω
  have hφlim : Tendsto (fun k => φ (u k).1) atTop (𝓝 (φ (μ[f | m] ω))) :=
    (hφc _ hmean).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨(continuous_fst.tendsto _).comp hlim, Eventually.of_forall fun k => (hu k).1⟩)
  exact le_of_tendsto_of_tendsto' ((continuous_snd.tendsto _).comp hlim) hφlim
    fun k => (hu k).2
