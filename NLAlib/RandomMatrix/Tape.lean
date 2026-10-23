/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exact
public import NLAlib.RandomMatrix.Gaussian.Basic

/-!
# Test matrices drawn from a random tape

A program draws its random numbers from a tape, one i.i.d. sequence per distribution
(`docs/design/Computation.md`, D12), and stores an $N \times k$ test matrix column-major:
`NLAlib.Computation.tapeMatrix x off N k` has entry $(i, j)$ equal to tape value
$\mathit{off} + i + Nj$. With a standard Gaussian tape the matrix drawn is a standard Gaussian
matrix, and two matrices drawn from disjoint stretches of the tape are independent. These are the
laws the probabilistic theorems about programs need, so that a program that draws its own test
matrices inherits the tail bounds of its specification with no new probability.

## Main results

* `NLAlib.hasLaw_tapeMatrix_of_hasLaw_iidSequence`: a Gaussian tape draws a Gaussian matrix.
* `NLAlib.indepFun_tapeMatrix_of_hasLaw_iidSequence`: consecutive draws are independent.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

open Computation

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The tape positions of an $N \times k$ draw from position `off` are distinct. -/
private theorem injective_tapePos (off N k : ℕ) :
    Function.Injective fun p : Fin N × Fin k => off + p.1.1 + N * p.2.1 := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have h' : i.1 + N * j.1 = i'.1 + N * j'.1 := by simp only at h; omega
  obtain ⟨h1, h2⟩ := (Nat.add_mul_eq_add_mul_iff_of_lt i.2 i'.2).mp h'
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- **A Gaussian tape draws a Gaussian matrix**: if the tape $x$ is an i.i.d. sequence of standard
Gaussians, the $N \times k$ matrix drawn from it from position $\mathit{off}$, column-major, is a
standard Gaussian matrix. No printed source.
Result: tape-gaussian-matrix -/
theorem hasLaw_tapeMatrix_of_hasLaw_iidSequence {x : Ω → ℕ → ℝ}
    (hx : HasLaw x (iidSequence (gaussianReal 0 1)) μ) (off N k : ℕ) :
    HasLaw (fun ω => tapeMatrix (𝕜 := ℝ) (x ω) off N k) (gaussianMatrix (Fin N) (Fin k)) μ := by
  refine hasLaw_gaussianMatrix_of_hasLaw_uncurry ?_
  have h := hx.comp_of_injective (injective_tapePos off N k)
  convert h using 2 with ω
  funext ⟨i, j⟩
  simp only [tapeMatrix]
  rfl

/-- **Consecutive draws are independent**: if the tape $x$ is an i.i.d. sequence with a
probability law $\nu$, the $N \times k$ matrix drawn from position $0$ and the $N \times \ell$
matrix drawn after it, from position $Nk$, are independent. No printed source.
Result: tape-independent-draws -/
theorem indepFun_tapeMatrix_of_hasLaw_iidSequence {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {x : Ω → ℕ → ℝ} (hx : HasLaw x (iidSequence ν) μ) (N k ℓ : ℕ) :
    IndepFun (fun ω => tapeMatrix (𝕜 := ℝ) (x ω) 0 N k)
      (fun ω => tapeMatrix (𝕜 := ℝ) (x ω) (N * k) N ℓ) μ := by
  have : IsProbabilityMeasure μ := hx.isProbabilityMeasure_iff.mpr inferInstance
  have hind := ((hasLaw_infinitePi_iff (ν := fun _ : ℕ => ν)).mp hx).1
  have hST : Disjoint (Finset.range (N * k)) (Finset.Ico (N * k) (N * k + N * ℓ)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_range, Finset.mem_Ico] at ha hb
    omega
  have h := hind.indepFun_finset₀ _ _ hST fun n => (hx.aemeasurable.eval n)
  have hS : ∀ (i : Fin N) (j : Fin k), i.1 + N * j.1 ∈ Finset.range (N * k) := by
    intro i j
    simp only [Finset.mem_range]
    nlinarith [i.2, j.2]
  have hT : ∀ (i : Fin N) (j : Fin ℓ), N * k + i.1 + N * j.1 ∈
      Finset.Ico (N * k) (N * k + N * ℓ) := by
    intro i j
    simp only [Finset.mem_Ico]
    constructor
    · omega
    · nlinarith [i.2, j.2]
  have := h.comp (φ := fun v : Finset.range (N * k) → ℝ =>
      (Matrix.of fun (i : Fin N) (j : Fin k) => v ⟨_, hS i j⟩ : Matrix (Fin N) (Fin k) ℝ))
    (ψ := fun v : Finset.Ico (N * k) (N * k + N * ℓ) → ℝ =>
      (Matrix.of fun (i : Fin N) (j : Fin ℓ) => v ⟨_, hT i j⟩ : Matrix (Fin N) (Fin ℓ) ℝ))
    (by fun_prop) (by fun_prop)
  convert this using 1 <;> funext ω <;> ext i j <;> simp [tapeMatrix]

end NLAlib
