/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Orthonormal
public import NLAlib.Matrix.Factorizations.Triangular
public import NLAlib.Matrix.Norms.Spectral
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Normwise contracts for black-box matrix multiplication, QR and samplers

Fast dense algorithms are analysed against black-box primitives with normwise guarantees, not
against an implementation ([DemmelDumitriuHoltzKleinberg2007]; [DemmelDumitriuHoltz2007];
[Shah2024, Section 1.3]). This file states those guarantees as predicates on total functions, so
that one analysis holds for every implementation meeting them:

* `NLAlib.IsMatMulErr u τ Ω μ mm`: $\|\mathbf{A}\mathbf{B} - \mathrm{MM}(\mathbf{A},\mathbf{B})\|_2
  \le \mu(d)\,u \max(\|\mathbf{A}\|_2\|\mathbf{B}\|_2, \tau)$ when
  $\|\mathbf{A}\|_2\|\mathbf{B}\|_2 \le \Omega$, $d$ the largest dimension, and
  $\mathrm{MM}(\mathbf{A}, \mathbf{A}^{\mathsf{H}})$ exactly Hermitian;
* `NLAlib.IsQRErr u τ Ω μ qr`: the computed $(\mathbf{Q}, \mathbf{R})$ has $\mathbf{R}$ upper
  trapezoidal, and a unitary $\mathbf{Q}'$ and a matrix $\mathbf{A}'$ with
  $\mathbf{A}' = \mathbf{Q}'\mathbf{R}$ are within $\mu(d)\,u$ of $\mathbf{Q}$ and within
  $\mu(d)\,u\max(\|\mathbf{A}\|_2, \tau)$ of $\mathbf{A}$;
* `NLAlib.IsUnifSampler`, `NLAlib.IsNormalSampler`: a computed sample is a deterministic
  perturbation of an ideal one, the coupling of [Shah2024, Definitions 1.3, 1.4].

The floor $\tau$ and the range $\Omega$ are those of `NLAlib.IsRoundingFn`: $\tau = 0$ with an
unbounded exponent, and a bounded-exponent implementation meets the predicates with
$\tau > 0$ (design note `docs/design/Eigensolvers-HermitianDiagonalization.md`, §12).

## Main definitions

* `NLAlib.MatMulMap`, `NLAlib.QRMap`: the types of the routines.
* `NLAlib.IsMatMulErr`, `NLAlib.IsQRErr`, `NLAlib.IsUnifSampler`, `NLAlib.IsNormalSampler`.

## Main results

Witnesses (exact arithmetic meets every contract) and the bridge from a mixed absolute–relative
product bound are in the design note `docs/design/Eigensolvers-HermitianDiagonalization.md`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable (𝕜 : Type*) [RCLike 𝕜]

/-- A **matrix-multiplication routine**: a total function of two matrices indexed by `Fin`, of
compatible shapes, to a matrix of the shape of their product. -/
abbrev MatMulMap : Type _ :=
  ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) 𝕜 → Matrix (Fin m) (Fin n) 𝕜 → Matrix (Fin l) (Fin n) 𝕜

/-- A **QR routine**: a total function from an $m \times n$ matrix to a square $m \times m$ factor
and an $m \times n$ factor. -/
abbrev QRMap : Type _ :=
  ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) 𝕜 → Matrix (Fin m) (Fin m) 𝕜 × Matrix (Fin m) (Fin n) 𝕜

variable {𝕜}

/-- `IsMatMulErr u τ Ω μ mm`: **the routine `mm` multiplies with normwise error
$\mu(d)\,u$**: for all $\mathbf{A} \in \Bbbk^{l \times m}$, $\mathbf{B} \in \Bbbk^{m \times n}$
with $\|\mathbf{A}\|_2\|\mathbf{B}\|_2 \le \Omega$, and $d = \max(l, m, n)$,
$$\|\mathbf{A}\mathbf{B} - \mathrm{mm}(\mathbf{A}, \mathbf{B})\|_2 \le
\mu(d)\,u\max(\|\mathbf{A}\|_2\|\mathbf{B}\|_2, \tau) \,,$$
and $\mathrm{mm}(\mathbf{A}, \mathbf{A}^{\mathsf{H}})$ is exactly Hermitian.
[Shah2024, Definition 1.1], with $\tau = 0$ and no range there. -/
structure IsMatMulErr (u τ Ω : ℝ) (μ : ℕ → ℝ) (mm : MatMulMap 𝕜) : Prop where
  /-- The normwise error bound in range. -/
  specNorm_mul_sub_le : ∀ {l m n : ℕ} (A : Matrix (Fin l) (Fin m) 𝕜)
    (B : Matrix (Fin m) (Fin n) 𝕜), specNorm A * specNorm B ≤ Ω →
      specNorm (A * B - mm A B) ≤ μ (max l (max m n)) * u * max (specNorm A * specNorm B) τ
  /-- A product with its own conjugate transpose is computed exactly Hermitian. -/
  isHermitian_conjTranspose : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜),
    Matrix.IsHermitian (mm A Aᴴ)

/-- `IsQRErr u τ Ω μ qr`: **the routine `qr` computes a backward-stable QR factorization**: for
every $\mathbf{A} \in \Bbbk^{m \times n}$ with $\|\mathbf{A}\|_2 \le \Omega$ and
$(\mathbf{Q}, \mathbf{R}) = \mathrm{qr}(\mathbf{A})$, $d = \max(m, n)$, the factor
$\mathbf{R}$ is upper trapezoidal and there are a unitary $\mathbf{Q}'$ and a matrix
$\mathbf{A}' = \mathbf{Q}'\mathbf{R}$ with
$$\|\mathbf{Q}' - \mathbf{Q}\|_2 \le \mu(d)\,u \,, \qquad
\|\mathbf{A} - \mathbf{A}'\|_2 \le \mu(d)\,u\max(\|\mathbf{A}\|_2, \tau) \,.$$
[Shah2024, Definition 1.2], with $\tau = 0$ and no range there. -/
def IsQRErr (u τ Ω : ℝ) (μ : ℕ → ℝ) (qr : QRMap 𝕜) : Prop :=
  ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜), specNorm A ≤ Ω →
    IsUpperTrapezoidal (qr A).2 ∧
      ∃ Q' : Matrix (Fin m) (Fin m) 𝕜, HasOrthonormalCols Q' ∧
        specNorm (Q' - (qr A).1) ≤ μ (max m n) * u ∧
        specNorm (A - Q' * (qr A).2) ≤ μ (max m n) * u * max (specNorm A) τ

/-- `IsUnifSampler u unif`: **`unif` turns an ideal uniform sample into a computed one**: for a
scale $s \ge 0$ and $v \in [-1, 1]$, the computed sample $c = \mathrm{unif}(s, v)$ lies in
$[-s, s]$ and $\lvert sv - c \rvert \le s u$. With $v$ uniform on $[-1, 1]$ this is the coupling
of [Shah2024, Definition 1.3]. -/
def IsUnifSampler (u : ℝ) (unif : ℝ → ℝ → ℝ) : Prop :=
  ∀ s v : ℝ, 0 ≤ s → v ∈ Set.Icc (-1 : ℝ) 1 → |unif s v| ≤ s ∧ |s * v - unif s v| ≤ s * u

/-- `IsNormalSampler u c normal`: **`normal` turns an ideal complex Gaussian sample into a
computed one** with relative error $c\,u$: $\lvert z - \mathrm{normal}(z) \rvert \le c\,u
\lvert z \rvert$ for every $z \in \mathbb{C}$. With $z$ standard complex Gaussian this is the
coupling of [Shah2024, Definition 1.4]. -/
def IsNormalSampler (u c : ℝ) (normal : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ‖z - normal z‖ ≤ c * u * ‖z‖

end NLAlib
