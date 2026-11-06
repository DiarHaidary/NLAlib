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
# A floating-point machine with black-box matrix multiplication and QR

Fast dense algorithms are analysed against black-box primitives with normwise guarantees, not
against an implementation ([DemmelDumitriuHoltzKleinberg2007]; [DemmelDumitriuHoltz2007];
[Shah2024, Section 1.3]). This file fixes **what an algorithm may do with data**:
`NLAlib.FloatMachine F Su Sg` bundles every operation on stored numbers of an abstract type `F`
(rounded $+, -, \times, /$, exact negation, exact comparison, rounded conversion of a natural
number, exact conversion to a natural number by the floor, the constants $0$ and $1$), the
matrix-multiplication and QR black boxes on matrices of stored complex numbers `F × F` (real and
imaginary parts, as IEEE arithmetic stores them), and the two samplers, from ideal samples of
abstract types `Su`, `Sg` to stored numbers. An algorithm written generically over `F`, `Su` and
`Sg` touches data only through the machine: `F` has no arithmetic instance, so exact arithmetic on
computed values does not typecheck (design note
`docs/design/Eigensolvers-HermitianDiagonalization.md`, §2.0).

The analysis decodes stored numbers by `dec : F → ℝ` and states the machine's contract
`NLAlib.FloatMachine.IsAccurate`: each scalar operation returns a rounding of its exact result on
the decoded operands, one rounding per operation (`NLAlib.IsRoundingOf`: relative error $u$
above the floor $\tau$, in the range $\Omega$), negation, comparisons, the floor conversion,
$0$ and $1$ are exact, and the black boxes and samplers
meet the normwise contracts `NLAlib.IsMatMulErr`, `NLAlib.IsQRErr`, `NLAlib.IsUnifSampler`,
`NLAlib.IsNormalSampler` through the decoding. The floor $\tau$ and range $\Omega$ are $0$ and
arbitrary with an unbounded exponent; a bounded-exponent machine meets the contract with
$\tau > 0$ (§12 of the note).

## Main definitions

* `NLAlib.MatMulMap`, `NLAlib.QRMap`: the types of the routines on a type of stored entries.
* `NLAlib.IsRoundingOf`: $z$ is a rounding of $a$.
* `NLAlib.IsMatMulErr`, `NLAlib.IsQRErr`, `NLAlib.IsUnifSampler`, `NLAlib.IsNormalSampler`.
* `NLAlib.FloatMachine`, `NLAlib.decodeComplex`, `NLAlib.decodeMatrix`,
  `NLAlib.FloatMachine.IsAccurate`.

## Main results

The witnesses (the exact machine meets the contract) and the bridge from a mixed
absolute–relative product bound are in the design note
`docs/design/Eigensolvers-HermitianDiagonalization.md`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- A **matrix-multiplication routine** on matrices with entries in `K`, indexed by `Fin`, of
compatible shapes. -/
abbrev MatMulMap (K : Type*) : Type _ :=
  ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) K → Matrix (Fin m) (Fin n) K → Matrix (Fin l) (Fin n) K

/-- A **QR routine** on matrices with entries in `K`: an $m \times n$ matrix to a square
$m \times m$ factor and an $m \times n$ factor. -/
abbrev QRMap (K : Type*) : Type _ :=
  ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) K → Matrix (Fin m) (Fin m) K × Matrix (Fin m) (Fin n) K

/-- `IsRoundingOf u τ Ω a z`: **$z$ is a rounding of $a$** with unit roundoff $u$, floor $\tau$
and range $\Omega$: if $\lvert a \rvert \le \Omega$ then $\lvert a - z \rvert \le
u\max(\lvert a \rvert, \tau)$. At $\tau = 0$ this is the standard model [Higham2002, (2.4)]; a
floor $\tau > 0$ is the absolute error of gradual underflow, $\Omega$ the overflow threshold. -/
def IsRoundingOf (u τ Ω a z : ℝ) : Prop :=
  |a| ≤ Ω → |a - z| ≤ u * max |a| τ

variable {K 𝕜 : Type*} [RCLike 𝕜]

/-- `IsMatMulErr dec u τ Ω μ mm`: **the routine `mm` multiplies with normwise error
$\mu(d)\,u$**, read through the decoding `dec` of stored entries: for stored $\mathbf{A}$,
$\mathbf{B}$ with decodings $\bar{\mathbf{A}}$, $\bar{\mathbf{B}}$,
$\|\bar{\mathbf{A}}\|_2\|\bar{\mathbf{B}}\|_2 \le \Omega$ and $d$ the largest dimension,
$$\|\bar{\mathbf{A}}\bar{\mathbf{B}} - \overline{\mathrm{mm}(\mathbf{A}, \mathbf{B})}\|_2 \le
\mu(d)\,u\max(\|\bar{\mathbf{A}}\|_2\|\bar{\mathbf{B}}\|_2, \tau) \,,$$
and when $\bar{\mathbf{B}} = \bar{\mathbf{A}}^{\mathsf{H}}$ the decoded product is exactly
Hermitian. [Shah2024, Definition 1.1], with the identity decoding, $\tau = 0$ and no range
there. -/
structure IsMatMulErr (dec : K → 𝕜) (u τ Ω : ℝ) (μ : ℕ → ℝ) (mm : MatMulMap K) : Prop where
  /-- The normwise error bound in range. -/
  specNorm_mul_sub_le : ∀ {l m n : ℕ} (A : Matrix (Fin l) (Fin m) K)
    (B : Matrix (Fin m) (Fin n) K), specNorm (A.map dec) * specNorm (B.map dec) ≤ Ω →
      specNorm (A.map dec * B.map dec - (mm A B).map dec) ≤
        μ (max l (max m n)) * u * max (specNorm (A.map dec) * specNorm (B.map dec)) τ
  /-- A product with its own conjugate transpose is computed exactly Hermitian. -/
  isHermitian_of_map_eq_conjTranspose : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (B : Matrix (Fin n) (Fin m) K), B.map dec = (A.map dec)ᴴ → ((mm A B).map dec).IsHermitian

/-- `IsQRErr dec u τ Ω μ qr`: **the routine `qr` computes a backward-stable QR factorization**,
read through the decoding `dec`: for stored $\mathbf{A}$ with decoding $\bar{\mathbf{A}}$,
$\|\bar{\mathbf{A}}\|_2 \le \Omega$, $(\mathbf{Q}, \mathbf{R}) = \mathrm{qr}(\mathbf{A})$ and
$d = \max(m, n)$, the decoded $\bar{\mathbf{R}}$ is upper trapezoidal and there is a unitary
$\mathbf{Q}'$ with
$$\|\mathbf{Q}' - \bar{\mathbf{Q}}\|_2 \le \mu(d)\,u \,, \qquad
\|\bar{\mathbf{A}} - \mathbf{Q}'\bar{\mathbf{R}}\|_2 \le \mu(d)\,u\max(\|\bar{\mathbf{A}}\|_2,
\tau) \,.$$
[Shah2024, Definition 1.2], with the identity decoding, $\tau = 0$ and no range there. -/
def IsQRErr (dec : K → 𝕜) (u τ Ω : ℝ) (μ : ℕ → ℝ) (qr : QRMap K) : Prop :=
  ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) K), specNorm (A.map dec) ≤ Ω →
    IsUpperTrapezoidal ((qr A).2.map dec) ∧
      ∃ Q' : Matrix (Fin m) (Fin m) 𝕜, HasOrthonormalCols Q' ∧
        specNorm (Q' - (qr A).1.map dec) ≤ μ (max m n) * u ∧
        specNorm (A.map dec - Q' * (qr A).2.map dec) ≤
          μ (max m n) * u * max (specNorm (A.map dec)) τ

/-- `IsUnifSampler dec u unif`: **`unif` turns an ideal uniform seed into a computed shift**: for
a stored scale $s$ with $\bar s \ge 0$ and a seed $v \in [-1, 1]$, the computed
$c = \mathrm{unif}(s, v)$ has $\lvert \bar c \rvert \le \bar s$ and
$\lvert \bar s v - \bar c \rvert \le \bar s u$. With $v$ uniform on $[-1, 1]$ this is the coupling
of [Shah2024, Definition 1.3]. -/
def IsUnifSampler {F : Type*} (dec : F → ℝ) (u : ℝ) (unif : F → ℝ → F) : Prop :=
  ∀ (s : F) (v : ℝ), 0 ≤ dec s → v ∈ Set.Icc (-1 : ℝ) 1 →
    |dec (unif s v)| ≤ dec s ∧ |dec s * v - dec (unif s v)| ≤ dec s * u

/-- `IsNormalSampler dec u c normal`: **`normal` turns an ideal complex Gaussian sample into a
stored one** with relative error $c\,u$: $\lvert z - \overline{\mathrm{normal}(z)} \rvert \le c\,u
\lvert z \rvert$ for every $z \in \mathbb{C}$. With $z$ standard complex Gaussian this is the
coupling of [Shah2024, Definition 1.4]. -/
def IsNormalSampler {K : Type*} (dec : K → ℂ) (u c : ℝ) (normal : ℂ → K) : Prop :=
  ∀ z : ℂ, ‖z - dec (normal z)‖ ≤ c * u * ‖z‖

/-- A **floating-point machine** with stored numbers `F`, ideal seeds `Su` and ideal Gaussian
samples `Sg`: the only operations an algorithm written over it may apply to data. Stored complex
numbers are pairs `F × F` (real and imaginary parts).
[Shah2024, Sections 1.2, 1.3]. -/
structure FloatMachine (F Su Sg : Type*) where
  /-- The stored zero. -/
  zero : F
  /-- The stored one. -/
  one : F
  /-- Rounded conversion of a natural number. -/
  ofNat : ℕ → F
  /-- Rounded addition. -/
  add : F → F → F
  /-- Rounded subtraction. -/
  sub : F → F → F
  /-- Rounded multiplication. -/
  mul : F → F → F
  /-- Rounded division. -/
  div : F → F → F
  /-- Negation. -/
  neg : F → F
  /-- Comparison of stored numbers. -/
  le : F → F → Bool
  /-- Conversion to a natural number: the floor of a nonnegative stored number. -/
  toNat : F → ℕ
  /-- Matrix multiplication of stored complex matrices. -/
  mm : MatMulMap (F × F)
  /-- QR factorization of stored complex matrices. -/
  qr : QRMap (F × F)
  /-- The uniform sampler: a stored scale and an ideal seed to a stored shift. -/
  unif : F → Su → F
  /-- The normal sampler: an ideal Gaussian sample to a stored complex number. -/
  normal : Sg → F × F

/-- The **decoding of a stored complex number** $(x, y)$: $\bar x + i\bar y$. -/
def decodeComplex {F : Type*} (dec : F → ℝ) (z : F × F) : ℂ :=
  ⟨dec z.1, dec z.2⟩

/-- The **decoding of a stored complex matrix**, entrywise by `NLAlib.decodeComplex`. -/
def decodeMatrix {F : Type*} {m n : Type*} (dec : F → ℝ) (A : Matrix m n (F × F)) :
    Matrix m n ℂ :=
  A.map (decodeComplex dec)

/-- `M.IsAccurate dec u τ Ω μM μQ cN`: **the contract of a floating-point machine** at decoding
`dec`, unit roundoff $u$, floor $\tau$, range $\Omega$, black-box constants $\mu_{\mathrm{MM}}$,
$\mu_{\mathrm{QR}}$ and normal-sampler constant $c_{\mathrm N}$: zero and one are exact; rounded
conversion, addition, subtraction, multiplication and division (by a nonzero) return a rounding
(`NLAlib.IsRoundingOf`) of the exact result on the decoded operands; negation and comparisons are
exact; conversion to a natural number is the exact floor $\lfloor\bar x\rfloor_+$; the black boxes
and samplers meet `NLAlib.IsMatMulErr`, `NLAlib.IsQRErr`, `NLAlib.IsUnifSampler` and
`NLAlib.IsNormalSampler` through the decoding. [Shah2024, Section 1.2 and Definitions 1.1–1.4],
with componentwise complex storage. -/
structure FloatMachine.IsAccurate {F : Type*} (M : FloatMachine F ℝ ℂ) (dec : F → ℝ)
    (u τ Ω : ℝ) (μM μQ : ℕ → ℝ) (cN : ℝ) : Prop where
  /-- Zero is exact. -/
  dec_zero : dec M.zero = 0
  /-- One is exact. -/
  dec_one : dec M.one = 1
  /-- Conversion rounds. -/
  ofNat : ∀ k : ℕ, IsRoundingOf u τ Ω k (dec (M.ofNat k))
  /-- Addition rounds. -/
  add : ∀ x y, IsRoundingOf u τ Ω (dec x + dec y) (dec (M.add x y))
  /-- Subtraction rounds. -/
  sub : ∀ x y, IsRoundingOf u τ Ω (dec x - dec y) (dec (M.sub x y))
  /-- Multiplication rounds. -/
  mul : ∀ x y, IsRoundingOf u τ Ω (dec x * dec y) (dec (M.mul x y))
  /-- Division by a nonzero rounds. -/
  div : ∀ x y, dec y ≠ 0 → IsRoundingOf u τ Ω (dec x / dec y) (dec (M.div x y))
  /-- Negation is exact. -/
  dec_neg : ∀ x, dec (M.neg x) = -dec x
  /-- Comparisons are exact. -/
  le_iff : ∀ x y, M.le x y = true ↔ dec x ≤ dec y
  /-- Conversion to a natural number is the exact floor (`0` below zero), as IEEE truncation. -/
  toNat_eq : ∀ x, M.toNat x = ⌊dec x⌋₊
  /-- The matrix-multiplication contract. -/
  isMatMulErr : IsMatMulErr (decodeComplex dec) u τ Ω μM M.mm
  /-- The QR contract. -/
  isQRErr : IsQRErr (decodeComplex dec) u τ Ω μQ M.qr
  /-- The uniform-sampler contract. -/
  isUnifSampler : IsUnifSampler dec u M.unif
  /-- The normal-sampler contract. -/
  isNormalSampler : IsNormalSampler (decodeComplex dec) u cN M.normal

end NLAlib
