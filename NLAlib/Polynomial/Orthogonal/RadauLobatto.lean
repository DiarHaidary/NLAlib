/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Gauss

/-!
# Gauss–Radau and Gauss–Lobatto rules

The Gauss–Radau rule of a measure $\mu$ with a prescribed node $c$ and $k$ free nodes puts the
free nodes at the zeros of the degree-$k$ orthogonal polynomial of the modified measure
$\lvert x - c\rvert\,d\mu(x)$ (`radauMeasure`) and takes interpolatory weights at the $k + 1$
nodes. For $\mu$ supported in $[a, b]$ and $c \in \{a, b\}$ it integrates every polynomial of
degree at most $2k$ exactly. The Gauss–Lobatto rule prescribes both endpoints $a$ and $b$, puts
$k$ free nodes at the zeros of the orthogonal polynomial of $\lvert(x - a)(x - b)\rvert\,d\mu(x)$
(`lobattoMeasure`), and integrates every polynomial of degree at most $2k + 1$ exactly.

Both rules are built on `interpolatoryQuadrature` and `gaussNodes`, as `gaussQuadrature` is, and
are defined for every measure, every prescribed node and every $k$. The Radau rule is also the
spectral measure of the Jacobi matrix of order $k + 1$ with its last diagonal entry modified so
that $c$ is an eigenvalue (`radauJacobiMatrix`, Golub's construction).

The theorems are in `NLAlibScaffold/Polynomial/Orthogonal/RadauLobatto.lean` until proved
(`docs/design/Polynomial-QuadratureRemainder.md`).

## Main definitions

* `NLAlib.radauMeasure`, `NLAlib.radauNodes`, `NLAlib.radauQuadrature`: the Radau rule.
* `NLAlib.lobattoMeasure`, `NLAlib.lobattoNodes`, `NLAlib.lobattoQuadrature`: the Lobatto rule.
* `NLAlib.radauJacobiAlpha`, `NLAlib.radauJacobiMatrix`: the modified Jacobi matrix.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-! ### The Gauss–Radau rule -/

/-- The **Radau modified measure** $\lvert x - c\rvert\,d\mu(x)$. For $\mu$ supported in
$[a, b]$ it is $(x - a)\,d\mu$ at $c = a$ and $(b - x)\,d\mu$ at $c = b$; its orthogonal
polynomials give the free nodes of the Radau rule with prescribed node $c$. -/
noncomputable def radauMeasure (μ : Measure ℝ) (c : ℝ) : Measure ℝ :=
  μ.withDensity fun x => ‖x - c‖ₑ

/-- The **nodes of the Radau rule** with prescribed node $c$ and $k$ free nodes: $c$ and the
Gauss nodes of order $k$ of `radauMeasure μ c`. For $\mu$ supported in $[a, b]$ and
$c \in \{a, b\}$ there are $k + 1$ of them when the modified measure is positive definite up to
degree $k$; otherwise there may be fewer, and the rule is $\mu$ itself. -/
noncomputable def radauNodes (μ : Measure ℝ) (c : ℝ) (k : ℕ) : Finset ℝ :=
  insert c (gaussNodes (radauMeasure μ c) k)

/-- The **Gauss–Radau rule** of $\mu$ with prescribed node $c$ and $k$ free nodes: the
interpolatory rule of $\mu$ at `radauNodes μ c k`. For $\mu$ supported in $[a, b]$ and
$c \in \{a, b\}$ it matches the first $2k + 1$ moments of $\mu$. Junk: for $c$ inside the
support it is still a measure on at most $k + 1$ points, with no exactness claimed. -/
noncomputable def radauQuadrature (μ : Measure ℝ) (c : ℝ) (k : ℕ) : Measure ℝ :=
  interpolatoryQuadrature μ (radauNodes μ c k)

/-- The Radau rule is a finite measure. -/
instance isFiniteMeasure_radauQuadrature (μ : Measure ℝ) (c : ℝ) (k : ℕ) :
    IsFiniteMeasure (radauQuadrature μ c k) := by
  unfold radauQuadrature
  infer_instance

/-! ### The Gauss–Lobatto rule -/

/-- The **Lobatto modified measure** $\lvert(x - a)(x - b)\rvert\,d\mu(x)$; for $\mu$ supported
in $[a, b]$ it is $(x - a)(b - x)\,d\mu$. -/
noncomputable def lobattoMeasure (μ : Measure ℝ) (a b : ℝ) : Measure ℝ :=
  μ.withDensity fun x => ‖(x - a) * (x - b)‖ₑ

/-- The **nodes of the Lobatto rule** on $[a, b]$ with $k$ free nodes: $a$, $b$ and the Gauss
nodes of order $k$ of `lobattoMeasure μ a b`. -/
noncomputable def lobattoNodes (μ : Measure ℝ) (a b : ℝ) (k : ℕ) : Finset ℝ :=
  insert a (insert b (gaussNodes (lobattoMeasure μ a b) k))

/-- The **Gauss–Lobatto rule** of $\mu$ on $[a, b]$ with $k$ free nodes: the interpolatory rule
of $\mu$ at `lobattoNodes μ a b k`. For $\mu$ supported in $[a, b]$, $a < b$, it matches the
first $2k + 2$ moments of $\mu$. -/
noncomputable def lobattoQuadrature (μ : Measure ℝ) (a b : ℝ) (k : ℕ) : Measure ℝ :=
  interpolatoryQuadrature μ (lobattoNodes μ a b k)

/-- The Lobatto rule is a finite measure. -/
instance isFiniteMeasure_lobattoQuadrature (μ : Measure ℝ) (a b : ℝ) (k : ℕ) :
    IsFiniteMeasure (lobattoQuadrature μ a b k) := by
  unfold lobattoQuadrature
  infer_instance

/-! ### The modified Jacobi matrix -/

/-- The **Radau corner** $\tilde\alpha_k = c - \beta_k\pi_{k-1}(c)/\pi_k(c)$ for $k \ge 1$ and
$\tilde\alpha_0 = c$: the last diagonal entry that makes $c$ a zero of the modified recurrence
$\tilde\pi_{k+1} = (x - \tilde\alpha_k)\pi_k - \beta_k\pi_{k-1}$, so an eigenvalue of
`radauJacobiMatrix μ c k`. Junk: $c$ when $\pi_k(c) = 0$ ($x/0 = 0$). [Golub1973, §7];
[GolubMeurant2010, Ch. 6] (locators to check). -/
noncomputable def radauJacobiAlpha (μ : Measure ℝ) (c : ℝ) : ℕ → ℝ
  | 0 => c
  | k + 1 => c - jacobiBeta μ (k + 1) * (orthogonalPolynomial μ k).eval c /
      (orthogonalPolynomial μ (k + 1)).eval c

/-- The **Radau Jacobi matrix** of order $k + 1$: the Jacobi matrix `jacobiMatrix μ (k + 1)`
with its last diagonal entry $\alpha_k$ replaced by `radauJacobiAlpha μ c k`. Its spectral
measure at $\sqrt{\mu(\mathbb{R})}\,\mathbf{e}_0$ is the Radau rule with $k$ free nodes.
[Golub1973, §7]; [GolubMeurant2010, Ch. 6] (locators to check). -/
noncomputable def radauJacobiMatrix (μ : Measure ℝ) (c : ℝ) (k : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun i j =>
    if i = Fin.last k ∧ j = Fin.last k then radauJacobiAlpha μ c k else jacobiMatrix μ (k + 1) i j

/-- The Radau corner at $k = 0$ is $c$, by definition. -/
theorem radauJacobiAlpha_zero (μ : Measure ℝ) (c : ℝ) : radauJacobiAlpha μ c 0 = c := rfl

/-- The Radau corner for $k \ge 1$, by definition. -/
theorem radauJacobiAlpha_succ (μ : Measure ℝ) (c : ℝ) (k : ℕ) :
    radauJacobiAlpha μ c (k + 1) = c - jacobiBeta μ (k + 1) * (orthogonalPolynomial μ k).eval c /
      (orthogonalPolynomial μ (k + 1)).eval c := rfl

end NLAlib
