/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.Deriv

/-!
# Supporting lines of real functions

A function $f : \mathbb{R} \to \mathbb{R}$ has a supporting line on a set $s$ at a point $x$ when
some affine function through $(x, f(x))$ lies below $f$ on $s$:
$f(x) + c(y - x) \le f(y)$ for all $y \in s$. A convex function has one at every point of $s$
where it is differentiable; a function that is not convex can still have one at the points that
matter, which is how Jensen's inequality survives for "almost convex" functions (Tropp and Webber's
Lemma 9.4). Mathlib has no subgradient of a real function (searched `Subgradient`,
`SupportingLine`). Upstream candidate for `Mathlib.Analysis.Convex.Deriv`.

## Main definitions

* `HasSupportingLineOn`: a supporting line of $f$ on $s$ at $x$.

## Main results

* `ConvexOn.hasSupportingLineOn`: a convex function differentiable at $x \in s$ has a supporting
  line on $s$ at $x$, its tangent.
-/

@[expose] public section

-- Stage B1b

/-- $f$ has a **supporting line on $s$ at $x$**: there is a slope $c$ with
$$f(x) + c\,(y - x) \le f(y) \quad \text{for all } y \in s\,.$$
Nothing is assumed about $x \in s$; the consumers take $x \in s$ from elsewhere.
[TroppWebber2023, Lemma 9.4], there as the hypothesis of the almost-convex Jensen inequality. -/
def HasSupportingLineOn (f : ℝ → ℝ) (s : Set ℝ) (x : ℝ) : Prop :=
  ∃ c : ℝ, ∀ y ∈ s, f x + c * (y - x) ≤ f y

/-- **A convex function has a supporting line at each point of differentiability**: if $f$ is
convex on $s$, $x \in s$ and $f$ is differentiable at $x$, its tangent
$y \mapsto f(x) + f'(x)(y - x)$ supports it on $s$. -/
theorem ConvexOn.hasSupportingLineOn {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) {x : ℝ}
    (hx : x ∈ s) (hd : DifferentiableAt ℝ f x) : HasSupportingLineOn f s x := by
  sorry
