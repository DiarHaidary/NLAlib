/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Contract
public import NLAlib.ForMathlib.Algebra.Order.Round

/-!
# A floating-point semantics meeting the standard-model contract

`NLAlib.Computation.gridSem t` is binary floating-point arithmetic with `t p` significant bits at
tag `p` and unbounded exponent: words are real numbers, a word decodes to its rounding to nearest
onto the grid of its tag (`Real.roundNearest`), and every operation rounds, at its (target) tag,
the exact result on the decoded operands, as `NLAlib.Computation.exactSem` computes it. It meets
the standard-model contract `NLAlib.Computation.IsRelErrSem` with unit roundoff $u_p = 2^{-t_p}$
and every value in range, and adds zero exactly (`NLAlib.Computation.AddsZeroExactly`), for
$t_p \ge 1$: so the hypotheses of the headline theorems of
`NLAlib/Computation/BLAS/RoundingErrors.lean` and `NLAlib/Computation/BLAS/Triangular.lean` hold
together for a semantics with $u > 0$, and those theorems are not about exact arithmetic only.

Decoding through the rounding makes every word represent a grid point, which is what
`NLAlib.Computation.AddsZeroExactly` needs: in a semantics whose words may be off the grid,
$\mathrm{fl}(0 + y) = \mathrm{fl}(y) \ne y$. Different precisions per tag make it a witness for
mixed precision through `convert` too. Design: `docs/design/Computation-Rounding.md` (R7).

## Main definitions

* `NLAlib.Computation.gridSem`: rounding to nearest onto a $t$-bit grid per tag.

## Main results

* `NLAlib.Computation.relErr_roundNearest`: rounding to nearest has relative error at most
  $2^{-t}$.
* `NLAlib.Computation.isRelErrSem_gridSem`: it meets the standard-model contract with
  $u_p = 2^{-t_p}$.
* `NLAlib.Computation.addsZeroExactly_gridSem`: it adds zero exactly.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P : Type}

/-- **Floating-point arithmetic on a grid**, `t p` significant bits at tag `p`, unbounded
exponent: a word $x$ at tag $p$ decodes to $\mathrm{fl}_p(x)$ (`Real.roundNearest (t p) x`), and
each operation is the operation of `NLAlib.Computation.exactSem` over $\mathbb{R}$ on the decoded
operands, rounded at its tag (a conversion at the target tag); comparisons are exact on the
decoded operands. -/
noncomputable def gridSem (t : P → ℕ) : ScalarSem P ℝ where
  lit p q := some (Real.roundNearest (t p) q)
  bin p b x y := ((exactSem (𝕜 := ℝ)).bin p b (Real.roundNearest (t p) x)
    (Real.roundNearest (t p) y)).map (Real.roundNearest (t p))
  un p o x := ((exactSem (𝕜 := ℝ)).un p o (Real.roundNearest (t p) x)).map
    (Real.roundNearest (t p))
  cmp p c x y := (exactSem (𝕜 := ℝ)).cmp p c (Real.roundNearest (t p) x)
    (Real.roundNearest (t p) y)
  convert p q x := some (Real.roundNearest (t q) (Real.roundNearest (t p) x))

/-- **Rounding to nearest has relative error at most $2^{-t}$**: $\mathrm{fl}(x) = x(1 + \delta)$
for some $\lvert \delta \rvert \le 2^{-t}$. [Higham2002, Theorem 2.2]. -/
theorem relErr_roundNearest (t : ℕ) (x : ℝ) : RelErr (2⁻¹ ^ t) x (Real.roundNearest t x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · refine ⟨0, by simp, ?_⟩
    simp [Real.roundNearest]
  · refine ⟨(Real.roundNearest t x - x) / x, ?_, by field_simp; ring⟩
    rw [abs_div, div_le_iff₀ (abs_pos.mpr hx), abs_sub_comm]
    exact Real.abs_sub_roundNearest_le t x

/-- **Floating-point arithmetic meets the standard model**: for $t_p \ge 1$ at every tag,
`NLAlib.Computation.gridSem t`, with the decoding $x \mapsto \mathrm{fl}_p(x)$, meets the contract
`NLAlib.Computation.IsRelErrSem` with unit roundoff $u_p = 2^{-t_p}$ and every value in range.
[Higham2002, Theorem 2.2], with the model (2.4) of §2.2 for each operation family.
Result: computation-grid-meets-contract -/
theorem isRelErrSem_gridSem (t : P → ℕ) (ht : ∀ p, 0 < t p) :
    IsRelErrSem (fun p => (2⁻¹ : ℝ) ^ t p) (fun p => Real.roundNearest (t p)) (fun _ _ => True)
      (gridSem t) := by
  have hfix p w := Real.roundNearest_roundNearest (ht p) w
  have hrel : ∀ p a, ∃ δ : ℝ, |δ| ≤ (2⁻¹ : ℝ) ^ t p ∧
      Real.roundNearest (t p) (Real.roundNearest (t p) a) = a * (1 + δ) := fun p a => by
    rw [hfix]
    exact (relErr_roundNearest (t p) a)
  refine
    { bin_err := ?_, bin_ok := ?_, lit_err := ?_, lit_ok := ?_, neg := ?_, conj := ?_, re := ?_,
      sqrt_err := ?_, sqrt_ok := ?_, cmp_eq := ?_, cmp_lt := ?_, cmp_le := ?_,
      convert_err := ?_, convert_ok := ?_ }
  · intro p b x y z hb h
    cases b <;> simp only [BinOp.IsArith] at hb <;>
      simp only [gridSem, exactSem, Option.map_some, Option.some.injEq] at h
    · subst h; exact hrel p _
    · subst h; exact hrel p _
    · subst h; exact hrel p _
    · split_ifs at h
      · simp at h
      · simp only [Option.map_some, Option.some.injEq] at h
        subst h; exact hrel p _
  · intro p b x y hb hdiv _
    cases b <;> simp only [BinOp.IsArith] at hb
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · simp [gridSem, exactSem, hdiv rfl]
  · intro p q z h
    simp only [gridSem, Option.some.injEq] at h
    subst h; exact hrel p _
  · intro p q _; exact ⟨_, rfl⟩
  · intro p x
    refine ⟨_, rfl, ?_⟩
    rw [hfix]
    exact Real.roundNearest_eq_self_of_mem_floatGrid
      (Real.neg_mem_floatGrid (Real.roundNearest_mem_floatGrid (ht p) x))
  · intro p x
    refine ⟨_, rfl, ?_⟩
    simp [hfix]
  · intro p x
    refine ⟨_, rfl, ?_⟩
    simp [hfix]
  · intro p x z h
    simp only [gridSem, exactSem] at h
    split_ifs at h
    · simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simpa using hrel p _
    · simp at h
  · intro p x hx
    simp [gridSem, exactSem, hx]
  · intro p x y; simp [gridSem, exactSem]
  · intro p x y; simp [gridSem, exactSem]
  · intro p x y; simp [gridSem, exactSem]
  · intro p q x z h
    simp only [gridSem, Option.some.injEq] at h
    subst h; exact hrel q _
  · intro p q x _; exact ⟨_, rfl⟩

/-- Floating-point arithmetic adds zero exactly: for $t_p \ge 1$ at every tag,
`NLAlib.Computation.gridSem t`, with the decoding $x \mapsto \mathrm{fl}_p(x)$, satisfies
`NLAlib.Computation.AddsZeroExactly`: if $x$ decodes to $0$, then $x \oplus y$ decodes to the
decoding of $y$, since that is a grid point and rounding fixes it. No printed source. -/
theorem addsZeroExactly_gridSem (t : P → ℕ) (ht : ∀ p, 0 < t p) :
    AddsZeroExactly (fun p => Real.roundNearest (t p)) (gridSem t) := by
  intro p x y z h hx
  simp only [gridSem, exactSem, hx, zero_add, Option.map_some, Option.some.injEq] at h
  subst h
  simp only [Real.roundNearest_roundNearest (ht p)]

end NLAlib.Computation
