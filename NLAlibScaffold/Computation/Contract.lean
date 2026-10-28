/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Contract
public import NLAlibScaffold.Computation.Rounding

/-!
# The arithmetic part of an error contract

`NLAlib.Computation.IsArithErrSem err dec safe sem` is the part of an error contract that the
kernel analyses use, with the error of each arithmetic operation given by a relation
`err p b a z` between the exact result $a$ on the decoded operands and the decoded result $z$.
The standard model is the relation `NLAlib.Computation.RelErr` (relative error at most the unit
roundoff); a model with underflow adds an absolute term (`docs/design/Computation-Rounding.md`,
R6). The run lemmas of the kernels are proved once against this structure, so each error model
reuses them. `NLAlib.Computation.AddsZeroExactly dec sem` says that adding a decoded zero is
exact, as it is in IEEE arithmetic, in fixed-point arithmetic and in exact arithmetic; with it the
kernels, which accumulate from a zero, keep the constants of [Higham2002, Chapter 3].

To move into `NLAlib/Computation/Contract.lean` when proved. Design:
`docs/design/Computation-Rounding.md` (R3, R4).

## Main definitions

* `NLAlib.Computation.IsArithErrSem`: arithmetic error and success clauses for an error
  relation.
* `NLAlib.Computation.AddsZeroExactly`: adding a decoded zero is exact.
* `NLAlib.Computation.HoldsDecoded`: a buffer holds a real matrix through a decoding (to move
  into `NLAlib/Computation/Exact.lean`, next to `NLAlib.Computation.Holds`).

## Main results

* `NLAlib.Computation.IsRelErrSem.isArithErrSem`: the standard-model contract gives the
  arithmetic part with the relation `NLAlib.Computation.RelErr`.
* `NLAlib.Computation.IsRelErrSem.nonneg`: the unit roundoff is nonnegative.
* `NLAlib.Computation.addsZeroExactly_exactSem`: exact arithmetic adds zero exactly.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P K : Type}

/-- **The arithmetic part of an error contract**, at error relation `err` (the decoded result is
related to the exact result on the decoded operands), decoding `dec` and range condition `safe`:
* arithmetic satisfies the error relation, and succeeds in range with a nonzero divisor;
* the literal $0$ succeeds and decodes to $0$;
* negation and conjugation are exact and defined on real decodings.
`NLAlib.Computation.IsRelErrSem` gives it with the relation of relative error
(`NLAlib.Computation.IsRelErrSem.isArithErrSem`). [Higham2002, §2.2], the model (2.4) there,
with the error clause abstracted. -/
structure IsArithErrSem (err : P → BinOp → ℝ → ℝ → Prop) (dec : P → K → ℝ)
    (safe : P → ℝ → Prop) (sem : ScalarSem P K) : Prop where
  /-- Arithmetic satisfies the error relation. -/
  bin_err : ∀ (p : P) (b : BinOp) (x y z : K), b.IsArith → sem.bin p b x y = some z →
    err p b (b.realOp (dec p x) (dec p y)) (dec p z)
  /-- Arithmetic succeeds in range, the divisor nonzero. -/
  bin_ok : ∀ (p : P) (b : BinOp) (x y : K), b.IsArith → (b = .div → dec p y ≠ 0) →
    safe p (b.realOp (dec p x) (dec p y)) → ∃ z, sem.bin p b x y = some z
  /-- The literal zero succeeds and decodes to zero. -/
  lit_zero : ∀ p : P, ∃ z, sem.lit p 0 = some z ∧ dec p z = 0
  /-- Negation is exact and defined. -/
  neg : ∀ (p : P) (x : K), ∃ z, sem.un p .neg x = some z ∧ dec p z = -dec p x
  /-- Conjugation is the identity on real decodings, and defined. -/
  conj : ∀ (p : P) (x : K), ∃ z, sem.un p .conj x = some z ∧ dec p z = dec p x

/-- **Adding zero is exact**: whenever an addition at tag `p` succeeds and its first operand
decodes to $0$, the result decodes to the second operand. True of IEEE arithmetic, where
$0 + y = y$ exactly because every word is representable; false under flush-to-zero (a subnormal
$y$ flushes to $0$) and for a semantics that rounds words off the grid
($\mathrm{fl}(0 + y) = \mathrm{fl}(y) \ne y$). `NLAlib.Computation.gridSem` meets it together
with the standard model at $u > 0$. No printed source. -/
def AddsZeroExactly (dec : P → K → ℝ) (sem : ScalarSem P K) : Prop :=
  ∀ (p : P) (x y z : K), sem.bin p .add x y = some z → dec p x = 0 → dec p z = dec p y

/-- **The standard model gives the arithmetic part** of the contract with the relation of
relative error: if `sem` meets `NLAlib.Computation.IsRelErrSem` at unit roundoff `u`, it meets
`NLAlib.Computation.IsArithErrSem` with $\mathrm{err}(p, b, a, z)$ the statement that $z =
a(1 + \delta)$ for some $\lvert \delta \rvert \le u(p)$, and the zero literal is safe whenever
every value is. [Higham2002, §2.2], the model (2.4) there. -/
theorem IsRelErrSem.isArithErrSem {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    {sem : ScalarSem P K} (h : IsRelErrSem u dec safe sem) (hsafe : ∀ p, safe p 0) :
    IsArithErrSem (fun p _ => RelErr (u p)) dec safe sem := by
  sorry

/-- **The unit roundoff of a contract is nonnegative** at every tag: an operation that succeeds
has an error $\delta$ with $\lvert \delta \rvert \le u(p)$, and the literal $0$ succeeds when it is
in range. No printed source. -/
theorem IsRelErrSem.nonneg {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    {sem : ScalarSem P K} (h : IsRelErrSem u dec safe sem) {p : P} (hp : safe p 0) :
    0 ≤ u p := by
  sorry

/-- **Exact arithmetic adds zero exactly**: `NLAlib.Computation.exactSem` over $\mathbb{R}$, with
the identity decoding, satisfies `NLAlib.Computation.AddsZeroExactly`. No printed source. -/
theorem addsZeroExactly_exactSem : AddsZeroExactly (P := P) (fun _ x => x)
    (exactSem (𝕜 := ℝ)) := by
  sorry

/-- Buffer `b` holds the real $N \times k$ matrix $\mathbf{M}$ at tag `p` through the decoding
`dec`, column-major from offset `off`: each cell holds a word that decodes to the entry. The
decoded form of `NLAlib.Computation.Holds`. -/
def HoldsDecoded [DecidableEq P] {N k : ℕ} (s : Store P K) (dec : P → K → ℝ) (p : P) (b off : ℕ)
    (M : Matrix (Fin N) (Fin k) ℝ) : Prop :=
  ∀ (i : Fin N) (j : Fin k), ∃ w, s.read p b (off + i + N * j) = some w ∧ dec p w = M i j

end NLAlib.Computation
