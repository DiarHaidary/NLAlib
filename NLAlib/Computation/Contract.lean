/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exact

/-!
# Error contracts on a value semantics

An error analysis of a program is done once, against a contract on the value semantics, and
holds for every semantics meeting it. `NLAlib.Computation.IsRelErrSem u dec safe sem` is Higham's
standard model as such a contract: at decoding `dec` (the real value of a stored word at a tag),
unit roundoff `u` and range condition `safe`, each operation family has an error clause and a
success clause. The success clauses matter: a theorem that asserts success (as
`NLAlib.Computation.RunsWithin` does) cannot be proved from error clauses alone, which the
semantics that always fails meets. Exact real arithmetic meets the full contract with $u = 0$ and
every value in range (`NLAlib.Computation.isRelErrSem_exactSem`); the always-failing semantics
does not (`NLAlib.Computation.not_isRelErrSem_failSem`). Design: `docs/design/Computation.md`
(D19, §7).

## Main definitions

* `NLAlib.Computation.IsRelErrSem`: the relative-error contract with success clauses.
* `NLAlib.Computation.BinOp.realOp`, `NLAlib.Computation.BinOp.IsArith`,
  `NLAlib.Computation.failSem`.

## Main results

* `NLAlib.Computation.isRelErrSem_exactSem`: exact arithmetic meets the contract.
* `NLAlib.Computation.not_isRelErrSem_failSem`: the always-failing semantics does not.
-/

@[expose] public section

namespace NLAlib.Computation

section Contracts
variable {P K : Type}

/-- Exact real meaning of the four arithmetic operations. -/
noncomputable def BinOp.realOp : BinOp → ℝ → ℝ → ℝ
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·) | .div => (· / ·) | _ => fun _ _ => 0

/-- The four arithmetic operations. -/
def BinOp.IsArith : BinOp → Prop
  | .add | .sub | .mul | .div => True
  | _ => False

/-- **The standard model as a contract on a value semantics**, at decoding `dec` (the real
value of a stored word at a tag), unit roundoff `u` and range condition `safe`. Each operation
family has an error clause and a success clause, since an error clause alone is met by the
semantics that always fails:
* arithmetic: the decoded result is the exact result times $1 + \delta$ with
  $\lvert \delta \rvert \le u$, and the operation succeeds when the exact result is in range and
  the divisor nonzero;
* literals: the same, for the rational value;
* `neg`, `conj`, `re`: exact and always defined on real decodings;
* `sqrt`: relative error, defined on nonnegative decodings;
* comparisons: exact on decoded values;
* `convert p q`: relative error at the target tag, defined when in range there.
[Higham2002, §2.2], the model (2.4) there for the arithmetic operations, here with success
clauses and for every operation family. -/
structure IsRelErrSem (u : P → ℝ) (dec : P → K → ℝ) (safe : P → ℝ → Prop)
    (sem : ScalarSem P K) : Prop where
  /-- Arithmetic has relative error at most the unit roundoff. -/
  bin_err : ∀ (p : P) (b : BinOp) (x y z : K), b.IsArith → sem.bin p b x y = some z →
    ∃ δ : ℝ, |δ| ≤ u p ∧ dec p z = b.realOp (dec p x) (dec p y) * (1 + δ)
  /-- Arithmetic succeeds in range, the divisor nonzero. -/
  bin_ok : ∀ (p : P) (b : BinOp) (x y : K), b.IsArith → (b = .div → dec p y ≠ 0) →
    safe p (b.realOp (dec p x) (dec p y)) → ∃ z, sem.bin p b x y = some z
  /-- Literals have relative error at most the unit roundoff. -/
  lit_err : ∀ (p : P) (q : ℚ) (z : K), sem.lit p q = some z →
    ∃ δ : ℝ, |δ| ≤ u p ∧ dec p z = (q : ℝ) * (1 + δ)
  /-- Literals in range succeed. -/
  lit_ok : ∀ (p : P) (q : ℚ), safe p q → ∃ z, sem.lit p q = some z
  /-- Negation is exact and defined. -/
  neg : ∀ (p : P) (x : K), ∃ z, sem.un p .neg x = some z ∧ dec p z = -dec p x
  /-- Conjugation is the identity on real decodings, and defined. -/
  conj : ∀ (p : P) (x : K), ∃ z, sem.un p .conj x = some z ∧ dec p z = dec p x
  /-- The real part is the identity on real decodings, and defined. -/
  re : ∀ (p : P) (x : K), ∃ z, sem.un p .re x = some z ∧ dec p z = dec p x
  /-- The square root has relative error at most the unit roundoff. -/
  sqrt_err : ∀ (p : P) (x z : K), sem.un p .sqrt x = some z →
    ∃ δ : ℝ, |δ| ≤ u p ∧ dec p z = √(dec p x) * (1 + δ)
  /-- The square root of a nonnegative decoding succeeds. -/
  sqrt_ok : ∀ (p : P) (x : K), 0 ≤ dec p x → ∃ z, sem.un p .sqrt x = some z
  /-- Equality tests are exact on decodings. -/
  cmp_eq : ∀ (p : P) (x y : K), sem.cmp p .eq x y = some (decide (dec p x = dec p y))
  /-- Strict comparisons are exact on decodings. -/
  cmp_lt : ∀ (p : P) (x y : K), sem.cmp p .lt x y = some (decide (dec p x < dec p y))
  /-- Comparisons are exact on decodings. -/
  cmp_le : ∀ (p : P) (x y : K), sem.cmp p .le x y = some (decide (dec p x ≤ dec p y))
  /-- Conversions have relative error at most the target's unit roundoff. -/
  convert_err : ∀ (p q : P) (x z : K), sem.convert p q x = some z →
    ∃ δ : ℝ, |δ| ≤ u q ∧ dec q z = dec p x * (1 + δ)
  /-- Conversions in range at the target succeed. -/
  convert_ok : ∀ (p q : P) (x : K), safe q (dec p x) → ∃ z, sem.convert p q x = some z

/-- **Exact real arithmetic meets the standard-model contract** with unit roundoff $0$, the identity
decoding and every value in range: `NLAlib.Computation.exactSem` over $\mathbb{R}$ satisfies every
error and success clause. [Higham2002, §2.2], the model (2.4) at $u = 0$.
Result: computation-exact-meets-contract -/
theorem isRelErrSem_exactSem : IsRelErrSem (P := P) (fun _ => 0) (fun _ x => x)
    (fun _ _ => True) (exactSem (𝕜 := ℝ)) where
  bin_err p b x y z hb h := by
    refine ⟨0, by simp, ?_⟩
    cases b <;> simp only [BinOp.IsArith] at hb <;> simp only [exactSem, Option.some.injEq] at h
    · subst h; simp [BinOp.realOp]
    · subst h; simp [BinOp.realOp]
    · subst h; simp [BinOp.realOp]
    · by_cases hy : y = 0
      · simp [hy] at h
      · simp only [hy, ↓reduceIte, Option.some.injEq] at h; subst h; simp [BinOp.realOp]
  bin_ok p b x y hb hdiv _ := by
    cases b <;> simp only [BinOp.IsArith] at hb <;> simp only [exactSem]
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · simp [hdiv rfl]
  lit_err p q z h := by
    simp only [exactSem, Option.some.injEq] at h
    exact ⟨0, by simp, by simp [← h]⟩
  lit_ok p q _ := ⟨_, rfl⟩
  neg p x := ⟨-x, rfl, rfl⟩
  conj p x := ⟨x, by simp [exactSem], rfl⟩
  re p x := ⟨x, by simp [exactSem], rfl⟩
  sqrt_err p x z h := by
    simp only [exactSem] at h
    split_ifs at h with hx
    simp only [Option.some.injEq] at h
    exact ⟨0, by simp, by simp [← h]⟩
  sqrt_ok p x hx := by simp [exactSem, hx]
  cmp_eq p x y := by simp only [exactSem]
  cmp_lt p x y := by simp only [exactSem, RCLike.im_to_real, and_self, ↓reduceIte]
  cmp_le p x y := by simp only [exactSem, RCLike.im_to_real, and_self, ↓reduceIte]
  convert_err p q x z h := by
    simp only [exactSem, Option.some.injEq] at h
    exact ⟨0, by simp, by simp [h]⟩
  convert_ok p q x _ := ⟨x, rfl⟩

/-- The semantics that always fails. -/
def failSem : ScalarSem P K :=
  ⟨fun _ _ => none, fun _ _ _ _ => none, fun _ _ _ => none, fun _ _ _ _ => none, fun _ _ _ => none⟩

/-- **The success clauses matter**: for a nonempty type of tags, the semantics that always fails
does not meet the standard-model contract, for any unit roundoff and decoding with every value in
range. No printed source.
Result: computation-failing-semantics -/
theorem not_isRelErrSem_failSem [Nonempty P] (u : P → ℝ) (dec : P → K → ℝ) :
    ¬ IsRelErrSem u dec (fun _ _ => True) (failSem (P := P) (K := K)) := fun h => by
  obtain ⟨z, hz⟩ := h.lit_ok (Classical.arbitrary P) 0 trivial
  simp [failSem] at hz

end Contracts

end NLAlib.Computation
