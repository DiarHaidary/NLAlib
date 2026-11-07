/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.GivensHessenberg

/-!
# The Givens unitary factor is Hessenberg (scaffold)

An addition to `NLAlib/Matrix/Factorizations/GivensHessenberg.lean` (stage SHIFTED-QR, wave W0,
design note `docs/design/Eigensolvers-ShiftedQR.md` §3.2, id Q0): the accumulated unitary factor
of Givens QR is upper Hessenberg, for any input. It makes the shifted QR step of
`NLAlib.shiftedQRStep` keep the Hessenberg form also when the shifted matrix is singular.

## Main results

* `NLAlib.isUpperHessenberg_givensHessenbergQ`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m p : ℕ}

/-- Step $k$ of Givens QR left-multiplies the conjugate transpose of the accumulated factor. -/
private theorem conjTranspose_givensHessenbergState_fst_succ (H : Matrix (Fin m) (Fin p) 𝕜)
    (k : ℕ) :
    ((givensHessenbergState H (k + 1)).1)ᴴ =
      givensHessenbergStep (givensHessenbergState H k).2 k * ((givensHessenbergState H k).1)ᴴ := by
  rw [show (givensHessenbergState H (k + 1)).1 = (givensHessenbergState H k).1 *
      (givensHessenbergStep (givensHessenbergState H k).2 k)ᴴ from rfl,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Invariant of the conjugate transpose of the accumulated factor after $k$ steps: its rows
above $k$ vanish beyond the superdiagonal, its row $k$ vanishes beyond column $k$, and its rows
from $k + 1$ on are unit vectors. -/
private theorem conjTranspose_givensHessenbergState_fst_invariant (H : Matrix (Fin m) (Fin p) 𝕜)
    (k : ℕ) :
    (∀ a b : Fin m, (a : ℕ) < k → (a : ℕ) + 1 < b →
      ((givensHessenbergState H k).1)ᴴ a b = 0) ∧
    (∀ a b : Fin m, (a : ℕ) = k → k < (b : ℕ) → ((givensHessenbergState H k).1)ᴴ a b = 0) ∧
    (∀ a b : Fin m, k + 1 ≤ (a : ℕ) →
      ((givensHessenbergState H k).1)ᴴ a b = if a = b then 1 else 0) := by
  induction k with
  | zero =>
    simp only [givensHessenbergState, Matrix.conjTranspose_one]
    refine ⟨fun a b h => absurd h (Nat.not_lt_zero _), fun a b _ hb => ?_, fun a b _ => rfl⟩
    exact Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega))
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [conjTranspose_givensHessenbergState_fst_succ]
    -- rows `k` and `k + 1` both vanish beyond column `k + 1`
    have hzero : ∀ b : Fin m, k + 1 < (b : ℕ) → ∀ c : Fin m,
        ((c : ℕ) = k ∨ (c : ℕ) = k + 1) → ((givensHessenbergState H k).1)ᴴ c b = 0 := by
      intro b hb c hc
      rcases hc with hc | hc
      · exact h2 c b hc (by omega)
      · rw [h3 c b (by omega), if_neg]
        intro h
        subst h
        omega
    refine ⟨fun a b ha hab => ?_, fun a b ha hab => ?_, fun a b ha => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha' | ha'
      · rw [givensHessenbergStep_mul_apply_of_ne (k := k) (a := a) _ _ (by omega) (by omega)]
        exact h1 a b ha' hab
      · rw [givensHessenbergStep_mul_apply_of_apply_eq_zero _ _ (b := b)
          (fun c hc => hzero b (by omega) c hc)]
        exact hzero b (by omega) a (Or.inl ha')
    · rw [givensHessenbergStep_mul_apply_of_apply_eq_zero _ _ (b := b)
        (fun c hc => hzero b hab c hc)]
      exact hzero b hab a (Or.inr ha)
    · rw [givensHessenbergStep_mul_apply_of_ne (k := k) (a := a) _ _ (by omega) (by omega)]
      exact h3 a b (by omega)

/-- **The unitary factor of Givens QR is upper Hessenberg**: for every
$\mathbf{H} \in \Bbbk^{m \times p}$, the factor $\mathbf{G}_0^{\mathsf{H}} \cdots
\mathbf{G}_{p-1}^{\mathsf{H}}$ (`NLAlib.givensHessenbergQ`), a product of rotations in the planes
$(k, k+1)$ in increasing order, vanishes below the first subdiagonal. No hypothesis on
$\mathbf{H}$: the planes, not the coefficients, give the pattern. [GolubVanLoan2013, §5.2.5].
Proof: induction on the number $k$ of steps in `NLAlib.givensHessenbergState`, with the
invariant that the first component $\mathbf{S}$ has $\mathbf{S}_{i,j} = 0$ for $j + 1 < i$ and
agrees with the identity in the columns $j > k$; right multiplication by
$\mathbf{G}_k^{\mathsf{H}}$ (`NLAlib.givensHessenbergStep`) mixes only the columns $k$ and $k+1$,
and column $k + 1$ of $\mathbf{S}$ is $\mathbf{e}_{k+1}$, so the new columns $k$, $k+1$ are
supported on rows $\le k + 1$ (`NLAlib.mul_givens_apply_left`, `NLAlib.mul_givens_apply_right`,
`NLAlib.mul_givens_apply_of_ne`; the identity case is trivial). M, about 40 lines. -/
theorem isUpperHessenberg_givensHessenbergQ (H : Matrix (Fin m) (Fin p) 𝕜) :
    IsUpperHessenberg (givensHessenbergQ H) := by
  intro i j hij
  have h := conjTranspose_givensHessenbergState_fst_invariant H p
  have hT : ((givensHessenbergState H p).1)ᴴ j i = 0 := by
    rcases lt_trichotomy (j : ℕ) p with hjp | hjp | hjp
    · exact h.1 j i hjp hij
    · exact h.2.1 j i hjp (by omega)
    · rw [h.2.2 j i (by omega), if_neg]
      intro hji
      subst hji
      omega
  rw [Matrix.conjTranspose_apply, star_eq_zero] at hT
  exact hT

end NLAlib
