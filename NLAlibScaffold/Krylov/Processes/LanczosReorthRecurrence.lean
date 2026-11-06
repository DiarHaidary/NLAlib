/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosReorthRecurrence
public import NLAlib.Krylov.Processes.ArnoldiRecurrence

/-!
# Exact Lanczos with full reorthogonalization is Lanczos for Hermitian matrices (scaffold)

Statements for `NLAlib/Krylov/Processes/LanczosReorthRecurrence.lean` (stage LANCZOS-REORTH,
design note `docs/design/Krylov-LanczosReorth.md` §2.3, ids A2, A3): for Hermitian $\mathbf{A}$
the two Gram–Schmidt passes subtract zero, so the reorthogonalized recurrence computes the
Lanczos states, basis and coefficients, and $\nu_j = \beta_j$; no breakdown hypothesis.

## Main results

* `Matrix.IsHermitian.lanczosReorthState_toLanczosState`,
  `Matrix.IsHermitian.lanczosReorthMatrix_eq`,
  `Matrix.IsHermitian.lanczosReorthState_nu`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- **Exact full reorthogonalization changes nothing for Hermitian matrices** (A2): for Hermitian
$\mathbf{A}$, every $\mathbf{b}$ and every $j$, the state of the reorthogonalized recurrence
restricts to the Lanczos state, and its stored vectors are the Lanczos vectors
$\mathbf{q}_0, \dots, \mathbf{q}_j$ (zero beyond $j$). No breakdown hypothesis: after breakdown
every vector involved is zero. [Paige1970]; [Parlett1998, §13.1] for the exact orthogonality.
Proof: strengthen to the invariant "`vecs i` $=$ `(lanczosState A b i).cur` for $i \le j$, zero
beyond, and the nonzero ones are orthonormal" and induct on $j$. In the step, $\mathbf{z}_j =
\mathbf{A}\mathbf{q}_j - \beta_j\mathbf{q}_{j-1} - \alpha_j\mathbf{q}_j$ is orthogonal to
$\mathbf{q}_0, \dots, \mathbf{q}_j$ in exact arithmetic: by `NLAlib.lanczosStep` it is
$\beta_{j+1}\mathbf{q}_{j+1}$, and the Lanczos vectors are the columns of the canonical basis
(`NLAlib.lanczosState_eq_lanczosC`, `Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix`), whose
distinct columns are orthogonal (`NLAlib.star_arnoldiMatrix_col_last_dotProduct_of_ne`, zero
columns included), so `NLAlib.cgsProject` returns its argument twice
(`Finset.sum_eq_zero`); the normalization is that of `NLAlib.lanczosStep`, and
`Function.update` extends the invariant. M, about 120 lines. -/
theorem _root_.Matrix.IsHermitian.lanczosReorthState_toLanczosState {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (j : ℕ) :
    (lanczosReorthState A b j).toLanczosState = lanczosState A b j ∧
      ∀ i, (lanczosReorthState A b j).vecs i =
        if i ≤ j then (lanczosState A b i).cur else 0 := by
  sorry

/-- **The reorthogonalized basis is the Lanczos basis** (A2) for Hermitian $\mathbf{A}$.
Proof: entrywise from `Matrix.IsHermitian.lanczosReorthState_toLanczosState` (the `cur` field),
`NLAlib.lanczosMatrix`, `NLAlib.lanczosReorthMatrix`. S, about 5 lines. -/
theorem _root_.Matrix.IsHermitian.lanczosReorthMatrix_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (q : ℕ) : lanczosReorthMatrix A b q = lanczosMatrix A b q := by
  sorry

/-- **The stored norm before orthogonalization is $\beta$** (A3): for Hermitian $\mathbf{A}$,
$\nu_{j+1} = \beta_{j+1}$ in exact arithmetic (nothing is subtracted).
Proof: unfold `NLAlib.lanczosReorthState` at $j + 1$ and `NLAlib.lanczosReorthStep`; the two
passes return $\mathbf{z}_j$ by the orthogonality in the proof of
`Matrix.IsHermitian.lanczosReorthState_toLanczosState`, so both fields are
$\|\mathbf{z}_j\|$. S, about 15 lines. -/
theorem _root_.Matrix.IsHermitian.lanczosReorthState_nu {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (j : ℕ) :
    (lanczosReorthState A b (j + 1)).nu = (lanczosReorthState A b (j + 1)).beta := by
  sorry

end NLAlib
