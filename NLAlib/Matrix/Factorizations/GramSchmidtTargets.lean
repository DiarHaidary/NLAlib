/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.GramSchmidt
public import NLAlib.Matrix.Factorizations.GramSchmidtProgramTree

/-!
# Gram–Schmidt as a program: the target

The target statement of Gram–Schmidt as a program, `NLAlib.MatrixFreeGramSchmidt`: the registered
tree `NLAlib.gramSchmidtProg.compiled` computes `NLAlib.gramSchmidtQ` in the matrix-free model,
within the counts `NLAlib.gramSchmidtCount` and $Nk + 3$ cells. The statement is the library's,
reviewed and registered in `docs/targets.toml`; a change to it, or to a definition it unfolds to,
needs the maintainer's approval (CONTRIBUTING §11). Its proof, `NLAlib.matrixFreeGramSchmidt`, is
in `NLAlib/Matrix/Factorizations/GramSchmidtProgram.lean`. Design: `docs/design/Computation.md`
(F1, F8).

## Main definitions

* `NLAlib.gramSchmidtCount`: the operation counts of the program.
* `NLAlib.MatrixFreeGramSchmidt`: the target.
-/

@[expose] public section

namespace NLAlib

open Computation

/-- The counts of `NLAlib.gramSchmidtProg` on an $N \times k$ matrix of full column
rank, with $J = k(k-1)/2$: $2NJ + Nk$ multiplications and additions, $NJ + Nk$ conjugations,
$J$ negations, $J + 2k$ literals, $k$ comparisons and square roots, and $Nk$ divisions. -/
noncomputable def gramSchmidtCount {P ι : Type} (p : P) (N k : ℕ) : OpCount P ι :=
  Finsupp.single (.bin p .mul) (2 * N * k.choose 2 + N * k) +
  Finsupp.single (.bin p .add) (2 * N * k.choose 2 + N * k) +
  Finsupp.single (.un p .conj) (N * k.choose 2 + N * k) +
  Finsupp.single (.un p .neg) (k.choose 2) + Finsupp.single (.lit p) (k.choose 2 + 2 * k) +
  Finsupp.single (.cmp p) k + Finsupp.single (.un p .sqrt) k +
  Finsupp.single (.bin p .div) (N * k)

/-- **The target of Gram–Schmidt as a program**, rank-revealing modified Gram–Schmidt in place,
in the matrix-free model. For every type of tags $P$ with decidable equality, every type of oracle
names $\iota$, every tag $p$ and every `RCLike` field $\Bbbk$, the registered tree
`gramSchmidtProg.compiled p` satisfies: for all sizes $N$ and $n = (k)$ and every $N \times k$
matrix $\mathbf{Y}$ over $\Bbbk$, held column-major in the one declared buffer at tag $p$ (the
initial state holds nothing else), under exact arithmetic with every oracle name meaning any
$N \times N$ matrix and any tape (the program uses neither), the program runs within the counts
`gramSchmidtCount p N k` and $Nk + 3$ cells at tag $p$, the declared buffer included (none at
any other tag), and ends with
`gramSchmidtQ Y`, the Gram–Schmidt factor of $\mathbf{Y}$ with zero columns where a column
depends on the earlier ones, in the declared buffer. No hypothesis on the rank of $\mathbf{Y}$. -/
def MatrixFreeGramSchmidt : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (𝕜 : Type) [RCLike 𝕜],
    MatrixFree (𝕜 := 𝕜) p (gramSchmidtProg.compiled (ι := ι) p) (fun _ _ => True)
      (fun N n => Matrix (Fin N) (Fin (n 0)) 𝕜)
      (fun _ _ Y => ![(flatten Y).map some]) (fun N n => gramSchmidtCount p N (n 0))
      (fun N n q => if q = p then N * n 0 + 3 else 0)
      (fun _ _ Y _ _ st => Holds st.store p 0 0 (gramSchmidtQ Y))

end NLAlib
