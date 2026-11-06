/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosReorthProgramRounding
public import NLAlib.Krylov.Processes.LanczosReorthRecurrence
public import NLAlib.Computation.StaticCost
public import NLAlib.Matrix.Computation.MatvecRoutine
public import NLAlibScaffold.Matrix.Computation.ClassicalGramSchmidt
public import NLAlibScaffold.Krylov.FinitePrecision.LanczosReorthSpectral
public import NLAlib.Krylov.Processes.LanczosProgramRounded
public import NLAlib.Krylov.Processes.LanczosOracleProgramRounded

/-!
# Lanczos with full reorthogonalization as a program: exact and rounded runs (scaffold)

Statements for the programs of `NLAlib/Krylov/Processes/LanczosReorthProgramTree.lean` (stage
LANCZOS-REORTH, design note `docs/design/Krylov-LanczosReorth.md` §2, ids G3–G8): the exact run
of the stored-matrix tree (the drafted target's output clause; the target itself is registered by
the maintainer), its static count, the rounded run of the generic loop for any certified product
and orthogonalization routine families, the CGS2 trees (stored and oracle), and their composition
with the backward model and interlacing. Patterned on
`NLAlib.LanczosImplementation.exec_rounded_compiled`
and `NLAlib.LanczosOracleImplementation.exec_rounded_compiled`; the run-time handles are
`work` $= 8$, `scalars` $= 9$, `coef` $= 10$, the matrix slot $7$.

## Main results

* `NLAlib.lanczosReorthProg.exec_storedInterp_compiled` (G3),
  `NLAlib.lanczosReorthProg.staticCost_count_le` (G4).
* `NLAlib.LanczosReorthImplementation.exec_rounded_loop` (G5).
* `NLAlib.LanczosReorthImplementation.exec_rounded_compiled` (G6),
  `NLAlib.LanczosReorthImplementation.exec_rounded_oracle_compiled` (G6o).
* `NLAlib.LanczosReorthImplementation.exec_rounded_compiled_backward` (G7),
  `NLAlib.LanczosReorthImplementation.exec_rounded_compiled_interlacing` (G8).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

/-- **The exact run of the stored-matrix tree** (G3): under `NLAlib.Computation.storedInterp` (exact
arithmetic, the matrix as ROM, column-major), from the declared inputs, the compiled tree
succeeds and its buffers hold $\mathbf{b}$, the basis `NLAlib.lanczosReorthMatrix`, the
coefficients $\alpha_j$, $\beta_j$, the input norm, the last previous vector and the norms
$\nu_{j+1}$ of `NLAlib.lanczosReorthState`, for every real matrix (no symmetry or breakdown
premise). The output clause of the drafted target `StoredEntriesLanczosReorth`
(design note §2.3); counts are G4. No printed source.
Proof: `NLAlib.lanczosReorthProg.toStmt_compiled`; then the proof of main's stored-entries
Lanczos target (in `NLAlib/Krylov/Processes/LanczosProgram.lean`) step for step, with the loop
invariant
extended by the basis columns $0..j$ and `nu`, and one more phase per step: the extra `nrm2` and
`NLAlib.Computation.exec_cgs2_exactSem` at $j + 1$ columns, matching `NLAlib.cgsProject` twice
(sums over `Finset.range (j + 1)` against `Matrix.mulVec` of the stored columns); zero branch and
zero continuation as in the plain proof (after breakdown every later vector, coefficient and
correction is $0$). L, about 700 lines; intermediate lemmas: the loop invariant, one step, the
initialization (reuse `NLAlib/Krylov/Processes/LanczosProgramInitialization.lean`). -/
theorem lanczosReorthProg.exec_storedInterp_compiled {P ι : Type} [DecidableEq P] (tag : P)
    (N q : ℕ) (b : Fin N → ℝ) (vals : ℕ → ℝ) (ξ : Dist → ℕ → ℝ) :
    ∃ out : St P ℝ (OpCount P ι),
      (lanczosReorthProg.compiled (ι := ι) tag).exec (storedInterp (N ^ 2) vals ξ tag) N ![q]
          (inputState tag (List.ofFn ![(Array.ofFn b).map some,
            Array.replicate (N * (q + 1)) none, Array.replicate q none,
            Array.replicate (q + 1) none, Array.replicate 1 none, Array.replicate N none,
            Array.replicate q none])) = some out ∧
      Holds out.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
      Holds out.store tag 1 0
        (lanczosReorthMatrix (fun i j : Fin N => vals (i + N * j)) b (q + 1)) ∧
      Holds out.store tag 2 0 (fun (j : Fin q) (_ : Fin 1) =>
        lanczosAlpha (fun i j : Fin N => vals (i + N * j))
          (lanczosReorthState (fun i j : Fin N => vals (i + N * j)) b j).toLanczosState) ∧
      Holds out.store tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) =>
        (lanczosReorthState (fun i j : Fin N => vals (i + N * j)) b j).beta) ∧
      out.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
      Holds out.store tag 5 0 (fun i (_ : Fin 1) =>
        (lanczosReorthState (fun i j : Fin N => vals (i + N * j)) b q).prev i) ∧
      Holds out.store tag 6 0 (fun (j : Fin q) (_ : Fin 1) =>
        (lanczosReorthState (fun i j : Fin N => vals (i + N * j)) b ((j : ℕ) + 1)).nu) := by
  sorry

private lemma sum_map_range_eq_finsetSum (f : ℕ → ℕ) (q : ℕ) :
    (List.map f (List.range q)).sum = ∑ x ∈ Finset.range q, f x := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private lemma two_mul_sum_range_id_add (q : ℕ) : 2 * ∑ x ∈ Finset.range q, x + q = q * q := by
  induction q with
  | zero => simp
  | succ q ih => rw [Finset.sum_range_succ]; nlinarith

/-- **The static count of the stored-matrix tree** (G4): every component of the static operation
count of `NLAlib.lanczosReorthProg.compiled` is at most `NLAlib.lanczosReorthCount`.
Proof: as main's static count of the plain tree
(`NLAlib/Krylov/Processes/LanczosProgramStaticCost.lean`): unfold the static cost of the compiled
tree
(`FStmt.staticCost`, `StaticCost.seq`, `StaticCost.branch`, `StaticCost.alloc`), evaluate the
nested loops (the inner loop bounds $j + 1$ give $\sum_{j<q}(j+1) = q(q+1)/2$), and compare
componentwise (`Finsupp.single_apply`, `omega`/`nlinarith` per kind). If a component of the
drafted formula is too small, enlarge it in the design note (it is a draft) and record the change.
M, about 80 lines. -/
theorem lanczosReorthProg.staticCost_count_le {P ι : Type} [DecidableEq P] (tag : P)
    (width : P → ℕ) (N q : ℕ) :
    ((lanczosReorthProg.compiled (ι := ι) tag).staticCost (fun k => Finsupp.single k 1)
      width N ![q]).count ≤ lanczosReorthCount tag N q := by
  classical
  intro k
  change (FStmt.staticCost (fun k => Finsupp.single k 1) width
    (lanczosReorthProg.compiled (ι := ι) tag) (Fin.cons N ![q])).count k ≤ _
  change (StaticCost.seq _ _).count k ≤ _
  simp only [FStmt.staticCost, StaticCost.seq, StaticCost.branch, StaticCost.alloc,
    StaticCost.step, StaticCost.zero, StaticCost.sequence_count_apply, Instr.kind, Instr.subst,
    IExp.evalIn, Finsupp.add_apply, Finsupp.sup_apply, List.map_const', List.sum_replicate,
    List.length_range, Finsupp.zero_apply]
  simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.cons_zero, add_zero, zero_add,
    smul_eq_mul, Matrix.Fin.cons_vecCons, Nat.succ_eq_add_one,
    Fin.snoc_apply_zero, Matrix.cons_val_zero, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty, List.map_const', List.length_range, List.sum_replicate,
    Fin.val_eq_zero, Fin.mk_one, Fin.cons_one, Matrix.cons_val_fin_one]
  cases k <;> simp only [lanczosReorthCount, Finsupp.add_apply, Finsupp.single_apply,
    OpKind.bin.injEq, OpKind.un.injEq, OpKind.lit.injEq, OpKind.cmp.injEq,
    OpKind.copy.injEq, OpKind.rom.injEq, reduceCtorEq, add_zero, zero_add, mul_zero,
    ite_false, sum_map_range_eq_finsetSum]
  -- the loop bodies depend on the step through the CGS2 width `j + 1`: Gauss's sum
  case bin p b =>
    have hS := two_mul_sum_range_id_add q
    cases b <;> by_cases hp : tag = p <;>
      simp [hp, Finset.sum_add_distrib, add_mul, ← Finset.sum_mul] <;> nlinarith
  case un p u =>
    have hS := two_mul_sum_range_id_add q
    cases u <;> by_cases hp : tag = p <;>
      simp [hp, Finset.sum_add_distrib, add_mul, ← Finset.sum_mul] <;> nlinarith
  case lit p =>
    have hS := two_mul_sum_range_id_add q
    by_cases hp : tag = p
    · simp [hp, Finset.sum_add_distrib]; nlinarith
    · simp [hp]
  all_goals (try split_ifs) <;> norm_num <;> ring_nf <;> omega

namespace LanczosReorthImplementation

variable {P ι K : Type} [DecidableEq P]

/-- **Rounded run of the generic loop** (G5): for any product routine family certified by
`NLAlib.Computation.IsMatvecRoutine` (coefficient $\varepsilon\|\mathbf{A}\|_2$,
$\varepsilon$ = `NLAlib.lanczosImplementationRoundoffBound`,
that is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u$) and any
orthogonalization routine family certified by `NLAlib.Computation.IsOrthRoutine` at $(\eta_0,
\varepsilon_1, \varepsilon_2,
\varepsilon_3)$, the loop `NLAlib.lanczosReorthLoop` succeeds from a state with the seven
declared buffers and the matrix slot $7$, keeps the shape, and its outputs satisfy
`NLAlib.LanczosReorthOutputs` for every $\tau > 0$. The scheme enters only through its
certificate. No printed source; `docs/design/Krylov-LanczosReorth.md` §1.4.
Proof: follow `NLAlib.LanczosImplementation.exec_rounded_compiled` (files
`NLAlib/Krylov/Processes/LanczosProgramRounded*.lean` on main: initialization, step, prefix, run,
commit) with a
step that has two more phases: after the second `axpy`, the `nrm2` of $\nu$
(`NLAlib.Computation.IsRelErrSem.exec_nrm2_abs_norm_sub_le`
type bound $|\nu - \|\mathbf{z}\|| \le \varepsilon\|\mathbf{z}\|$), then `horth t`
(`IsOrthRoutine.run`
with the basis columns $0..t$ as $\mathbf{V}$, `work` as $\mathbf{w}$, `coef` as $\mathbf{h}$; its
frame keeps the basis and the coefficients), then main's `nrm2`/zero test/`rscl` normalization
lemmas applied to $\mathbf{z}'$. The run of an admissible prefix is assembled field by field
(`orth_eq` from the certificate, the rest as in main's `NLAlib.LanczosRun` construction,
`abs_norm_v_sq_sub_one_le` for $j \le m + 1$ from $\beta_j > 0$). Composability of
`mv`/`orth` from the certificates' `composable` fields; `hpre` is preserved because only
buffers $1..6, 8..10$ are written. H, about 1200 lines; intermediate lemmas: the store invariant
(a `NLAlib.LanczosImplementation.StoreContext` with the basis prefix and `nu`), one step, the
prefix induction, the
initialization (reused), and the assembly of `NLAlib.LanczosReorthRun`. -/
theorem exec_rounded_loop {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K (OpCount P ι))
    (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (st : St P K (OpCount P ι)) (N q : ℕ) (slot : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (pre : Store P K → Prop) (hpre : pre st.store)
    (hpreFrame : ∀ s s' : Store P K, pre s → s'.shape = s.shape →
      (∀ i, s'.read tag 7 i = s.read tag 7 i) → pre s')
    (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A) pre 1 8
      (IExp.const N * IExp.var t) 0 (mv 8 (IExp.var t)))
    (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit) {η₀ ε₁ ε₂ ε₃ : ℝ}
    (hε : 0 ≤ ε₁ ∧ 0 ≤ ε₂ ∧ 0 ≤ ε₃)
    (horth : ∀ t : ℕ, IsOrthRoutine I dec tag N (t + 1) η₀ ε₁ ε₂ ε₃ (fun _ => True) 1 8 10 0 0
      (orth 8 10 (IExp.var t)))
    (hA : Aᵀ = A) (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ out : St P K (OpCount P ι),
      exec I (lanczosReorthLoop tag (IExp.const N) (IExp.const q) 0 1 2 3 4 5 6 mv orth).run
        st = some out ∧
      out.store.shape = st.store.shape ∧
      (b ≠ 0 → LanczosReorthOutputs out.store dec tag N q A b
        (lanczosImplementationRoundoffBound N (u tag)) τ η₀ ε₁ ε₂ ε₃) := by
  sorry

/-- **Rounded run of the stored-matrix CGS2 tree** (G6): under the standard model, for symmetric
decoded $\mathbf{A}$ (ROM words) and $\mathbf{b} \ne \mathbf{0}$, the compiled tree succeeds,
keeps the shape and its outputs satisfy `NLAlib.LanczosReorthOutputs` with the CGS2 parameters at
$q$ columns, $c_1$ = `NLAlib.cgsPassBound` $N\,q\,u\,\eta_0$
= <!-- value cgsPassBound N q u \eta_0 -->$2(1+\eta_0)\sqrt{q+1}\,(N+q+2)\,u$:
$(\eta_0, 2c_1, 3c_1, 2(\eta_0 + c_1)^2)$. No printed source.
Proof: `NLAlib.lanczosReorthProg.toStmt_compiled`; the ROM load into slot $7$ as in main's
`NLAlib/Krylov/Processes/LanczosProgramRoundedInitialization.lean` (decoded matrix `HoldsDecoded …
7 0 A`); then
`NLAlib.LanczosReorthImplementation.exec_rounded_loop` with `mv` the `gemv` call, certified by
`NLAlib.Computation.IsRelErrSem.isMatvecRoutine_gemv` (its coefficient $\gamma_N\sqrt
N\|\mathbf{A}\|
\le \varepsilon\|\mathbf{A}\|$, `IsMatvecRoutine.mono`), and `orth` the `NLAlib.cgs2` call at
$t + 1$ columns, certified by `NLAlib.Computation.IsRelErrSem.isOrthRoutine_cgs2` and made uniform
in
$t$ by monotonicity of `NLAlib.cgsPassBound` in $j$ (`IsOrthRoutine` parameters enlarged with
`NLAlib.IsOrthErr.mono` inside the certificate). L, about 200 lines. -/
theorem exec_rounded_compiled {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K (OpCount P ι))
    (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (hc : ∀ k, I.charge k = Finsupp.single k 1)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (values : ℕ → K)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hrom : ∀ i < N * N, I.rom i = some (values i))
    (hdecode : ∀ i j : Fin N, dec tag (values (N * j + i)) = A i j) (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) (hbnz : b ≠ 0)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100) (hu : ((N + q + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100)
    (hc₁ : cgsPassBound N q (u tag) η₀ ≤ 1 / 100) {τ : ℝ} (hτ : 0 < τ) :
    ∃ out : St P K (OpCount P ι),
      (lanczosReorthProg.compiled tag).exec I N ![q] st = some out ∧
      out.store.shape = st.store.shape ∧
      LanczosReorthOutputs out.store dec tag N q A b
        (lanczosImplementationRoundoffBound N (u tag)) τ η₀ (2 * cgsPassBound N q (u tag) η₀)
        (3 * cgsPassBound N q (u tag) η₀) (2 * (η₀ + cgsPassBound N q (u tag) η₀) ^ 2) := by
  sorry

/-- **Rounded run of the matrix-free CGS2 tree** (G6o): as
`NLAlib.LanczosReorthImplementation.exec_rounded_compiled` with an oracle of accuracy
$\eta\|\mathbf{A}\|_2$, $\eta \le \varepsilon$ (`NLAlib.Computation.IsMatvecErr`), and no ROM.
Pattern: `NLAlib.LanczosOracleImplementation.exec_rounded_compiled`.
Proof: `NLAlib.lanczosReorthOracleProg.toStmt_compiled`; the empty slot $7$; then
`NLAlib.LanczosReorthImplementation.exec_rounded_loop` with `mv` the `apply` call certified by
`NLAlib.Computation.IsMatvecErr.isMatvecRoutine` (mono to $\varepsilon\|\mathbf{A}\|$) and `orth`
as in
G6. M, about 100 lines. -/
theorem exec_rounded_oracle_compiled {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P) (o : ι)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (st : St P K (OpCount P ι)) (N q : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    {η : ℝ} (hmv : IsMatvecErr I o dec tag A (η * specNorm A))
    (hηmv : η ≤ lanczosImplementationRoundoffBound N (u tag)) (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) (hbnz : b ≠ 0)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100) (hu : ((N + q + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100)
    (hc₁ : cgsPassBound N q (u tag) η₀ ≤ 1 / 100) {τ : ℝ} (hτ : 0 < τ) :
    ∃ out : St P K (OpCount P ι),
      (lanczosReorthOracleProg.compiled tag o).exec I N ![q] st = some out ∧
      out.store.shape = st.store.shape ∧
      LanczosReorthOutputs out.store dec tag N q A b
        (lanczosImplementationRoundoffBound N (u tag)) τ η₀ (2 * cgsPassBound N q (u tag) η₀)
        (3 * cgsPassBound N q (u tag) η₀) (2 * (η₀ + cgsPassBound N q (u tag) η₀) ^ 2) := by
  sorry

/-- **The program-level backward model** (G7): in the setting of
`NLAlib.LanczosReorthImplementation.exec_rounded_compiled`, every admissible prefix of $m$ steps
whose run satisfies the fixed-point condition has computed tridiagonal equal to the exact Lanczos
tridiagonal of $(\mathbf{H}', \mathbf{b})$ for a symmetric $\mathbf{H}'$ within
backwardRadius $+ 3\|\mathbf{A}\|_2(3\varepsilon + 2\sqrt{3(m+1)}\,\mu)$ of $\mathbf{A}$ in
Frobenius norm. No printed source; [Paige1970] in substance.
Proof: `NLAlib.LanczosReorthImplementation.exec_rounded_compiled`, unfold
`NLAlib.LanczosReorthOutputs` at $m$, then `NLAlib.LanczosReorthRun.exists_pure_backward` with
$\delta_b = 3\varepsilon$. S, about 30 lines. -/
theorem exec_rounded_compiled_backward {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (hc : ∀ k, I.charge k = Finsupp.single k 1)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (values : ℕ → K)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hrom : ∀ i < N * N, I.rom i = some (values i))
    (hdecode : ∀ i j : Fin N, dec tag (values (N * j + i)) = A i j) (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) (hbnz : b ≠ 0)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100) (hu : ((N + q + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100)
    (hc₁ : cgsPassBound N q (u tag) η₀ ≤ 1 / 100) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ out : St P K (OpCount P ι),
      (lanczosReorthProg.compiled tag).exec I N ![q] st = some out ∧
      ∃ (α β ν : ℕ → ℝ),
        HoldsDecoded out.store dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => α ((j : ℕ) + 1)) ∧
        HoldsDecoded out.store dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => β j) ∧
        HoldsDecoded out.store dec tag 6 0 (fun (j : Fin q) (_ : Fin 1) => ν ((j : ℕ) + 1)) ∧
        ∀ m, 0 < m → m ≤ q → (∀ j < m, τ * ν (j + 1) < β (j + 1)) →
          ∃ L : LanczosReorthRun N m, L.H = A ∧ (∀ j ≤ m, L.α j = α j ∧ L.β j = β j) ∧
            (L.recLevel ≤ 1 / 100 →
              Real.sqrt (3 * ((m : ℝ) + 1)) * L.orthLevel ≤ L.η₀ →
              ∃ H' : Matrix (Fin N) (Fin N) ℝ, H'ᵀ = H' ∧
                frobNorm (H' - A) ≤ L.backwardRadius + 3 * specNorm A *
                  (3 * lanczosImplementationRoundoffBound N (u tag) +
                    2 * Real.sqrt (3 * ((m : ℝ) + 1)) * L.orthLevel) ∧
                lanczosTridiagonal H' b m = L.toLanczosData.tridiagonal) := by
  sorry

/-- **The program-level interlacing headline** (G8): in the setting of
`NLAlib.LanczosReorthImplementation.exec_rounded_compiled_backward`, on every admissible prefix
with the fixed-point condition the computed Ritz values interlace the eigenvalues of
$\mathbf{A}$ up to backwardRadius:
$\lambda_{i+N-m}(\mathbf{A}) - e \le \theta_i \le \lambda_i(\mathbf{A}) + e$. No printed source.
Proof: `NLAlib.LanczosReorthImplementation.exec_rounded_compiled`, unfold the outputs at $m$, then
`NLAlib.LanczosReorthRun.eigenvalue_tridiagonal_le_add` and
`NLAlib.LanczosReorthRun.eigenvalue_sub_le_eigenvalue_tridiagonal` (the run's parameters satisfy
$\eta_0 \le 1/100$ and $\tau \le 1$ by the hypotheses). S, about 30 lines. -/
theorem exec_rounded_compiled_interlacing {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (hc : ∀ k, I.charge k = Finsupp.single k 1)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (values : ℕ → K)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hrom : ∀ i < N * N, I.rom i = some (values i))
    (hdecode : ∀ i j : Fin N, dec tag (values (N * j + i)) = A i j) (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) (hbnz : b ≠ 0)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100) (hu : ((N + q + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100)
    (hc₁ : cgsPassBound N q (u tag) η₀ ≤ 1 / 100) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ out : St P K (OpCount P ι),
      (lanczosReorthProg.compiled tag).exec I N ![q] st = some out ∧
      ∃ (α β ν : ℕ → ℝ),
        HoldsDecoded out.store dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => α ((j : ℕ) + 1)) ∧
        HoldsDecoded out.store dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => β j) ∧
        HoldsDecoded out.store dec tag 6 0 (fun (j : Fin q) (_ : Fin 1) => ν ((j : ℕ) + 1)) ∧
        ∀ m, 0 < m → m ≤ q → (∀ j < m, τ * ν (j + 1) < β (j + 1)) →
          ∃ L : LanczosReorthRun N m, L.H = A ∧ (∀ j ≤ m, L.α j = α j ∧ L.β j = β j) ∧
            (L.recLevel ≤ 1 / 100 →
              Real.sqrt (3 * ((m : ℝ) + 1)) * L.orthLevel ≤ L.η₀ →
              ∀ i < m, eigenvalue A (i + (N - m)) - L.backwardRadius ≤
                  eigenvalue L.toLanczosData.tridiagonal i ∧
                eigenvalue L.toLanczosData.tridiagonal i ≤ eigenvalue A i + L.backwardRadius) := by
  sorry

end LanczosReorthImplementation

end NLAlib
