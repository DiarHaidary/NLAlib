/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosReorthProgram
public import NLAlib.Krylov.FinitePrecision.LanczosReorthSpectral

/-!
# Rounded runs of Lanczos with full reorthogonalization as a program

The rounded runs of the CGS2 trees `NLAlib.lanczosReorthProg.compiled` (stored matrix) and
`NLAlib.lanczosReorthOracleProg.compiled` (matrix-free) under the standard model: both succeed
and their decoded outputs satisfy `NLAlib.LanczosReorthOutputs` with the CGS2 parameters at $q$
columns; composed with the backward model of `NLAlib.LanczosReorthRun`, the computed tridiagonal
of every admissible prefix is the exact Lanczos tridiagonal of a nearby symmetric matrix, and the
computed Ritz values interlace the eigenvalues of $\mathbf{A}$ up to the backward radius.
Patterned on `NLAlib.LanczosImplementation.exec_rounded_compiled` and
`NLAlib.LanczosOracleImplementation.exec_rounded_compiled`.

## Main results

* `NLAlib.LanczosReorthImplementation.exec_rounded_compiled`,
  `NLAlib.LanczosReorthImplementation.exec_rounded_oracle_compiled`: the rounded runs.
* `NLAlib.LanczosReorthImplementation.exec_rounded_compiled_backward`: the backward model.
* `NLAlib.LanczosReorthImplementation.exec_rounded_compiled_interlacing`: interlacing.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

namespace LanczosReorthImplementation

variable {P ι K : Type} [DecidableEq P]

/-- The CGS2 call at step $t < q$ ($t + 1$ columns) is certified at the parameters of $q$
columns: under the standard model with $0 \le \eta_0 \le 1/100$, $(N + q + 2)u \le 1/100$ and
$c_1$ = `NLAlib.cgsPassBound` $N\,q\,u\,\eta_0 \le 1/100$, `NLAlib.cgs2` meets
`NLAlib.Computation.IsOrthRoutine` at $(\eta_0, 2c_1, 3c_1, 2(\eta_0 + c_1)^2)$. -/
private theorem isOrthRoutine_cgs2_of_lt {C : Type} [AddMonoid C] {u : P → ℝ}
    {dec : P → K → ℝ} (I : Interp P ι K C)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q t : ℕ} (ht : t < q) {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100)
    (hu : ((N + q + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100)
    (hc₁ : cgsPassBound N q (u tag) η₀ ≤ 1 / 100) :
    IsOrthRoutine I dec tag N (t + 1) η₀ (2 * cgsPassBound N q (u tag) η₀)
      (3 * cgsPassBound N q (u tag) η₀) (2 * (η₀ + cgsPassBound N q (u tag) η₀) ^ 2)
      (fun _ => True) 1 8 10 0 0 (cgs2 tag (IExp.const N) (IExp.var t + 1) 1 8 0 10 0) := by
  have hu0 := hsem.nonneg (p := tag) trivial
  have hmono := cgsPassBound_le_cgsPassBound N (show t + 1 ≤ q by omega) hu0 hη₀
  have hc0 : 0 ≤ cgsPassBound N (t + 1) (u tag) η₀ := by
    rw [cgsPassBound_def]; positivity
  have hO := hsem.isOrthRoutine_cgs2 I hz tag (N := N) (j := t + 1) (IExp.const N)
    (IExp.var t + 1) rfl rfl 1 8 10 0 0 hη₀ hη
    ((mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) hu0).trans hu)
    (hmono.trans hc₁)
  refine ⟨hO.composable, fun st V w hp hV hw hwc hhc h1 h2 h3 => ?_⟩
  obtain ⟨out, W, Hw, mid, hr, hw1, hw2, he⟩ := hO.run st V w hp hV hw hwc hhc h1 h2 h3
  have h₃ : 2 * (η₀ + cgsPassBound N (t + 1) (u tag) η₀) ^ 2 ≤
      2 * (η₀ + cgsPassBound N q (u tag) η₀) ^ 2 := by
    gcongr
  refine ⟨out, W, Hw, mid, hr, hw1, hw2, fun hV => (he.residual hV).trans
    (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)), fun hV => (he.orth hV).trans
    (add_le_add (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right h₃ (norm_nonneg _)))⟩

/-- The outputs `NLAlib.LanczosReorthOutputs` read only the declared buffers $0, \dots, 6$, so they
survive the release of a matrix slot allocated after them. -/
private theorem lanczosReorthOutputs_pop {s : Store P K} (hsize : s.size = 8) {dec : P → K → ℝ}
    {tag : P} {N q : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ} {ε τ η₀ ε₁ ε₂ ε₃ : ℝ}
    (h : LanczosReorthOutputs s dec tag N q A b ε τ η₀ ε₁ ε₂ ε₃) :
    LanczosReorthOutputs s.pop dec tag N q A b ε τ η₀ ε₁ ε₂ ε₃ := by
  have rdo : ∀ p k i, k < 7 → Store.read s.pop p k i = s.read p k i :=
    fun p k i hk => Store.read_pop_of_lt (by rw [hsize]; omega)
  obtain ⟨v, α, β, ν, h0, h1, h2, h3, h6, hδ, hm⟩ := h
  refine ⟨v, α, β, ν, fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_,
    fun i j => ?_, hδ, hm⟩
  · rw [rdo tag 0 _ (by omega)]; exact h0 i j
  · rw [rdo tag 1 _ (by omega)]; exact h1 i j
  · rw [rdo tag 2 _ (by omega)]; exact h2 i j
  · rw [rdo tag 3 _ (by omega)]; exact h3 i j
  · rw [rdo tag 6 _ (by omega)]; exact h6 i j

/-- **The rounded run of the stored-matrix CGS2 tree**: under the standard model, for symmetric
decoded $\mathbf{A}$ (ROM words) and $\mathbf{b} \ne \mathbf{0}$, the compiled tree succeeds,
keeps the shape and its outputs satisfy `NLAlib.LanczosReorthOutputs` with the CGS2 parameters at
$q$ columns, $c_1$ = `NLAlib.cgsPassBound` $N\,q\,u\,\eta_0$
= <!-- value cgsPassBound N q u \eta_0 -->$2(1+\eta_0)\sqrt{q+1}\,(N+q+2)\,u$:
$(\eta_0, 2c_1, 3c_1, 2(\eta_0 + c_1)^2)$. No printed source.
Result: lanczos-reorth-rounded-program -/
theorem exec_rounded_compiled {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K (OpCount P ι))
    (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem)
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
  have hu0 := hsem.nonneg (p := tag) trivial
  obtain ⟨mid, hload, shm, hbm, hmA⟩ := exec_rom_load I tag st N q values hshape hrom
  have hn : (N : ℝ) * u tag < 1 := by
    have hs := (lanczosImplementationRoundoffBound_kernel_bounds N hu0 hsmall).1
    push_cast at hs
    nlinarith
  have hc0 : 0 ≤ cgsPassBound N q (u tag) η₀ := by
    rw [cgsPassBound_def]; positivity
  obtain ⟨out₁, hrun, shout, hout⟩ := exec_rounded_loop I tag hsem hz mid N q (N * N)
    A b shm (fun i => by rw [hbm i]; exact hb i) (fun s => HoldsDecoded s dec tag 7 0 A)
    (fun i j => ⟨_, hmA i j, hdecode i j⟩)
    (fun s s' hs _ h7 i j => by rw [h7]; exact hs i j)
    (fun work j => gemv tag (IExp.const N) (IExp.const N) 7 0 1 (IExp.const N * j) work 0)
    (fun t => (hsem.isMatvecRoutine_gemv I tag hz N A 7 1 8 0 (IExp.const N * IExp.var t) 0
      hn (by omega) (by omega)).mono (mul_le_mul_of_nonneg_right
        (roundingFactor_mul_sqrt_le_lanczosImplementationRoundoffBound N hu0 hsmall)
        (specNorm_nonneg A)))
    (fun work coef j => cgs2 tag (IExp.const N) (j + 1) 1 work 0 coef 0)
    ⟨by linarith, by linarith, by positivity⟩
    (fun t ht => isOrthRoutine_cgs2_of_lt I hsem hz tag ht hη₀ hη hu hc₁) hA hsmall hτ
  have hsize : st.store.size = 7 := by simpa [Store.shape] using congrArg Array.size hshape
  have hsize₁ : out₁.store.size = 8 := by
    simpa [Store.shape] using congrArg Array.size (shout.trans shm)
  refine ⟨_, exec_compiled_eq_some I tag st N q hsize hload hrun, ?_,
    lanczosReorthOutputs_pop hsize₁ (hout hbnz)⟩
  change Store.shape out₁.store.pop = _
  rw [Store.shape_pop, shout, shm, hshape]
  rfl

/-- **The rounded run of the matrix-free CGS2 tree**: under the standard model, for symmetric
$\mathbf{A}$, an oracle of accuracy $\eta\|\mathbf{A}\|_2$ (`NLAlib.Computation.IsMatvecErr`)
with $\eta \le \varepsilon$ = `NLAlib.lanczosImplementationRoundoffBound` $N\,u \le 1/100$ and
$\mathbf{b} \ne \mathbf{0}$, the compiled tree succeeds, keeps the shape and its outputs satisfy
`NLAlib.LanczosReorthOutputs` with the CGS2 parameters at $q$ columns, $c_1$ =
`NLAlib.cgsPassBound` $N\,q\,u\,\eta_0$: $(\eta_0, 2c_1, 3c_1, 2(\eta_0 + c_1)^2)$.
Pattern: `NLAlib.LanczosOracleImplementation.exec_rounded_compiled`. No printed source.
Result: lanczos-reorth-rounded-program -/
theorem exec_rounded_oracle_compiled {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P) (o : ι)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K (OpCount P ι)) (N q : ℕ)
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
  have hu0 := hsem.nonneg (p := tag) trivial
  have hsize : st.store.size = 7 := by simpa [Store.shape] using congrArg Array.size hshape
  let st₁ := st.allocate tag (0 : IExp ℕ).eval (I.width tag)
  have sh₁ : st₁.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, 0)] := by
    simp only [st₁, St.shape_allocate, hshape, IExp.eval_ofNat]
    rfl
  have hc0 : 0 ≤ cgsPassBound N q (u tag) η₀ := by
    rw [cgsPassBound_def]; positivity
  obtain ⟨out₁, hrun, shout, hout⟩ := exec_rounded_loop I tag hsem hz st₁ N q 0 A b sh₁
    (fun i => by rw [St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega)]; exact hb i)
    (fun _ => True) trivial (fun _ _ _ _ _ => trivial)
    (fun work j => stmt (.apply o tag work 0 1 (IExp.const N * j) 1))
    (fun t => (hmv.isMatvecRoutine 1 8 (IExp.const N * IExp.var t) 0 (by omega)).mono
      (mul_le_mul_of_nonneg_right hηmv (specNorm_nonneg A)))
    (fun work coef j => cgs2 tag (IExp.const N) (j + 1) 1 work 0 coef 0)
    ⟨by linarith, by linarith, by positivity⟩
    (fun t ht => isOrthRoutine_cgs2_of_lt I hsem hz tag ht hη₀ hη hu hc₁) hA hsmall hτ
  have hsize₁ : out₁.store.size = 8 := by
    simpa [Store.shape] using congrArg Array.size (shout.trans sh₁)
  refine ⟨out₁.release tag (0 : IExp ℕ).eval (I.width tag), ?_, ?_,
    lanczosReorthOutputs_pop hsize₁ (hout hbnz)⟩
  · rw [Prog.exec_eq_exec_toStmt, lanczosReorthOracleProg.toStmt_compiled]
    change exec I (.seq (.alloc tag (0 : IExp ℕ) _) .skip) st = _
    rw [exec_seq_skip]
    exact exec_alloc_of_exec_eq_some _ _ _ _ _ _ hrun
  · change Store.shape out₁.store.pop = _
    rw [Store.shape_pop, shout, sh₁, hshape]
    rfl

/-- **The program-level backward model**: under the standard model, for symmetric decoded
$\mathbf{A}$ (ROM words), $\mathbf{b} \ne \mathbf{0}$, $\varepsilon$ =
`NLAlib.lanczosImplementationRoundoffBound` $N\,u \le 1/100$, $0 \le \eta_0 \le 1/100$,
$(N + q + 2)u \le 1/100$, `NLAlib.cgsPassBound` $N\,q\,u\,\eta_0 \le 1/100$ and
$0 < \tau \le 1$, the stored-matrix CGS2 tree succeeds, and every admissible prefix of $m$
steps ($\tau\nu_j < \beta_j$) is a `NLAlib.LanczosReorthRun` $L$ whose coefficients are the
decoded ones; if its recurrence and orthogonality levels satisfy the fixed-point condition, its
computed tridiagonal is the exact Lanczos tridiagonal of $(\mathbf{H}', \mathbf{b})$ for a
symmetric $\mathbf{H}'$ with
$\|\mathbf{H}' - \mathbf{A}\|_{\mathsf{F}} \le r + 3\|\mathbf{A}\|_2(3\varepsilon +
2\sqrt{3(m+1)}\,\mu)$, $r$ = `NLAlib.LanczosReorthRun.backwardRadius` and $\mu$ the
orthogonality level. No printed source for the program statement; [Paige1971, §6.1] in
substance.
Result: lanczos-reorth-backward-model -/
theorem exec_rounded_compiled_backward {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem)
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
  obtain ⟨out, hexec, -, hout⟩ := exec_rounded_compiled I tag hsem hz st N q A b values hshape
    hb hrom hdecode hA hsmall hbnz hη₀ hη hu hc₁ hτ
  obtain ⟨v, α, β, ν, -, -, h2, h3, h6, hδ, hm⟩ := hout
  refine ⟨out, hexec, α, β, ν, h2, h3, h6, fun m hm0 hmq hadm => ?_⟩
  obtain ⟨L, hH, hv, hcoef, -, hLτ, hLη, -⟩ := hm m hm0 hmq hadm
  refine ⟨L, hH, fun j hj => ⟨(hcoef j hj).1, (hcoef j hj).2.1⟩, fun hrec hsm => ?_⟩
  have hδL : ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - L.v 1)‖ ≤
      3 * lanczosImplementationRoundoffBound N (u tag) := by
    rw [hv 1 le_rfl (by omega)]
    exact hδ
  obtain ⟨H', h1, h2', h3'⟩ := L.exists_pure_backward (hLη ▸ hη) hsm hrec (hLτ ▸ hτ1) hbnz hδL
  rw [hH] at h2'
  exact ⟨H', h1, h2', h3'⟩

/-- **Interlacing at the program level**: under the standard model, for symmetric decoded
$\mathbf{A}$ (ROM words), $\mathbf{b} \ne \mathbf{0}$, $\varepsilon$ =
`NLAlib.lanczosImplementationRoundoffBound` $N\,u \le 1/100$, $0 \le \eta_0 \le 1/100$,
$(N + q + 2)u \le 1/100$, `NLAlib.cgsPassBound` $N\,q\,u\,\eta_0 \le 1/100$ and
$0 < \tau \le 1$, the stored-matrix CGS2 tree succeeds and on every admissible prefix of $m$
steps whose run $L$ satisfies the fixed-point condition the computed Ritz values $\theta_i$
interlace the eigenvalues of $\mathbf{A}$ up to $e$ = `NLAlib.LanczosReorthRun.backwardRadius`:
$\lambda_{i+N-m}(\mathbf{A}) - e \le \theta_i \le \lambda_i(\mathbf{A}) + e$ for $i < m$.
No printed source.
Result: lanczos-reorth-interlacing -/
theorem exec_rounded_compiled_interlacing {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem)
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
  obtain ⟨out, hexec, -, hout⟩ := exec_rounded_compiled I tag hsem hz st N q A b values hshape
    hb hrom hdecode hA hsmall hbnz hη₀ hη hu hc₁ hτ
  obtain ⟨v, α, β, ν, -, -, h2, h3, h6, -, hm⟩ := hout
  refine ⟨out, hexec, α, β, ν, h2, h3, h6, fun m hm0 hmq hadm => ?_⟩
  obtain ⟨L, hH, -, hcoef, -, hLτ, hLη, -⟩ := hm m hm0 hmq hadm
  refine ⟨L, hH, fun j hj => ⟨(hcoef j hj).1, (hcoef j hj).2.1⟩, fun hrec hsm i hi => ?_⟩
  have hlo := L.eigenvalue_sub_le_eigenvalue_tridiagonal (hLη ▸ hη) hsm hrec (hLτ ▸ hτ1) hi
  have hhi := L.eigenvalue_tridiagonal_le_add (hLη ▸ hη) hsm hrec (hLτ ▸ hτ1) hi
  rw [hH] at hlo hhi
  exact ⟨hlo, hhi⟩

end LanczosReorthImplementation

end NLAlib
