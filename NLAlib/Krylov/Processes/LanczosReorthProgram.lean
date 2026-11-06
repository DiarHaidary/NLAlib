/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosReorthProgramRoundedLoop
public import NLAlib.Matrix.Computation.ClassicalGramSchmidtProgram
public import NLAlib.Krylov.Processes.LanczosReorthRecurrence
public import NLAlib.Computation.StaticCost

/-!
# Lanczos with full reorthogonalization as a program: the exact run and the count

For the stored-matrix tree `NLAlib.lanczosReorthProg.compiled`: its run is the ROM load of the
matrix followed by the scoped loop; its exact run (exact arithmetic, the matrix as ROM) writes
the basis, the coefficients and the norms of the exact recurrence `NLAlib.lanczosReorthState`;
and its static operation count is at most `NLAlib.lanczosReorthCount`. The exact run is the
rounded run of `NLAlib.LanczosReorthImplementation.exec_lanczosReorthLoop` at unit roundoff
$u = 0$, where every local defect vanishes.

## Main results

* `NLAlib.LanczosReorthImplementation.exec_rom_load`,
  `NLAlib.LanczosReorthImplementation.exec_compiled_eq_some`: the run of the tree.
* `NLAlib.lanczosReorthProg.exec_storedInterp_compiled`: the exact run.
* `NLAlib.lanczosReorthProg.staticCost_count_le`: the static count.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

namespace LanczosReorthImplementation

variable {P ι K : Type} [DecidableEq P]

/-- The ROM load of `NLAlib.lanczosReorthProg`: from a store with the seven declared buffers and
a matrix slot of length $N^2$ allocated after them, under an interpretation whose ROM holds
`values` at the indices below $N^2$, the load succeeds, keeps the shape and the input buffer,
and writes the slot $7$ column-major. -/
theorem exec_rom_load (I : Interp P ι K (OpCount P ι)) (tag : P) (st : St P K (OpCount P ι))
    (N q : ℕ) (values : ℕ → K)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q)])
    (hrom : ∀ i < N * N, I.rom i = some (values i)) :
    ∃ mid : St P K (OpCount P ι),
      exec I (forRange (IExp.const N * IExp.const N) fun i =>
        stmt (.rom tag ⟨7, .var i⟩ (.var i)) : Builder P ι ℕ ℕ Unit).run
          (st.allocate tag (N * N) (I.width tag)) = some mid ∧
      mid.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
        (tag, 1), (tag, N), (tag, q), (tag, N * N)] ∧
      (∀ i : Fin N, mid.store.read tag 0 i = st.store.read tag 0 i) ∧
      ∀ i j : Fin N, mid.store.read tag 7 (0 + i + N * j) = some (values (N * j + i)) := by
  have hsize : st.store.size = 7 := by simpa [Store.shape] using congrArg Array.size hshape
  let st₁ := st.allocate tag (N * N) (I.width tag)
  have sh₁ : st₁.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, N * N)] := by
    simp only [st₁, St.shape_allocate, hshape]
    rfl
  obtain ⟨loaded, erom, shrom, reads, frame⟩ :=
    exec_forRange_rom I tag st₁ (IExp.const N * IExp.const N) 7 values
      (by rw [sh₁]; rfl) (by simpa only [IExp.eval_mul, IExp.eval_const] using hrom)
  refine ⟨{ st₁ with store := loaded, cnt := st₁.cnt + (N * N) • I.charge (.rom tag) }, ?_,
    shrom.trans sh₁, fun i => ?_, fun i j => ?_⟩
  · change exec I (.seq (.loop (IExp.const N * IExp.const N)
      (fun i => .seq (.rom tag ⟨7, .var i⟩ (.var i)) .skip)) .skip) st₁ = _
    rw [exec_seq_skip]
    simpa only [IExp.eval_mul, IExp.eval_const] using erom
  · change loaded.read tag 0 i = _
    rw [frame tag 0 i (by omega), St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega)]
  · change loaded.read tag 7 (0 + i + N * j) = _
    rw [zero_add, Nat.add_comm]
    exact reads (N * j + i) (by
      change N * (j : ℕ) + (i : ℕ) < N * N
      calc
        N * (j : ℕ) + (i : ℕ) < N * (j : ℕ) + N := Nat.add_lt_add_left i.isLt _
        _ = N * ((j : ℕ) + 1) := by ring
        _ ≤ N * N := Nat.mul_le_mul_left N j.isLt)

/-- The run of `NLAlib.lanczosReorthProg.compiled` from a store with the seven declared buffers
is the ROM load into a fresh matrix slot, then the scoped loop with `gemv` products and `cgs2`
orthogonalization, then the release of the slot. -/
theorem exec_compiled_eq_some (I : Interp P ι K (OpCount P ι)) (tag : P)
    (st : St P K (OpCount P ι)) (N q : ℕ) {mid out : St P K (OpCount P ι)}
    (hsize : st.store.size = 7)
    (hload : exec I (forRange (IExp.const N * IExp.const N) fun i =>
        stmt (.rom tag ⟨7, .var i⟩ (.var i)) : Builder P ι ℕ ℕ Unit).run
          (st.allocate tag (N * N) (I.width tag)) = some mid)
    (hloop : exec I (lanczosReorthLoop tag (IExp.const N) (IExp.const q) 0 1 2 3 4 5 6
        (fun work j => gemv tag (IExp.const N) (IExp.const N) 7 0 1 (IExp.const N * j) work 0)
        (fun work coef j => cgs2 tag (IExp.const N) (j + 1) 1 work 0 coef 0)).run mid =
      some out) :
    (lanczosReorthProg.compiled tag).exec I N ![q] st =
      some (out.release tag (N * N) (I.width tag)) := by
  rw [Prog.exec_eq_exec_toStmt, lanczosReorthProg.toStmt_compiled]
  change exec I (.seq (.alloc tag (IExp.const N * IExp.const N) _) .skip) st = _
  rw [exec_seq_skip]
  apply exec_alloc_of_exec_eq_some
  rw [hsize]
  change exec I (do
    forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨7, .var i⟩ (.var i))
    lanczosReorthLoop tag (IExp.const N) (IExp.const q) 0 1 2 3 4 5 6
      (fun work j => gemv tag (IExp.const N) (IExp.const N) 7 0 1 (IExp.const N * j) work 0)
      (fun work coef j => cgs2 tag (IExp.const N) (j + 1) 1 work 0 coef 0) :
        Builder P ι ℕ ℕ Unit).run (st.allocate tag (N * N) (I.width tag)) = some out
  rw [exec_run_bind I (b := forRange (IExp.const N * IExp.const N) fun i =>
    stmt (.rom tag ⟨7, .var i⟩ (.var i))) (fun _ => rfl), hload, Option.bind_some]
  exact hloop

/-- A rounded step with accuracy $0$ is exact: the work vector is
$\mathbf{z} = \mathbf{w} - (\mathbf{v}_c \cdot \mathbf{w})\mathbf{v}_c$ for
$\mathbf{w} = \mathbf{A}\mathbf{v}_c - \beta_p\mathbf{v}_p$, the coefficient is
$\alpha = \mathbf{v}_c \cdot \mathbf{w}$, the norms are $\nu = \|\mathbf{z}\|$ and
$\beta = \|\mathbf{z}'\|$, and $\mathbf{v}_n = \|\mathbf{z}'\|^{-1}\mathbf{z}'$. -/
private theorem RoundedStep.exact {N m : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {G : Matrix (Fin N) (Fin m) ℝ → (Fin N → ℝ) → (Fin m → ℝ) → (Fin N → ℝ) → Prop}
    {V : Matrix (Fin N) (Fin m) ℝ} {vp vc vn : Fin N → ℝ} {βp α ν β : ℝ}
    {uv wv zv z' : Fin N → ℝ} {h : Fin m → ℝ}
    (hs : RoundedStep A 0 G V vp vc vn βp α ν β uv wv zv z' h) :
    zv = A *ᵥ vc - βp • vp - (vc ⬝ᵥ (A *ᵥ vc - βp • vp)) • vc ∧ ν = ‖WithLp.toLp 2 zv‖ ∧
      G V zv h z' ∧ β = ‖WithLp.toLp 2 z'‖ ∧ vn = ‖WithLp.toLp 2 z'‖⁻¹ • z' ∧
      α = vc ⬝ᵥ (A *ᵥ vc - βp • vp) := by
  have z0 : ∀ x : Fin N → ℝ, ‖WithLp.toLp 2 x‖ ≤ 0 → x = 0 := fun x h =>
    (WithLp.toLp_eq_zero 2).mp (norm_le_zero_iff.mp h)
  obtain ⟨e₁, e₂, e₃, e₄, -, e₅, eG, e₆, e₇, -, hvz⟩ := hs
  simp only [zero_mul] at e₁ e₂ e₃ e₄ e₅ e₆ e₇
  have hu : uv = A *ᵥ vc := (sub_eq_zero.mp (z0 _ e₁)).symm
  have hw : wv = uv - βp • vp := (sub_eq_zero.mp (z0 _ e₂)).symm
  have ha : α = vc ⬝ᵥ wv := (sub_eq_zero.mp (abs_nonpos_iff.mp e₃)).symm
  have hβ : β = ‖WithLp.toLp 2 z'‖ := sub_eq_zero.mp (abs_nonpos_iff.mp e₆)
  have hz' : z' = β • vn := sub_eq_zero.mp (z0 _ e₇)
  refine ⟨by rw [(sub_eq_zero.mp (z0 _ e₄)).symm, ha, hw, hu],
    sub_eq_zero.mp (abs_nonpos_iff.mp e₅), eG, hβ, ?_, by rw [ha, hw, hu]⟩
  by_cases h0 : β = 0
  · rw [hvz h0, ← hβ, h0, inv_zero, zero_smul]
  · rw [← hβ, hz', smul_smul, inv_mul_cancel₀ h0, one_smul]

end LanczosReorthImplementation

open LanczosReorthImplementation

/-- One exact Gram–Schmidt pass against the stored columns as a matrix product: for
$Q_k = \mathbf{v}_{k+1}$ ($k \le c$), the projection of $\mathbf{w}$ against
$Q_0, \dots, Q_c$ is $\mathbf{w} - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w}$ for the basis
$\mathbf{V} = (\mathbf{v}_1, \dots, \mathbf{v}_{c+1})$. -/
private theorem cgsProject_eq_sub_basisOf_mulVec {N c : ℕ} (Q v : ℕ → Fin N → ℝ)
    (hQ : ∀ k ≤ c, Q k = v (k + 1)) (w : Fin N → ℝ) :
    cgsProject Q (c + 1) w = w - LanczosReorthRun.basisOf v (c + 1) *ᵥ
      ((LanczosReorthRun.basisOf v (c + 1))ᵀ *ᵥ w) := by
  ext r
  simp only [cgsProject, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, LanczosReorthRun.basisOf,
    Matrix.of_apply, star_trivial]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun i => (∑ x, Q i x * w x) * Q i r) (c + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hQ k (by omega)]
  ring

/-- The exact recurrence read off the stored sequences: sequences that start with
$\mathbf{v}_0 = \mathbf{0}$, $\beta_0 = 0$, $\mathbf{v}_1 = \mathbf{b}/\|\mathbf{b}\|$ and satisfy
the exact step relations of the program (Paige's updates, two Gram–Schmidt passes, the norms)
are the states of `NLAlib.lanczosReorthState`. -/
private theorem lanczosReorthState_eq_of_exact {N q : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : ℕ → Fin N → ℝ) (β ν : ℕ → ℝ) (hv0 : v 0 = 0) (hb0 : β 0 = 0)
    (hv1 : v 1 = ‖WithLp.toLp 2 b‖⁻¹ • b)
    (hstep : ∀ j < q, ∃ zv z' : Fin N → ℝ,
      zv = A *ᵥ v (j + 1) - β j • v j - (v (j + 1) ⬝ᵥ (A *ᵥ v (j + 1) - β j • v j)) •
        v (j + 1) ∧
      ν (j + 1) = ‖WithLp.toLp 2 zv‖ ∧
      z' = (zv - LanczosReorthRun.basisOf v (j + 1) *ᵥ
          ((LanczosReorthRun.basisOf v (j + 1))ᵀ *ᵥ zv)) -
        LanczosReorthRun.basisOf v (j + 1) *ᵥ ((LanczosReorthRun.basisOf v (j + 1))ᵀ *ᵥ
          (zv - LanczosReorthRun.basisOf v (j + 1) *ᵥ
            ((LanczosReorthRun.basisOf v (j + 1))ᵀ *ᵥ zv))) ∧
      β (j + 1) = ‖WithLp.toLp 2 z'‖ ∧ v (j + 2) = ‖WithLp.toLp 2 z'‖⁻¹ • z') :
    ∀ c ≤ q, (lanczosReorthState A b c).cur = v (c + 1) ∧
      (lanczosReorthState A b c).prev = v c ∧ (lanczosReorthState A b c).beta = β c ∧
      (∀ k ≤ c, (lanczosReorthState A b c).vecs k = v (k + 1)) ∧
      (0 < c → (lanczosReorthState A b c).nu = ν c) := by
  intro c
  induction c with
  | zero =>
    intro _
    refine ⟨?_, by simp only [lanczosReorthState, hv0], by simp only [lanczosReorthState, hb0],
      fun k hk => ?_, fun h => absurd h (lt_irrefl 0)⟩
    · simp only [lanczosReorthState, zero_add, hv1]
      rfl
    · obtain rfl : k = 0 := by omega
      simp only [lanczosReorthState, Function.update_self, zero_add, hv1]
      rfl
  | succ c ih =>
    intro hc
    obtain ⟨hcur, hprev, hbeta, hvecs, -⟩ := ih (by omega)
    obtain ⟨zv, z', hzv, hν, hz', hβ, hvn⟩ := hstep c (by omega)
    have hz : A *ᵥ (lanczosReorthState A b c).cur -
        ((lanczosReorthState A b c).beta : ℝ) • (lanczosReorthState A b c).prev -
        (lanczosAlpha A (lanczosReorthState A b c).toLanczosState : ℝ) •
          (lanczosReorthState A b c).cur = zv := by
      rw [hzv, lanczosAlpha]
      simp only [LanczosReorthState.toLanczosState, hcur, hprev, hbeta, RCLike.re_to_real,
        star_trivial, RCLike.ofReal_real_eq_id, id]
    have hz'' : cgsProject (lanczosReorthState A b c).vecs (c + 1)
        (cgsProject (lanczosReorthState A b c).vecs (c + 1) zv) = z' := by
      rw [cgsProject_eq_sub_basisOf_mulVec _ v hvecs, cgsProject_eq_sub_basisOf_mulVec _ v hvecs,
        hz']
    have hst : lanczosReorthState A b (c + 1) =
        ⟨Function.update (lanczosReorthState A b c).vecs (c + 1)
          ((‖WithLp.toLp 2 z'‖⁻¹ : ℝ) • z'), (lanczosReorthState A b c).cur,
          (‖WithLp.toLp 2 z'‖⁻¹ : ℝ) • z', ‖WithLp.toLp 2 z'‖, ‖WithLp.toLp 2 zv‖⟩ := by
      change lanczosReorthStep A c (lanczosReorthState A b c) = _
      simp only [lanczosReorthStep, hz, hz'', RCLike.ofReal_real_eq_id, id]
    rw [hst]
    refine ⟨hvn.symm, hcur, hβ.symm, fun k hk => ?_, fun _ => hν.symm⟩
    by_cases hkc : k = c + 1
    · subst k
      simp only [Function.update_self]
      exact hvn.symm
    · simp only [Function.update_of_ne hkc]
      exact hvecs k (by omega)

/-- The exact run of the scoped loop of `NLAlib.lanczosReorthProg`: under exact arithmetic,
from a store with the seven declared buffers holding $\mathbf{b}$ and the matrix $\mathbf{A}$ in
the slot $7$, the loop with `gemv` products and `cgs2` orthogonalization succeeds and writes the
basis, the coefficients, the input norm, the previous vector and the norms of
`NLAlib.lanczosReorthState`. -/
private theorem exec_lanczosReorthLoop_exactSem {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem) (tag : P) (N q : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (st : St P ℝ (OpCount P ι))
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, N * N)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ w = b i)
    (hA : HoldsDecoded st.store (fun _ (x : ℝ) => x) tag 7 0 A) :
    ∃ out : St P ℝ (OpCount P ι),
      exec I (lanczosReorthLoop tag (IExp.const N) (IExp.const q) 0 1 2 3 4 5 6
        (fun work j => gemv tag (IExp.const N) (IExp.const N) 7 0 1 (IExp.const N * j) work 0)
        (fun work coef j => cgs2 tag (IExp.const N) (j + 1) 1 work 0 coef 0)).run st =
          some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 0 i = some w ∧ w = b i) ∧
      (∀ c ≤ q, ∀ i : Fin N, out.store.read tag 1 (N * c + i) =
        some ((lanczosReorthState A b c).cur i)) ∧
      (∀ c < q, out.store.read tag 2 c =
        some (lanczosAlpha A (lanczosReorthState A b c).toLanczosState)) ∧
      (∀ c ≤ q, out.store.read tag 3 c = some (lanczosReorthState A b c).beta) ∧
      out.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
      (∀ i : Fin N, out.store.read tag 5 i = some ((lanczosReorthState A b q).prev i)) ∧
      (∀ c < q, out.store.read tag 6 c = some (lanczosReorthState A b (c + 1)).nu) := by
  have hsem : IsRelErrSem (fun _ => (0 : ℝ)) (fun _ (x : ℝ) => x) (fun _ _ => True) I.sem :=
    hI ▸ isRelErrSem_exactSem
  have hz : AddsZeroExactly (fun _ (x : ℝ) => x) I.sem := hI ▸ addsZeroExactly_exactSem
  have hε : lanczosImplementationRoundoffBound N 0 = 0 := by
    rw [lanczosImplementationRoundoffBound_def]; ring
  have hsmall : lanczosImplementationRoundoffBound N 0 ≤ 1 / 100 := by rw [hε]; norm_num
  obtain ⟨out, v, α, β, ν, hrun, shout, hbl, hVl, hαl, hβl, hνl, hpl, ⟨w4, h4, e4⟩, hv0, hb0,
      -, hdir, hb01, hpf⟩ := exec_lanczosReorthLoop I tag hsem hz st N q (N * N) A b hshape hb
    (fun s => HoldsDecoded s (fun _ (x : ℝ) => x) tag 7 0 A) hA
    (fun s s' hs _ h7 i j => by rw [h7]; exact hs i j)
    (fun work j => gemv tag (IExp.const N) (IExp.const N) 7 0 1 (IExp.const N * j) work 0)
    (fun t => (hsem.isMatvecRoutine_gemv I tag hz N A 7 1 8 0 (IExp.const N * IExp.var t) 0
      (by simp) (by omega) (by omega)).mono (mul_le_mul_of_nonneg_right
        (roundingFactor_mul_sqrt_le_lanczosImplementationRoundoffBound N le_rfl hsmall)
        (specNorm_nonneg A)))
    (fun work coef j => cgs2 tag (IExp.const N) (j + 1) 1 work 0 coef 0)
    (fun _ V w _ w' => w' = (w - V *ᵥ (Vᵀ *ᵥ w)) - V *ᵥ (Vᵀ *ᵥ (w - V *ᵥ (Vᵀ *ᵥ w))))
    (fun t ht => ⟨executionComposable_single I (fun _ => rfl), fun s V w hs hV hw => by
      obtain ⟨out, mid, hr, hw1, hw2⟩ := exec_cgs2_exactSem I hI tag (IExp.const N)
        (IExp.var t + 1) rfl rfl 1 8 10 0 0 s V w
        (fun i j => by
          obtain ⟨x, hx, hxe⟩ := hV i j
          change s.store.read tag 1 (0 + i + N * j) = some (V i j)
          rw [hx]
          exact congrArg some hxe)
        (fun i => by
          obtain ⟨x, hx, hxe⟩ := hw i
          rw [IExp.eval_zero, zero_add, hx]
          exact congrArg some hxe)
        (fun i hi => ⟨N, by simp [hs, workspaceShape], by simpa using hi⟩)
        (fun i hi => ⟨q + 1, by simp [hs, workspaceShape], by simp at hi ⊢; omega⟩)
        ⟨by omega, by omega, by omega⟩
      exact ⟨out, _, _, mid, hr, hw1, hw2, rfl⟩⟩) hsmall
  have hv1 : v 1 = ‖WithLp.toLp 2 b‖⁻¹ • b := by
    by_cases hb0' : b = 0
    · rw [hb01 hb0', hb0', smul_zero]
    · have := hdir hb0'
      rw [hε, mul_zero] at this
      exact (sub_eq_zero.mp ((WithLp.toLp_eq_zero 2).mp (norm_le_zero_iff.mp this))).symm
  rw [hε] at hpf
  choose uv wv zv z' hh hpf' using hpf
  have hstep := fun j (hj : j < q) => (hpf' j hj).exact
  have hst := lanczosReorthState_eq_of_exact A b v β ν hv0 hb0 hv1 fun j hj => by
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := hstep j hj
    exact ⟨_, _, h1, h2, h3, h4, h5⟩
  refine ⟨out, hrun, shout, hbl, fun c hc i => ?_, fun c hc => ?_, fun c hc => ?_, ?_,
    fun i => ?_, fun c hc => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := hVl c hc i
    rw [hw, (hst c hc).1]
  · obtain ⟨w, hw, rfl⟩ := hαl c hc
    obtain ⟨hcur, hprev, hbeta, -, -⟩ := hst c hc.le
    rw [hw, (hstep c hc).2.2.2.2.2]
    simp only [lanczosAlpha, LanczosReorthState.toLanczosState, hcur, hprev, hbeta,
      RCLike.re_to_real, star_trivial, RCLike.ofReal_real_eq_id, id]
  · obtain ⟨w, hw, rfl⟩ := hβl c hc
    rw [hw, (hst c hc).2.2.1]
  · rw [hε, zero_mul] at e4
    have hw4 : w4 = ‖WithLp.toLp 2 b‖ := by
      linarith [abs_nonneg (‖WithLp.toLp 2 b‖ - w4), abs_le.mp e4]
    rw [h4, hw4]
  · obtain ⟨w, hw, rfl⟩ := hpl i
    rw [hw, (hst q le_rfl).2.1]
  · obtain ⟨w, hw, rfl⟩ := hνl c hc
    rw [hw, ((hst (c + 1) (by omega)).2.2.2.2 (by omega))]

/-- **The exact run of the stored-matrix tree**: under `NLAlib.Computation.storedInterp` (exact
arithmetic, the matrix as ROM, column-major), from the declared inputs, the compiled tree
succeeds and its buffers hold $\mathbf{b}$, the basis `NLAlib.lanczosReorthMatrix`, the
coefficients $\alpha_j$, $\beta_j$, the input norm, the last previous vector and the norms
$\nu_{j+1}$ of `NLAlib.lanczosReorthState`, for every real matrix (no symmetry or breakdown
premise). The output clause of the drafted target `StoredEntriesLanczosReorth`
(design note §2.3). No printed source.
Result: lanczos-reorth-program -/
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
  classical
  set A : Matrix (Fin N) (Fin N) ℝ := fun i j => vals (i + N * j) with hAdef
  let I : Interp P ι ℝ (OpCount P ι) := storedInterp (N ^ 2) vals ξ tag
  let st : St P ℝ (OpCount P ι) := inputState tag (List.ofFn ![(Array.ofFn b).map some,
    Array.replicate (N * (q + 1)) none, Array.replicate q none,
    Array.replicate (q + 1) none, Array.replicate 1 none, Array.replicate N none,
    Array.replicate q none])
  have hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q)] := by
    simp [st, inputState, Store.shape]
  obtain ⟨mid, hload, shm, hbm, hmA⟩ := exec_rom_load I tag st N q vals hshape
    (fun i hi => if_pos (by simpa only [Nat.pow_two] using hi))
  obtain ⟨out₁, hrun, shout, hbl, hVl, hαl, hβl, h4, hpl, hνl⟩ :=
    exec_lanczosReorthLoop_exactSem I rfl tag N q A b mid shm
      (fun i => ⟨b i, by rw [hbm i]; simp [st, inputState, Store.read, i.isLt], rfl⟩)
      (fun i j => ⟨_, by rw [hmA i j, Nat.add_comm], rfl⟩)
  have hsize₁ : out₁.store.size = 8 := by
    simpa [Store.shape] using congrArg Array.size (shout.trans shm)
  have rdo : ∀ p k i, k < 7 →
      (out₁.release tag (N * N) (I.width tag)).store.read p k i = out₁.store.read p k i :=
    fun p k i hk => Store.read_pop_of_lt (by rw [hsize₁]; omega)
  have hc0 (n : ℕ) (i : ℕ) (c : Fin 1) : 0 + i + n * c = i := by rw [Fin.val_eq_zero c]; ring
  have hsize : st.store.size = 7 := by simpa [Store.shape] using congrArg Array.size hshape
  refine ⟨_, exec_compiled_eq_some I tag st N q hsize hload hrun, fun i c => ?_, fun i j => ?_,
    fun j c => ?_,
    fun j c => ?_, by rw [rdo tag 4 _ (by omega), h4], fun i c => ?_, fun j c => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := hbl i
    rw [rdo tag 0 _ (by omega), hc0, hw]
  · rw [rdo tag 1 _ (by omega), show 0 + (i : ℕ) + N * j = N * j + i by ring,
      hVl j (by omega) i]
    simp only [lanczosReorthMatrix, Matrix.of_apply]
  · rw [rdo tag 2 _ (by omega), hc0, hαl j j.isLt]
  · rw [rdo tag 3 _ (by omega), hc0, hβl j (by omega)]
  · rw [rdo tag 5 _ (by omega), hc0, hpl i]
  · rw [rdo tag 6 _ (by omega), hc0, hνl j j.isLt]

/-- The static count of the stored-matrix tree: every component of the static operation
count of `NLAlib.lanczosReorthProg.compiled` is at most `NLAlib.lanczosReorthCount`. -/
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
  have hsum (f : ℕ → ℕ) : (List.map f (List.range q)).sum = ∑ x ∈ Finset.range q, f x := by
    rfl
  -- the loop bodies depend on the step through the CGS2 width `j + 1`: Gauss's sum
  have hS : 2 * ∑ x ∈ Finset.range q, x + q = q * q := by
    have h := Finset.sum_range_id_mul_two q
    rcases q with _ | q
    · simp
    · simp only [Nat.add_sub_cancel] at h
      nlinarith
  cases k <;> simp only [lanczosReorthCount, Finsupp.add_apply, Finsupp.single_apply,
    OpKind.bin.injEq, OpKind.un.injEq, OpKind.lit.injEq, OpKind.cmp.injEq,
    OpKind.copy.injEq, OpKind.rom.injEq, reduceCtorEq, add_zero, zero_add, mul_zero,
    ite_false, hsum]
  case bin p b =>
    cases b <;> by_cases hp : tag = p <;>
      simp [hp, Finset.sum_add_distrib, add_mul, ← Finset.sum_mul] <;> nlinarith
  case un p u =>
    cases u <;> by_cases hp : tag = p <;>
      simp [hp, Finset.sum_add_distrib, add_mul, ← Finset.sum_mul] <;> nlinarith
  case lit p =>
    by_cases hp : tag = p
    · simp [hp, Finset.sum_add_distrib]; nlinarith
    · simp [hp]
  all_goals (try split_ifs) <;> norm_num <;> ring_nf <;> omega

end NLAlib
