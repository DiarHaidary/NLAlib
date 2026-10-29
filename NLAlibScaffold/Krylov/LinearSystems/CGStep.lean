/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.CGRun
public import NLAlibScaffold.Krylov.LinearSystems.CGProgramTree
public import NLAlibScaffold.Krylov.Processes.LanczosProgramRun

/-!
# One step of the conjugate gradient program in the standard model

One step of `NLAlib.cgStepWith` under `NLAlib.Computation.IsRelErrSem`, for any product `mv`
meeting a normwise matvec specification (`NLAlib.LanczosMvSpec`), from a state with
$\nu \ne 0$ and a direction whose curvature is positive in the standard model, succeeds and has
the local errors of the clauses of `NLAlib.CGRun` (`NLAlib.CGStepData.IsStep`): the product,
the curvature and the squared residual norm ($\gamma_N$), the two divisions ($u$) and the three
updates ($\gamma_2$). The tools are those of the Lanczos step
(`NLAlibScaffold/Krylov/Processes/LanczosStep.lean`). Helper file of
`NLAlibScaffold/Krylov/LinearSystems/CGRounding.lean`.

Research branch `research/hscg-fp`. Design: `docs/design/research/Krylov-CGRounding.md` (§2.2).

## Main definitions

* `NLAlib.CGStepData`, `NLAlib.CGStepData.IsStep`: the data and the local errors of one step.

## Main results

* `NLAlib.exec_cgStepWith`: one step.
-/

@[expose] public section

open Finset
open scoped Matrix

namespace NLAlib

open Computation Builder

/-- The data of one computed step of conjugate gradients: the product $\mathbf{s}$, the
curvature $\mu$, the step length $\gamma$, the new iterate, residual and direction, the new
squared residual norm $\nu'$, the coefficient $\delta$, and the errors. -/
structure CGStepData (N : ℕ) where
  /-- The computed product. -/
  s : Fin N → ℝ
  /-- Its error. -/
  es : Fin N → ℝ
  /-- The computed curvature. -/
  μ : ℝ
  /-- Its error. -/
  eμ : ℝ
  /-- The step length. -/
  γ : ℝ
  /-- Its relative error. -/
  eγ : ℝ
  /-- The new iterate. -/
  x : Fin N → ℝ
  /-- Its error. -/
  ex : Fin N → ℝ
  /-- The new residual. -/
  r : Fin N → ℝ
  /-- Its error. -/
  er : Fin N → ℝ
  /-- The new squared residual norm. -/
  ν : ℝ
  /-- Its relative error. -/
  θ : ℝ
  /-- The direction coefficient. -/
  δ : ℝ
  /-- Its relative error. -/
  eδ : ℝ
  /-- The new direction. -/
  p : Fin N → ℝ
  /-- Its error. -/
  ep : Fin N → ℝ

/-- **The local errors of one step** from $(\mathbf{x}, \mathbf{r}, \mathbf{p}, \nu)$, as the
clauses of `NLAlib.CGRun` at one index. -/
structure CGStepData.IsStep {N : ℕ} (D : CGStepData N) (A : Matrix (Fin N) (Fin N) ℝ) (ε : ℝ)
    (x r p : Fin N → ℝ) (ν : ℝ) : Prop where
  /-- The computed product. -/
  s_eq : D.s = A *ᵥ p + D.es
  /-- The product error. -/
  norm_es_le : ‖WithLp.toLp 2 D.es‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 p‖
  /-- The computed curvature. -/
  μ_eq : D.μ = p ⬝ᵥ D.s + D.eμ
  /-- The curvature error. -/
  abs_eμ_le : |D.eμ| ≤ ε * ‖WithLp.toLp 2 p‖ * ‖WithLp.toLp 2 D.s‖
  /-- The curvature is positive. -/
  μ_pos : 0 < D.μ
  /-- The step length. -/
  γ_eq : D.γ = ν / D.μ * (1 + D.eγ)
  /-- Its relative error. -/
  abs_eγ_le : |D.eγ| ≤ ε
  /-- The iterate update. -/
  x_succ : D.x = x + D.γ • p + D.ex
  /-- The iterate update error. -/
  norm_ex_le : ‖WithLp.toLp 2 D.ex‖ ≤ ε * (‖WithLp.toLp 2 x‖ + |D.γ| * ‖WithLp.toLp 2 p‖)
  /-- The residual update. -/
  r_succ : D.r = r - D.γ • D.s + D.er
  /-- The residual update error. -/
  norm_er_le : ‖WithLp.toLp 2 D.er‖ ≤ ε * (‖WithLp.toLp 2 r‖ + |D.γ| * ‖WithLp.toLp 2 D.s‖)
  /-- The new squared residual norm. -/
  ν_eq : D.ν = ‖WithLp.toLp 2 D.r‖ ^ 2 * (1 + D.θ)
  /-- Its relative error. -/
  abs_θ_le : |D.θ| ≤ ε
  /-- The direction coefficient. -/
  δ_eq : D.δ = D.ν / ν * (1 + D.eδ)
  /-- Its relative error. -/
  abs_eδ_le : |D.eδ| ≤ ε
  /-- The direction update. -/
  p_succ : D.p = D.r + D.δ • p + D.ep
  /-- The direction update error. -/
  norm_ep_le : ‖WithLp.toLp 2 D.ep‖ ≤ ε * (‖WithLp.toLp 2 D.r‖ + |D.δ| * ‖WithLp.toLp 2 p‖)

section Pieces

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C) {p : P}
  {u : P → ℝ} {dec : P → K → ℝ}

/-- **A copy of a decoded cell** into a writable cell. -/
theorem exec_copy_decCell (st : St P K C) {S : Array (P × ℕ)} (hsh : st.store.shape = S)
    (dst src : Cell ℕ ℕ) {L : ℕ} {v : ℝ} (hS : S[dst.buf]? = some (p, L)) (hd : dst.idx.eval < L)
    (hv : DecCell st.store p dec src.buf src.idx.eval v) :
    ∃ st' : St P K C, exec I (ins (ι := ι) (.copy p dst src)).run st = some st' ∧
      StoreFrame p st.store st'.store (StoreBlock dst.buf dst.idx.eval 1) ∧
      DecCell st'.store p dec dst.buf dst.idx.eval v := by
  obtain ⟨w, hw, hdw⟩ := hv
  obtain ⟨s₁, hs₁⟩ := exists_write_of_shape hsh hS hd w
  obtain ⟨st₁, h₁, hst₁⟩ := exec_ins_copy I (st := st) (dst := dst) (src := src) hw hs₁
  exact ⟨st₁, h₁, hst₁ ▸ storeFrame_of_write hs₁, hdw ▸ hst₁ ▸ DecCell.of_write hs₁⟩

/-- **A negation of a decoded cell** into a writable cell (exact). -/
theorem exec_neg_decCell (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C)
    {S : Array (P × ℕ)} (hsh : st.store.shape = S) (dst src : Cell ℕ ℕ) {L : ℕ} {v : ℝ}
    (hS : S[dst.buf]? = some (p, L)) (hd : dst.idx.eval < L)
    (hv : DecCell st.store p dec src.buf src.idx.eval v) :
    ∃ st' : St P K C, exec I (ins (ι := ι) (.un p .neg dst src)).run st = some st' ∧
      StoreFrame p st.store st'.store (StoreBlock dst.buf dst.idx.eval 1) ∧
      DecCell st'.store p dec dst.buf dst.idx.eval (-v) := by
  obtain ⟨w, hw, hdw⟩ := hv
  obtain ⟨z, hz, hdz⟩ := h.neg p w
  obtain ⟨s₁, hs₁⟩ := exists_write_of_shape hsh hS hd z
  obtain ⟨st₁, h₁, hst₁⟩ := exec_ins_un I (st := st) (dst := dst) (x := src) hw hz hs₁
  refine ⟨st₁, h₁, hst₁ ▸ storeFrame_of_write hs₁, ⟨z, ?_, by rw [hdz, hdw]⟩⟩
  rw [hst₁]; exact Store.read_of_write_eq_some hs₁

/-- **A zero literal** into a writable cell. -/
theorem exec_lit_zero_decCell (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C)
    {S : Array (P × ℕ)} (hsh : st.store.shape = S) (dst : Cell ℕ ℕ) {L : ℕ}
    (hS : S[dst.buf]? = some (p, L)) (hd : dst.idx.eval < L) :
    ∃ st' : St P K C, exec I (ins (ι := ι) (.lit p dst 0)).run st = some st' ∧
      StoreFrame p st.store st'.store (StoreBlock dst.buf dst.idx.eval 1) ∧
      DecCell st'.store p dec dst.buf dst.idx.eval 0 := by
  obtain ⟨z0, hz0⟩ := h.lit_ok p 0 trivial
  have hdz0 : dec p z0 = 0 := by
    obtain ⟨δ, -, hδ⟩ := h.lit_err p 0 z0 hz0
    simpa using hδ
  obtain ⟨s₁, hs₁⟩ := exists_write_of_shape hsh hS hd z0
  obtain ⟨st₁, h₁, hst₁⟩ := exec_ins_lit I (st := st) (dst := dst) hz0 hs₁
  refine ⟨st₁, h₁, hst₁ ▸ storeFrame_of_write hs₁, ⟨z0, ?_, hdz0⟩⟩
  rw [hst₁]; exact Store.read_of_write_eq_some hs₁

/-- **A division of decoded cells** by a nonzero value: one rounding. -/
theorem exec_div_decCell (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C)
    {S : Array (P × ℕ)} (hsh : st.store.shape = S) (dst x y : Cell ℕ ℕ) {L : ℕ} {a c : ℝ}
    (hS : S[dst.buf]? = some (p, L)) (hd : dst.idx.eval < L)
    (hx : DecCell st.store p dec x.buf x.idx.eval a)
    (hy : DecCell st.store p dec y.buf y.idx.eval c) (hc : c ≠ 0) :
    ∃ (st' : St P K C) (δ : ℝ), exec I (ins (ι := ι) (.bin p .div dst x y)).run st = some st' ∧
      StoreFrame p st.store st'.store (StoreBlock dst.buf dst.idx.eval 1) ∧ |δ| ≤ u p ∧
      DecCell st'.store p dec dst.buf dst.idx.eval (a / c * (1 + δ)) := by
  obtain ⟨wx, hwx, hdx⟩ := hx
  obtain ⟨wy, hwy, hdy⟩ := hy
  obtain ⟨z, hz⟩ := h.bin_ok p .div wx wy trivial (fun _ => hdy ▸ hc) trivial
  obtain ⟨δ, hδ, hdz⟩ := h.bin_err p .div wx wy z trivial hz
  obtain ⟨s₁, hs₁⟩ := exists_write_of_shape hsh hS hd z
  refine ⟨_, δ, (exec_seq_instr_bin I hwx hwy hz hs₁).trans (exec_skip I _),
    storeFrame_of_write hs₁, hδ, ⟨z, Store.read_of_write_eq_some hs₁, ?_⟩⟩
  rw [hdz, hdx, hdy]; rfl

/-- **`axpy` on two disjoint slots of `W`**: $\mathbf{y}' = \mathbf{y} + a\mathbf{x}$ up to
$\gamma_2(\|\mathbf{y}\| + \lvert a\rvert\|\mathbf{x}\|)$. -/
theorem exec_axpy_decVec (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hu : 2 * u p < 1)
    (st : St P K C) (a : Cell ℕ ℕ) {W : ℕ}
    (X Y : IExp ℕ) {N : ℕ} {x y : Fin N → ℝ} {av : ℝ} (haW : a.buf ≠ W)
    (hXY : X.eval + N ≤ Y.eval ∨ Y.eval + N ≤ X.eval)
    (ha : DecCell st.store p dec a.buf a.idx.eval av)
    (hx : DecVec st.store p dec W X.eval x) (hy : DecVec st.store p dec W Y.eval y) :
    ∃ (st' : St P K C) (y' : Fin N → ℝ),
      exec I (axpy p a W X W Y (.const N)).run st = some st' ∧
      StoreFrame p st.store st'.store (StoreBlock W Y.eval N) ∧
      DecVec st'.store p dec W Y.eval y' ∧
      ‖WithLp.toLp 2 (y' - (y + av • x))‖ ≤
        roundingFactor 2 (u p) * (‖WithLp.toLp 2 y‖ + |av| * ‖WithLp.toLp 2 x‖) := by
  obtain ⟨st₂, Wv, h₂, hb₂, hW⟩ := IsRelErrSem.exec_axpy I p st h a W X W Y (.const N)
    av (vecSeq x) (vecSeq y) hu ha hx.nat hy.nat (fun h' => absurd h' haW) (fun _ i hi j hj he => by
      simp only [IExp.eval_const] at hi hj; omega)
  have hf₂ := storeFrame_of_writeBlock hb₂
  simp only [Array.size_map, List.size_toArray, List.length_range, IExp.eval_const] at hf₂
  refine ⟨st₂, fun i => dec p (Wv i), h₂, hf₂, DecVec.of_writeBlock hb₂, ?_⟩
  have hu0 : 0 ≤ u p := h.nonneg trivial
  have hγ0 : 0 ≤ roundingFactor 2 (u p) := roundingFactor_nonneg hu0 (by exact_mod_cast hu)
  have hW' : ∀ i : Fin N, ∃ θ δ : ℝ, |θ| ≤ roundingFactor 2 (u p) ∧ |δ| ≤ u p ∧
      dec p (Wv i) = av * x i * (1 + θ) + y i * (1 + δ) := fun i => by
    simpa [vecSeq_fin] using hW i (by simp)
  choose θ δ hθ hδ hWe using hW'
  have heq : (fun i : Fin N => dec p (Wv i)) - (y + av • x) =
      (fun i : Fin N => (av * x i) * θ i) + fun i => y i * δ i := by
    ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hWe]; ring
  rw [heq, WithLp.toLp_add]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_toLp_mul_le (x := fun i => av * x i) hγ0 hθ
  have h2 := norm_toLp_mul_le (x := y) hu0 hδ
  have h3 : ‖WithLp.toLp 2 (fun i => av * x i)‖ = |av| * ‖WithLp.toLp 2 x‖ := by
    rw [show (fun i => av * x i) = av • x from rfl, WithLp.toLp_smul, norm_smul,
      Real.norm_eq_abs]
  rw [h3] at h1
  have huγ : u p ≤ roundingFactor 2 (u p) := (le_roundingFactor_one hu0 (by linarith)).trans
    (roundingFactor_le_roundingFactor hu0 (by norm_num) (by exact_mod_cast hu))
  nlinarith [norm_nonneg (WithLp.toLp 2 y), abs_nonneg av, norm_nonneg (WithLp.toLp 2 x)]

/-- **The inner product of two slots** into a writable cell outside `W`: $\mu$ is
$\mathbf{x}^{\mathsf{T}}\mathbf{y}$ up to $\gamma_N\|\mathbf{x}\|\|\mathbf{y}\|$. -/
theorem exec_dot_decCell (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hN : (N : ℝ) * u p < 1) (st : St P K C)
    {S : Array (P × ℕ)} (hsh : st.store.shape = S) (dst : Cell ℕ ℕ) {W L : ℕ} (X Y : IExp ℕ)
    {x y : Fin N → ℝ} (hdW : dst.buf ≠ W) (hS : S[dst.buf]? = some (p, L))
    (hd : dst.idx.eval < L) (hx : DecVec st.store p dec W X.eval x)
    (hy : DecVec st.store p dec W Y.eval y) :
    ∃ (st' : St P K C) (μ : ℝ), exec I (dot p dst W X W Y (.const N)).run st = some st' ∧
      StoreFrame p st.store st'.store (StoreBlock dst.buf dst.idx.eval 1) ∧
      DecCell st'.store p dec dst.buf dst.idx.eval μ ∧
      |μ - x ⬝ᵥ y| ≤ roundingFactor N (u p) * ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
  obtain ⟨z0, -⟩ := h.lit_ok p 0 trivial
  obtain ⟨st₁, w₁, h₁, hw₁, hb₁⟩ := IsRelErrSem.exec_dot_abs_sum_mul_sub_le I p st h hz dst
    W X W Y (.const N) (vecSeq x) (vecSeq y) hN hx.nat hy.nat (fun h' => absurd h' hdW)
    (fun h' => absurd h' hdW) ⟨z0, exists_write_of_shape hsh hS hd z0⟩
  refine ⟨st₁, dec p w₁, h₁, storeFrame_of_write hw₁, DecCell.of_write hw₁, ?_⟩
  simp only [IExp.eval_const, sum_range_extendZero (fun a b => a * b),
    sum_range_extendZero (fun a b => |a| * |b|)] at hb₁
  rw [abs_sub_comm]
  calc _ ≤ _ := hb₁
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (sum_abs_mul_abs_le_norm x y)
        (roundingFactor_nonneg (h.nonneg trivial) hN)

/-- **The squared norm of a decoded vector** into a writable cell outside its buffer:
$\nu = \|\mathbf{x}\|^2(1 + \theta)$, $1 + \theta$ a product of $N$ rounding errors (a weighted
mean of the product form of `dot`). -/
theorem exec_dot_self_decCell (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hu1 : u p < 1) (st : St P K C)
    {S : Array (P × ℕ)} (hsh : st.store.shape = S) (dst : Cell ℕ ℕ) {X L : ℕ} (xo : IExp ℕ)
    {x : Fin N → ℝ} (hdX : dst.buf ≠ X) (hS : S[dst.buf]? = some (p, L))
    (hd : dst.idx.eval < L) (hx : DecVec st.store p dec X xo.eval x) :
    ∃ (st' : St P K C) (ν θ : ℝ), exec I (dot p dst X xo X xo (.const N)).run st = some st' ∧
      StoreFrame p st.store st'.store (StoreBlock dst.buf dst.idx.eval 1) ∧
      DecCell st'.store p dec dst.buf dst.idx.eval ν ∧ IsRoundingProduct (u p) N θ ∧
      ν = ‖WithLp.toLp 2 x‖ ^ 2 * (1 + θ) := by
  obtain ⟨z0, -⟩ := h.lit_ok p 0 trivial
  obtain ⟨st₁, w₁, h₁, hw₁, η, hη, hd₁⟩ :=
    IsRelErrSem.exec_dot_eq_sum_mul_one_add_isRoundingProduct I p st h hz dst X xo X xo
      (.const N) (vecSeq x) (vecSeq x) hx.nat hx.nat (fun h' => absurd h' hdX)
      (fun h' => absurd h' hdX) ⟨z0, exists_write_of_shape hsh hS hd z0⟩
  have hsum : dec p w₁ = ∑ i : Fin N, x i * x i * (1 + η i) := by
    rw [hd₁, IExp.eval_const, ← Fin.sum_univ_eq_sum_range (fun i => vecSeq x i * vecSeq x i *
      (1 + η i))]
    simp [vecSeq_fin]
  obtain ⟨θ, hθ, hθe⟩ := exists_isRoundingProduct_sum_mul_one_add_eq (h.nonneg trivial) hu1
    Finset.univ (fun i : Fin N => x i * x i) (fun i => η i) (fun i _ => mul_self_nonneg _)
    (fun i _ => hη i (by simp))
  refine ⟨st₁, dec p w₁, θ, h₁, storeFrame_of_write hw₁, DecCell.of_write hw₁, hθ, ?_⟩
  rw [hsum, hθe, EuclideanSpace.norm_sq_eq]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs, sq]

/-- A cell or a slot outside the blocks of a frame, by arithmetic on the indices. -/
local macro "cg_nb" : tactic => `(tactic| (intro hb; simp only [StoreBlock, IExp.eval_ofNat,
  IExp.eval_const, IExp.eval_zero, IExp.eval_one, IExp.eval_add, IExp.eval_mul] at hb; omega))

/-- **The product, the curvature and the step length of a CG step**: $\mathbf{s} \leftarrow
\mathbf{A}\mathbf{p}$ in slot `2N`, $\mu \leftarrow \mathbf{p}^{\mathsf{T}}\mathbf{s}$ in `s[1]`,
$\gamma \leftarrow \nu/\mu$ in `s[2]` and in `gC`. The curvature is positive by `hpos`. -/
theorem exec_cg_curvature (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hN : (N : ℝ) * u p < 1)
    {mv : ℕ → IExp ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit} {R : ℕ} {s₀ : Store P K}
    {A : Matrix (Fin N) (Fin N) ℝ} {c ε : ℝ} (hmv : LanczosMvSpec I mv p dec R s₀ A c)
    (hc : c ≤ ε * specNorm A) (hεN : roundingFactor N (u p) ≤ ε)
    (st : St P K C) {S : Array (P × ℕ)} (hsh : st.store.shape = S)
    (hR : ∀ i, st.store.read p R i = s₀.read p R i) {W sb Lg : ℕ} (pc : IExp ℕ) (gC : Cell ℕ ℕ)
    (hWs : W ≠ sb) (hRW : R ≠ W) (hS : S[sb]? = some (p, 7)) (hSW : S[W]? = some (p, 5 * N))
    (hSg : S[gC.buf]? = some (p, Lg)) (hgi : gC.idx.eval < Lg) (hgW : gC.buf ≠ W)
    (hgs : gC.buf ≠ sb) (hpc : 3 * N ≤ pc.eval ∧ pc.eval + N ≤ 5 * N) {pv : Fin N → ℝ}
    {ν : ℝ} (hp : DecVec st.store p dec W pc.eval pv) (hν : DecCell st.store p dec sb 0 ν)
    (hpos : ∀ (es : Fin N → ℝ) (eμ : ℝ), ‖WithLp.toLp 2 es‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 pv‖ →
      |eμ| ≤ ε * ‖WithLp.toLp 2 pv‖ * ‖WithLp.toLp 2 (A *ᵥ pv + es)‖ →
      0 < pv ⬝ᵥ (A *ᵥ pv + es) + eμ) :
    ∃ (st' : St P K C) (sv : Fin N → ℝ) (μ γ eγ : ℝ), (∀ f, exec I (mv W pc (2 * IExp.const N) >>=
        fun _ => dot p ⟨sb, 1⟩ W pc W (2 * IExp.const N) (.const N) >>=
        fun _ => ins (.bin p .div ⟨sb, 2⟩ ⟨sb, 0⟩ ⟨sb, 1⟩) >>=
        fun _ => ins (.copy p gC ⟨sb, 2⟩) >>= f).run st = exec I (f ()).run st') ∧
      StoreFrame p st.store st'.store (fun b i => StoreBlock W (2 * N) N b i ∨
        StoreBlock sb 1 2 b i ∨ StoreBlock gC.buf gC.idx.eval 1 b i) ∧
      DecVec st'.store p dec W (2 * N) sv ∧ DecCell st'.store p dec sb 2 γ ∧
      DecCell st'.store p dec gC.buf gC.idx.eval γ ∧
      ‖WithLp.toLp 2 (sv - A *ᵥ pv)‖ ≤ c * ‖WithLp.toLp 2 pv‖ ∧
      |μ - pv ⬝ᵥ sv| ≤ roundingFactor N (u p) * ‖WithLp.toLp 2 pv‖ * ‖WithLp.toLp 2 sv‖ ∧
      0 < μ ∧ γ = ν / μ * (1 + eγ) ∧ |eγ| ≤ u p := by
  obtain ⟨z0, -⟩ := h.lit_ok p 0 trivial
  obtain ⟨st₁, sv, h₁, hf₁, hs₁, hb₁⟩ := hmv.2 st W pc (2 * IExp.const N) pv hRW hR
    (by simp; omega) hp fun i hi => ⟨z0, exists_write_of_shape hsh hSW (by simp; omega) z0⟩
  replace hf₁ : StoreFrame p st.store st₁.store (StoreBlock W (2 * N) N) := hf₁
  replace hs₁ : DecVec st₁.store p dec W (2 * N) sv := hs₁
  have hs₁' : DecVec st₁.store p dec W (2 * IExp.const N).eval sv := hs₁
  obtain ⟨st₂, μ, h₂, hf₂, hμ₂, hb₂⟩ := exec_dot_decCell I h hz hN st₁ (hf₁.1.trans hsh)
    ⟨sb, 1⟩ pc (2 * IExp.const N) (x := pv) (y := sv) hWs.symm hS (by norm_num)
    (hp.frame hf₁ fun i hi => by cg_nb) hs₁'
  have hμ : 0 < μ := by
    have := hpos (sv - A *ᵥ pv) (μ - pv ⬝ᵥ sv) (hb₁.trans (by gcongr)) (by
      rw [add_sub_cancel]
      refine hb₂.trans ?_
      gcongr)
    rwa [add_sub_cancel, add_sub_cancel] at this
  obtain ⟨st₃, eγ, h₃, hf₃, heγ, hγ₃⟩ := exec_div_decCell I h st₂ ((hf₁.trans hf₂).1.trans hsh)
    ⟨sb, 2⟩ ⟨sb, 0⟩ ⟨sb, 1⟩ hS (by norm_num)
    ((hν.frame hf₁ (by cg_nb)).frame hf₂ (by cg_nb)) hμ₂ hμ.ne'
  obtain ⟨st₄, h₄, hf₄, hγ₄⟩ := exec_copy_decCell I st₃ ((hf₁.trans hf₂ |>.trans hf₃).1.trans hsh)
    gC ⟨sb, 2⟩ hSg hgi hγ₃
  refine ⟨st₄, sv, μ, ν / μ * (1 + eγ), eγ, fun f => ?_, ?_,
    ((hs₁.frame hf₂ fun i hi => by cg_nb).frame hf₃ fun i hi => by cg_nb).frame hf₄
      fun i hi => by cg_nb, hγ₃.frame hf₄ (by cg_nb), hγ₄, hb₁, hb₂, hμ, rfl, heγ⟩
  · rw [exec_bind_of_exec_eq_some I h₁ (hmv.1 _ _ _),
      exec_bind_of_exec_eq_some I h₂ (seqShape_dot _ _ _ _ _ _ _),
      exec_bind_of_exec_eq_some I h₃ (seqShape_ins _),
      exec_bind_of_exec_eq_some I h₄ (seqShape_ins _)]
  · refine (((hf₁.trans hf₂).trans hf₃).trans hf₄).mono fun b i hb => ?_
    rcases hb with ((hb | ⟨rfl, h1, h2⟩) | ⟨rfl, h1, h2⟩) | hb
    · exact Or.inl hb
    · exact Or.inr (Or.inl ⟨rfl, by simp at h1; omega, by simp at h2; omega⟩)
    · exact Or.inr (Or.inl ⟨rfl, by simp at h1; omega, by simp at h2; omega⟩)
    · exact Or.inr (Or.inr hb)

/-- **The iterate and residual updates and the coefficient of a CG step**:
$\mathbf{x} \leftarrow \gamma\mathbf{p} + \mathbf{x}$, `s[6]` $\leftarrow -\gamma$,
$\mathbf{r} \leftarrow -\gamma\mathbf{s} + \mathbf{r}$, $\nu' \leftarrow
\mathbf{r}^{\mathsf{T}}\mathbf{r}$ in `s[4]`, $\delta \leftarrow \nu'/\nu$ in `s[5]` and in
`dC`. -/
theorem exec_cg_update (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hu2 : 2 * u p < 1) (hu1 : u p < 1)
    (st : St P K C) {S : Array (P × ℕ)} (hsh : st.store.shape = S) {W sb Ld : ℕ}
    (pc : IExp ℕ) (dC : Cell ℕ ℕ) (hWs : W ≠ sb) (hS : S[sb]? = some (p, 7))
    (hSd : S[dC.buf]? = some (p, Ld)) (hdi : dC.idx.eval < Ld) (hdW : dC.buf ≠ W)
    (hds : dC.buf ≠ sb) (hpc : 3 * N ≤ pc.eval ∧ pc.eval + N ≤ 5 * N)
    {xv rv pv sv : Fin N → ℝ} {ν γ : ℝ} (hx : DecVec st.store p dec W 0 xv)
    (hr : DecVec st.store p dec W N rv) (hp : DecVec st.store p dec W pc.eval pv)
    (hs : DecVec st.store p dec W (2 * N) sv) (hν : DecCell st.store p dec sb 0 ν)
    (hγ : DecCell st.store p dec sb 2 γ) (hν0 : ν ≠ 0) :
    ∃ (st' : St P K C) (x' r' : Fin N → ℝ) (ν' θ δ eδ : ℝ), (∀ f, exec I
        (axpy p ⟨sb, 2⟩ W pc W 0 (.const N) >>= fun _ =>
          ins (.un p .neg ⟨sb, 6⟩ ⟨sb, 2⟩) >>= fun _ =>
          axpy p ⟨sb, 6⟩ W (2 * IExp.const N) W (.const N) (.const N) >>= fun _ =>
          dot p ⟨sb, 4⟩ W (.const N) W (.const N) (.const N) >>= fun _ =>
          ins (.bin p .div ⟨sb, 5⟩ ⟨sb, 4⟩ ⟨sb, 0⟩) >>= fun _ =>
          ins (.copy p dC ⟨sb, 5⟩) >>= f).run st = exec I (f ()).run st') ∧
      StoreFrame p st.store st'.store (fun b i => StoreBlock W 0 (2 * N) b i ∨
        StoreBlock sb 4 3 b i ∨ StoreBlock dC.buf dC.idx.eval 1 b i) ∧
      DecVec st'.store p dec W 0 x' ∧ DecVec st'.store p dec W N r' ∧
      DecCell st'.store p dec sb 4 ν' ∧ DecCell st'.store p dec sb 5 δ ∧
      DecCell st'.store p dec dC.buf dC.idx.eval δ ∧
      ‖WithLp.toLp 2 (x' - (xv + γ • pv))‖ ≤
        roundingFactor 2 (u p) * (‖WithLp.toLp 2 xv‖ + |γ| * ‖WithLp.toLp 2 pv‖) ∧
      ‖WithLp.toLp 2 (r' - (rv - γ • sv))‖ ≤
        roundingFactor 2 (u p) * (‖WithLp.toLp 2 rv‖ + |γ| * ‖WithLp.toLp 2 sv‖) ∧
      IsRoundingProduct (u p) N θ ∧ ν' = ‖WithLp.toLp 2 r'‖ ^ 2 * (1 + θ) ∧
      δ = ν' / ν * (1 + eδ) ∧ |eδ| ≤ u p := by
  obtain ⟨st₁, x', h₁, hf₁, hx₁, hb₁⟩ := exec_axpy_decVec I h hu2 st ⟨sb, 2⟩ (W := W) pc 0
    hWs.symm (by simp; omega) hγ hp (by simpa using hx)
  have hx₁' : DecVec st₁.store p dec W 0 x' := by simpa using hx₁
  replace hf₁ : StoreFrame p st.store st₁.store (StoreBlock W 0 N) := by simpa using hf₁
  obtain ⟨st₂, h₂, hf₂, hg₂⟩ := exec_neg_decCell I h st₁ (hf₁.1.trans hsh) ⟨sb, 6⟩ ⟨sb, 2⟩ hS
    (by norm_num) (hγ.frame hf₁ (by cg_nb))
  have hs₂ : DecVec st₂.store p dec W (2 * IExp.const N).eval sv :=
    (hs.frame hf₁ fun i hi => by cg_nb).frame hf₂ fun i hi => by cg_nb
  have hr₂ : DecVec st₂.store p dec W (IExp.const N).eval rv :=
    (hr.frame hf₁ fun i hi => by cg_nb).frame hf₂ fun i hi => by cg_nb
  obtain ⟨st₃, r', h₃, hf₃, hr₃, hb₃⟩ := exec_axpy_decVec I h hu2 st₂ ⟨sb, 6⟩ (W := W)
    (2 * IExp.const N) (.const N) hWs.symm (by simp; omega) hg₂ hs₂ hr₂
  have hr₃' : DecVec st₃.store p dec W (IExp.const N).eval r' := hr₃
  replace hf₃ : StoreFrame p st₂.store st₃.store (StoreBlock W N N) := hf₃
  have hf₁₃ := (hf₁.trans hf₂).trans hf₃
  obtain ⟨st₄, ν', θ, h₄, hf₄, hν₄, hθ, hν'⟩ := exec_dot_self_decCell I h hz hu1 st₃
    (hf₁₃.1.trans hsh) ⟨sb, 4⟩ (X := W) (.const N) hWs.symm hS (by norm_num) hr₃'
  obtain ⟨st₅, eδ, h₅, hf₅, heδ, hδ₅⟩ := exec_div_decCell I h st₄ ((hf₁₃.trans hf₄).1.trans hsh)
    ⟨sb, 5⟩ ⟨sb, 4⟩ ⟨sb, 0⟩ hS (by norm_num) hν₄ (hν.frame (hf₁₃.trans hf₄) (by cg_nb)) hν0
  obtain ⟨st₆, h₆, hf₆, hδ₆⟩ := exec_copy_decCell I st₅
    (((hf₁₃.trans hf₄).trans hf₅).1.trans hsh) dC ⟨sb, 5⟩ hSd hdi hδ₅
  refine ⟨st₆, x', r', ν', θ, ν' / ν * (1 + eδ), eδ, fun f => ?_, ?_,
    ((((hx₁'.frame hf₂ fun i hi => by cg_nb).frame hf₃ fun i hi => by cg_nb).frame hf₄
      fun i hi => by cg_nb).frame hf₅ fun i hi => by cg_nb).frame hf₆ fun i hi => by cg_nb,
    ((hr₃.frame hf₄ fun i hi => by cg_nb).frame hf₅ fun i hi => by cg_nb).frame hf₆
      fun i hi => by cg_nb,
    (hν₄.frame hf₅ (by cg_nb)).frame hf₆ (by cg_nb), hδ₅.frame hf₆ (by cg_nb), hδ₆, hb₁, ?_,
    hθ, hν', rfl, heδ⟩
  · rw [exec_bind_of_exec_eq_some I h₁ (seqShape_axpy _ _ _ _ _ _ _),
      exec_bind_of_exec_eq_some I h₂ (seqShape_ins _),
      exec_bind_of_exec_eq_some I h₃ (seqShape_axpy _ _ _ _ _ _ _),
      exec_bind_of_exec_eq_some I h₄ (seqShape_dot _ _ _ _ _ _ _),
      exec_bind_of_exec_eq_some I h₅ (seqShape_ins _),
      exec_bind_of_exec_eq_some I h₆ (seqShape_ins _)]
  · refine (((hf₁₃.trans hf₄).trans hf₅).trans hf₆).mono fun b i hb => ?_
    simp only [StoreBlock, IExp.eval_ofNat] at hb ⊢
    rcases hb with ((((hb | hb) | hb) | hb) | hb) | hb
    · exact Or.inl ⟨hb.1, hb.2.1, by omega⟩
    · exact Or.inr (Or.inl ⟨hb.1, by omega, by omega⟩)
    · exact Or.inl ⟨hb.1, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨hb.1, by omega, by omega⟩)
    · exact Or.inr (Or.inl ⟨hb.1, by omega, by omega⟩)
    · exact Or.inr (Or.inr hb)
  · simpa [sub_eq_add_neg, neg_smul, abs_neg] using hb₃

/-- **The direction update of a CG step**: $\mathbf{p}' \leftarrow \mathbf{r}$ then
$\mathbf{p}' \leftarrow \delta\mathbf{p} + \mathbf{p}'$ in slot `pn`, then `s[0]` $\leftarrow
\nu'$ and `nC` $\leftarrow \nu'$. -/
theorem exec_cg_direction (h : IsRelErrSem u dec (fun _ _ => True) I.sem) {N : ℕ}
    (hu2 : 2 * u p < 1) (st : St P K C) {S : Array (P × ℕ)} (hsh : st.store.shape = S)
    {W sb Ln : ℕ} (pc pn : IExp ℕ) (nC : Cell ℕ ℕ) (hWs : W ≠ sb) (hS : S[sb]? = some (p, 7))
    (hSW : S[W]? = some (p, 5 * N)) (hSn : S[nC.buf]? = some (p, Ln)) (hni : nC.idx.eval < Ln)
    (hnW : nC.buf ≠ W) (hns : nC.buf ≠ sb) (hpc : 3 * N ≤ pc.eval ∧ pc.eval + N ≤ 5 * N)
    (hpn : 3 * N ≤ pn.eval ∧ pn.eval + N ≤ 5 * N)
    (hcn : pc.eval + N ≤ pn.eval ∨ pn.eval + N ≤ pc.eval) {rv pv : Fin N → ℝ} {δ ν' : ℝ}
    (hr : DecVec st.store p dec W N rv) (hp : DecVec st.store p dec W pc.eval pv)
    (hν' : DecCell st.store p dec sb 4 ν') (hδ : DecCell st.store p dec sb 5 δ) :
    ∃ (st' : St P K C) (p' : Fin N → ℝ), exec I (copyv p W (.const N) W pn (.const N) >>=
        fun _ => axpy p ⟨sb, 5⟩ W pc W pn (.const N) >>=
        fun _ => ins (.copy p ⟨sb, 0⟩ ⟨sb, 4⟩) >>= fun _ => ins (.copy p nC ⟨sb, 0⟩)).run st =
        some st' ∧
      StoreFrame p st.store st'.store (fun b i => StoreBlock W pn.eval N b i ∨
        StoreBlock sb 0 1 b i ∨ StoreBlock nC.buf nC.idx.eval 1 b i) ∧
      DecVec st'.store p dec W pn.eval p' ∧ DecCell st'.store p dec sb 0 ν' ∧
      DecCell st'.store p dec nC.buf nC.idx.eval ν' ∧
      ‖WithLp.toLp 2 (p' - (rv + δ • pv))‖ ≤
        roundingFactor 2 (u p) * (‖WithLp.toLp 2 rv‖ + |δ| * ‖WithLp.toLp 2 pv‖) := by
  have hr' : DecVec st.store p dec W (IExp.const N).eval rv := hr
  obtain ⟨st₁, h₁, hf₁, hp₁⟩ := exec_copyv_decVec I st hsh W (.const N) W pn hr' hSW
    (by omega) fun _ => by simp; omega
  obtain ⟨st₂, p', h₂, hf₂, hp₂, hb₂⟩ := exec_axpy_decVec I h hu2 st₁ ⟨sb, 5⟩ (W := W) pc pn
    hWs.symm hcn (hδ.frame hf₁ (by cg_nb)) (hp.frame hf₁ fun i hi => by cg_nb) hp₁
  obtain ⟨st₃, h₃, hf₃, hν₃⟩ := exec_copy_decCell I st₂ ((hf₁.trans hf₂).1.trans hsh) ⟨sb, 0⟩
    ⟨sb, 4⟩ hS (by norm_num) ((hν'.frame hf₁ (by cg_nb)).frame hf₂ (by cg_nb))
  obtain ⟨st₄, h₄, hf₄, hν₄⟩ := exec_copy_decCell I st₃ (((hf₁.trans hf₂).trans hf₃).1.trans hsh)
    nC ⟨sb, 0⟩ hSn hni hν₃
  refine ⟨st₄, p', ?_, ?_, (hp₂.frame hf₃ fun i hi => by cg_nb).frame hf₄ fun i hi => by cg_nb,
    hν₃.frame hf₄ (by cg_nb), hν₄, hb₂⟩
  · rw [exec_bind_of_exec_eq_some I h₁ (seqShape_copyv _ _ _ _ _ _),
      exec_bind_of_exec_eq_some I h₂ (seqShape_axpy _ _ _ _ _ _ _),
      exec_bind_of_exec_eq_some I h₃ (seqShape_ins _)]
    exact h₄
  · refine (((hf₁.trans hf₂).trans hf₃).trans hf₄).mono fun b i hb => ?_
    rcases hb with ((hb | hb) | hb) | hb
    · exact Or.inl hb
    · exact Or.inl hb
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hb)

end Pieces

end NLAlib
