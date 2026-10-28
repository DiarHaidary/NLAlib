/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.RoundingErrors
public import NLAlib.Matrix.Norms.Compare
public import NLAlibScaffold.Krylov.FinitePrecision.LanczosRun
public import NLAlibScaffold.Krylov.Processes.LanczosProgramRun

/-!
# Rounding errors of the Lanczos program

A run of `NLAlib.lanczosBasisProg` (matrix-free) or `NLAlib.lanczosBasisDenseProg` (stored
matrix) in the standard model succeeds, and its outputs are the coefficients and vectors of an
`NLAlib.LanczosRun` with an explicit accuracy parameter: the stability analysis of
`NLAlib.Krylov.FinitePrecision` then applies to the computed $\mathbf{T}_k$ and
$\mathbf{V}_{k+1}$. The number of steps $k$ is read off the outputs: the first $j$ with
$\beta_j = 0$, or $q$.

The five error clauses of `NLAlib.LanczosRun` come from the kernels: the product from the matvec
contract `NLAlib.Computation.IsMatvecErr` (an assumption on the oracle; for the stored matrix,
from `gemv` and `NLAlib.norm_toLp_map_abs_mulVec_abs_le`), the two updates from `axpy`
($\gamma_2$), the inner product from `dot` ($\gamma_N$, then Cauchy–Schwarz), the normalisation
from `rscl` ($u$); near unit length from `dot`, `sqrt` and `rscl` together, through products of
rounding errors (`NLAlib.Computation.IsRoundingProduct`): $\gamma_{N+4}$, Higham's count. Success
is unconditional in the standard model: the only partial operations are the square root of the
computed $\mathbf{z}^{\mathsf{T}}\mathbf{z} \ge 0$ and the division by $\beta_j$, which runs only
when $\beta_j$ computes to a nonzero value.

The matrix-free headline is an instance of the access model
`NLAlib.Computation.MatrixFreeRounded` (`NLAlib.lanczosBasisProg_matrixFreeRounded`).
Design: `docs/design/Krylov-LanczosRounding.md` (§2).

## Main definitions

* `NLAlib.lanczosSteps`: the number of steps before breakdown, from the computed $\beta$.
* `NLAlib.lanczosRoundingEps`: the accuracy parameter.
* `NLAlib.LanczosOutputs`: the output buffers decode to $\alpha$, $\beta$, $\mathbf{V}$.
* `NLAlib.HasLanczosRunOutputs`: the outputs of a final state form a `NLAlib.LanczosRun`.

## Main results

* `NLAlib.hasLanczosRunOutputs_of_lanczosRunFacts`: the assembly of the run from the step
  errors of `NLAlibScaffold/Krylov/Processes/LanczosProgramRun.lean`.
* `NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg`: the matrix-free bridge.
* `NLAlib.lanczosBasisProg_matrixFreeRounded`: the same as an instance of the access model.
* `NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisDenseProg`: the dense bridge.
-/

@[expose] public section

open Finset
open scoped Matrix

namespace NLAlib

open Computation Builder

/-- **The number of steps before breakdown**, from the computed off-diagonal coefficients
(`β j` $= \beta_{j+1}$, 0-based as the program writes them): $j + 1$ for the first $j < q$ with
$\beta_{j+1} = 0$, else $q$. -/
noncomputable def lanczosSteps (β : ℕ → ℝ) (q : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, j < q ∧ β j = 0 then Nat.find h + 1 else q

/-- **The accuracy parameter of the Lanczos program**:
$\varepsilon = \max(\varepsilon_{\mathrm{mv}}, \gamma_{N+4}(u))$, the matvec accuracy and the
bound of the other four kernels ($u$, $\gamma_2$, $\gamma_N \le \gamma_{N+4}$) and of the
normalisation ($\gamma_{N+4}$). -/
noncomputable def lanczosRoundingEps (N : ℕ) (u εmv : ℝ) : ℝ :=
  max εmv (roundingFactor (N + 4) u)

section
variable {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {c g₂ gN u γ : ℝ} {v uv w z : ℕ → Fin N → ℝ}
  {α β : ℕ → ℝ}

/-- A step from the zero vector after a breakdown computes zeros. -/
theorem LanczosStepErr.eq_zero {j : ℕ}
    (hS : LanczosStepErr H c g₂ gN u γ (v j) (v (j + 1)) (β j) (uv (j + 1)) (w (j + 1))
      (z (j + 1)) (α (j + 1)) (β (j + 1)) (v (j + 2))) (hv : v (j + 1) = 0) (hβ : β j = 0) :
    α (j + 1) = 0 ∧ β (j + 1) = 0 ∧ v (j + 2) = 0 := by
  have hu : uv (j + 1) = 0 := by
    have := hS.norm_u_sub_le
    rw [hv, Matrix.mulVec_zero, sub_zero, WithLp.toLp_zero, norm_zero, mul_zero] at this
    exact WithLp.toLp_injective 2 (norm_le_zero_iff.mp this)
  have hw : w (j + 1) = 0 := by
    have := hS.norm_w_sub_le
    rw [hu, hβ, zero_smul, sub_zero, sub_zero, WithLp.toLp_zero, norm_zero, abs_zero,
      zero_mul, zero_add, mul_zero] at this
    exact WithLp.toLp_injective 2 (norm_le_zero_iff.mp this)
  have hα : α (j + 1) = 0 := by
    have := hS.abs_α_sub_le
    rw [hv, hw, zero_dotProduct, sub_zero, WithLp.toLp_zero, norm_zero, mul_zero] at this
    exact abs_nonpos_iff.mp this
  have hz : z (j + 1) = 0 := by
    have := hS.norm_z_sub_le
    rw [hw, hα, hv, smul_zero, sub_zero, sub_zero, WithLp.toLp_zero, norm_zero, mul_zero,
      add_zero, mul_zero] at this
    exact WithLp.toLp_injective 2 (norm_le_zero_iff.mp this)
  have hβ' := hS.β_eq_zero hz
  exact ⟨hα, hβ', hS.v_eq_zero hβ'⟩

/-- After a breakdown every later output of the recurrence is zero. -/
theorem LanczosStepErr.eq_zero_of_breakdown {q k : ℕ}
    (hS : ∀ j < q, LanczosStepErr H c g₂ gN u γ (v j) (v (j + 1)) (β j) (uv (j + 1))
      (w (j + 1)) (z (j + 1)) (α (j + 1)) (β (j + 1)) (v (j + 2))) (hk : 0 < k) (hkq : k ≤ q)
    (hβ : β k = 0) : ∀ j, k ≤ j → j ≤ q → v (j + 1) = 0 ∧ β j = 0 := by
  intro j hkj hjq
  induction j, hkj using Nat.le_induction with
  | base =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact ⟨(hS k (by omega)).v_eq_zero hβ, hβ⟩
  | succ j hkj ih =>
    obtain ⟨hv, hβj⟩ := ih (by omega)
    obtain ⟨-, h1, h2⟩ := (hS j (by omega)).eq_zero hv hβj
    exact ⟨h2, h1⟩

theorem lanczosSteps_pos {β : ℕ → ℝ} {q : ℕ} (hq : 0 < q) : 0 < lanczosSteps β q := by
  unfold lanczosSteps; split_ifs <;> omega

theorem lanczosSteps_le (β : ℕ → ℝ) (q : ℕ) : lanczosSteps β q ≤ q := by
  unfold lanczosSteps
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact le_rfl

theorem ne_zero_of_add_one_lt_lanczosSteps {β : ℕ → ℝ} {q j : ℕ}
    (hj : j + 1 < lanczosSteps β q) : β j ≠ 0 := by
  intro h0
  unfold lanczosSteps at hj
  split_ifs at hj with h
  · exact Nat.find_min h (by omega) ⟨by have := (Nat.find_spec h).1; omega, h0⟩
  · exact h ⟨j, by omega, h0⟩

theorem eq_zero_of_lanczosSteps_lt {β : ℕ → ℝ} {q : ℕ} (hk : lanczosSteps β q < q) :
    β (lanczosSteps β q - 1) = 0 := by
  unfold lanczosSteps at hk ⊢
  split_ifs at hk ⊢ with h
  · simpa using (Nat.find_spec h).2
  · omega

theorem exists_lanczosRun_of_lanczosStepErr {q : ℕ} (hq : 0 < q) (hH : Hᵀ = H) {ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : (q : ℝ) * ε ≤ 1 / 100) (hc : c ≤ ε * specNorm H) (hg₂ : g₂ ≤ ε)
    (hgN : gN ≤ ε) (hu : u ≤ ε) (hγ : γ ≤ ε) (hv0 : v 0 = 0) (hβ0 : β 0 = 0)
    (h1 : |‖WithLp.toLp 2 (v 1)‖ ^ 2 - 1| ≤ γ)
    (hS : ∀ j < q, LanczosStepErr H c g₂ gN u γ (v j) (v (j + 1)) (β j) (uv (j + 1))
      (w (j + 1)) (z (j + 1)) (α (j + 1)) (β (j + 1)) (v (j + 2))) :
    ∃ L : LanczosRun N (lanczosSteps (fun j => β (j + 1)) q), L.H = H ∧ L.ε = ε ∧
      (∀ j < lanczosSteps (fun j => β (j + 1)) q, L.α (j + 1) = α (j + 1) ∧
        L.β (j + 1) = β (j + 1)) ∧
      ∀ j ≤ lanczosSteps (fun j => β (j + 1)) q, L.v (j + 1) = v (j + 1) := by
  set k := lanczosSteps (fun j => β (j + 1)) q with hk
  have hk0 : 0 < k := lanczosSteps_pos hq
  have hkq : k ≤ q := lanczosSteps_le _ q
  have hne : ∀ i, i + 1 < k → β (i + 1) ≠ 0 := fun i hi =>
    ne_zero_of_add_one_lt_lanczosSteps (β := fun j => β (j + 1)) hi
  refine ⟨{
      H := H
      v := v
      u := uv
      w := w
      z := z
      α := α
      β := β
      eu := fun j => uv j - H *ᵥ v j
      ew := fun j => w j - (uv j - β (j - 1) • v (j - 1))
      ez := fun j => z j - (w j - α j • v j)
      eα := fun j => α j - v j ⬝ᵥ w j
      δ := fun j => β j • v (j + 1) - z j
      ε := ε
      transpose_H := hH
      ε_nonneg := hε
      k_pos := hk0
      k_mul_ε_le := ?_
      v_zero := hv0
      β_zero := hβ0
      u_eq := fun j _ => by abel
      norm_eu_le := fun j hj => ?_
      w_eq := fun j _ => by simp
      norm_ew_le := fun j hj => ?_
      α_eq := fun j _ => by ring
      abs_eα_le := fun j hj => ?_
      z_eq := fun j _ => by abel
      norm_ez_le := fun j hj => ?_
      smul_v_eq := fun j _ => by abel
      norm_δ_le := fun j hj => ?_
      abs_norm_v_sq_sub_one_le := fun j h1j hjk => ?_
      abs_norm_v_succ_sq_sub_one_le := fun hβk => ?_
      β_nonneg := fun j hj => ?_
      β_pos := fun j h1j hjk => ?_
     }, rfl, rfl,
    fun j _ => ⟨rfl, rfl⟩, fun j _ => rfl⟩
  · exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hkq) hε).trans hsmall
  · exact (hS j (by omega)).norm_u_sub_le.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  · simpa using (hS j (by omega)).norm_w_sub_le.trans
      (mul_le_mul_of_nonneg_right hg₂ (by positivity))
  · exact (hS j (by omega)).abs_α_sub_le.trans (by gcongr)
  · exact (hS j (by omega)).norm_z_sub_le.trans
      (mul_le_mul_of_nonneg_right hg₂ (by positivity))
  · exact (hS j (by omega)).norm_smul_sub_le.trans (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rcases i with _ | i
    · exact h1.trans hγ
    · exact ((hS i (by omega)).abs_norm_sq_sub_one_le (hne i (by omega))).trans hγ
  · obtain ⟨i, hi⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    rw [hi] at hβk ⊢
    exact ((hS i (by omega)).abs_norm_sq_sub_one_le hβk).trans hγ
  · rcases j with _ | i
    · exact hβ0.ge
    · exact (hS i (by omega)).β_nonneg
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact lt_of_le_of_ne (hS i (by omega)).β_nonneg (hne i hjk).symm
end

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- **The outputs of the Lanczos program**: in state `st`, at tag `p` and decoding `dec`, the
buffers `alpha` and `beta` hold words decoding to $\alpha_j$, $\beta_j$ ($j < q$) and buffer `Q`
holds $q + 1$ columns of $N$ words decoding to $\mathbf{V}_j$ ($j \le q$, column-major). -/
def LanczosOutputs (st : St P K C) (p : P) (dec : P → K → ℝ) (alpha beta Q : ℕ) {N : ℕ}
    (q : ℕ) (α β : ℕ → ℝ) (V : ℕ → Fin N → ℝ) : Prop :=
  (∀ j < q, ∃ w, st.store.read p alpha j = some w ∧ dec p w = α j) ∧
  (∀ j < q, ∃ w, st.store.read p beta j = some w ∧ dec p w = β j) ∧
  (∀ j ≤ q, ∀ i : Fin N, ∃ w, st.store.read p Q (i + N * j) = some w ∧ dec p w = V j i)

/-- **The outputs of a Lanczos run form a `NLAlib.LanczosRun`**: the output buffers of `st`
decode to $\alpha$, $\beta$, $\mathbf{V}$ (`NLAlib.LanczosOutputs`); $\mathbf{v}_1$ is a
computed normalisation of $\mathbf{b}$ ($c\mathbf{v}_1 = \mathbf{b} + \boldsymbol{\delta}_0$,
$c > 0$, $\lVert\boldsymbol{\delta}_0\rVert \le u\lVert\mathbf{b}\rVert$); with
$k$ = `NLAlib.lanczosSteps β q`, every later output is $0$ ($\alpha_j = \beta_j = 0$ for
$k \le j < q$, and $\mathbf{V}_j = \mathbf{0}$ for $k \le j \le q$ when the last step is
terminal, the convention $\mathbf{v}_{k+1} = \mathbf{0}$ of [Chen, `sec:model`]); and there is a
run `L : NLAlib.LanczosRun N k` with matrix $\mathbf{H}$, accuracy parameter $\varepsilon$, the
computed coefficients ($L.\alpha_{j+1} = \alpha_j$, $L.\beta_{j+1} = \beta_j$, $j < k$) and the
computed vectors ($L.\mathbf{v}_{j+1} = \mathbf{V}_j$, $j \le k$). -/
def HasLanczosRunOutputs (st : St P K C) (p : P) (dec : P → K → ℝ) (u ε : ℝ)
    (alpha beta Q : ℕ) {N : ℕ} (q : ℕ) (H : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) : Prop :=
  ∃ (α β : ℕ → ℝ) (V : ℕ → Fin N → ℝ), LanczosOutputs st p dec alpha beta Q q α β V ∧
    (∃ (c : ℝ) (δ₀ : Fin N → ℝ), 0 < c ∧ c • V 0 = b + δ₀ ∧
      ‖WithLp.toLp 2 δ₀‖ ≤ u * ‖WithLp.toLp 2 b‖) ∧
    (∀ j, lanczosSteps β q ≤ j → j < q → α j = 0 ∧ β j = 0) ∧
    (β (lanczosSteps β q - 1) = 0 → ∀ j, lanczosSteps β q ≤ j → j ≤ q → V j = 0) ∧
    ∃ L : LanczosRun N (lanczosSteps β q), L.H = H ∧ L.ε = ε ∧
      (∀ j < lanczosSteps β q, L.α (j + 1) = α j ∧ L.β (j + 1) = β j) ∧
      ∀ j ≤ lanczosSteps β q, L.v (j + 1) = V j

omit [AddMonoid C] in
/-- **The facts of a run give a `NLAlib.LanczosRun`**: the outputs of a state satisfying
`NLAlib.LanczosRunFacts` with product bound $c \le \varepsilon\|\mathbf{H}\|_2$, for a
symmetric $\mathbf{H}$, $q \ge 1$, $(N + 4)u < 1$, $\gamma_{N+4} \le \varepsilon$ and
$q\varepsilon \le 1/100$, form a run (`NLAlib.HasLanczosRunOutputs`). -/
theorem hasLanczosRunOutputs_of_lanczosRunFacts {st : St P K C} {p : P} {dec : P → K → ℝ}
    {u ε c : ℝ} {La Lb LQ q N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {bv : Fin N → ℝ} (hq : 0 < q)
    (hH : Hᵀ = H) (hu0 : 0 ≤ u) (hN : ((N + 4 : ℕ) : ℝ) * u < 1) (hc : c ≤ ε * specNorm H)
    (hγ : roundingFactor (N + 4) u ≤ ε) (hsmall : (q : ℝ) * ε ≤ 1 / 100)
    (hF : LanczosRunFacts p dec La Lb LQ q H c u bv st.store) :
    HasLanczosRunOutputs st p dec u ε La Lb LQ q H bv := by
  obtain ⟨v, uv, w, z, α, β, hv0, hβ0, hst, hun, hS, hout, hQ⟩ := hF
  have hmono : ∀ m ≤ N + 4, roundingFactor m u ≤ ε := fun m hm =>
    (roundingFactor_le_roundingFactor hu0 hm hN).trans hγ
  have huε : u ≤ ε := (le_roundingFactor_one hu0
    (by simpa using cast_mul_lt_one_of_le (m := 1) hu0 (by omega) hN)).trans (hmono 1 (by omega))
  set k := lanczosSteps (fun j => β (j + 1)) q with hk
  have hk0 : 0 < k := lanczosSteps_pos hq
  have hkq : k ≤ q := lanczosSteps_le _ q
  have hbrk : β k = 0 → ∀ j, k ≤ j → j ≤ q → v (j + 1) = 0 ∧ β j = 0 :=
    LanczosStepErr.eq_zero_of_breakdown hS hk0 hkq
  have hβk : (fun j => β (j + 1)) (k - 1) = β k := by simp only; congr 1; omega
  refine ⟨fun j => α (j + 1), fun j => β (j + 1), fun j => v (j + 1),
    ⟨fun j hj => (hout j hj).1, fun j hj => (hout j hj).2, fun j hj i => ?_⟩, hst, ?_, ?_,
    exists_lanczosRun_of_lanczosStepErr hq hH ((roundingFactor_nonneg hu0 hN).trans hγ) hsmall
      hc (hmono 2 (by omega)) (hmono N (by omega)) huε hγ hv0 hβ0 hun hS⟩
  · obtain ⟨w', hw', hd'⟩ := hQ j hj i
    exact ⟨w', by rw [add_comm]; exact hw', hd'⟩
  · intro j hkj hjq
    have hb0 : β k = 0 :=
      hβk ▸ eq_zero_of_lanczosSteps_lt (β := fun j => β (j + 1)) (q := q) (by omega)
    obtain ⟨hv, hβj⟩ := hbrk hb0 j hkj hjq.le
    obtain ⟨hα, hβ', -⟩ := (hS j hjq).eq_zero hv hβj
    exact ⟨hα, hβ'⟩
  · intro hb0 j hkj hjq
    exact (hbrk (hβk ▸ hb0) j hkj hjq).1

/-- An oracle meeting `NLAlib.Computation.IsMatvecErr` meets `NLAlib.LanczosMvSpec`. -/
theorem lanczosMvSpec_apply (I : Interp P ι K C) (p : P) (o : ι) (dec : P → K → ℝ) (R : ℕ)
    (s₀ : Store P K) (k₀ : K) {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {c : ℝ}
    (hmv : IsMatvecErr I o dec p H c) :
    LanczosMvSpec I (fun W src dst => stmt (.apply o p W dst W src 1)) p dec R s₀ H c := by
  refine ⟨fun _ _ _ => seqShape_stmt _, fun st W src dst x _ _ hd hx hw => ?_⟩
  obtain ⟨hht, hor⟩ := hmv
  choose ws hws hdws using hx
  set g : ℕ → K := fun i => if h : i < N then ws ⟨i, h⟩ else k₀
  have hX : st.store.readBlock p W src.eval (I.height o * (1 : IExp ℕ).eval) =
      some ((List.range N).toArray.map g) := by
    rw [hht, IExp.eval_one, mul_one]
    exact Store.readBlock_eq_some_map_range g fun i hi => by simp [g, hi, hws ⟨i, hi⟩]
  obtain ⟨Y, hY, hoY, hbound⟩ := hor ((List.range N).toArray.map g) (by simp)
  obtain ⟨s', hs'⟩ := Store.exists_writeBlock_eq_some_of_write (s := st.store) (p := p) (b := W)
    (off := dst.eval) (xs := Y) fun j hj => hw j (hY ▸ hj)
  have hrun : exec I (stmt (ι := ι) (.apply o p W dst W src 1)).run st =
      some { st with store := s', cnt := st.cnt + (I.charge (.load p o) +
        (1 : IExp ℕ).eval • I.charge (.matvec p o)) } := by
    rw [show (stmt (ι := ι) (.apply o p W dst W src 1)).run = .seq (.apply o p W dst W src 1) .skip
      from rfl, exec_seq_skip, exec, if_pos (by rw [hht, IExp.eval_one, mul_one]; omega), hX,
      Option.bind_some, IExp.eval_one, hoY, Option.bind_some, hs']
    rfl
  have hf := storeFrame_of_writeBlock hs'
  rw [hY] at hf
  refine ⟨_, fun i => dec p (Y[i.1]'(hY ▸ i.2)), hrun, hf,
    fun i => ⟨Y[i.1]'(hY ▸ i.2), ?_, rfl⟩, ?_⟩
  · rw [Store.read_of_writeBlock_eq_some_of_lt hs' (hY ▸ i.2)]; simp
  · rw [WithLp.toLp_sub, norm_sub_rev, ← WithLp.toLp_sub]
    have hxe : (fun i : Fin N => dec p (g i)) = x := by
      ext i; simp [g, hdws]
    simpa [hxe] using hbound

/-- `gemv` on a stored matrix meets `NLAlib.LanczosMvSpec` with
$c = \sqrt{N}\gamma_N\|\mathbf{H}\|_2$ (`NLAlib.norm_toLp_map_abs_mulVec_abs_le`). -/
theorem lanczosMvSpec_gemv (I : Interp P ι K C) {u : P → ℝ} {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (p : P)
    (s₀ : Store P K) {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (hM : HoldsDecoded s₀ dec p 0 0 M)
    (hN : (N : ℝ) * u p < 1) :
    LanczosMvSpec I (fun W src dst => gemv p (.const N) (.const N) 0 0 W src W dst) p dec 0 s₀ M
      (√(N : ℝ) * roundingFactor N (u p) * specNorm M) := by
  refine ⟨fun _ _ _ => seqShape_gemv _ _ _ _ _ _ _ _ _, fun st W src dst x hRW hR hd hx hw => ?_⟩
  have hA : HoldsDecoded st.store dec p 0 (0 : IExp ℕ).eval M := fun i j => by
    rw [hR]; exact hM i j
  obtain ⟨st', Wv, he, hb, hbd⟩ := IsRelErrSem.exec_gemv_abs_mulVec_sub_le I p st h hz
    (.const N) (.const N) 0 0 W src W dst M x hN hA (fun i => hx i) (fun h' => absurd h'.symm hRW)
    (fun _ => hd.symm) hw
  have hf := storeFrame_of_writeBlock hb
  simp only [Array.size_map, List.size_toArray, List.length_range, IExp.eval_const] at hf
  refine ⟨st', fun i => dec p (Wv i), he, hf, DecVec.of_writeBlock hb, ?_⟩
  have hγ : 0 ≤ roundingFactor N (u p) := roundingFactor_nonneg (h.nonneg trivial) hN
  calc _ ≤ ‖WithLp.toLp 2 (roundingFactor N (u p) • (M.map abs *ᵥ fun j => |x j|))‖ :=
        norm_toLp_le_of_abs_le fun i => by
          rw [Pi.sub_apply, abs_sub_comm, Pi.smul_apply, smul_eq_mul]; exact hbd i
    _ = roundingFactor N (u p) * ‖WithLp.toLp 2 (M.map abs *ᵥ fun j => |x j|)‖ := by
        rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hγ]
    _ ≤ roundingFactor N (u p) * (√(N : ℝ) * specNorm M * ‖WithLp.toLp 2 x‖) := by
        gcongr; simpa using norm_toLp_map_abs_mulVec_abs_le M x
    _ = _ := by ring
/-- **The matrix-free Lanczos program yields a `NLAlib.LanczosRun`** in the standard model:
under `NLAlib.Computation.IsRelErrSem` with every value in range and adding zero exactly, for a
real symmetric $\mathbf{H}$ served by an oracle meeting `NLAlib.Computation.IsMatvecErr` with
bound $\varepsilon_{\mathrm{mv}}\lVert\mathbf{H}\rVert_2$, a start vector $\mathbf{b}$ of $N$
words decoding to a nonzero vector, $q \ge 1$, $(N + 4)u_p < 1$ and $q\varepsilon \le 1/100$ for
$\varepsilon = \max(\varepsilon_{\mathrm{mv}}, \gamma_{N+4})$, the run of $q$ steps succeeds and
its outputs form a run `L : NLAlib.LanczosRun N k` with accuracy parameter $\varepsilon$,
$k$ the steps before breakdown, the computed coefficients and vectors, $\mathbf{v}_1$ the
computed normalisation of $\mathbf{b}$, and every output after breakdown $0$
(`NLAlib.HasLanczosRunOutputs`). The hypothesis $(N + 4)u_p < 1$ is not implied by
$q\varepsilon \le 1/100$: $\gamma_{N+4}$ is negative past $(N + 4)u_p = 1$. Constructed from
[Chen, `sec:model`] and [Higham2002, §§2.2, 3.1, Lemma 3.3]. -/
theorem _root_.NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg
    {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C) (p : P) (o : ι)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    {N : ℕ} (q : ℕ) (H : Matrix (Fin N) (Fin N) ℝ) (hH : Hᵀ = H) {εmv : ℝ}
    (hmv : IsMatvecErr I o dec p H (εmv * specNorm H)) (b : Fin N → K)
    (hb : (fun i => dec p (b i)) ≠ 0) (hq : 0 < q) (hu : ((N + 4 : ℕ) : ℝ) * u p < 1)
    (hsmall : (q : ℝ) * lanczosRoundingEps N (u p) εmv ≤ 1 / 100) :
    ∃ st', exec I (lanczosBasisProg p o (.const N) (.const q) 0 1 2 3).run
        (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
          Array.replicate q none, Array.replicate (N * (q + 1)) none]) = some st' ∧
      HasLanczosRunOutputs st' p dec (u p) (lanczosRoundingEps N (u p) εmv) 1 2 3 q H
        fun i => dec p (b i) := by
  have hu0 : 0 ≤ u p := h.nonneg trivial
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact absurd (funext fun i => i.elim0) hb
    · exact hN
  obtain ⟨st', he, hF⟩ := IsRelErrSem.exists_lanczosRunFacts_of_lanczosBasisProgWith I h hz hu
    (q := q) (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
      Array.replicate q none, Array.replicate (N * (q + 1)) none])
    (lanczosMvSpec_apply I p o dec 0 _ (b ⟨0, hN0⟩) hmv) (B := 0) (La := 1) (Lb := 2) (LQ := 3)
    (bv := fun i => dec p (b i)) (fun i => ⟨b i, by simp [inputState, Store.read], rfl⟩) hb
    (by simp [inputState]) (by simp [inputState]) (by simp [inputState, Store.shape])
    (by simp [inputState, Store.shape]) (by simp [inputState, Store.shape]) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  exact ⟨st', he, hasLanczosRunOutputs_of_lanczosRunFacts hq hH hu0 hu
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (specNorm_nonneg _)) (le_max_right _ _) hsmall
    hF⟩

/-- **The matrix-free Lanczos program in the access model**: the headline
`NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg` as an instance of
`NLAlib.Computation.MatrixFreeRounded` with one size parameter $q \ge 1$, the input
$\mathbf{b}$ (with empty output buffers), matvec bound $\varepsilon_{\mathrm{mv}}
\lVert\mathbf{H}\rVert_2$, precondition $\mathbf{H}^{\mathsf{T}} = \mathbf{H}$,
$\mathbf{b} \ne \mathbf{0}$ (decoded), $(N + 4)u_p < 1$, $q\varepsilon \le 1/100$, and
postcondition `NLAlib.HasLanczosRunOutputs` with $\varepsilon = \max(\varepsilon_{\mathrm{mv}},
\gamma_{N+4})$. [Chen, `sec:model`], [Higham2002, §§2.2, 3.1, Lemma 3.3]. -/
theorem lanczosBasisProg_matrixFreeRounded (p : P) (o : ι) (u : P → ℝ) (dec : P → K → ℝ)
    (εmv : ℝ) :
    MatrixFreeRounded (C := C) (r := 1) (b := 4) p
      (fun N n => (lanczosBasisProg p o (.const N) (.const (n 0)) 0 1 2 3).run)
      (fun _ n => 0 < n 0) (fun N _ => Fin N → K)
      (fun N n b => ![(List.ofFn fun i => some (b i)).toArray, Array.replicate (n 0) none,
        Array.replicate (n 0) none, Array.replicate (N * (n 0 + 1)) none])
      u dec (fun _ _ H => εmv * specNorm H)
      (fun N n b H => Hᵀ = H ∧ (fun i => dec p (b i)) ≠ 0 ∧ ((N + 4 : ℕ) : ℝ) * u p < 1 ∧
        (n 0 : ℝ) * lanczosRoundingEps N (u p) εmv ≤ 1 / 100)
      (fun N n b H st => HasLanczosRunOutputs st p dec (u p) (lanczosRoundingEps N (u p) εmv)
        1 2 3 (n 0) H fun i => dec p (b i)) := by
  intro N n hn b H I h hz hmv ⟨hH, hb, hu, hsmall⟩
  simpa [List.ofFn_succ] using
    IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg I p o h hz (n 0) H hH (hmv o) b hb hn hu
      hsmall

/-- **The dense Lanczos program yields a `NLAlib.LanczosRun`** in the standard model: under
`NLAlib.Computation.IsRelErrSem` with every value in range and adding zero exactly, with the
product computed by `gemv` from the $N \times N$ words `Hw` (buffer 0, column-major) decoding to
a symmetric $\mathbf{H}$, a start vector $\mathbf{b}$ of $N$ words decoding to a nonzero
vector, $q \ge 1$, $(N + 4)u_p < 1$ and $q\varepsilon \le 1/100$ for
$\varepsilon = \max(\sqrt{N}\gamma_N, \gamma_{N+4})$, the run of $q$ steps succeeds and its
outputs form a run `L : NLAlib.LanczosRun N k` as in
`NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisProg`
(`NLAlib.HasLanczosRunOutputs`); every hypothesis is on the data, the sizes and $u_p$.
[Chen, `sec:model`], [Higham2002, §§2.2, 3.1, 3.5, Lemma 3.3]. -/
theorem _root_.NLAlib.Computation.IsRelErrSem.exists_lanczosRun_of_lanczosBasisDenseProg
    {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C) (p : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    {N : ℕ} (q : ℕ) (Hw : Fin N → Fin N → K)
    (hH : (Matrix.of fun i j => dec p (Hw i j))ᵀ = Matrix.of fun i j => dec p (Hw i j))
    (b : Fin N → K) (hb : (fun i => dec p (b i)) ≠ 0)
    (hq : 0 < q) (hu : ((N + 4 : ℕ) : ℝ) * u p < 1)
    (hsmall : (q : ℝ) * lanczosRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p)) ≤
      1 / 100) :
    ∃ st', exec I (lanczosBasisDenseProg p (.const N) (.const q) 0 1 2 3 4).run
        (inputState p [(List.ofFn fun t : Fin (N * N) =>
            some (Hw ⟨t % N, Nat.mod_lt _ (Nat.pos_of_mul_pos_right
              (Nat.zero_lt_of_lt t.2))⟩ ⟨t / N, Nat.div_lt_of_lt_mul t.2⟩)).toArray,
          (List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
          Array.replicate q none, Array.replicate (N * (q + 1)) none]) = some st' ∧
      HasLanczosRunOutputs st' p dec (u p)
        (lanczosRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p))) 2 3 4 q
        (Matrix.of fun i j => dec p (Hw i j)) fun i => dec p (b i) := by
  have hu0 : 0 ≤ u p := h.nonneg trivial
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact absurd (funext fun i => i.elim0) hb
    · exact hN
  have huN : (N : ℝ) * u p < 1 := cast_mul_lt_one_of_le hu0 (by omega) hu
  set st₀ : St P K C := inputState p [(List.ofFn fun t : Fin (N * N) =>
      some (Hw ⟨t % N, Nat.mod_lt _ (Nat.pos_of_mul_pos_right (Nat.zero_lt_of_lt t.2))⟩
        ⟨t / N, Nat.div_lt_of_lt_mul t.2⟩)).toArray,
    (List.ofFn fun i => some (b i)).toArray, Array.replicate q none, Array.replicate q none,
    Array.replicate (N * (q + 1)) none] with hst₀
  have hM : HoldsDecoded st₀.store dec p 0 0 (Matrix.of fun i j => dec p (Hw i j)) := by
    intro i j
    have hlt : (i : ℕ) + N * j < N * N := by nlinarith [i.2, j.2]
    refine ⟨Hw i j, ?_, rfl⟩
    simp only [hst₀, inputState, Store.read]
    suffices Hw ⟨(i + N * j) % N, Nat.mod_lt _ hN0⟩ ⟨(i + N * j) / N, Nat.div_lt_of_lt_mul hlt⟩ =
        Hw i j by simpa [hlt] using this
    congr 1 <;> apply Fin.ext
    · simp [Nat.mod_eq_of_lt i.2]
    · simp [Nat.add_mul_div_left _ _ hN0, Nat.div_eq_of_lt i.2]
  obtain ⟨st', he, hF⟩ := IsRelErrSem.exists_lanczosRunFacts_of_lanczosBasisProgWith I h hz hu
    (q := q) st₀ (lanczosMvSpec_gemv I h hz p st₀.store _ hM huN) (B := 1) (La := 2) (Lb := 3)
    (LQ := 4) (bv := fun i => dec p (b i))
    (fun i => ⟨b i, by simp [hst₀, inputState, Store.read], rfl⟩) hb
    (by simp [hst₀, inputState]) (by simp [hst₀, inputState])
    (by simp [hst₀, inputState, Store.shape]) (by simp [hst₀, inputState, Store.shape])
    (by simp [hst₀, inputState, Store.shape]) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  exact ⟨st', he, hasLanczosRunOutputs_of_lanczosRunFacts hq hH hu0 hu
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (specNorm_nonneg _)) (le_max_right _ _) hsmall
    hF⟩

end NLAlib
