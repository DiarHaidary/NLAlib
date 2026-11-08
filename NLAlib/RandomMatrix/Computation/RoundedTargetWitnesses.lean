/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.GridMachine
public import NLAlib.RandomMatrix.Computation.NewtonSchulzSignTargets
public import NLAlib.RandomMatrix.Computation.DeflationTargets
public import NLAlib.RandomMatrix.Computation.SpectralBisectionTargets
public import NLAlib.ForMathlib.Analysis.SpecificLimits.Basic

/-!
# Non-vacuity witnesses of the rounded targets

The non-vacuity witnesses (`docs/design/Computation-Hardening.md`, §2.2; `scripts/Targets.lean`,
item 7) of the three rounded probabilistic targets `NLAlib.MatrixFreeRoundedProbNewtonSchulzSign`,
`NLAlib.MatrixFreeRoundedProbDeflate` and `NLAlib.MatrixFreeRoundedProbEigh`: at every size
$N \ge N_0$ every hypothesis of the model is met at once, by **rounded arithmetic with $u > 0$**,
not by exact arithmetic at a nominal $u$. The semantics is `NLAlib.Computation.gridSem` with
$t$ bits at every tag (rounding to nearest, unbounded exponent; decoding $x \mapsto
\mathrm{fl}(x)$, $u = 2^{-t}$), $t$ chosen from $N$ so that the precision hypotheses hold; the
kernels are the correctly rounded `NLAlib.gridMM t` and `NLAlib.gridQR t` and the tape is rounded
to nearest (the spectral bisection witness writes its stored identity with the machine
`NLAlib.gridMachine t`).
The stored inputs are on the grid: the identity matrix in pairs, and powers of two.

A bounded-exponent semantics cannot witness these targets: they assume the standard model with
every value in range (`IsRelErrSem … (fun _ _ => True)`: every operation succeeds with relative
error at most $u$, which fails under underflow and overflow) and a machine at floor $\tau = 0$.

## Main results

* `NLAlib.matrixFreeRoundedProbNewtonSchulzSign_nonVacuous`,
  `NLAlib.matrixFreeRoundedProbDeflate_nonVacuous`,
  `NLAlib.matrixFreeRoundedProbEigh_nonVacuous`: the witnesses.
-/

@[expose] public section

open Filter
open scoped Matrix

namespace NLAlib

open Computation

/-- **An interpretation of the rounded witnesses exists**: the grid semantics with $t$ bits at
every tag (`NLAlib.Computation.gridSem`), kernel `true` the correctly rounded product
`NLAlib.gridMM t` and kernel `false` the correctly rounded QR factorization `NLAlib.gridQR t`, in
the interleaved layout (no oracle, no read-only data, a zero tape and charge, which the contracts
do not read). No printed source. -/
private theorem exists_gridKernelInterp (P : Type) (t : ℕ) :
    ∃ I : Interp P Bool ℝ (OpCount P Bool), I.sem = gridSem (fun _ => t) ∧
      IsMatMulKernel I true pairLayout (gridMM t) ∧ IsQRKernel I false pairLayout (gridQR t) :=
  ⟨{ sem := gridSem fun _ => t
     charge _ := 0
     tape _ _ := 0
     oracle _ _ _ := none
     height _ := 0
     rom _ := none
     romSize _ := 0
     width _ := 0
     kernel o := bif o then liftMM pairLayout (gridMM t) else liftQR pairLayout (gridQR t)
     kshape o := bif o then mmShape (pairLayout (K := ℝ)) else qrShape (pairLayout (K := ℝ)) },
    rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- `1/2` is on the grid of $t \ge 1$ bits. -/
private theorem roundNearest_half {t : ℕ} (ht : 0 < t) : Real.roundNearest t (1 / 2) = 1 / 2 := by
  rw [one_div, ← pow_one (2⁻¹ : ℝ)]
  exact Real.roundNearest_two_inv_pow ht 1

/-- The stored identity matrix in pairs decodes to the identity on the grid of $t \ge 1$ bits. -/
private theorem decodeMatrix_roundNearest_identity {t : ℕ} (ht : 0 < t) (N : ℕ) :
    decodeMatrix (Real.roundNearest t)
      (Matrix.of fun i j : Fin N => if i = j then ((1 : ℝ), (0 : ℝ)) else (0, 0)) = 1 := by
  ext i j : 2
  by_cases h : i = j
  · subst h
    apply Complex.ext <;>
      simp [decodeMatrix, decodeComplex, Real.roundNearest_one ht, Real.roundNearest_zero]
  · apply Complex.ext <;>
      simp [decodeMatrix, decodeComplex, Real.roundNearest_zero, h]

/-- **The Newton–Schulz sign target is not vacuous**: for every $N_0$, at $N = N_0 + 1$, the
grid semantics with $t$ bits ($t$ large, from $N$), the kernel `NLAlib.gridMM t`,
$\Omega = 9(N + 1)$, $\mu(d) = 2d$, the stored identity matrix,
$\varepsilon = 1/2$, $\bar b = 1$ and the step limit
$F = \lceil N(1/2, 1/(32N)) \rceil + 1$ meet every hypothesis of
`NLAlib.MatrixFreeRoundedProbNewtonSchulzSign` (with $a = 1$). The witness of the target
(`scripts/Targets.lean`, item 7). No printed source. -/
theorem matrixFreeRoundedProbNewtonSchulzSign_nonVacuous : ∀ N₀ : ℕ,
    ∃ (P ι : Type) (_ : DecidableEq P) (p : P) (mm : ι) (K : Type) (_ : Inhabited K)
      (dec : P → K → ℝ) (u Ω : ℝ) (μ : ℕ → ℝ),
    MatrixFreeRoundedProb.NonVacuous p (newtonSchulzSignProg.compiled p mm) (fun N _ => 0 < N)
      (fun N _ => Matrix (Fin N) (Fin N) (K × K) × K × K)
      (fun N _ x => ![(pairLayout.toArray x.1).map some, #[some x.2.1, some x.2.2],
        Array.replicate (2 * (N * N)) none])
      dec (fun _ _ => 1) (fun N n => newtonSchulzSignCount p mm N (n 0))
      (fun N _ q => if q = p then 8 * (N * N) + 7 else 0)
      (fun _ _ I => IsRelErrSem (fun _ => u) dec (fun _ _ => True) I.sem ∧
        ∃ mmR : MatMulMap (K × K), IsMatMulKernel I mm pairLayout mmR ∧
          IsMatMulErr (decodeComplex (dec p)) u 0 Ω μ mmR)
      (fun _ => True)
      (fun N n x => (decodeMatrix (dec p) x.1).IsHermitian ∧ 0 ≤ u ∧ 0 ≤ μ N ∧
        9 * (N + 1) ≤ Ω ∧ specNorm (decodeMatrix (dec p) x.1) ≤ dec p x.2.2 ∧
        0 < dec p x.2.1 ∧ dec p x.2.1 ≤ 1 / 2 ∧
        ∃ a : ℝ, 0 < a ∧ (∀ y ∈ spectrum ℝ (decodeMatrix (dec p) x.1), a ≤ |y|) ∧
          640 * N * √(N : ℝ) * (8 + μ N) *
              (newtonSchulzSteps (a / (2 * dec p x.2.2)) (dec p x.2.1 / (16 * N)) + 1) * u ≤
            a / dec p x.2.2 * dec p x.2.1 ∧
          newtonSchulzSteps (a / (2 * dec p x.2.2)) (dec p x.2.1 / (16 * N)) + 1 ≤ n 0)
      (fun N _ x st => ∃ Y : Matrix (Fin N) (Fin N) (K × K), pairLayout.Holds st.store p 2 0 Y ∧
        specNorm (cfc Real.sign (decodeMatrix (dec p) x.1) - decodeMatrix (dec p) Y) ≤
          dec p x.2.1)
      (fun _ _ _ => 0) N₀ := by
  intro N₀
  obtain ⟨N, hN₀, hN⟩ : ∃ N, N₀ ≤ N ∧ 0 < N := ⟨N₀ + 1, by omega, by omega⟩
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set S := newtonSchulzSteps (1 / (2 * 1)) (1 / 2 / (16 * (N : ℝ)))
  obtain ⟨t, ⟨ht, hB⟩, hu⟩ := ((eventually_pos_and_lt_two_pow 1).and
    (eventually_mul_two_inv_pow_le (640 * N * √(N : ℝ) * (8 + 2 * N) * (S + 1))
      (by norm_num : (0 : ℝ) < 1 / 1 * (1 / 2)))).exists
  obtain ⟨I, hIs, hImm, -⟩ := exists_gridKernelInterp Unit t
  refine ⟨Unit, Bool, inferInstance, (), true, ℝ, inferInstance, fun _ => Real.roundNearest t,
    2⁻¹ ^ t, 9 * ((N : ℝ) + 1), fun d => 2 * d, N, fun _ => ⌈S⌉₊ + 1, hN₀, hN,
    (Matrix.of fun i j => if i = j then (1, 0) else (0, 0), 1 / 2, 1), ?_, I,
    fun _ _ y => Real.roundNearest t y,
    hIs ▸ isIndexExactSem_gridSem _ (fun _ => ht) 1 (fun _ => hB),
    ⟨hIs ▸ isRelErrSem_gridSem _ (fun _ => ht), gridMM t, hImm, isMatMulErr_gridMM ht _⟩,
    trivial⟩
  dsimp only
  rw [decodeMatrix_roundNearest_identity ht, Real.roundNearest_one ht, roundNearest_half ht]
  refine ⟨Matrix.isHermitian_one, by positivity, by positivity, le_rfl, specNorm_one.le,
    by norm_num, le_rfl, 1, one_pos, fun y hy => ?_, hu, ?_⟩
  · rw [spectrum.one_eq, Set.mem_singleton_iff] at hy
    simp [hy]
  · push_cast
    exact add_le_add_left (Nat.le_ceil S) 1

/-- **The deflation target is not vacuous**: for every $N_0$, at $N = N_0 + 1$ and full rank
$r = N$, the grid semantics with $t$ bits ($t$ large, from $N$), the kernels `NLAlib.gridMM t`
and `NLAlib.gridQR t`, the tape rounded to nearest
($c = 1$), $\mu_{\mathrm{MM}}(d) = \mu_{\mathrm{QR}}(d) = 2d$, $\Omega = 8\sqrt2\sqrt N$, the
stored identity matrix with $\mathbf{U} = \mathbf{V} = \mathbf{S} = \mathbf{I}$,
$\beta = 1/(30\sqrt2\sqrt N)$, $t = 0$ (the norm tail) and $x = 1$ meet every hypothesis of
`NLAlib.MatrixFreeRoundedProbDeflate`. The witness of the target (`scripts/Targets.lean`,
item 7). No printed source. -/
theorem matrixFreeRoundedProbDeflate_nonVacuous : ∀ N₀ : ℕ,
    ∃ (P ι : Type) (_ : DecidableEq P) (p : P) (mm qr : ι) (K : Type) (_ : Inhabited K)
      (dec : P → K → ℝ) (u Ω : ℝ) (μM μQ : ℕ → ℝ) (c : ℝ),
    MatrixFreeRoundedProb.NonVacuous p (deflateProg.compiled p mm qr) (fun N n => n 0 ≤ N)
      (fun N n => DeflationData K N (n 0))
      (fun N n d => ![(pairLayout.toArray d.A).map some, Array.replicate (2 * (N * n 0)) none])
      dec (fun _ _ => 2) (fun N n => deflateCount p mm qr N (n 0))
      (fun N n q => if q = p then 10 * (N * N) + 2 * (N * n 0) + 2 else 0)
      (fun _ _ I => IsRelErrSem (fun _ => u) dec (fun _ _ => True) I.sem ∧
        (∃ mmR : MatMulMap (K × K), IsMatMulKernel I mm pairLayout mmR ∧
          IsMatMulErr (decodeComplex (dec p)) u 0 Ω μM mmR) ∧
        ∃ qrR : QRMap (K × K), IsQRKernel I qr pairLayout qrR ∧
          IsQRErr (decodeComplex (dec p)) u 0 Ω μQ qrR)
      (fun ρ => IsTapeRounding dec p u 0 (2 * Ω) (fun _ => c) ρ ∧
        ∀ (g : Dist) (i j : ℕ) (y : ℝ), ρ g i y = ρ g j y)
      (fun N _ d => HasOrthonormalCols d.U ∧ HasOrthonormalCols d.V ∧ IsUnit d.S ∧
        specNorm (d.U * d.S * d.Vᴴ - decodeMatrix (dec p) d.A) ≤ d.β ∧ d.β ≤ 1 ∧ 0 ≤ d.t ∧
        0 < d.x ∧ 0 ≤ c ∧ 0 ≤ u ∧ (c + 3) * u ≤ 1 / 10 ∧
        (specNorm d.S + 2) * specNorm d.S⁻¹ * (√2 * (2 * √(N : ℝ) + d.t)) / d.x * d.β ≤ 1 / 5 ∧
        (4 * μQ N + 4 * √(N : ℝ) * (2 * (c + 3)) + 2 * μM N) * u ≤ d.β ∧
        2 * (specNorm d.S + 1) * (√2 * (2 * √(N : ℝ) + d.t)) ≤ Ω)
      (fun N n d st => ∃ Q : Matrix (Fin N) (Fin (n 0)) (K × K),
        pairLayout.Holds st.store p 1 0 Q ∧ ∃ W : Matrix (Fin (n 0)) (Fin (n 0)) ℂ,
          HasOrthonormalCols W ∧ specNorm (d.U * W - decodeMatrix (dec p) Q) ≤
            6 * ((specNorm d.S + 2) * specNorm d.S⁻¹ * (√2 * (2 * √(N : ℝ) + d.t)) / d.x) * d.β)
      (fun _ n d => 2 * Real.exp (-d.t ^ 2 / 2) + (n 0 : ℝ) ^ 2 * d.x ^ 2) N₀ := by
  intro N₀
  obtain ⟨N, hN₀, hN⟩ : ∃ N, N₀ ≤ N ∧ 0 < N := ⟨N₀ + 1, by omega, by omega⟩
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h2 : (0 : ℝ) < √2 := by positivity
  have hNr : (0 : ℝ) < √(N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  set β : ℝ := 1 / (30 * √2 * √(N : ℝ))
  have hβ : 0 < β := by positivity
  obtain ⟨t, ⟨ht, hB⟩, hu₁, hu₂⟩ := ((eventually_pos_and_lt_two_pow 2).and
    ((eventually_mul_two_inv_pow_le (1 + 3) (by norm_num : (0 : ℝ) < 1 / 10)).and
      (eventually_mul_two_inv_pow_le
        (4 * (2 * (N : ℝ)) + 4 * √(N : ℝ) * (2 * (1 + 3)) + 2 * (2 * N)) hβ))).exists
  obtain ⟨I, hIs, hImm, hIqr⟩ := exists_gridKernelInterp Unit t
  refine ⟨Unit, Bool, inferInstance, (), true, false, ℝ, inferInstance,
    fun _ => Real.roundNearest t, 2⁻¹ ^ t, 8 * √2 * √(N : ℝ), fun d => 2 * d, fun d => 2 * d, 1,
    N, fun _ => N, hN₀, le_rfl,
    ⟨Matrix.of fun i j => if i = j then (1, 0) else (0, 0), 1, 1, 1, β, 0, 1⟩, ?_,
    I, fun _ _ y => Real.roundNearest t y,
    hIs ▸ isIndexExactSem_gridSem _ (fun _ => ht) 2 (fun _ => hB),
    ⟨hIs ▸ isRelErrSem_gridSem _ (fun _ => ht),
      ⟨gridMM t, hImm, isMatMulErr_gridMM ht _⟩,
      gridQR t, hIqr, isQRErr_gridQR ht _⟩,
    isTapeRounding_roundNearest ht () _, fun _ _ _ _ => rfl⟩
  dsimp only
  rw [decodeMatrix_roundNearest_identity ht, specNorm_one, inv_one, specNorm_one]
  simp only [Matrix.mul_one, Matrix.conjTranspose_one, sub_self, specNorm_zero]
  have hβ₁ : β ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.one_lt_sqrt_two, Real.one_le_sqrt.mpr (show (1 : ℝ) ≤ N by exact_mod_cast hN)]
  have hβ₅ : (1 + 2) * 1 * (√2 * (2 * √(N : ℝ) + 0)) / 1 * β = 1 / 5 := by
    simp only [β]
    field_simp
    ring
  refine ⟨hasOrthonormalCols_one, hasOrthonormalCols_one, isUnit_one, hβ.le, hβ₁, le_rfl,
    one_pos, zero_le_one, by positivity, hu₁, hβ₅.le, hu₂, le_of_eq (by ring)⟩

/-- **The spectral bisection target is not vacuous**: for every $N_0$, at $N = N_0 + 1$, the grid
semantics with $t$ bits ($t$ large, from $N$), the kernels `NLAlib.gridMM t` and
`NLAlib.gridQR t`, the tape rounded to nearest ($c \equiv 1$),
$\mu_{\mathrm{MM}}(d) = \mu_{\mathrm{QR}}(d) = 2d$, $\theta = 1$, the stored identity matrix,
$R_0 = 1$, $\varepsilon = 2^{-15}$, $\ell = \mathsf{bisectionDepth}(\varepsilon) + 2$, a power of
two $\beta = 2^{-k}$ below the bound $\bar\beta$ of the target, the step limit
$F = \lceil N_{\mathrm{st}} \rceil$ and $\Omega$ the lower bound of the target meet every hypothesis
of `NLAlib.MatrixFreeRoundedProbEigh`. The witness of the target (`scripts/Targets.lean`, item 7).
No printed source. -/
theorem matrixFreeRoundedProbEigh_nonVacuous : ∀ N₀ : ℕ,
    ∃ (P ι : Type) (_ : DecidableEq P) (p : P) (mm qr : ι) (K : Type) (_ : Inhabited K)
      (dec : P → K → ℝ) (u Ω θ : ℝ) (μM μQ : ℕ → ℝ) (c : Dist → ℝ),
    MatrixFreeRoundedProb.NonVacuous p (eighProg.compiled p mm qr) (fun _ _ => True)
      (fun N _ => EighData K N)
      (fun N _ x => ![(pairLayout.toArray x.A).map some, #[some x.R₀, some x.ε, some x.β],
        Array.replicate (2 * (N * N)) none, Array.replicate N none])
      dec (fun N _ => N + 4) (fun N n => eighCount p mm qr N (n 0) (n 1))
      (fun N n q => if q = p then 4 * (N * N) + N + 3 + 64 * (N + 1) ^ 2 * (n 0 + 3) else 0)
      (fun _ _ I => IsRelErrSem (fun _ => u) dec (fun _ _ => True) I.sem ∧ MulShrinks dec I.sem ∧
        (∃ mmR : MatMulMap (K × K), IsMatMulKernel I mm pairLayout mmR ∧
          IsMatMulErr (decodeComplex (dec p)) u 0 Ω μM mmR) ∧
        ∃ qrR : QRMap (K × K), IsQRKernel I qr pairLayout qrR ∧
          IsQRErr (decodeComplex (dec p)) u 0 Ω μQ qrR)
      (fun ρ => IsTapeRounding dec p u 0 (2 * Ω) c ρ ∧
        (∀ (g : Dist) (i j : ℕ) (y : ℝ), ρ g i y = ρ g j y) ∧
        ∀ g : Dist, (Set.range (ρ g 0)).Countable ∧ ∀ z, MeasurableSet (ρ g 0 ⁻¹' {z}))
      (fun N n x =>
        let uM := (c .uniform + 1) * u
        let cN := 2 * (c .gaussian + 3)
        let ℓ := n 0
        let βb := ((ℓ : ℝ) - 1) ^ 2 * dec p x.ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
          √(N * min (N : ℝ) (ℓ + 1) * min (N : ℝ) (Real.exp 1)) *
          (2 * √2 * √(N : ℝ) + √(Real.log (96 * N * min (N : ℝ) (ℓ + 1) / θ))))
        let Nst := newtonSchulzSteps (θ / (12 * N * ℓ * (ℓ + 1))) (dec p x.β / (16 * N))
        1 ≤ N ∧ (decodeMatrix (dec p) x.A).IsHermitian ∧
        specNorm (decodeMatrix (dec p) x.A) ≤ dec p x.R₀ ∧ 0 < dec p x.R₀ ∧
        0 < dec p x.ε ∧ dec p x.ε ≤ 2⁻¹ ^ 15 ∧ 0 < θ ∧ θ ≤ 1 ∧ bisectionDepth (dec p x.ε) ≤ ℓ ∧
        0 < dec p x.β ∧ dec p x.β ≤ βb ∧
        0 ≤ u ∧ 0 ≤ c .uniform ∧ 0 ≤ c .gaussian ∧ (c .gaussian + 3) * u ≤ 1 / 10 ∧
        Monotone μM ∧ Monotone μQ ∧ 0 ≤ μM 0 ∧ 0 ≤ μQ 0 ∧
        146 * N * ℓ * (ℓ + 1) * (4 * μM N + 10 + 10 * √(N : ℝ)) * uM ≤ θ * dec p x.β ∧
        2048 * (N + Nst + 1) * (4 * μM N + 10 + 10 * √(N : ℝ)) * uM ≤ dec p x.β ∧
        16 * (4 * μQ N + 4 * √(N : ℝ) * (cN + 1) + 2 * μM N + 1) * uM ≤ dec p x.β ∧
        Nst ≤ n 1 ∧
        16 * (2 * dec p x.R₀ + N + 2 * ℓ + 2 * √2 * √(N : ℝ) +
          √(Real.log (96 * N * min (N : ℝ) (ℓ + 1) / θ))) ≤ Ω)
      (fun N _ x st => ∃ (U : Matrix (Fin N) (Fin N) (K × K)) (d : Fin N → K),
        pairLayout.Holds st.store p 2 0 U ∧ (∀ i : Fin N, st.store.read p 3 i = some (d i)) ∧
        IsApproxDiagonalization (decodeMatrix (dec p) x.A) (decodeMatrix (dec p) U)
          (fun i => dec p (d i)) (2 * dec p x.ε * dec p x.R₀) (dec p x.ε / 3))
      (fun _ _ _ => θ) N₀ := by
  intro N₀
  obtain ⟨N, hN₀, hN⟩ : ∃ N, N₀ ≤ N ∧ 0 < N := ⟨N₀ + 1, by omega, by omega⟩
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨L, hL⟩ : ∃ L, L = bisectionDepth (2⁻¹ ^ 15) + 2 := ⟨_, rfl⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hβb : 0 < ((L : ℝ) - 1) ^ 2 * 2⁻¹ ^ 15 * √1 / (52 * (L : ℝ) ^ 2 * (2 * L - 1) *
      √(N * min (N : ℝ) (L + 1) * min (N : ℝ) (Real.exp 1)) *
      (2 * √2 * √(N : ℝ) + √(Real.log (96 * N * min (N : ℝ) (L + 1) / 1)))) := by
    have hm : 0 < (N : ℝ) * min (N : ℝ) (L + 1) * min (N : ℝ) (Real.exp 1) :=
      mul_pos (mul_pos hNr (lt_min hNr (by positivity))) (lt_min hNr (Real.exp_pos 1))
    refine div_pos (mul_pos (mul_pos (pow_pos (by linarith) 2) (by norm_num)) (by simp))
      (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos (by linarith) 2))
        (by linarith)) (Real.sqrt_pos.mpr hm)) (add_pos_of_pos_of_nonneg
          (mul_pos (by positivity) (Real.sqrt_pos.mpr hNr)) (Real.sqrt_nonneg _)))
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hβb (by norm_num : (2⁻¹ : ℝ) < 1)
  obtain ⟨β, hβ, hβk⟩ : ∃ β : ℝ, 0 < β ∧ β = 2⁻¹ ^ k := ⟨_, by positivity, rfl⟩
  set Nst := newtonSchulzSteps (1 / (12 * N * L * (L + 1))) (β / (16 * N))
  set μ : ℝ := 4 * (2 * (N : ℝ)) + 10 + 10 * √(N : ℝ)
  obtain ⟨t, ⟨ht, hB⟩, hu₁, hu₂, hu₃, hu₄⟩ := ((eventually_pos_and_lt_two_pow (N + 4)).and
    ((eventually_mul_two_inv_pow_le (1 + 3) (by norm_num : (0 : ℝ) < 1 / 10)).and
    ((eventually_mul_two_inv_pow_le (146 * N * L * (L + 1) * μ * (1 + 1))
      (by positivity : (0 : ℝ) < 1 * β)).and
    ((eventually_mul_two_inv_pow_le (2048 * (N + Nst + 1) * μ * (1 + 1)) hβ).and
    (eventually_mul_two_inv_pow_le (16 * (4 * (2 * (N : ℝ)) + 4 * √(N : ℝ) * (2 * (1 + 3) + 1) +
      2 * (2 * N) + 1) * (1 + 1)) hβ))))).exists
  have hM := isAccurate_gridMachine ht 0
  obtain ⟨I, hIs, hImm, hIqr⟩ := exists_gridKernelInterp Unit t
  have hRβ : Real.roundNearest t β = β := by rw [hβk]; exact Real.roundNearest_two_inv_pow ht k
  have hmono : Monotone fun d : ℕ => 2 * (d : ℝ) := fun a b h =>
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) zero_le_two
  refine ⟨Unit, Bool, inferInstance, (), true, false, ℝ, inferInstance,
    fun _ => Real.roundNearest t, 2⁻¹ ^ t, 16 * (2 * 1 + N + 2 * L + 2 * √2 * √(N : ℝ) +
      √(Real.log (96 * N * min (N : ℝ) (L + 1) / 1))), 1, fun d => 2 * d, fun d => 2 * d,
    fun _ => 1, N, ![L, ⌈Nst⌉₊], hN₀, trivial, ⟨(gridMachine t).identityMat N, 1, 2⁻¹ ^ 15, β⟩,
    ?_, I, fun _ _ y => Real.roundNearest t y,
    hIs ▸ isIndexExactSem_gridSem _ (fun _ => ht) (N + 4) (fun _ => hB),
    ⟨hIs ▸ isRelErrSem_gridSem _ (fun _ => ht), hIs ▸ mulShrinks_gridSem _ (fun _ => ht),
      ⟨gridMM t, hImm, isMatMulErr_gridMM ht _⟩,
      gridQR t, hIqr, isQRErr_gridQR ht _⟩,
    isTapeRounding_roundNearest ht () _, fun _ _ _ _ => rfl, fun _ =>
      ⟨Real.countable_range_roundNearest t, fun z =>
        measurable_roundNearest t (measurableSet_singleton z)⟩⟩
  dsimp only
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hM.decodeMatrix_identityMat, Real.roundNearest_one ht, Real.roundNearest_two_inv_pow ht, hRβ]
  refine ⟨hN, Matrix.isHermitian_one, specNorm_one.le, one_pos, by positivity, le_rfl, one_pos,
    le_rfl, by omega, hβ, hβk ▸ hk.le, by positivity, zero_le_one, zero_le_one, hu₁, hmono, hmono,
    by simp, by simp, (le_of_eq (by ring)).trans hu₂, (le_of_eq (by ring)).trans hu₃,
    (le_of_eq (by ring)).trans hu₄, Nat.le_ceil _, le_rfl⟩

end NLAlib
