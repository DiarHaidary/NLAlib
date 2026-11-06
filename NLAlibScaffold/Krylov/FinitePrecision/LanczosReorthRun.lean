/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosReorthRun
public import NLAlibScaffold.Matrix.Perturbation.OrthErr

/-!
# Orthogonality, coefficients and the perturbed relation of a reorthogonalized run (scaffold)

Statements for `NLAlib/Krylov/FinitePrecision/LanczosReorthRun.lean` (stage LANCZOS-REORTH,
design note `docs/design/Krylov-LanczosReorth.md` §3.2–3.3, ids D2–D8 and the prefix
restriction), in the proof order D5 → D3 → D4 → D6 → D7: orthogonality of the computed basis on
the admissible prefix [Paige1970], the coefficient bounds, the reorthogonalization coefficients
(the one place symmetry is used), the perturbed three-term relation with the discarded
coefficients in its residual, the projection form [Simon1984b], and the dimension count.

Common hypotheses: `hη : L.η₀ ≤ 1 / 100` and the fixed-point condition
`hsmall : √(3(k+1)) * L.orthLevel ≤ L.η₀` of §1.2; for the coefficient and residual bounds also
`hrec : L.recLevel ≤ 1 / 100` and `hτ : L.τ ≤ 1`. The constants are generous proof-sketch values;
a proof giving other constants records them in `docs/constants.toml`.

## Main results

* `NLAlib.LanczosReorthRun.recurrenceError_eq`: the residual of the three-term relation.
* `NLAlib.LanczosReorthRun.norm_transpose_mulVec_v_le`: one column (D5a).
* `NLAlib.LanczosReorthRun.frobNorm_gram_sub_one_le`: S2 (D5).
* `NLAlib.LanczosReorthRun.coeff_le`: D3. `NLAlib.LanczosReorthRun.norm_coef_le`: D4.
* `NLAlib.LanczosReorthRun.frobNorm_residual_le`: S1 (D6).
* `NLAlib.LanczosReorthRun.specNorm_transpose_mul_mul_sub_tridiagonal_le`: S1′ (D7).
* `NLAlib.LanczosReorthRun.succ_le_card`: D8. `NLAlib.LanczosReorthRun.exists_ofLE`: prefixes.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace LanczosReorthRun

variable {n k : ℕ} (L : LanczosReorthRun n k)

/-- **The residual of the three-term relation** (D2): column $j$ of the residual of the
underlying data is the reorthogonalization correction plus the local errors,
$\mathbf{f}_j = \mathbf{V}_{j+1}\mathbf{h}_{j+1} + (\mathbf{z}_{j+1} - \mathbf{V}_{j+1}
\mathbf{h}_{j+1} - \mathbf{z}_{j+1}') - \boldsymbol\delta_{j+1} - \mathbf{e}^u_{j+1} -
\mathbf{e}^w_{j+1} - \mathbf{e}^z_{j+1}$. No printed source.
Proof: unfold `NLAlib.LanczosData.recurrenceError`, `NLAlib.LanczosReorthRun.toLanczosData`;
rewrite with the fields `u_eq`, `w_eq`, `z_eq`, `smul_v_eq` and `abel`. S, about 15 lines. -/
theorem recurrenceError_eq {j : ℕ} (hj : j < k) :
    L.toLanczosData.recurrenceError j =
      basisOf L.v (j + 1) *ᵥ (fun i => L.h (j + 1) i) +
        (L.z (j + 1) - basisOf L.v (j + 1) *ᵥ (fun i => L.h (j + 1) i) - L.z' (j + 1)) -
        L.δ (j + 1) - L.eu (j + 1) - L.ew (j + 1) - L.ez (j + 1) := by
  sorry

/-- **One admissible column is nearly orthogonal to the previous ones** (D5a): if
$\|\mathbf{V}_{j+1}^{\mathsf{T}}\mathbf{V}_{j+1} - \mathbf{I}\|_2 \le \eta_0 \le 1/100$ then
$\|\mathbf{V}_{j+1}^{\mathsf{T}}\mathbf{v}_{j+2}\| \le \mu$ = `NLAlib.LanczosReorthRun.orthLevel`.
[Paige1970] (the criterion in substance).
Proof: $\beta\mathbf{v}_{j+2} = \mathbf{z}' + \boldsymbol\delta$ (`smul_v_eq`); `orth_eq`'s
`IsOrthErr.orth` gives $\|\mathbf{V}^{\mathsf{T}}\mathbf{z}'\| \le \varepsilon_1\|\mathbf{z}'\| +
\varepsilon_3\|\mathbf{z}\|$; admissibility with `abs_ν_sub_le`, `abs_β_sub_le` gives
$\|\mathbf{z}\| \le (1+\varepsilon)/((1-\varepsilon)\tau)\,\|\mathbf{z}'\|$ and $\beta \ge
(1-\varepsilon)\|\mathbf{z}'\| > 0$; $\|\mathbf{V}^{\mathsf{T}}\boldsymbol\delta\| \le
\sqrt{1+\eta_0}\,\varepsilon\|\mathbf{z}'\|$ by
`NLAlib.specNorm_le_sqrt_of_specNorm_gram_sub_one_le`;
divide by $\beta$ and compare with $2(\varepsilon_1 + \varepsilon_3/\tau + \varepsilon)$
(`ε_le`). S, about 40 lines. -/
theorem norm_transpose_mulVec_v_le {j : ℕ} (hj : j < k)
    (hV : specNorm ((basisOf L.v (j + 1))ᵀ * basisOf L.v (j + 1) - 1) ≤ L.η₀)
    (hη : L.η₀ ≤ 1 / 100) :
    ‖WithLp.toLp 2 ((basisOf L.v (j + 1))ᵀ *ᵥ L.v (j + 2))‖ ≤ L.orthLevel := by
  sorry

/-- **Orthogonality of the computed basis on the admissible prefix** (D5, S2): under the
fixed-point condition, for every $m \le k + 1$,
$\|\mathbf{V}_m^{\mathsf{T}}\mathbf{V}_m - \mathbf{I}\|_{\mathsf F} \le \sqrt{3m}\,\mu$.
[Paige1970] for Lanczos with reorthogonalization; [GiraudLangouRozloznikVandenEshof2005,
Theorem 2] for the CGS2 kernel constants.
Proof: strong induction on $m$ with `NLAlib.frobNorm_gram_sub_one_le_of_columns`: the column
hypothesis at $c < m$ is `NLAlib.LanczosReorthRun.norm_transpose_mulVec_v_le` at $j = c - 1$
(for $c \ge 1$; $c = 0$ is the empty basis), whose precondition comes from the induction
hypothesis at $c$ ($\|\cdot\|_2 \le \|\cdot\|_{\mathsf F}$, `specNorm_le_frobNorm`, and
$\sqrt{3c}\,\mu \le \sqrt{3(k+1)}\,\mu \le \eta_0$); the norm hypothesis is
`abs_norm_v_sq_sub_one_le` with $\varepsilon \le \mu$. Note `basisOf` is the
`Matrix.of` of `NLAlib.frobNorm_gram_sub_one_le_of_columns`. M, about 50 lines. -/
theorem frobNorm_gram_sub_one_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀) :
    ∀ m ≤ k + 1, frobNorm ((basisOf L.v m)ᵀ * basisOf L.v m - 1) ≤
      Real.sqrt (3 * m) * L.orthLevel := by
  sorry

/-- **Coefficient bounds without growth in $j$** (D3): $|\alpha_{j+1}|$, $\beta_{j+1}$ and
$\|\mathbf{z}_{j+1}\|$ are at most $\tfrac32\|\mathbf{H}\|_2$. [Paige1976] for the plain case
(there with growth); here orthogonality is available first.
Proof: order D5 → D3. From `frobNorm_gram_sub_one_le` the basis is nearly orthonormal. Expand
$\|\mathbf{z}\|^2$ with $\mathbf{z} = \mathbf{H}\mathbf{v}_{j+1} - \beta_j\mathbf{v}_j -
\alpha_{j+1}\mathbf{v}_{j+1} + \mathbf{e}$ ($\mathbf{e}$ the three local errors): the cross terms
are $\le \mu$ times products of coefficients and $\|\mathbf{H}\|$, and $\mathbf{v}_j^{\mathsf{T}}
\mathbf{H}\mathbf{v}_{j+1} = \beta_j + O(\mu\|\mathbf{H}\|)$ by symmetry and the relation at
step $j$, so $\|\mathbf{z}\| \le (1 + c\mu + c\varepsilon)\|\mathbf{H}\| + c\mu\beta_j$; $|\alpha|$
from `α_eq`, `abs_eα_le`; $\beta \le (1+\varepsilon)\|\mathbf{z}'\|$ and $\|\mathbf{z}'\|^2 =
\mathbf{z}'^{\mathsf{T}}(\mathbf{z} - \mathbf{V}\mathbf{h} - \mathbf{r})$ with
`NLAlib.IsOrthErr.norm_coef_le` give $\|\mathbf{z}'\| \le (1 + c\,\mathrm{rec})\|\mathbf{z}\|$.
Induction on $j$ closes with `hrec`. M, about 120 lines. -/
theorem coeff_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    ∀ j < k, |L.α (j + 1)| ≤ 3 / 2 * specNorm L.H ∧ L.β (j + 1) ≤ 3 / 2 * specNorm L.H ∧
      ‖WithLp.toLp 2 (L.z (j + 1))‖ ≤ 3 / 2 * specNorm L.H := by
  sorry

/-- **The discarded reorthogonalization coefficients are small** (D4): for symmetric
$\mathbf{H}$, $\|\mathbf{h}_{j+1}\| \le 16\sqrt{j+1}\,(\mu + \varepsilon + \varepsilon_2)
\|\mathbf{H}\|_2$. The one place symmetry is needed: without it the coefficients are $O(1)$
(Arnoldi). [Paige1970] in substance; [Simon1984b] for semi-orthogonal variants.
Proof: induction on $j$. By `NLAlib.IsOrthErr.norm_coef_le`, bound $\|\mathbf{V}_{j+1}^{\mathsf{T}}
\mathbf{z}_{j+1}\|$ componentwise: for $i \le j - 1$ (0-based columns before the previous one)
$\mathbf{v}_i^{\mathsf{T}}\mathbf{H}\mathbf{v}_{j+1} = (\mathbf{H}\mathbf{v}_i)^{\mathsf{T}}
\mathbf{v}_{j+1}$ (`transpose_H`, `Matrix.dotProduct_mulVec`); expand $\mathbf{H}\mathbf{v}_i$ by
`NLAlib.LanczosReorthRun.recurrenceError_eq` at $i$: off-diagonal Gram entries ($\le\mu$ by
`norm_transpose_mulVec_v_le`, times coefficients $\le \tfrac32\|\mathbf{H}\|$ from `coeff_le`),
the term $\mathbf{h}_i^{\mathsf{T}}\mathbf{V}_i^{\mathsf{T}}\mathbf{v}_{j+1}$ ($\le\|\mathbf{h}_i\|
\mu$, second order) and the local errors ($\le c(\varepsilon + \varepsilon_2)\|\mathbf{H}\|$); the
previous column carries the same terms plus the cancellation
$\beta_j(\|\mathbf{v}_{j+1}\|^2 - \|\mathbf{v}_j\|^2) = O(\varepsilon\|\mathbf{H}\|)$; the current
column is $\alpha(1 - \|\mathbf{v}\|^2) + O(\varepsilon) = O(\varepsilon\|\mathbf{H}\|)$. Sum the
squares over $j + 1$ components; $\|\mathbf{V}^{\mathsf{T}}\mathbf{z}'\| \le
\varepsilon_1\|\mathbf{z}'\|
+ \varepsilon_3\|\mathbf{z}\| \le (\varepsilon_1 + \varepsilon_3)\tfrac32\|\mathbf{H}\|$ with
$\varepsilon_3 \le \varepsilon_3/\tau$. L, about 200 lines; intermediate lemmas: the componentwise
bound for one earlier column, and the sum over columns. -/
theorem norm_coef_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    ∀ j < k, ‖WithLp.toLp 2 (fun i : Fin (j + 1) => L.h (j + 1) i)‖ ≤
      16 * Real.sqrt ((j : ℝ) + 1) * L.recLevel * specNorm L.H := by
  sorry

/-- **The perturbed Lanczos relation of a reorthogonalized run** (D6, S1): with the discarded
coefficients in the residual, $\|\mathbf{F}_k\|_{\mathsf F} \le 20(k+1)\,(\mu + \varepsilon +
\varepsilon_2)\,\|\mathbf{H}\|_2$; the relation itself is `NLAlib.LanczosData.mul_basis`.
[Paige1970] for the reorthogonalized relation; [Paige1976] for the rounding part.
Proof: column $j$ by `NLAlib.LanczosReorthRun.recurrenceError_eq`: $\|\mathbf{V}_{j+1}\mathbf{h}\|
\le \sqrt{1+\eta_0}\cdot 16\sqrt{j+1}\,\mathrm{rec}\,\|\mathbf{H}\|$ (`norm_coef_le`,
`NLAlib.specNorm_le_sqrt_of_specNorm_gram_sub_one_le`), the orthogonalization residual $\le
\varepsilon_2\|\mathbf{z}\|$, $\boldsymbol\delta$, $\mathbf{e}^u$, $\mathbf{e}^w$, $\mathbf{e}^z$
$\le
c\varepsilon\|\mathbf{H}\|$ (`coeff_le`, and $\|\mathbf{v}\| \le 1 + \varepsilon$ from
`abs_norm_v_sq_sub_one_le`);
then $\|\mathbf{F}\|_{\mathsf F}^2 = \sum_j\|\mathbf{f}_j\|^2 \le \sum_j (17\sqrt{j+1})^2
\mathrm{rec}^2\|\mathbf{H}\|^2$ and $\sum_{j<k}(j+1) \le (k+1)^2/2$. M, about 60 lines. -/
theorem frobNorm_residual_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    frobNorm L.toLanczosData.residual ≤ 20 * ((k : ℝ) + 1) * L.recLevel * specNorm L.H := by
  sorry

/-- **The projection form** (D7, S1′): $\|\mathbf{V}_k^{\mathsf{T}}\mathbf{H}\mathbf{V}_k -
\mathbf{T}_k\|_2 \le 40(k+1)(\mu + \varepsilon + \varepsilon_2)\|\mathbf{H}\|_2$.
[Simon1984b] (semi-orthogonality suffices).
Proof: multiply `NLAlib.LanczosData.mul_basis` by $\mathbf{V}_k^{\mathsf{T}}$:
$\mathbf{V}_k^{\mathsf{T}}\mathbf{H}\mathbf{V}_k - \mathbf{T}_k = (\mathbf{G} - \mathbf{I})
\mathbf{T}_k + \mathbf{V}_k^{\mathsf{T}}(\beta_k\mathbf{v}_{k+1})\mathbf{e}^{\mathsf{T}} +
\mathbf{V}_k^{\mathsf{T}}\mathbf{F}_k$; bound with `frobNorm_gram_sub_one_le`, `coeff_le`
($\|\mathbf{T}_k\|_2 \le \tfrac92\|\mathbf{H}\|$), `norm_transpose_mulVec_v_le`,
`frobNorm_residual_le`. S, about 30 lines. -/
theorem specNorm_transpose_mul_mul_sub_tridiagonal_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    specNorm (L.toLanczosData.basisᵀ * L.H * L.toLanczosData.basis -
      L.toLanczosData.tridiagonal) ≤ 40 * ((k : ℝ) + 1) * L.recLevel * specNorm L.H := by
  sorry

/-- **Full reorthogonalization stops by step $n$** (D8): the admissible prefix has
$k + 1 \le n$ (strict admissibility makes $\mathbf{v}_{k+1}$ a genuine column). No printed
source.
Proof: `frobNorm_gram_sub_one_le` at $m = k + 1$ gives $\|\cdot\|_2 \le \eta_0 < 1$
(`specNorm_le_frobNorm`); apply `NLAlib.le_of_specNorm_gram_sub_one_lt_one`. S, about 8 lines. -/
theorem succ_le_card (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀) : k + 1 ≤ n := by
  sorry

/-- **Prefixes of a run are runs** (replaces E6, whose terminal case $\beta_k = 0$ cannot occur
under strict admissibility): for $0 < m \le k$ there is a run of $m$ steps with the same data and
parameters. Proof: build the structure field by field from `L`, restricting each `∀ j < k` field
to `j < m` (`lt_of_lt_of_le`); the norm field `abs_norm_v_sq_sub_one_le` restricts to
$j \le m + 1$. S, about 40 lines. -/
theorem exists_ofLE {m : ℕ} (hm : 0 < m) (hmk : m ≤ k) :
    ∃ L' : LanczosReorthRun n m, L'.H = L.H ∧ L'.v = L.v ∧ L'.α = L.α ∧ L'.β = L.β ∧
      L'.ν = L.ν ∧ L'.h = L.h ∧ L'.ε = L.ε ∧ L'.τ = L.τ ∧ L'.η₀ = L.η₀ ∧ L'.ε₁ = L.ε₁ ∧
      L'.ε₂ = L.ε₂ ∧ L'.ε₃ = L.ε₃ := by
  sorry

end LanczosReorthRun

end NLAlib
