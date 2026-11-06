/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Contract
public import NLAlib.Matrix.Computation.EntrywiseRounding
public import NLAlib.Matrix.Computation.InterpMachine

/-!
# The floating-point machine of a value semantics: contract and exact operations (scaffold)

Statements for `NLAlib/Matrix/Computation/InterpMachine.lean` (stage COMPDYN S1c, design note
`docs/design/Computation-SignDeflatePrograms.md`, §2): under the standard model with every value
in range and an exact literal $1$, the machine of a semantics meets the machine contract
`NLAlib.FloatMachine.IsAccurate` with floor $0$, given routines and samplers meeting theirs; the
semantics decides flags; the normal sampler of a tape rounding meets the normal-sampler contract;
and on exact real arithmetic the entrywise machine operations decode to their exact values (the
exact specifications of the complex kernels).

## Main results

* `NLAlib.Computation.isAccurate_toFloatMachine`: the machine contract.
* `NLAlib.Computation.IsRelErrSem.decidesFlags`.
* `NLAlib.Computation.isNormalSampler_gaussianNormal`: the normal sampler of a tape rounding.
* `NLAlib.Computation.decodeMatrix_hermShift_toFloatMachine_exactSem`,
  `NLAlib.Computation.decodeMatrix_hermScale_toFloatMachine_exactSem`,
  `NLAlib.Computation.decodeMatrix_hermAvg_toFloatMachine_exactSem`,
  `NLAlib.Computation.decodeMatrix_conjTransposeMat_toFloatMachine_exactSem`,
  `NLAlib.Computation.traceRe_toFloatMachine_exactSem`,
  `NLAlib.Computation.boxTest_toFloatMachine_exactSem_iff`,
  `NLAlib.Computation.decodeMatrix_addParts_toFloatMachine_exactSem`,
  `NLAlib.Computation.decodeMatrix_subParts_toFloatMachine_exactSem`,
  `NLAlib.Computation.decodeMatrix_mulParts_toFloatMachine_exactSem`: exact specifications.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

variable {P K : Type} [Inhabited K]

/-- **The machine of a semantics meets the machine contract**: if the value semantics `sem`
meets the standard model at unit roundoff $u \ge 0$ with every value in range
(`NLAlib.Computation.IsRelErrSem`), its literal $1$ is exact, and the routines `mm`, `qr` and the
samplers `unif`, `normal` meet `NLAlib.IsMatMulErr`, `NLAlib.IsQRErr`, `NLAlib.IsUnifSampler` and
`NLAlib.IsNormalSampler` at $u$, floor $0$ and range $\Omega$ through the decoding at tag `p`,
then the machine of `sem` at `p` with these black boxes and the floor conversion meets
`NLAlib.FloatMachine.IsAccurate` at $u$, floor $0$, range $\Omega$. No printed source.
Proof: field by field. `dec_zero`: `lit_err` at $q = 0$ and `lit_ok` (`trivial`), so the literal
decodes to $0 \cdot (1 + \delta)$; `dec_one`: `hlit 1 le_rfl`; `ofNat`, `add`, `sub`, `mul`,
`div`: `lit_ok`/`bin_ok` give `some z`, so the machine's `Option.getD` is `z`, and `lit_err`/
`bin_err` give $\bar z = a(1 + \delta)$, hence $\lvert a - \bar z\rvert = \lvert a\delta\rvert \le
u\lvert a\rvert \le u\max(\lvert a\rvert, 0)$ (`NLAlib.IsRoundingOf`, `abs_mul`, `le_max_left`);
`dec_neg`: `neg`; `le_iff`: `cmp_le` and `decide_eq_true_iff`; `toNat_eq`: `rfl`; the black boxes:
the hypotheses. M, about 40 lines. -/
theorem isAccurate_toFloatMachine {sem : ScalarSem P K} {dec : P → K → ℝ} {u : ℝ} (Ω : ℝ)
    (hsem : IsRelErrSem (fun _ => u) dec (fun _ _ => True) sem) (hlit : IsExactIntLit dec sem 1)
    (hu : 0 ≤ u) (p : P) {μM μQ : ℕ → ℝ} {cN : ℝ} {mm : MatMulMap (K × K)}
    {qr : QRMap (K × K)} {unif : K → ℝ → K} {normal : ℂ → K × K}
    (hmm : IsMatMulErr (decodeComplex (dec p)) u 0 Ω μM mm)
    (hqr : IsQRErr (decodeComplex (dec p)) u 0 Ω μQ qr)
    (hunif : IsUnifSampler (dec p) u 0 unif)
    (hnormal : IsNormalSampler (decodeComplex (dec p)) u cN 0 Ω normal) :
    (sem.toFloatMachine p (fun x => ⌊dec p x⌋₊) mm qr unif normal).IsAccurate (dec p) u 0 Ω μM μQ
      cN := by
  sorry

/-- **The standard model decides flags**: a value semantics meeting the standard model with
every value in range and an exact literal $1$ decides flags at every tag
(`NLAlib.Computation.ScalarSem.DecidesFlags`): its literals $0$ and $1$ decode to $0$ and $1$ and
its equality test is exact. No printed source.
Proof: `lit_ok` at $0$ (`trivial`) and `lit_err` give a literal decoding to $0$; `hlit 1 le_rfl`
one decoding to $1$; `cmp_eq` at both pairs, `decide_eq_false` (`zero_ne_one`) and
`decide_eq_true rfl`. S, about 8 lines. -/
theorem IsRelErrSem.decidesFlags {sem : ScalarSem P K} {dec : P → K → ℝ} {u : P → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) sem) (hlit : IsExactIntLit dec sem 1) (p : P) :
    sem.DecidesFlags p := by
  sorry

/-- **The normal sampler of a tape rounding meets the normal-sampler contract**: if `sem` meets
the standard model at $u \ge 0$ with every value in range and exact literals up to $2$, and the
rounding $\rho$ of an ideal real Gaussian draw $x$ with $\lvert x\rvert \le 2\Omega$ errs by at most
$c\,u\lvert x\rvert$ with $c \ge 0$ and $(c + 3)u \le 1/10$, then the sampler
`NLAlib.Computation.ScalarSem.gaussianNormal` of $\rho$ meets `NLAlib.IsNormalSampler` at $u$ with
constant $2(c + 3)$, floor $0$ and range $\Omega$. No printed source.
Proof: the stored $s = \mathrm{fl}(\sqrt{\mathrm{fl}(1/2)})$ decodes to
$2^{-1/2}\sqrt{1 + \delta_1}(1 + \delta_2)$ (`lit_err`, `hlit`, `bin_err`, `sqrt_err`, each with
its success clause; `Real.sqrt_mul`, `Real.sqrt_inv`); each part $x = \sqrt2\operatorname{Re} z$
(resp. $\operatorname{Im}$), $\lvert x\rvert \le \sqrt2\lvert z\rvert \le 2\Omega$
(`Complex.abs_re_le_norm`), is stored as $x(1 + \theta)$, $\lvert\theta\rvert \le cu$, and the
rounded product decodes to $(x/\sqrt2)(1 + \theta)\sqrt{1 + \delta_1}(1 + \delta_2)(1 + \delta_3)$;
the relative error of each part is at most $1.06(c + 3)u$ for $(c + 3)u \le 1/10$
($\lvert\sqrt{1 + \delta} - 1\rvert \le \lvert\delta\rvert$; $\prod(1 + a_i) - 1 \le
e^{\sum\lvert a_i\rvert} - 1$, `Real.add_one_le_exp`), so the modulus error is at most
$2(c + 3)u\lvert z\rvert$ (`Complex.norm_eq_sqrt_sq_add_sq` or `Complex.sq_norm`,
`Complex.normSq_apply`). M, about 60 lines. -/
theorem isNormalSampler_gaussianNormal {sem : ScalarSem P K} {dec : P → K → ℝ} {u c Ω : ℝ}
    (hsem : IsRelErrSem (fun _ => u) dec (fun _ _ => True) sem) (hlit : IsExactIntLit dec sem 2)
    (p : P) {ρ : ℝ → K} (hρ : ∀ x : ℝ, |x| ≤ 2 * Ω → |dec p (ρ x) - x| ≤ c * u * |x|)
    (hc : 0 ≤ c) (hu : 0 ≤ u) (hcu : (c + 3) * u ≤ 1 / 10) :
    IsNormalSampler (decodeComplex (dec p)) u (2 * (c + 3)) 0 Ω (sem.gaussianNormal p ρ) := by
  sorry

/-! ### Exact specifications: the machine of exact real arithmetic -/

variable {Su Sg : Type} {toNat : ℝ → ℕ} {mm : MatMulMap (ℝ × ℝ)} {qr : QRMap (ℝ × ℝ)}
  {unif : ℝ → Su → ℝ} {normal : Sg → ℝ × ℝ}

/-- **The exact shift**: on exact real arithmetic (`NLAlib.Computation.exactSem`, decoding the
identity), the stored Hermitian shift of a stored matrix with Hermitian decoding $\mathbf{A}$ by
$c$ decodes to $\mathbf{A} - c\mathbf{I}$. No printed source.
Proof: `ext i j`; unfold `NLAlib.FloatMachine.hermShift`, `NLAlib.FloatMachine.hermFrom`,
`NLAlib.Computation.ScalarSem.toFloatMachine`, `NLAlib.Computation.exactSem`,
`NLAlib.decodeMatrix`, `NLAlib.decodeComplex`; `split_ifs`; the upper triangle is copied, the
lower triangle is the conjugate of the upper one, which is the entry by `hA`
(`Matrix.IsHermitian.apply`), and the diagonal imaginary part of a Hermitian matrix is $0$
(`Matrix.IsHermitian.coe_re_apply_self` or `Complex.conj_eq_iff_im`); `Complex.ext`. S, about
15 lines. -/
theorem decodeMatrix_hermShift_toFloatMachine_exactSem (p : P) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (ℝ × ℝ)} (hA : (decodeMatrix id A).IsHermitian) (c : ℝ) :
    decodeMatrix id (((exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif
      normal).hermShift A c) = decodeMatrix id A - c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  sorry

/-- **The exact scaling**: on exact real arithmetic, the stored Hermitian scaling of a stored
matrix with Hermitian decoding $\mathbf{A}$ by $c$ decodes to $c^{-1}\mathbf{A}$ (at $c = 0$ both
sides are $\mathbf{0}$: the failed division reads as $0$). No printed source.
Proof: as `NLAlib.Computation.decodeMatrix_hermShift_toFloatMachine_exactSem`, with
`div_eq_inv_mul` and `by_cases hc : c = 0` (`exactSem` fails on a zero divisor, so
`Option.getD` gives `default = 0`). S, about 15 lines. -/
theorem decodeMatrix_hermScale_toFloatMachine_exactSem (p : P) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (ℝ × ℝ)} (hA : (decodeMatrix id A).IsHermitian) (c : ℝ) :
    decodeMatrix id (((exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif
      normal).hermScale A c) = c⁻¹ • decodeMatrix id A := by
  sorry

/-- **The exact Hermitian part**: on exact real arithmetic, the scaled Hermitian part of a stored
matrix with decoding $\mathbf{A}$ by $c$ decodes to $c^{-1}(\mathbf{A} + \mathbf{A}^{\mathsf{H}})$,
for every $\mathbf{A}$. No printed source.
Proof: as `NLAlib.Computation.decodeMatrix_hermShift_toFloatMachine_exactSem`, with
`Matrix.conjTranspose_apply`, `Complex.conj_re`, `Complex.conj_im`; the diagonal is
$2\operatorname{Re} a_{ii}/c$ and imaginary part $0$. S, about 15 lines. -/
theorem decodeMatrix_hermAvg_toFloatMachine_exactSem (p : P) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (ℝ × ℝ)) (c : ℝ) :
    decodeMatrix id (((exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif
      normal).hermAvg A c) = c⁻¹ • (decodeMatrix id A + (decodeMatrix id A)ᴴ) := by
  sorry

/-- **The exact conjugate transpose**: on exact real arithmetic, the stored conjugate transpose
of a stored matrix with decoding $\mathbf{A}$ decodes to $\mathbf{A}^{\mathsf{H}}$. No printed
source.
Proof: `ext i j`; unfold `NLAlib.FloatMachine.conjTransposeMat`; `Complex.ext` with
`Complex.conj_re`, `Complex.conj_im`. S, 4 lines. -/
theorem decodeMatrix_conjTransposeMat_toFloatMachine_exactSem (p : P) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ℝ × ℝ)) :
    decodeMatrix id (((exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif
      normal).conjTransposeMat A) = (decodeMatrix id A)ᴴ := by
  sorry

/-- **The exact real trace**: on exact real arithmetic, the rounded trace of the real parts of a
stored matrix with decoding $\mathbf{A}$ is $\operatorname{Re}\operatorname{tr}\mathbf{A}$. No
printed source.
Proof: unfold `NLAlib.FloatMachine.traceRe`; `List.foldl` of `(· + ·)` from $0$ over
`List.finRange n` is the sum (`List.sum_finRange`-style induction or `Fin.sum_univ_eq_sum_range`);
`Matrix.trace`, `Complex.re_sum`. S, about 8 lines. -/
theorem traceRe_toFloatMachine_exactSem (p : P) {n : ℕ} (A : Matrix (Fin n) (Fin n) (ℝ × ℝ)) :
    ((exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif normal).traceRe A =
      (Matrix.trace (decodeMatrix id A)).re := by
  sorry

/-- **The exact max-modulus test**: on exact real arithmetic, the test that every part of every
entry of a stored $m \times n$ matrix lies in $[\mathit{lo}, \mathit{hi}]$, by the machine's
comparisons, is true exactly when it does. No printed source.
Proof: `List.all_eq_true`, `List.mem_finRange`, `Bool.and_eq_true`; the comparison of
`NLAlib.Computation.exactSem` on reals is `decide` (`RCLike.im` of a real is $0$). S, 6 lines. -/
theorem boxTest_toFloatMachine_exactSem_iff (p : P) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ℝ × ℝ)) (lo hi : ℝ) :
    let M := (exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif normal
    ((List.finRange m).all fun i => (List.finRange n).all fun j =>
      M.le lo (A i j).1 && M.le (A i j).1 hi && M.le lo (A i j).2 && M.le (A i j).2 hi) = true ↔
      ∀ i j, lo ≤ (A i j).1 ∧ (A i j).1 ≤ hi ∧ lo ≤ (A i j).2 ∧ (A i j).2 ≤ hi := by
  sorry

/-- **The exact entrywise sum**: on exact real arithmetic, adding the real and imaginary parts
of two stored matrices with the machine's addition decodes to the sum of the decodings. No
printed source.
Proof: `ext i j`; `Complex.ext`; `simp` with `NLAlib.Computation.exactSem`. S, 3 lines. -/
theorem decodeMatrix_addParts_toFloatMachine_exactSem (p : P) {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) (ℝ × ℝ)) :
    let M := (exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif normal
    decodeMatrix id (Matrix.of fun i j => (M.add (A i j).1 (B i j).1, M.add (A i j).2 (B i j).2)) =
      decodeMatrix id A + decodeMatrix id B := by
  sorry

/-- **The exact entrywise difference**: on exact real arithmetic, subtracting the real and
imaginary parts of two stored matrices with the machine's subtraction decodes to the difference
of the decodings. No printed source.
Proof: as `NLAlib.Computation.decodeMatrix_addParts_toFloatMachine_exactSem`. S, 3 lines. -/
theorem decodeMatrix_subParts_toFloatMachine_exactSem (p : P) {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) (ℝ × ℝ)) :
    let M := (exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif normal
    decodeMatrix id (Matrix.of fun i j => (M.sub (A i j).1 (B i j).1, M.sub (A i j).2 (B i j).2)) =
      decodeMatrix id A - decodeMatrix id B := by
  sorry

/-- **The exact real scaling**: on exact real arithmetic, multiplying both parts of every entry of
a stored matrix with decoding $\mathbf{A}$ by a stored real $a$ decodes to $a\mathbf{A}$. No
printed source.
Proof: as `NLAlib.Computation.decodeMatrix_addParts_toFloatMachine_exactSem`, with
`Complex.real_smul`. S, 3 lines. -/
theorem decodeMatrix_mulParts_toFloatMachine_exactSem (p : P) {m n : ℕ} (a : ℝ)
    (A : Matrix (Fin m) (Fin n) (ℝ × ℝ)) :
    let M := (exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif normal
    decodeMatrix id (Matrix.of fun i j => (M.mul a (A i j).1, M.mul a (A i j).2)) =
      a • decodeMatrix id A := by
  sorry

end NLAlib.Computation
