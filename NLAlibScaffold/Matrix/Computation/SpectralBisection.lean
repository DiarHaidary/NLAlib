/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisection
public import NLAlibScaffold.Matrix.Computation.Deflation
public import NLAlibScaffold.Matrix.Computation.NewtonSchulzSign

/-!
# Deterministic analysis of randomized spectral bisection (scaffold)

Statements for `NLAlib/Matrix/Computation/SpectralBisection.lean` (stage HDIAG, wave W4, design
note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.8): the local guarantee of one
node of the machine algorithm, read through the decoding, given its good events and the
guarantees of its children ([Shah2024, Lemma 4.1]), the depth
of the recursion, the number of nodes and of splits, and the global deterministic guarantee: if
every internal node of the recursion tree has a good sample, the output is an approximate
diagonalization with residual $2\varepsilon R_0$ and singular values of $\mathbf{U}$ in
$[1 - \varepsilon/3, 1 + \varepsilon/3]$. The probability is in
`NLAlibScaffold/Eigensolvers/SpectralBisection.lean`.

## Main results

* `NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub`: rank recovery.
* `NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some`: the child
  invariant.
* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`:
  Lemma 4.1.
* `NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`: the depth.
* `NLAlib.FloatMachine.IsAccurate.encard_eighNodeAt_ne_none_le`,
  `NLAlib.encard_eighNodeAt_isSplit_le`: the counts.
* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample`: the
  global deterministic guarantee.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib


/-- **Rank recovery on Event I**: under the node hypotheses of
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`
(contracts, precision, step limit, floor and range), for an internal node ($k \ge 2$, $R >
\varepsilon R_0$) and a seed $v \in [-1, 1]$ whose ideal shift $c' = (R/\ell)v$ is at distance at
least $w$ from every eigenvalue (Event I), the node's step splits exactly when $0 < i_+(\mathbf{A}
- c'\mathbf{I}) < k$; moreover then $k_+ = i_+(\mathbf{A} - c'\mathbf{I})$. [Shah2024, proof of
Lemma 4.1], "the estimates $k_\pm$ are the exact ranks".
Proof: the rounded shift is within $1.3Ru$ of $\mathbf{A} - c'\mathbf{I}$
(`NLAlib.IsUnifSampler`, the machine-computed scale $\mathrm{fl}(R/\mathrm{fl}(\ell))$,
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_le`), so its eigenvalues have
modulus $\ge w/2$;
`NLAlib.FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le` (scale
$2R$, modulus $w/2$, accuracy $\beta$), `Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le` and
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermScale_le`,
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermAvg_le` put $\mathbf{P}_+$ within
$\beta$ of the true projector; its diagonal sum is within $k\beta$ of the trace
(`NLAlib.norm_apply_le_specNorm`), which is the inertia
(`Matrix.IsHermitian.re_trace_smul_one_add_cfc_sign`); the rounded sum
(`NLAlib.FloatMachine.IsAccurate.abs_sum_sub_traceRe_le`) is within $1/8$ more, so $\mathrm{fl}(t +
\mathrm{fl}(1/2))$ lies in $(r + 1/4, r + 3/4)$ for the inertia $r$ and its floor (`toNat_eq`,
`Nat.floor_eq_iff`) is $r$; unfold `NLAlib.eighStep`. M, about 90 lines. -/
theorem FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false) {smp : EighSample ℝ ℂ N}
    (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ smp).IsSplit ↔
      0 < inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) ∧
      inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) < y.k := by
  sorry

/-- **The children of a good node satisfy the node invariant**: under the node hypotheses of
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample` (without
the children's guarantee), every child $y'$ of the node (`NLAlib.eighChild`) has a Hermitian matrix
with $\|\mathbf{A}'\|_2 \le R'$, its own window. [Shah2024, proof of Lemma 4.1], (4.10)–(4.13).
Proof: leaves have no child. A shift child (all eigenvalues on one side of $c'$, by
`NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub` and the inertia) has
spectrum of $\mathbf{A} \mp (R/2)\mathbf{I}$ in $[-(1/2 + 1/\ell)R, (1/2 + 1/\ell)R]$ since $\lvert
c'\rvert \le R/\ell$; add the diagonal rounding
(`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_le`,
`NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_hermFrom`). A split child:
`NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_hermFrom`; for the norm,
`Matrix.IsHermitian.exists_hasOrthonormalCols_mul_conjTranspose_eq` gives the frame
$\mathbf{V}_\pm$ with spectrum of the compression in $[c', R]$ (resp. $[-R, c']$),
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le` with Event
II gives $\|\mathbf{V}_\pm\mathbf{W}_\pm - \mathbf{Q}_\pm\|_2 \le \eta$, and the two products, the
Hermitian part and the rounding
(`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermScale_le`,
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermAvg_le`) add at most $(2 +
2\eta)R\eta \le R/\ell$. M, about 120 lines. -/
theorem FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hμQ : 0 ≤ μQ y.k) (hcN : 0 ≤ cN) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hudefl : (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    {smp : EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w (√(ρ / 2) / y.k)
        (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y smp)
    {b : Bool} {y' : EighNode F} (hy' : eighChild M N signFuel R₀ β y smp b = some y') :
    (decodeMatrix dec y'.A).IsHermitian ∧ specNorm (decodeMatrix dec y'.A) ≤ dec y'.R := by
  sorry

/-- **Local guarantee of a node of spectral bisection** (Lemma 4.1): let the machine meet
`NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ with $u \ge 0$ and constants
$\mu_{\mathrm{MM}}(k), \mu_{\mathrm{QR}}(k), c_{\mathrm N} \ge 0$. Let the node $y$ have a stored
matrix with Hermitian decoding $\mathbf{A}$ of size $k$, $\|\mathbf{A}\|_2 \le R$, $\ell \ge 20$,
$0 < \varepsilon \le 1/8$ (decoded stored values), let $R_0 > 0$, $0 < \rho \le 1$,
$0 < w \le R$, the stored accuracy $\beta$ with $0 < \beta \le$ `NLAlib.bisectionSignTol` $k$
$\varepsilon$ $\rho$ $\ell$, and $N_y = N(w/(8R), \beta/(16k))$ (`NLAlib.newtonSchulzSteps`).
Suppose
$$640\,k^{3/2}(8 + \mu_{\mathrm{MM}}(k))(N_y + 1)\,u \le \frac{w}{4R}\,\beta \,, \qquad
(4\mu_{\mathrm{QR}}(k) + 4\sqrt k(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(k) + 1)\,u \le \beta
\,,$$
the sign step limit is at least $N_y$, $0 \le \tau$,
$4k^{3/2}\tau \le \min(\sqrt{\rho/2}, \varepsilon R_0)$ and
$16(R_0 + R + k + \ell + \sqrt{\log(4/\rho)}) \le \Omega$; that, when $k \ge 2$ and the
machine's leaf test $R \le \mathrm{fl}(\varepsilon R_0)$ fails, the
node's sample satisfies `NLAlib.IsEighGoodSample` with $w$, $x = \sqrt{\rho/2}/k$ and
$t = \sqrt2(2\sqrt k + \sqrt{2\log(4/\rho)})$; and that every child $y'$ of the node returns an
approximate diagonalization of its matrix with residual $\varepsilon'(R' + R_0)$ and singular
values within $\varepsilon'/3$ of $1$ (its own tolerance and window). Then the node returns an
approximate diagonalization (`NLAlib.IsApproxDiagonalization`) of $\mathbf{A}$ with residual
$\varepsilon(R + R_0)$ and singular values within $\varepsilon/3$ of $1$. [Shah2024, Lemma 4.1],
there with the probabilities of the events folded in, $R_0$-free bounds on the children's
$\|\mathbf{D}_\pm\|_2$ (the $R_0$ part is absorbed by the slack $\varepsilon R_0/\ell$), and
Events I–III as conditions.
Proof: unfold `NLAlib.eighAux` and `NLAlib.eighStep`. Leaves: $k \le 1$ is exact,
$R \le \varepsilon R_0$ has residual $\|\mathbf{A}\|_2 \le \varepsilon R_0$. Otherwise follow
[Shah2024, proof of Lemma 4.1]: the branch is the true one
(`NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub`, whose proof also gives
$\|\mathbf{P}_\pm - \mathbf{\Pi}_\pm\|_2 \le \beta$); the children satisfy the node invariant
(`NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some`); on a split,
`Matrix.IsHermitian.exists_hasOrthonormalCols_mul_conjTranspose_eq` gives
the frames $\mathbf{V}_\pm$ and
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le` with Event
II gives $\|\mathbf{Q}_\pm - \mathbf{V}_\pm\mathbf{W}_\pm\|_2 \le \eta$; replace $\mathbf{V}_\pm$ by
$\mathbf{V}_\pm\mathbf{W}_\pm$. The children's window and tolerance are the machine's
`NLAlib.eighNextParams`: $R' \le (1/2 + 2/\ell)R(1 + \delta)$ and
$(1 - 1/\ell)\varepsilon(1 - \delta) \le \varepsilon' \le (1 - 1/\ell)\varepsilon(1 + \delta)$ with
$\delta \le 4u + u\tau/\varepsilon$ (each `ofNat`, `div`, `add`/`sub`, `mul` one rounding,
`IsRoundingOf`); the accounting below uses these, the slack $\varepsilon R_0/\ell$ absorbing
$\delta$. Then the source's estimates (4.14)–(4.20): the singular
values of $[\mathbf{W}_+\ \mathbf{W}_-]$, and the residual split into five terms, with
$\|\mathbf{D}_\pm\|_2$ bounded from the children's residual $\varepsilon'(R' + R_0)$ (its $R_0$
part, dropped by the source, is absorbed by the slack $\varepsilon R_0/\ell$). Split into private
lemmas: deflation, assembly of $\mathbf{U}$, residual. H, about 250 lines. -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hμQ : 0 ≤ μQ y.k) (hcN : 0 ≤ cN) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hudefl : (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    {f : ℕ} {s : List Bool → EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w (√(ρ / 2) / y.k)
        (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y (s []))
    (hchild : ∀ (b : Bool) (y' : EighNode F), eighChild M N signFuel R₀ β y (s []) b = some y' →
      IsApproxDiagonalization (decodeMatrix dec y'.A)
        (decodeMatrix dec (eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).1)
        (fun i => dec ((eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).2 i))
        (dec y'.ε * (dec y'.R + dec R₀)) (dec y'.ε / 3)) :
    IsApproxDiagonalization (decodeMatrix dec y.A)
      (decodeMatrix dec (eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).1)
      (fun i => dec ((eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).2 i))
      (dec y.ε * (dec y.R + dec R₀)) (dec y.ε / 3) := by
  sorry

/-- **The recursion stops by depth $\ell$**: under `NLAlib.FloatMachine.IsAccurate` with
$0 \le u$, $100\ell^2u \le 1$, $0 \le \tau$, $100\tau \le \varepsilon\min(R_0, 1)$ (an absolute
floor bound: the rounded parameters $\mathrm{fl}(2/\ell)$, $\mathrm{fl}((1 - 1/\ell)\varepsilon_j)$
have floor errors $u\tau$) and $16(R_0 + \ell) \le \Omega$, for stored $\varepsilon$, $R_0$ with $0
< \varepsilon \le 2^{-15}$, $R_0 > 0$ and a depth counter $\ell \ge \lceil \log_2(1/\varepsilon)
\rceil + 5$ (`NLAlib.bisectionDepth`), the tree of `NLAlib.eighNodeAt` from the root
$(\mathbf{A}, R_0, \varepsilon, \ell)$ has no node at a path longer than $\ell$, for every
accuracy and samples. [Shah2024, proof of Theorem 4.2], "the
depth of the tree $d$ is no more than $\ell$".
Proof: a node at depth $j$ has window $R_j$ within a factor $(1 + u)^{4j}$ of
$R_0\prod_{i<j}(1/2 + 2/(\ell + i))$ and tolerance $\varepsilon_j$ within $(1 - u)^{4j}$ of
$\varepsilon(\ell - 1)/(\ell + j - 1)$ (the machine's rounded parameters, `NLAlib.eighNextParams`)
and depth parameter $\ell + j$ (induction on the path, unfolding `NLAlib.eighChild`); the products
telescope: $\prod_{i<\ell}(\ell + i + 4)/(\ell + i) = \frac{2\ell(2\ell+1)(2\ell+2)(2\ell+3)}
{\ell(\ell+1)(\ell+2)(\ell+3)} =: P_\ell$; with $2^{-\ell} \le \varepsilon/32$ (`Nat.le_ceil`,
`Real.rpow_logb`) it suffices that $P_\ell/32 \le (\ell - 1)/(2\ell - 1)$, i.e.
$(2\ell+1)(2\ell+3)(2\ell-1) \le 8(\ell-1)(\ell+2)(\ell+3)$, whose difference is
$20\ell^2 + 10\ell - 45 > 0$ for $\ell \ge 2$ (at $\ell = 20$: $0.4355 \le 0.487$), so
$R_\ell \le \varepsilon_\ell R_0$ with a relative margin of order $1/\ell$, which absorbs
$(1 + u)^{8\ell} \le 1 + 1/(10\ell)$ and the rounding of the test $\mathrm{fl}(\varepsilon_\ell
R_0)$ (floor: $\tau \le \varepsilon R_0/100$), and
the node at depth $\ell$ is a leaf of `NLAlib.eighStep`. M, about 60 lines. -/
theorem FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ}
    {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N)
    {a : List Bool} (ha : ℓ < a.length) :
    eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s = none := by
  sorry

/-- **The recursion tree has at most $(k + 1)(\ell + 1)$ nodes**: under the hypotheses of
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`, the set of paths at which
`NLAlib.eighNodeAt` has a node has at most $(k + 1)(\ell + 1)$ elements, $k$ the size of the root.
[Shah2024, proof of Theorem 4.2], $\lvert X \rvert \le nd$ there.
Proof: below the root every node has size at least $1$, and the sizes of the nodes at one depth
sum to at most $k$ (a split partitions its size, a shift keeps it, a leaf has no child: unfold
`NLAlib.eighChild`, `NLAlib.eighStep`); with the depth bound, at most $k + 1$ nodes at each of the
depths $0, \dots, \ell$ (`Set.encard_le_card`-type counting over `List Bool` of bounded length,
`Set.encard_iUnion_le`). L, about 70 lines. -/
theorem FloatMachine.IsAccurate.encard_eighNodeAt_ne_none_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ}
    {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N) :
    {a : List Bool | eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s ≠ none}.encard ≤
      (k + 1) * (ℓ + 1) := by
  sorry

/-- **At most $k$ nodes split**: for every machine, root of size $k$, accuracy and samples, the set
of paths at which `NLAlib.eighNodeAt` has a node whose step `NLAlib.eighStep` (with that path's
sample) is a split has at most $k$ elements. [Shah2024, proof of Theorem 4.2],
$\lvert X_D \rvert = n - 1$ there.
Proof: the tree may be infinite (chains of shifts), so do not induct on the size alone: prove
$S_m(x) \le \max(k - 1, 0)$ for the splits at paths of length at most $m$, by induction on $m$
uniformly in $x$ (a shift: $S_m(x) = S_{m-1}(x')$ with the same size; a split: children of sizes
$k_+, k - k_+ \ge 1$ and $\max(k_+ - 1, 0) + \max(k - k_+ - 1, 0) + 1 \le k - 1$; a leaf: $0$;
count with `Set.encard_union_le` over the paths starting with `true` and `false`), then pass to
the union over $m$ (`Set.encard_iUnion_le`-type monotone limit). L, about 80 lines. -/
theorem encard_eighNodeAt_isSplit_le {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    {N signFuel : ℕ} {R₀ β : F} (x : EighNode F) (s : List Bool → EighSample Su Sg N) :
    {a : List Bool | ∃ y, eighNodeAt M N signFuel R₀ β a x s = some y ∧
      (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit}.encard ≤ x.k := by
  sorry

/-- **Global deterministic guarantee of spectral bisection**: let the machine meet
`NLAlib.FloatMachine.IsAccurate` with $u \ge 0$ and
$\mu_{\mathrm{MM}}$, $\mu_{\mathrm{QR}}$ monotone and nonnegative and $c_{\mathrm N} \ge 0$; let
the stored $\mathbf{A}$ have Hermitian decoding with $\|\mathbf{A}\|_2 \le R_0$, for stored
$R_0 > 0$, $\varepsilon$ and $\beta$ (decoded values) with $0 < \varepsilon \le 2^{-15}$,
$0 < \theta \le 1$, a depth counter $\ell \ge$ `NLAlib.bisectionDepth` $\varepsilon$, and an
accuracy (a precomputed threshold)
$$0 < \beta \le \frac{\varepsilon\sqrt\theta}{2880\,\ell\, n^{3/2}\bigl(2\sqrt n +
\sqrt{2\log(16n/\theta)}\bigr)} \,, \qquad
N_* = N\Bigl(\frac{\theta}{32n(n+1)\ell(\ell+1)}, \frac{\beta}{16n}\Bigr) \,.$$
Suppose $640\,n^{3/2}(8 + \mu_{\mathrm{MM}}(n))(N_* + 1)\cdot16n(n+1)\ell(\ell+1)\,u \le
\theta\beta$, $(4\mu_{\mathrm{QR}}(n) + 4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1)u
\le \beta$, the sign step limit is at least $N_*$, $0 \le \tau$,
$100n^{3/2}\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon\min(R_0, 1))$ and
$16(R_0 + n + \ell + \sqrt{\log(16n/\theta)}) \le \Omega$. If every internal node $y$ (size at
least $2$, and the machine's test $R_y \le \mathrm{fl}(\varepsilon_y R_0)$ fails) of the tree of
`NLAlib.eighNodeAt` has a good sample (`NLAlib.IsEighGoodSample` with $w_y = \theta
R_y/(2k_y\ell_y(n+1)(\ell+1))$, $x_y = \sqrt{\theta/(8n)}/k_y$, $t_y = \sqrt2(2\sqrt{k_y} +
\sqrt{2\log(16n/\theta)})$), then the decoded output of $\mathsf{eigh}(\mathbf{A}, \varepsilon)$
(`NLAlib.eigh`) is an approximate diagonalization of $\mathbf{A}$ with residual $2\varepsilon R_0$
and singular values within $\varepsilon/3$ of $1$. [Shah2024, Theorem 4.2], deterministic part.
Proof: induct on the fuel with the node-level hypotheses as a predicate over paths (the
children's trees are `eighNodeAt a y' (fun a' => s (b :: a'))` definitionally, so no snoc lemma
is needed); the depth is at most $\ell$
(`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`), so the budget $\ell + 1$ of
`NLAlib.eigh` is never exhausted. Treat leaves directly ($k \le 1$ exact; $R \le \varepsilon_y R_0$
residual $\le \varepsilon_y R_0$; the local lemma's $0 < w$ fails at a leaf with $R_y = 0$). At an
internal node apply
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`, its
matrix hypotheses coming from the parent through
`NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some` (at the root from
`hA`, `hR₀`), and its parameter hypotheses from the depth $j$: $k_y \le n$, $\ell \le \ell_y \le
2\ell$, $\varepsilon_y \ge \varepsilon/3$, $R_y \le R_0$, hence `NLAlib.bisectionSignTol` at $y$ is
at least $\beta$, $w_y/(4R_y) \ge \theta/(16n(n+1)\ell(\ell+1))$ and $N_y \le N_*$
(`NLAlib.newtonSchulzSteps_le_of_le_abs`, `NLAlib.newtonSchulzSteps_le_of_le`, monotone $\mu$), all
up to the factors $(1 \pm u)^{4j}$ of the machine-computed parameters: `husign` forces
$u \le 10^{-11}\varepsilon$ and `hτ` bounds the floor absolutely, so the floor error $u\tau$ in each
$\varepsilon_j$ is negligible; the node floor condition ($4k^{3/2}\tau \le \min(\sqrt{\rho/2},
\varepsilon_yR_0)$) and the depth lemmas' ($100\tau \le \varepsilon\min(R_0, 1)$) follow from `hτ`
since $\varepsilon_y \ge \varepsilon/3$. At the root $R = R_0$ gives
residual $2\varepsilon R_0$. H, about 200 lines. -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hμM : Monotone μM) (hμQ : Monotone μQ)
    (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian) {R₀ ε β : F}
    {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) +
      √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (dec R₀ + n + ℓ + √(Real.log (16 * n / θ))) ≤ Ω) {s : List Bool → EighSample ℝ ℂ n}
    (hgood : ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → 2 ≤ y.k →
        M.le y.R (M.mul y.ε R₀) = false →
        IsEighGoodSample dec (θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)))
          (√(θ / (8 * n)) / y.k) (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (16 * n / θ)))) y
          (s a)) :
    IsApproxDiagonalization (decodeMatrix dec A) (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β s).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β s).2 i)) (2 * dec ε * dec R₀) (dec ε / 3) := by
  sorry

end NLAlib
