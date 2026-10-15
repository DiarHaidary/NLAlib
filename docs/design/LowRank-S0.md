# Design note: LowRank stage S0, shared definitions and exact identities

Status: drafted 2026-10-15 under `docs/PORT_LOWRANK.md` (maintainer decisions of 2026-10-15; D1,
D2, D4, D5, D9, D11 to D14; §4.1 items 1 to 5; the S0 entry of §7); reviewed 2026-10-15,
amendments in §8, which overrides §0 to §7 where they disagree (§3 stays as drafted). This note
decides D14: **the sketch orientation**, `obliqueProjector X S := X * pinv (S * X) * S` (§7 Q1,
hard to reverse). Departures from the brief, each argued below: a fourth file
`Matrix/Factorizations/SketchedLowRank.lean` for `rsvd` and `generalizedNystrom` (statement budget,
§4, Q4); `sketchAndSolve` takes the sketch, like the core (Q3); four equivariance lemmas, TW
Lemma 5.2 and a PSD rank lemma are added (consumers in §0); the size is about 1300 lines, not 900
(§4). **Missing infrastructure:** nothing below the Matrix layer. In the Matrix layer: the
singular values of a Gram matrix (two lemmas), the gauge equality of item 5, and the public form of
a private lemma of `PrincipalAngles.lean` (§3.6). Everything else S0 uses is built and named in
the proof routes.

## 0. Scope and consumers

Deterministic, over `𝕜`, every shape and rank. $\mathbf{A}$ : `Matrix m n 𝕜`; the test matrix
$\mathbf{\Omega}$ : `Matrix n l 𝕜` multiplies on the right; the co-range test matrix
$\mathbf{\Psi}$ : `Matrix m p 𝕜` is applied as $\mathbf{\Psi}^{\mathsf{H}}$ (D2); a sketch
$\mathbf{S}$ : `Matrix k m 𝕜` is applied as it is (the Sketching round's orientation).

| Item | Consumers |
|---|---|
| `obliqueProjector`, its API, the rank interface | S2b and S6 (early-truncated GN is `obliqueProjector (truncatedSVD (A * Ω) k) Ψᴴ * A`); S6 shape (a) of the GN identity, stated for a fixed `X` of any rank; S7 (GN under an OSI, `IsSubspaceInjection Ψᴴ (A * Ω) a`); Solvers |
| the exact split (linear, Gram, Frobenius, gauge) | S6 (shape (a): one integral of the second term), S7 (the second term bounded by the injection, §3.7), S2b/S6 (early-truncated GN), users wanting gauge bounds for sketched projections |
| `sketchAndSolve`, `mul_sketchAndSolve`, EW (5.1) | S6 (EW Theorem 2.1 and unbiasedness: the mean of `sketchAndSolve A Ψᴴ ((1 - P_A) * B)` vanishes by symmetry); Solvers (sketch-and-solve, as a named output) |
| core noise `HasOrthonormalCols.sketchAndSolve_eq_add` | S2a (the perturbed-truncation lemma at $\mathbf{C} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}$, $\mathbf{E} = \mathbf{N}$); S6 (spectral core noise of truncated GN) |
| `rsvd`, `generalizedNystrom`, `nystrom` and their bridges | every later stage; users |
| GN core-form bridge `HasOrthonormalCols.generalizedNystrom_eq` | S2a (factored form, D5), S6 (truncated GN is $\mathbf{Q}\llbracket\hat{\mathbf{X}}\rrbracket_k$), S7 |
| GN Frobenius split | S6 (EW Theorem 4.2(a), TYUC Theorem 4.3), S7 (CEMT Corollary 2.8) |
| exactness at low rank (`…_eq_self_of_rank_eq`) | S3, S5, S6 (the a.s. exact branch at $\operatorname{rank}\mathbf{A} \le \ell$; assessment A1, A10) |
| equivariance (`…_mul_mul_conjTranspose`) | S4 (EW's symmetrisation: $\mathbf{\Lambda}/(\mathbf{P}\mathbf{\Omega}) = \mathbf{P}((\mathbf{P}^{\mathsf{T}}\mathbf{\Lambda}\mathbf{P})/\mathbf{\Omega})\mathbf{P}^{\mathsf{T}}$); S3 and S6 (reduction of $\mathbf{A} = \mathbf{U}\mathbf{\Sigma}\mathbf{V}^{\mathsf{H}}$ to $\mathbf{\Sigma}$ under an invariant law) |
| Gram correspondence (general factor, nuclear form, singular values, PSD square-root forms) | S1 (Nyström structural bound in every gauge), S2a item 7.5 (truncation under the correspondence), S4 (EW 3.2 from 3.6(a)), S5 (everything) |
| PSD facts, `rank_conjTranspose_mul_mul` | S2a item 7.1 (Nyström instance, $\mathbf{0} \preceq \hat{\mathbf{H}} \preceq \mathbf{H}$), S5; the oblique API for Nyström |
| Schur-complement order facts (variational form, monotone, superadditive, monotone in the range) | S4 (Fact 6.1(c) for the finite block-permutation average; Fact 6.1(d)); MT Example 11.3 for users |
| "Nyström helps" (TW Lemma 5.2) | S5 docstrings (comparison with the RSVD on the same sample); Solvers (Nyström preconditioning) |
| gauge equality $\lVert\mathbf{X}\mathbf{X}^{\mathsf{H}}\rVert_\Phi = \lVert\mathbf{X}^{\mathsf{H}}\mathbf{X}\rVert_\Phi$ | S1 (Gram form of the structural bound) |
| `IsSubspaceInjection.rank_mul_eq`, `.frobNorm_obliqueProjector_mul_sq_le` | S7 (every OSI statement); the reproof of `frobNorm_sub_mul_pinv_mul_sq_le` |

Not in S0: the structural bound (S1); truncation (S2a, S2b); anything probabilistic; the
signed-permutation conjugation average (S4, brief §4.3 (iv)); EW Lemma 5.8 (S10, review A5); a
streaming or cost model (brief §0.1).

## 1. Objects

Five definitions, all `def` (not `abbrev`: users search for them and an `abbrev` unfolds in goals;
D1). New and amended §5.3 rows, added by the PR that adds the definition (two reviews, CONTRIBUTING
§9):

| Concept | Spelling | Bridge |
|---|---|---|
| oblique projector (amended row) | predicate: Mathlib's `IsIdempotentElem P`, unchanged. From a basis and a sketch: `obliqueProjector X S := X * pinv (S * X) * S`, every shape and rank, written $\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$ in docstrings. The two-bases formula `X * (Yᴴ * X)⁻¹ * Yᴴ` is `obliqueProjector X Yᴴ`; it is a lemma, not a spelling (as `pinv` did for `⁻¹`) | `isIdempotentElem_obliqueProjector`; `obliqueProjector_of_isUnit`; `IsIdempotentElem.obliqueProjector_eq` (every idempotent is one) |
| a sketch that loses no rank of `X` (new row) | `(S * X).rank = X.rank`, as a hypothesis; no predicate (§2, Q2) | `rank_mul_eq_iff_injOn`; `IsSubspaceInjection.rank_mul_eq` |
| sketch-and-solve solution (new row) | `sketchAndSolve A S B := pinv (S * A) * (S * B)`, matrix right-hand side; the minimum-norm minimizer of $\lVert\mathbf{S}(\mathbf{A}\mathbf{X} - \mathbf{B})\rVert_{\mathsf{F}}$ | `mul_sketchAndSolve : A * sketchAndSolve A S B = obliqueProjector A S * B`; columnwise `isLeastSquaresSolution_pinv_mulVec` |
| low-rank approximations from sketches (new row) | `rsvd A Ω := rangeProjector (A * Ω) * A`; `generalizedNystrom A Ω Ψ := obliqueProjector (A * Ω) Ψᴴ * A`; `nystrom A Ω := generalizedNystrom A Ω Ω` (square `A`, theorems take `A.PosSemidef`). Docstrings: $\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}$, $\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle$, $\mathbf{A}\langle\mathbf{\Omega}\rangle$. Truncations have no names: `truncatedSVD (rsvd A Ω) k` (late), `rangeProjector (truncatedSVD (A * Ω) k) * A` and `obliqueProjector (truncatedSVD (A * Ω) k) Ψᴴ * A` (early) | `rsvd_eq_obliqueProjector`, `generalizedNystrom_def`, `nystrom_def` (source formulas); `nystrom_conjTranspose_mul_self` (Gram correspondence); `nystrom_selectionMatrix` |
| Nyström residual, Schur complement with respect to $\mathbf{\Omega}$ | `H - nystrom H Ω`, no definition (as the §5.3 row "generalized Schur complement"); docstrings $\mathbf{H}/\mathbf{\Omega}$, introduced in words | `conjTranspose_mul_self_sub_nystrom`; `nystrom_selectionMatrix` to `Factorizations/Nystrom.lean`'s selection residual |

`nystrom` is `generalizedNystrom A Ω Ω` for every square `A` (D1), so `nystrom_def` is
$\mathbf{A}\mathbf{\Omega}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})^{+}
\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}$; for Hermitian $\mathbf{A}$ this is MT (2.3),
$(\mathbf{A}\mathbf{\Omega})(\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})^{+}
(\mathbf{A}\mathbf{\Omega})^{\mathsf{H}}$, and EW Definition 3.4. Its docstring states the
convention and that no theorem is claimed off the PSD cone (degenerate case "Hermitian but not
PSD": `Matrix.PosSemidef.rank_conjTranspose_mul_mul` and `nystrom_le` fail there; §3.4).

**Mathlib search.** `LinearAlgebra/Projection.lean` has `Submodule.linearProjOfIsCompl` (projection
onto `p` along a complement `q`, a linear map into `p`) and `LinearMap.IsProj`; neither is a total
matrix-valued function of a basis and a sketch, and no S0 statement or consumer needs a bridge to
them (Q11). Searched, none, for: oblique projector with a pseudoinverse, Nyström, sketch-and-solve,
generalized Nyström, Schur complement monotonicity in the Loewner order, singular values of
$\mathbf{A}^{\mathsf{H}}\mathbf{A}$ (`Analysis/InnerProductSpace/SingularValues.lean` has none).
Used directly: `Matrix.rank_conjTranspose_mul_self`, `Matrix.rank_conjTranspose`,
`Matrix.rank_mul_le_left`, `Matrix.PosSemidef.conjTranspose_mul_mul_same`,
`Matrix.PosSemidef.dotProduct_mulVec_zero_iff`, `CFC.sqrt`, `CFC.sqrt_mul_sqrt_self`,
`CFC.sqrt_nonneg`, `Matrix.nonneg_iff_posSemidef`. **No deviation from Mathlib**: the predicate
stays `IsIdempotentElem`, and `obliqueProjector` is a construction Mathlib does not have. No entry
in `Mathlib-deviations.md`.

## 2. Interfaces

No new predicate or structure. One hypothesis recurs: the sketch is injective on the column space
of $\mathbf{X}$. It is spelled `(S * X).rank = X.rank` in every statement (13 statements of S0, and
S6's and S7's), the hypothesis of EW Lemma 5.1 ($\operatorname{rank}\mathbf{A} =
\operatorname{rank}(\mathbf{\Omega}^{*}\mathbf{A})$) literally. It is to `obliqueProjector` what
`Function.Injective A.mulVec` is to full column rank: a fixed raw spelling with a §5.3 row, not a
named predicate (Q2). Constructors:
- `rank_mul_eq_iff_injOn`: the meaning, $\mathbf{S}$ injective on
  $\operatorname{range}\mathbf{X}$, in the form `IsSubspaceInjection.injOn` concludes;
- `IsSubspaceInjection.rank_mul_eq` (Sketching, §3.7), from `IsSubspaceInjection S X a`, `0 < a`;
- `Matrix.PosSemidef.rank_conjTranspose_mul_mul` (§3.4): Nyström always satisfies it;
- for an orthonormal `Q`, `mulVec_injective_iff_rank_eq` turns it into full column rank of `S * Q`;
- S6: `ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix` applied to `Xᴴ`, with `Matrix.rank_conjTranspose`,
  gives it almost surely when `X.rank ≤ card p` (the Haar twin `ae_rank_mul_eq_min_of_hasLaw_haarFrame`).

Under D14 the predicate and the projector share their matrix: a user holding
`h : IsSubspaceInjection Ψᴴ (A * Ω) a` writes `h.rank_mul_eq ha` for the hypothesis of every
statement about `obliqueProjector (A * Ω) Ψᴴ`.

## 3. Statement shapes

`namespace NLAlib`, `open scoped Matrix MatrixOrder` (and `ComplexOrder` where Mathlib's PSD API
needs it). Variables `{𝕜 : Type*} [RCLike 𝕜] {k l m n p q r : Type*}`, `[Fintype _]` on each;
`[DecidableEq _]` only where `1`, `⁻¹`, `HasOrthonormalCols`, `selectionMatrix` or `CFC.sqrt`
appears (`CFC.sqrt` on `Matrix n n 𝕜` as in `Functions/AbsoluteValue.lean`). Docstrings below are
shortened; the full ones carry the citation of §5 and, for definitions, the junk value.

**Degenerate cases** (checked for every statement; the per-file notes say where a case bites).
- *Junk value of the core.* `obliqueProjector X S` is total. It is always idempotent with range
  $\mathbf{X}\operatorname{range}((\mathbf{S}\mathbf{X})^{\mathsf{H}}) \subseteq
  \operatorname{range}\mathbf{X}$, all of $\operatorname{range}\mathbf{X}$ exactly under the rank
  hypothesis; it is $\mathbf{0}$ when $\mathbf{S}\mathbf{X} = \mathbf{0}$. The unconditional
  statements are idempotence, $(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{\Pi} = \mathbf{0}$, the
  rank, the specialisations at $\mathbf{S} = \mathbf{I}$ and $\mathbf{X}^{\mathsf{H}}$, scaling,
  annihilation of $\ker\mathbf{S}$, equivariance, and `mul_sketchAndSolve`. Everything that fixes
  $\operatorname{range}\mathbf{X}$ carries the rank hypothesis, which is necessary: with $\mathbf{X}
  = \mathbf{I}_2$, $\mathbf{S} = \mathbf{e}_1^{\mathsf{H}}$ and $\mathbf{M} = \begin{bmatrix} 1 & 1
  \\ 0 & 1\end{bmatrix}$, $\mathbf{\Pi}_{\mathbf{X},\mathbf{S}} = \mathbf{e}_1\mathbf{e}_1^{\mathsf{H}}$
  but $\mathbf{\Pi}_{\mathbf{X}\mathbf{M},\mathbf{S}}$ has second row $(\tfrac12, 0)$ (review A13f);
  with $\mathbf{S} = \mathbf{0}$ the decomposition (5.1) would claim `pinv A * B = 0`.
- *Empty index types.* `r` empty: `X = 0`, $\mathbf{\Pi} = \mathbf{0} = \mathbf{P}_{\mathbf{X}}$ and
  the rank hypothesis holds. `k` empty: $\mathbf{\Pi} = \mathbf{0}$ and the hypothesis holds iff
  `X = 0`. `l` empty: `A * Ω = 0`, `rsvd`, `generalizedNystrom`, `nystrom` are `0`; the variational
  form's set is a singleton at `y = 0`. `m` or `n` empty: every matrix is zero.
- *$\mathbf{A} = \mathbf{0}$, $\mathbf{\Omega} = \mathbf{0}$, $\mathbf{\Psi} = \mathbf{0}$.* Outputs
  `0`; rank hypotheses on `A * Ω = 0` hold; `generalizedNystrom_eq_self_of_rank_eq` needs `A = 0`
  when `Ω = 0` (its hypothesis `(A * Ω).rank = A.rank` says so).
- *Rank-deficient $\mathbf{A}\mathbf{\Omega}$, $\ell > n$, repeated selection indices.* No statement
  assumes full column rank of `A * Ω` or injectivity of a selection; GN's rank hypothesis is on
  `Ψᴴ * (A * Ω)` relative to `A * Ω` (brief §1, review A13f), so S6's shape (a) takes
  `q = X.rank` for any `X`.
- *$\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{X}) < \operatorname{rank}\mathbf{X}$.*
  Excluded by hypothesis wherever it matters (above); the unconditional statements still hold.
- *Hermitian but not PSD inputs to Nyström.* Every Nyström theorem except the general-factor and
  selection ones takes `A.PosSemidef`. Counterexample for the rank lemma:
  $\mathbf{A} = \operatorname{diag}(1, -1)$, $\mathbf{\Omega} = (1, 1)^{\mathsf{T}}$ gives
  $\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega} = 0 \ne \mathbf{A}\mathbf{\Omega}$.
- *Padded indices.* The singular-value statements hold at every `k : ℕ`, including the zero
  padding, so no index carries a range (§5.2).
- Ties, truncation ranks and the probabilistic cases of the brief's checklist do not arise in S0.

### 3.1 `Matrix/Subspaces/ObliqueProjector.lean` (24)

Variables `{X : Matrix m r 𝕜} {S : Matrix k m 𝕜}`.

```lean
/-- The **oblique projector** $\mathbf{\Pi}_{\mathbf{X},\mathbf{S}} =
\mathbf{X}(\mathbf{S}\mathbf{X})^{+}\mathbf{S}$ defined by a basis $\mathbf{X}$ and a sketch
$\mathbf{S}$: the fitted values of the least-squares problem sketched by $\mathbf{S}$. Total:
always idempotent, with range $\mathbf{X}\operatorname{range}((\mathbf{S}\mathbf{X})^{\mathsf{H}})$;
it projects onto $\operatorname{range}\mathbf{X}$ exactly when
$\operatorname{rank}(\mathbf{S}\mathbf{X}) = \operatorname{rank}\mathbf{X}$, and is $\mathbf{0}$
when $\mathbf{S}\mathbf{X} = \mathbf{0}$. ... -/
noncomputable def obliqueProjector (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) : Matrix m m 𝕜 :=
  X * pinv (S * X) * S

/-- The rank interface: $\mathbf{S}$ keeps the rank of $\mathbf{X}$ iff it is injective on
$\operatorname{range}\mathbf{X}$. -/
theorem rank_mul_eq_iff_injOn :
    (S * X).rank = X.rank ↔ Set.InjOn S.mulVec (LinearMap.range X.mulVecLin)
theorem isIdempotentElem_obliqueProjector (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) :
    IsIdempotentElem (obliqueProjector X S)
theorem one_sub_rangeProjector_mul_obliqueProjector [DecidableEq m] (X : Matrix m r 𝕜)
    (S : Matrix k m 𝕜) : (1 - rangeProjector X) * obliqueProjector X S = 0
theorem rank_obliqueProjector (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) :
    (obliqueProjector X S).rank = (S * X).rank
theorem obliqueProjector_mul_self_iff : obliqueProjector X S * X = X ↔ (S * X).rank = X.rank
/-- **Exactness at low rank**: under the rank hypothesis $\mathbf{\Pi}$ fixes every
$\mathbf{B}$ with $\operatorname{range}\mathbf{B} \subseteq \operatorname{range}\mathbf{X}$. -/
theorem obliqueProjector_mul_eq_self_of_range_le {B : Matrix m n 𝕜} (h : (S * X).rank = X.rank)
    (hB : LinearMap.range B.mulVecLin ≤ LinearMap.range X.mulVecLin) : obliqueProjector X S * B = B
theorem range_obliqueProjector (h : (S * X).rank = X.rank) :
    LinearMap.range (obliqueProjector X S).mulVecLin = LinearMap.range X.mulVecLin
/-- Under the rank hypothesis $\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$ depends on $\mathbf{X}$ only
through its range (false without it, review A13f). -/
theorem obliqueProjector_eq_of_range_eq {X' : Matrix m q 𝕜} (h : (S * X).rank = X.rank)
    (hX : LinearMap.range X.mulVecLin = LinearMap.range X'.mulVecLin) :
    obliqueProjector X S = obliqueProjector X' S
theorem obliqueProjector_mul_of_isUnit [DecidableEq r] {M : Matrix r r 𝕜}
    (h : (S * X).rank = X.rank) (hM : IsUnit M) : obliqueProjector (X * M) S = obliqueProjector X S
theorem obliqueProjector_one [DecidableEq m] (X : Matrix m r 𝕜) :
    obliqueProjector X (1 : Matrix m m 𝕜) = rangeProjector X
theorem obliqueProjector_conjTranspose_self (X : Matrix m r 𝕜) :
    obliqueProjector X Xᴴ = rangeProjector X
/-- Rescaling the sketch does not change the projector (the $(\sqrt{k})^{-1}$ of Gaussian sketches,
D2); a real scalar is the case `RCLike.real_smul_eq_coe_smul`. -/
theorem obliqueProjector_smul_right (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) {c : 𝕜} (hc : c ≠ 0) :
    obliqueProjector X (c • S) = obliqueProjector X S
/-- The invertible case: $\mathbf{X}(\mathbf{T}\mathbf{X})^{-1}\mathbf{T}$, the former §5.3
spelling with $\mathbf{T} = \mathbf{Y}^{\mathsf{H}}$. -/
theorem obliqueProjector_of_isUnit [DecidableEq r] {T : Matrix r m 𝕜} (h : IsUnit (T * X)) :
    obliqueProjector X T = X * (T * X)⁻¹ * T
theorem obliqueProjector_mul_eq_zero_of_mul_eq_zero {B : Matrix m n 𝕜} (X : Matrix m r 𝕜)
    (h : S * B = 0) : obliqueProjector X S * B = 0
/-- Equivariance under an isometry $\mathbf{U}$ ($\mathbf{U}^{\mathsf{H}}\mathbf{U} = \mathbf{I}$). -/
theorem HasOrthonormalCols.obliqueProjector_mul_mul_conjTranspose [DecidableEq m]
    {U : Matrix n m 𝕜} (hU : HasOrthonormalCols U) (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) :
    obliqueProjector (U * X) (S * Uᴴ) = U * obliqueProjector X S * Uᴴ

/-! ### The exact error split -/

/-- **The exact error split, linear form**:
$(\mathbf{I}-\mathbf{\Pi})\mathbf{B} = (\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B} -
\mathbf{\Pi}(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$. -/
theorem one_sub_obliqueProjector_mul [DecidableEq m] (h : (S * X).rank = X.rank)
    (B : Matrix m n 𝕜) :
    (1 - obliqueProjector X S) * B =
      (1 - rangeProjector X) * B - obliqueProjector X S * ((1 - rangeProjector X) * B)
/-- **The exact error split, Gram form**: the two terms have orthogonal ranges, so the Gram
matrix of the error is the sum of the two Gram matrices. -/
theorem conjTranspose_mul_self_one_sub_obliqueProjector_mul [DecidableEq m]
    (h : (S * X).rank = X.rank) (B : Matrix m n 𝕜) :
    ((1 - obliqueProjector X S) * B)ᴴ * ((1 - obliqueProjector X S) * B) =
      ((1 - rangeProjector X) * B)ᴴ * ((1 - rangeProjector X) * B) +
        (obliqueProjector X S * ((1 - rangeProjector X) * B))ᴴ *
          (obliqueProjector X S * ((1 - rangeProjector X) * B))
/-- **The exact error split** in squared Frobenius norm (the trace of the Gram form). -/
theorem frobNorm_one_sub_obliqueProjector_mul_sq [DecidableEq m] (h : (S * X).rank = X.rank)
    (B : Matrix m n 𝕜) :
    frobNorm ((1 - obliqueProjector X S) * B) ^ 2 =
      frobNorm ((1 - rangeProjector X) * B) ^ 2 +
        frobNorm (obliqueProjector X S * ((1 - rangeProjector X) * B)) ^ 2
/-- The split in every quadratic unitarily invariant norm (D4's Gram form). -/
theorem SymmetricGauge.matrixNorm_conjTranspose_mul_self_one_sub_obliqueProjector_mul_le
    [DecidableEq m] (Φ : SymmetricGauge) (h : (S * X).rank = X.rank) (B : Matrix m n 𝕜) :
    Φ.matrixNorm (((1 - obliqueProjector X S) * B)ᴴ * ((1 - obliqueProjector X S) * B)) ≤
      Φ.matrixNorm (((1 - rangeProjector X) * B)ᴴ * ((1 - rangeProjector X) * B)) +
        Φ.matrixNorm ((obliqueProjector X S * ((1 - rangeProjector X) * B))ᴴ *
          (obliqueProjector X S * ((1 - rangeProjector X) * B)))

/-! ### Sketch-and-solve -/

/-- The **sketch-and-solve solution** $\hat{\mathbf{X}} = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{B}$,
the minimum-norm minimizer of $\lVert\mathbf{S}(\mathbf{A}\mathbf{X} - \mathbf{B})\rVert_{\mathsf{F}}$;
total (it is $\mathbf{0}$ when $\mathbf{S}\mathbf{A} = \mathbf{0}$). -/
noncomputable def sketchAndSolve (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (B : Matrix m p 𝕜) :
    Matrix n p 𝕜 :=
  pinv (S * A) * (S * B)
theorem mul_sketchAndSolve (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (B : Matrix m p 𝕜) :
    A * sketchAndSolve A S B = obliqueProjector A S * B
/-- **Sketch-and-solve error decomposition**: $\hat{\mathbf{X}} = \mathbf{A}^{+}\mathbf{B} +
(\mathbf{S}\mathbf{A})^{+}\mathbf{S}(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}$ when
$\operatorname{rank}(\mathbf{S}\mathbf{A}) = \operatorname{rank}\mathbf{A}$; basis-free form of
EW (5.1). -/
theorem sketchAndSolve_eq_pinv_mul_add [DecidableEq m] {A : Matrix m n 𝕜}
    (h : (S * A).rank = A.rank) (B : Matrix m p 𝕜) :
    sketchAndSolve A S B = pinv A * B + sketchAndSolve A S ((1 - rangeProjector A) * B)
/-- **Core noise**: for orthonormal $\mathbf{Q}$ with $\mathbf{S}\mathbf{Q}$ of full column rank,
the sketched core is $\mathbf{Q}^{\mathsf{H}}\mathbf{B} + \mathbf{N}$ with
$\mathbf{N} = (\mathbf{S}\mathbf{Q})^{+}\mathbf{S}(\mathbf{I}-\mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{B}$. -/
theorem HasOrthonormalCols.sketchAndSolve_eq_add [DecidableEq m] [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) (h : (S * Q).rank = Q.rank)
    (B : Matrix m p 𝕜) :
    sketchAndSolve Q S B = Qᴴ * B + sketchAndSolve Q S ((1 - Q * Qᴴ) * B)
```

Proof routes. Idempotence: `pinv_mul_mul_pinv`. Annihilation: `rangeProjector_mul_self`. Rank:
`Matrix.rank_mul_le_left`, `rank_pinv`, and $\mathbf{S}\mathbf{\Pi}\mathbf{X} = \mathbf{S}\mathbf{X}$
(`mul_pinv_mul_self`). `rank_mul_eq_iff_injOn`: rank–nullity on `X.mulVecLin` composed with
`S.mulVecLin` (`LinearMap.finrank_range_add_finrank_ker`), as `IsSubspaceInjection.injOn` is proved.
`mul_self_iff`: `pinv_mul` gives $\mathbf{\Pi}\mathbf{X} = \mathbf{X}\mathbf{P}_{(\mathbf{S}\mathbf{X})^{\mathsf{H}}}$,
and under the hypothesis $\operatorname{range}(\mathbf{S}\mathbf{X})^{\mathsf{H}} =
\operatorname{range}\mathbf{X}^{\mathsf{H}}$ (inclusion plus equal `finrank`); the converse from
`rank_obliqueProjector`. Range invariance: write $\mathbf{X} = \mathbf{Q}\mathbf{R}$ with
$\mathbf{Q}$ an orthonormal basis of the range indexed by `Fin X.rank` (`Matrix/Basic/OrthonormalBasis.lean`),
$\mathbf{R} = \mathbf{Q}^{\mathsf{H}}\mathbf{X}$ of full row rank and $\mathbf{S}\mathbf{Q}$ of full
column rank, then `pinv_mul_rev` and `mul_pinv_self_of_injective_conjTranspose` give
$\mathbf{\Pi}_{\mathbf{X},\mathbf{S}} = \mathbf{Q}(\mathbf{S}\mathbf{Q})^{+}\mathbf{S}$ for both
$\mathbf{X}$ and $\mathbf{X}'$. Specialisations: `mul_pinv`,
`mul_pinv_conjTranspose_mul_self_mul_conjTranspose`, `pinv_smul`, `pinv_of_isUnit`. Equivariance:
`hU.conjTranspose_mul_cancel_left`. Split: $\mathbf{\Pi}\mathbf{P}_{\mathbf{X}} = \mathbf{P}_{\mathbf{X}}$
from `obliqueProjector_mul_eq_self_of_range_le`, then the cross terms vanish by
`one_sub_rangeProjector_mul_obliqueProjector`; Frobenius by `frobNorm_sq_eq_re_trace`; gauge by
`matrixNorm_add_le`. Sketch-and-solve: linearity in `B`, and $(\mathbf{S}\mathbf{A})^{+}\mathbf{S}
\mathbf{A}\mathbf{A}^{+} = \mathbf{P}_{(\mathbf{S}\mathbf{A})^{\mathsf{H}}}\mathbf{A}^{+} =
\mathbf{A}^{+}$ (`range_mulVecLin_pinv`, ranges equal under the hypothesis). Core noise: the
previous lemma with `hQ.pinv_eq`, `hQ.rangeProjector_eq`.

### 3.2 `Matrix/Subspaces/Oblique.lean` (amended: 3 new, 6 deprecated)

`Oblique.lean` keeps the theory of a general idempotent and now imports `ObliqueProjector.lean`
(nothing imports `Oblique.lean`, so there is no cycle). Its section "The oblique projector of two
bases" is restated on `obliqueProjector`, in every rank where the statement allows:

```lean
/-- **Every idempotent is an oblique projector**: $\mathbf{P} = \mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$
whenever $\operatorname{range}\mathbf{X} = \operatorname{range}\mathbf{P}$ and
$\operatorname{range}\mathbf{S}^{\mathsf{H}} = \operatorname{range}\mathbf{P}^{\mathsf{H}}$; no
independence of the columns of $\mathbf{X}$ is needed (e.g. $\mathbf{X} = \mathbf{S} = \mathbf{P}$). -/
theorem _root_.IsIdempotentElem.obliqueProjector_eq {P : Matrix n n 𝕜} (hP : IsIdempotentElem P)
    {X : Matrix n p 𝕜} {S : Matrix k n 𝕜}
    (hX : LinearMap.range X.mulVecLin = LinearMap.range P.mulVecLin)
    (hS : LinearMap.range Sᴴ.mulVecLin = LinearMap.range Pᴴ.mulVecLin) : obliqueProjector X S = P
/-- The norm of the oblique projector between two frames, any widths and any overlap. -/
theorem HasOrthonormalCols.specNorm_obliqueProjector [DecidableEq p] [DecidableEq q]
    {U : Matrix n p 𝕜} {V : Matrix n q 𝕜} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    specNorm (obliqueProjector U Vᴴ) = specNorm (pinv (Vᴴ * U))
theorem HasOrthonormalCols.specNorm_obliqueProjector_mul_cos [DecidableEq p] {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (h : IsUnit (Vᴴ * U)) {j : ℕ}
    (hj : j + 1 = Fintype.card p) :
    specNorm (obliqueProjector U Vᴴ) * Real.cos (principalAngle U V j) = 1
```

`@[deprecated]` (proofs unchanged, removed after a release; Q5): `isIdempotentElem_mul_inv_mul_conjTranspose`
(use `isIdempotentElem_obliqueProjector`, `obliqueProjector_of_isUnit`), `mul_inv_mul_conjTranspose_mul_self`
(`obliqueProjector_mul_self_iff`), `mul_inv_mul_conjTranspose_mulVec_eq_zero`
(`obliqueProjector_mul_eq_zero_of_mul_eq_zero`), `IsIdempotentElem.eq_mul_inv_mul_conjTranspose`,
`HasOrthonormalCols.specNorm_mul_inv_mul_conjTranspose` and its `_mul_cos` twin. Kept:
`IsIdempotentElem.isUnit_conjTranspose_mul_of_range_le` (an invertibility fact, not a projector
spelling). Proof of `obliqueProjector_eq`: both sides idempotent with range $\operatorname{range}\mathbf{P}$;
kernels agree because $\mathbf{S}(\operatorname{range}\mathbf{P}) = \operatorname{range}\mathbf{S}$
(equal dimensions), so $\mathbf{\Pi}\mathbf{v} = \mathbf{0}$ iff $\mathbf{S}\mathbf{v} = \mathbf{0}$
iff $\mathbf{P}\mathbf{v} = \mathbf{0}$. Degenerate `P = 0`: `X = 0`, both sides `0`.

### 3.3 `Matrix/Factorizations/SketchedLowRank.lean` (11)

Variables `{A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}`.

```lean
/-- The **randomized SVD approximation** (range-finder approximation)
$\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}$ for a test matrix $\mathbf{\Omega}$, here
deterministic; two passes over $\mathbf{A}$. Rank at most $\lvert l \rvert$. -/
noncomputable def rsvd (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) : Matrix m n 𝕜 :=
  rangeProjector (A * Ω) * A
theorem rsvd_eq_obliqueProjector [DecidableEq m] (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
    rsvd A Ω = obliqueProjector (A * Ω) 1 * A
/-- The **generalized Nyström approximation**
$\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle =
\mathbf{A}\mathbf{\Omega}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})^{+}\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}$:
one pass, both sketches $\mathbf{A}\mathbf{\Omega}$ and $\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}$ linear in $\mathbf{A}$. -/
noncomputable def generalizedNystrom (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (Ψ : Matrix m p 𝕜) :
    Matrix m n 𝕜 :=
  obliqueProjector (A * Ω) Ψᴴ * A
theorem generalizedNystrom_def (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (Ψ : Matrix m p 𝕜) :
    generalizedNystrom A Ω Ψ = A * Ω * pinv (Ψᴴ * A * Ω) * Ψᴴ * A
theorem generalizedNystrom_one [DecidableEq m] (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
    generalizedNystrom A Ω (1 : Matrix m m 𝕜) = rsvd A Ω
/-- **GN error = RSVD error + sketch-and-solve excess**, exactly, in squared Frobenius norm,
when $\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}) =
\operatorname{rank}(\mathbf{A}\mathbf{\Omega})$ (no full rank of $\mathbf{A}\mathbf{\Omega}$ assumed). -/
theorem frobNorm_sub_generalizedNystrom_sq [DecidableEq m]
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) :
    frobNorm (A - generalizedNystrom A Ω Ψ) ^ 2 =
      frobNorm (A - rsvd A Ω) ^ 2 + frobNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) ^ 2
theorem rsvd_eq_self_of_rank_eq (h : (A * Ω).rank = A.rank) : rsvd A Ω = A
theorem generalizedNystrom_eq_self_of_rank_eq (hΩ : (A * Ω).rank = A.rank)
    (hΨ : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) : generalizedNystrom A Ω Ψ = A
/-- **Core form of GN** (the single-view bridge): for any orthonormal basis $\mathbf{Q}$ of
$\operatorname{range}(\mathbf{A}\mathbf{\Omega})$, $\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle
= \mathbf{Q}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q})^{+}\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}$. -/
theorem HasOrthonormalCols.generalizedNystrom_eq [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q)
    (hQY : LinearMap.range Q.mulVecLin = LinearMap.range (A * Ω).mulVecLin)
    (hΨ : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) :
    generalizedNystrom A Ω Ψ = Q * sketchAndSolve Q Ψᴴ A
theorem HasOrthonormalCols.rsvd_mul_mul_conjTranspose [DecidableEq m] [DecidableEq n]
    {m' n' : Type*} [Fintype m'] [Fintype n'] {U : Matrix m' m 𝕜} {V : Matrix n' n 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
    rsvd (U * A * Vᴴ) (V * Ω) = U * rsvd A Ω * Vᴴ
theorem HasOrthonormalCols.generalizedNystrom_mul_mul_conjTranspose [DecidableEq m] [DecidableEq n]
    {m' n' : Type*} [Fintype m'] [Fintype n'] {U : Matrix m' m 𝕜} {V : Matrix n' n 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (Ψ : Matrix m p 𝕜) :
    generalizedNystrom (U * A * Vᴴ) (V * Ω) (U * Ψ) = U * generalizedNystrom A Ω Ψ * Vᴴ
```

Proof routes: `rsvd_eq_obliqueProjector` and `generalizedNystrom_one` by `obliqueProjector_one`;
the GN split is `frobNorm_one_sub_obliqueProjector_mul_sq` at `X := A * Ω`, `B := A`, with
`A - rsvd A Ω = (1 - rangeProjector (A * Ω)) * A`; exactness from $\operatorname{range}(\mathbf{A}\mathbf{\Omega}) \subseteq
\operatorname{range}\mathbf{A}$ (`range_mulVecLin_le_iff_exists_mul`), equal `finrank`, and
`obliqueProjector_mul_eq_self_of_range_le`; core form by
`obliqueProjector_eq_of_range_eq` and `mul_sketchAndSolve`; equivariance by
`HasOrthonormalCols.rangeProjector_mul` (§3.6) and the projector equivariance. Degenerate: the GN
split without `h` is false (the Gram cross term survives, review A13f); `rsvd_eq_self_of_rank_eq`
at `A = 0` is trivial; for `Ω = 0`, `hΩ` forces `A = 0`. The unsquared GN gauge forms are not
stated (D4: GN is Frobenius only); the projector-level gauge split covers a user who wants one.

### 3.4 `Matrix/Factorizations/Nystrom.lean` (extended: 16 new, 24 in the file)

Variables `{F : Matrix m n 𝕜} {A : Matrix n n 𝕜} {Ω : Matrix n l 𝕜}`.

```lean
/-- The **Nyström approximation** $\mathbf{A}\langle\mathbf{\Omega}\rangle =
\mathbf{A}\mathbf{\Omega}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})^{+}\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}$,
the generalized Nyström approximation with $\mathbf{\Psi} = \mathbf{\Omega}$; defined for every
square $\mathbf{A}$, a theorem's subject only for positive semidefinite $\mathbf{A}$. -/
noncomputable def nystrom (A : Matrix n n 𝕜) (Ω : Matrix n l 𝕜) : Matrix n n 𝕜 :=
  generalizedNystrom A Ω Ω
theorem nystrom_def (A : Matrix n n 𝕜) (Ω : Matrix n l 𝕜) :
    nystrom A Ω = A * Ω * pinv (Ωᴴ * A * Ω) * Ωᴴ * A
/-- **The Gram correspondence**: the Nyström approximation of
$\mathbf{F}^{\mathsf{H}}\mathbf{F}$ is the Gram matrix of the randomized SVD approximation of
$\mathbf{F}$, for every factor, test matrix and rank. -/
theorem nystrom_conjTranspose_mul_self (F : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
    nystrom (Fᴴ * F) Ω = (rsvd F Ω)ᴴ * rsvd F Ω
/-- **The Gram correspondence, error form**: $\mathbf{H} - \mathbf{H}\langle\mathbf{\Omega}\rangle
= \mathbf{E}^{\mathsf{H}}\mathbf{E}$ with $\mathbf{E} = (\mathbf{I} - \mathbf{P}_{\mathbf{F}\mathbf{\Omega}})\mathbf{F}$. -/
theorem conjTranspose_mul_self_sub_nystrom (F : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
    Fᴴ * F - nystrom (Fᴴ * F) Ω = (F - rsvd F Ω)ᴴ * (F - rsvd F Ω)
theorem singularValues_conjTranspose_mul_self_sub_nystrom (F : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (k : ℕ) : singularValues (Fᴴ * F - nystrom (Fᴴ * F) Ω) k = singularValues (F - rsvd F Ω) k ^ 2
/-- Nuclear-norm (trace) form: CEMT's Imported Theorem 2.4, EW Fact 3.5. -/
theorem nuclearNorm_conjTranspose_mul_self_sub_nystrom (F : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
    nuclearNorm (Fᴴ * F - nystrom (Fᴴ * F) Ω) = frobNorm (F - rsvd F Ω) ^ 2
/-- $\mathbf{A}\langle\mathbf{\Omega}\rangle = \mathbf{A}^{1/2}\mathbf{P}_{\mathbf{A}^{1/2}\mathbf{\Omega}}\mathbf{A}^{1/2}$ (MT §14.2). -/
theorem _root_.Matrix.PosSemidef.nystrom_eq [DecidableEq n] (hA : A.PosSemidef) (Ω : Matrix n l 𝕜) :
    nystrom A Ω = CFC.sqrt A * rangeProjector (CFC.sqrt A * Ω) * CFC.sqrt A
theorem _root_.Matrix.PosSemidef.sub_nystrom_eq [DecidableEq n] (hA : A.PosSemidef)
    (Ω : Matrix n l 𝕜) :
    A - nystrom A Ω = (CFC.sqrt A - rsvd (CFC.sqrt A) Ω)ᴴ * (CFC.sqrt A - rsvd (CFC.sqrt A) Ω)
/-- The singular values of the Nyström error are the squared singular values of the
range-finder error of $\mathbf{A}^{1/2}$, at every index. -/
theorem _root_.Matrix.PosSemidef.singularValues_sub_nystrom [DecidableEq n] (hA : A.PosSemidef)
    (Ω : Matrix n l 𝕜) (k : ℕ) :
    singularValues (A - nystrom A Ω) k = singularValues (CFC.sqrt A - rsvd (CFC.sqrt A) Ω) k ^ 2
theorem _root_.Matrix.PosSemidef.nystrom (hA : A.PosSemidef) (Ω : Matrix n l 𝕜) :
    (nystrom A Ω).PosSemidef
theorem _root_.Matrix.PosSemidef.nystrom_le (hA : A.PosSemidef) (Ω : Matrix n l 𝕜) :
    nystrom A Ω ≤ A
/-- Nyström always satisfies the rank hypothesis of the oblique projector. -/
theorem _root_.Matrix.PosSemidef.rank_conjTranspose_mul_mul (hA : A.PosSemidef) (Ω : Matrix n l 𝕜) :
    (Ωᴴ * (A * Ω)).rank = (A * Ω).rank
theorem _root_.Matrix.PosSemidef.nystrom_eq_self_of_rank_eq (hA : A.PosSemidef)
    (h : (A * Ω).rank = A.rank) : nystrom A Ω = A
/-- Representation invariance (EW Fact 6.1(b)); the invertible-`M` case is
`range (Ω * M) = range Ω`. -/
theorem _root_.Matrix.PosSemidef.nystrom_eq_of_range_eq (hA : A.PosSemidef) {Ω' : Matrix n q 𝕜}
    (h : LinearMap.range Ω.mulVecLin = LinearMap.range Ω'.mulVecLin) : nystrom A Ω = nystrom A Ω'
/-- The selection case: the Nyström approximation along `selectionMatrix e` is the matrix whose
residual `Matrix.PosSemidef.sub_submatrix_mul_pinv_mul` and its neighbours study. -/
theorem nystrom_selectionMatrix [DecidableEq n] (A : Matrix n n 𝕜) (e : p → n) :
    nystrom A (selectionMatrix e) = A.submatrix id e * pinv (A.submatrix e e) * A.submatrix e id
theorem HasOrthonormalCols.nystrom_mul_mul_conjTranspose [DecidableEq n] {n' : Type*} [Fintype n']
    {U : Matrix n' n 𝕜} (hU : HasOrthonormalCols U) (A : Matrix n n 𝕜) (Ω : Matrix n l 𝕜) :
    nystrom (U * A * Uᴴ) (U * Ω) = U * nystrom A Ω * Uᴴ
```

Proof routes. Gram correspondence: one line from `pinv_eq_pinv_conjTranspose_mul_self_mul`
(as `mul_pinv_conjTranspose_mul_self_mul_conjTranspose` at $\mathbf{Y} = \mathbf{F}\mathbf{\Omega}$),
since $(\mathbf{F}\mathbf{\Omega})^{\mathsf{H}}\mathbf{F}\mathbf{\Omega} =
\mathbf{\Omega}^{\mathsf{H}}\mathbf{F}^{\mathsf{H}}\mathbf{F}\mathbf{\Omega}$, then
`isStarProjection_rangeProjector` for $\mathbf{F}^{\mathsf{H}}\mathbf{P}\mathbf{F} =
(\mathbf{P}\mathbf{F})^{\mathsf{H}}\mathbf{P}\mathbf{F}$. Singular values: `singularValues_conjTranspose_mul_self`
(§3.6). Nuclear: `Matrix.PosSemidef.nuclearNorm_eq_re_trace`, `frobNorm_sq_eq_re_trace`. PSD forms:
rewrite $\mathbf{A} = (\mathbf{A}^{1/2})^{\mathsf{H}}\mathbf{A}^{1/2}$ (`CFC.sqrt_mul_sqrt_self`,
`CFC.sqrt_nonneg`, Hermitian square root) and apply the general-factor forms. Rank:
`rank_mul_eq_iff_injOn`, and $\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}\mathbf{y} = \mathbf{0}$
forces $\mathbf{A}\mathbf{\Omega}\mathbf{y} = \mathbf{0}$ by `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`.
Exactness: range equality plus the rank lemma and `obliqueProjector_mul_eq_self_of_range_le`.
Range invariance: the square-root form; $\operatorname{range}(\mathbf{A}^{1/2}\mathbf{\Omega})$
depends on $\operatorname{range}\mathbf{\Omega}$ only (`rangeProjector_inj`). Selection:
`mul_selectionMatrix`, `conjTranspose_selectionMatrix_mul`, `conjTranspose_selectionMatrix_mul_mul_selectionMatrix`.
Equivariance: the GN equivariance at `V := U`, `Ψ := Ω`. Degenerate: Hermitian non-PSD (§3 list);
`F` with `m` empty gives `F = 0` and both sides `0`; `l` empty gives `nystrom A Ω = 0`.

### 3.5 `Matrix/Factorizations/NystromOrder.lean` (6)

```lean
/-- **Variational form of the Schur complement** $\mathbf{H}/\mathbf{\Omega}$:
$\operatorname{Re}\langle\mathbf{x}, (\mathbf{H}/\mathbf{\Omega})\mathbf{x}\rangle =
\min_{\mathbf{y}} \operatorname{Re}\langle\mathbf{x}-\mathbf{\Omega}\mathbf{y},
\mathbf{H}(\mathbf{x}-\mathbf{\Omega}\mathbf{y})\rangle$. -/
theorem _root_.Matrix.PosSemidef.isLeast_re_quadForm_sub_mulVec {H : Matrix n n 𝕜}
    (hH : H.PosSemidef) (Ω : Matrix n l 𝕜) (x : n → 𝕜) :
    IsLeast (Set.range fun y : l → 𝕜 => RCLike.re (quadForm H (x - Ω *ᵥ y)))
      (RCLike.re (quadForm (H - nystrom H Ω) x))
/-- **Monotonicity** of $\mathbf{H}\mapsto\mathbf{H}/\mathbf{\Omega}$ (MT Corollary 11.2, EW Fact 6.1(d)). -/
theorem _root_.Matrix.PosSemidef.sub_nystrom_le_sub_nystrom {H H' : Matrix n n 𝕜}
    (hH : H.PosSemidef) (h : H ≤ H') (Ω : Matrix n l 𝕜) : H - nystrom H Ω ≤ H' - nystrom H' Ω
/-- **Concavity** of $\mathbf{H}\mapsto\mathbf{H}/\mathbf{\Omega}$, as superadditivity with
nonnegative weights (EW Fact 6.1(c) is the case of weights summing to one). -/
theorem sum_smul_sub_nystrom_le {ι : Type*} (s : Finset ι) {H : ι → Matrix n n 𝕜} {w : ι → ℝ}
    (hH : ∀ i ∈ s, (H i).PosSemidef) (hw : ∀ i ∈ s, 0 ≤ w i) (Ω : Matrix n l 𝕜) :
    ∑ i ∈ s, w i • (H i - nystrom (H i) Ω) ≤
      (∑ i ∈ s, w i • H i) - nystrom (∑ i ∈ s, w i • H i) Ω
/-- More samples, better approximation: monotone in $\operatorname{range}\mathbf{\Omega}$. -/
theorem _root_.Matrix.PosSemidef.nystrom_le_nystrom_of_range_le {H : Matrix n n 𝕜}
    (hH : H.PosSemidef) {Ω' : Matrix n q 𝕜}
    (h : LinearMap.range Ω.mulVecLin ≤ LinearMap.range Ω'.mulVecLin) : nystrom H Ω ≤ nystrom H Ω'
/-- **Nyström helps** (TW Lemma 5.2), singular-value form. -/
theorem _root_.Matrix.PosSemidef.singularValues_sub_nystrom_le [DecidableEq n] {H : Matrix n n 𝕜}
    (hH : H.PosSemidef) (Ω : Matrix n l 𝕜) (k : ℕ) :
    singularValues (H - nystrom H Ω) k ≤ singularValues ((1 - rangeProjector Ω) * H) k
/-- **Nyström helps** in every unitarily invariant norm. -/
theorem SymmetricGauge.matrixNorm_sub_nystrom_le [DecidableEq n] (Φ : SymmetricGauge)
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) (Ω : Matrix n l 𝕜) :
    Φ.matrixNorm (H - nystrom H Ω) ≤ Φ.matrixNorm ((1 - rangeProjector Ω) * H)
```

Proof routes. Variational form: the duplicate search of review A13e lands on
`isLeast_re_quadForm_fromBlocks` (`Pseudoinverse/GeneralizedSchur.lean`), which is reused, not
reproved: apply it to `fromBlocks (Ωᴴ * H * Ω) (Ωᴴ * H) (H * Ω) H = Mᴴ * H * M` with
`M = fromCols Ω 1` (PSD by `Matrix.PosSemidef.conjTranspose_mul_mul_same`); its Schur complement
is `H - nystrom H Ω` by `nystrom_def`, its quadratic form at `Sum.elim y x` is
`quadForm H (Ω *ᵥ y + x)`, and `y ↦ -y` gives the stated set. Monotonicity and superadditivity:
pointwise in `x` from the variational form (a minimum of a sum is at least the sum of minima), then
`Matrix.IsHermitian.le_iff_re_quadForm_le`. Range monotonicity: the square-root form and
`rangeProjector_mono`, then `conjTranspose_mul_mul_le_conjTranspose_mul_mul`. Nyström helps
(basis-free, not TW's block argument): with $\mathbf{E} = \mathbf{H} - \mathbf{H}\langle\mathbf{\Omega}\rangle$
and $\mathbf{P} = \mathbf{P}_{\mathbf{\Omega}}$, $\mathbf{E}\mathbf{\Omega} = \mathbf{0}$ (Gram form), so
$\mathbf{E} = (\mathbf{I}-\mathbf{P})\mathbf{E}(\mathbf{I}-\mathbf{P}) \preceq (\mathbf{I}-\mathbf{P})\mathbf{H}(\mathbf{I}-\mathbf{P})$;
then `eigenvalue_le_eigenvalue_of_le`, `Matrix.PosSemidef.singularValues_eq_eigenvalue`, and
`IsStarProjection.singularValues_mul_le` (through `singularValues_conjTranspose`) for the right
factor $\mathbf{I}-\mathbf{P}$; the gauge form by `matrixNorm_le_of_singularValues_le`. Degenerate:
`s` empty, weights `0`, `l` empty (both sides of the variational form are
$\operatorname{Re}\langle\mathbf{x},\mathbf{H}\mathbf{x}\rangle$), `Ω = 0` in Nyström helps (equality).
Loewner antitonicity of the inverse (brief §4.1 item 4) exists: `Matrix.PosDef.inv_le_inv_of_le`
(`Inequalities/Order.lean`); no new statement.

### 3.6 Other Matrix-layer additions (4)

1. `Matrix/Spectral/SingularValues.lean`:
   `singularValues_conjTranspose_mul_self (A : Matrix m n 𝕜) (k : ℕ) : singularValues (Aᴴ * A) k = singularValues A k ^ 2`
   and `singularValues_mul_conjTranspose_self` (`… (A * Aᴴ) k = …`), by
   `Matrix.PosSemidef.singularValues_eq_eigenvalue` with `sq_singularValues` and
   `sq_singularValues_eq_eigenvalue_mul_conjTranspose_self`. Searched Mathlib's
   `LinearMap.singularValues`: none.
2. `Matrix/Norms/UnitarilyInvariant.lean`: `SymmetricGauge.matrixNorm_mul_conjTranspose_self (Φ)
   (A : Matrix m n 𝕜) : Φ.matrixNorm (A * Aᴴ) = Φ.matrixNorm (Aᴴ * A)` (brief item 5), by
   `matrixNorm_congr` and item 1.
3. `Matrix/Basic/Projector.lean`: `HasOrthonormalCols.rangeProjector_mul` (`rangeProjector (Q * X) =
   Q * rangeProjector X * Qᴴ`), today `private` in `Subspaces/PrincipalAngles.lean`, moved and made
   public (second user: `rsvd` equivariance; CONTRIBUTING §3).
4. `Matrix/Spectral/ProjectedLowRank.lean`: docstring only. `HasOrthonormalCols.frobNorm_sub_mul_sq`
   is already the core-form split of D1 (assessment R1); it is named so and cited
   [TroppYurtseverUdellCevher2017, Lemma A.3]. Not restated (one spelling).

### 3.7 Sketching additions (2, and one reproof)

```lean
-- Sketching/Properties/SubspaceEmbedding.lean, after `injOn`
theorem IsSubspaceInjection.rank_mul_eq [Fintype p] (h : IsSubspaceInjection S U a) (ha : 0 < a) :
    (S * U).rank = U.rank
-- Sketching/Properties/LeastSquares.lean
/-- The sketched part of the error split is controlled by the injection:
$\lVert\mathbf{\Pi}_{\mathbf{A},\mathbf{S}}\mathbf{Y}\rVert_{\mathsf{F}}^2 \le
\lVert\mathbf{S}\mathbf{Y}\rVert_{\mathsf{F}}^2 / a$. -/
theorem IsSubspaceInjection.frobNorm_obliqueProjector_mul_sq_le [Fintype r]
    (h : IsSubspaceInjection S A a) (ha : 0 < a) (Y : Matrix n r 𝕜) :
    frobNorm (obliqueProjector A S * Y) ^ 2 ≤ frobNorm (S * Y) ^ 2 / a
```

`IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le` keeps its name and statement and is reproved
from `frobNorm_one_sub_obliqueProjector_mul_sq` (its left side is `(1 - obliqueProjector A S) * Y`
by `mul_sketchAndSolve`) and the lemma above at `(1 - rangeProjector A) * Y` (rule 6); its docstring
points to the identity. Route of the new lemma: columns of $\mathbf{W} = \mathbf{\Pi}\mathbf{Y}$ lie in
$\operatorname{range}\mathbf{A}$ and $\mathbf{S}\mathbf{W} = \mathbf{P}_{\mathbf{S}\mathbf{A}}\mathbf{S}\mathbf{Y}$,
so $a\lVert\mathbf{W}\rVert_{\mathsf{F}}^2 \le \lVert\mathbf{S}\mathbf{W}\rVert_{\mathsf{F}}^2 \le
\lVert\mathbf{S}\mathbf{Y}\rVert_{\mathsf{F}}^2$. Degenerate `a ≤ 0`: excluded by `ha` (the
injection is vacuous there).

## 4. Files

In order; the brief's 900 lines (D12) become about 1300, because S0 states 66 public
declarations (24 + 3 + 11 + 16 + 6 + 4 in the Matrix layer, 2 in Sketching). Not in the brief's
estimate: equivariance (4), Nyström helps (2), the rank interface bridge, the PSD rank lemma, the
three restated `Oblique.lean` results and the promoted lemma.

| # | File | Statements | Lines (est.) | Imports (new) | Depends on |
|---|---|---|---|---|---|
| 1 | `Matrix/Spectral/SingularValues.lean`, `Matrix/Norms/UnitarilyInvariant.lean`, `Matrix/Basic/Projector.lean` (additions) | 2 + 1 + 1 | 60 | none | none |
| 2 | `Matrix/Subspaces/ObliqueProjector.lean` (new) | 24 | 600 | `Pseudoinverse/Pinv`, `Basic/Projector`, `Norms/Projector`, `Norms/UnitarilyInvariant` | 1 |
| 3 | `Matrix/Subspaces/Oblique.lean` (amended) | 3 new, 6 deprecated | +70 | 2 | 2 |
| 4 | `Matrix/Factorizations/SketchedLowRank.lean` (new) | 11 | 280 | 2 | 1, 2 |
| 5 | `Matrix/Factorizations/Nystrom.lean` (extended, 242 now) | 16 new, 24 total | +380 | 4, `Functions/AbsoluteValue`, `Norms/Nuclear`, `Basic/Selection` | 1, 4 |
| 6 | `Matrix/Factorizations/NystromOrder.lean` (new) | 6 | 240 | 5, `Spectral/Weyl`, `Spectral/SingularValueInequalities`, `Basic/QuadForm` | 5 |
| 7 | `Sketching/Properties/SubspaceEmbedding.lean`, `Sketching/Properties/LeastSquares.lean` (additions, reproof) | 1 + 1 | 60 | `LeastSquares` imports 2 | 2 |
| 8 | `Matrix/Spectral/ProjectedLowRank.lean` | docstring | 0 | none | none |

Every file stays under 1000 lines and 25 statements. Files 3, 4 and 7 are independent of each other
once 2 is in; 6 needs 5. One proof agent per file, or 1 with 8 and 3 with 7 (short, CONTRIBUTING
§11). **Split against the brief's D12**: `rsvd` and `generalizedNystrom` get their own file (4)
because `Nystrom.lean` with them would hold 35 statements; the topic of file 4 is "low-rank
approximations from a range sketch and a co-range sketch" (Q4). The CI root files are regenerated by
`mk_all`.

## 5. Material

**Prototype** (read-only, `~/Documents/prove2me/lean/NLAlib/LowRank/`; ledger dispositions):
- `Nystrom/Structural.lean` (211 lines). `nystrom` (`A * Ω * pinv (Ωᵀ * A * Ω) * (Ωᵀ * A)`, real) →
  `nystrom`; `nystrom_eq_of_eq_transpose_mul` → `nystrom_conjTranspose_mul_self`;
  `sub_nystrom_eq_of_eq_transpose_mul` → `conjTranspose_mul_self_sub_nystrom`;
  `posSemidef_nystrom_of_eq_transpose_mul`, `posSemidef_sub_nystrom_of_eq_transpose_mul`,
  `posSemidef_nystrom`, `posSemidef_sub_nystrom` → `Matrix.PosSemidef.nystrom`,
  `Matrix.PosSemidef.nystrom_le`; `trace_sub_nystrom_eq_of_eq_transpose_mul` →
  `nuclearNorm_conjTranspose_mul_self_sub_nystrom`; `specNorm_sub_nystrom_eq_of_eq_transpose_mul` →
  cut, index `0` of the singular-value form; `one_sub_mul_moorePenroseInverse_mul_eq_residual` → cut
  (`rangeProjector_inj`, `HasOrthonormalCols.rangeProjector_eq`);
  `integrable_and_integral_trace_sub_nystrom_le` → S5.
- `Nystrom/SketchedRegression.lean` (206). `sketchedCore` → `sketchAndSolve Q Ψᴴ A`;
  `sketchedOutput` → `obliqueProjector Q Ψᴴ * A`; `coreNoise` → no definition;
  `sketchedCore_eq`, `coreNoise_eq`, `sketchedCore_eq_add_coreNoise` →
  `HasOrthonormalCols.sketchAndSolve_eq_add`; `sketchedCore_eq_of_eq_mul`,
  `sketchedOutput_eq_of_eq_mul` → `obliqueProjector_mul_eq_self_of_range_le` and the core-noise
  lemma at zero noise; `error_decomp` → `one_sub_obliqueProjector_mul`; `frobSq_error` →
  `frobNorm_one_sub_obliqueProjector_mul_sq`; `transpose_mul_residual_eq`, `sketch_decomp`,
  `frobSq_transpose_mul_residual`, `specNorm_transpose_mul_residual` → S6 (they live in the
  $\mathbf{Q}_\perp$ coordinates the Gaussian blocks need).
- `Nystrom/RawNystromBridge.lean` (108). `rawGeneralizedNystrom` → `generalizedNystrom`;
  `rawGeneralizedNystrom_eq_sketchedOutput` → `HasOrthonormalCols.generalizedNystrom_eq`;
  `moorePenroseInverse_mul_eq_pinvR_mul_pinvL` → exists (`pinv_mul_rev`);
  `isUnit_rowGram_of_frame_factorization` → cut (`obliqueProjector_eq_of_range_eq` removes the need).
- `Nystrom/GeneralizedNystrom.lean`, `GaussianNystrom.lean`, `RawGaussianNystrom.lean`: read for the
  shape of their consumers; S6.
- The prototype's four representations (`projResidual` with a hypothesis-level `Q`, `nystrom`,
  `sketchedCore`/`sketchedOutput`, `rawGeneralizedNystrom`) and their bridge files collapse into
  `obliqueProjector` (D1). Atlas ids of the prototype (`nystrom-structural`,
  `sketched-regression`) are not reused: they name files, not results.

**The maintainer's notes** (read-only material, never cited, not ledgered; D13):
`~/Documents/Papers/LRA-paper/main.tex` (`lem:completion` and the sketched core, test orientation
$\mathbf{\Psi}^{\mathsf{T}}$) and the formalization's `Deterministic/SketchedRegression.lean`
(`frobSq_sub_mul_eq` is the existing `HasOrthonormalCols.frobNorm_sub_mul_sq`;
`sketchedCore_eq_add_core_noise` is the core-noise lemma; its `Fin`-indexed frames and complement
`Qp` are not reproduced). The design assessment's R1 and A1 are §3.1's core-form items. No S0
result first appears in the manuscript, so no S0 docstring says "proved without a literature source".

**Literature**, locators confirmed against the PDFs:
- EW (arXiv:2605.19096 v2): Definition 3.4 and Fact 3.5 (p. 8; Fact 3.5 states
  $\hat{\mathbf{H}} = \hat{\mathbf{A}}^{*}\hat{\mathbf{A}}$ and the trace identity), Definition 4.1
  (p. 9), Lemma 5.1 with (5.1), (5.2) (p. 11; hypothesis $\operatorname{rank}\mathbf{A} =
  \operatorname{rank}(\mathbf{\Omega}^{*}\mathbf{A})$, test orientation), Fact 6.1 (a)–(d) (p. 17).
- TYUC SIMAX (arXiv:1609.00048): (4.1)–(4.3) and Lemmas A.3, A.4 (p. 29). The co-range sketch is
  $\mathbf{\Psi}\in\mathbb{F}^{\ell\times m}$ applied as $\mathbf{\Psi}\mathbf{A}$: the sketch
  orientation (§7 Q1).
- CEMT: Imported Theorem 2.4 (p. 17 printed; nuclear form, after Gittens and Mahoney Lemma 1),
  Lemma 2.6 (p. 18 printed; after TYUC Lemma A.4).
- MT: §2.7, (2.3), (2.4) (p. 415); Proposition 11.1 ($|\mathbf{E}|^2 = (\mathbf{B}^{*}\mathbf{B})/\mathbf{X}$)
  and Corollary 11.2 (monotonicity) (p. 470–471); §14.2 (p. 495); Algorithm 8 (RSVD).
- TW (arXiv:2306.12418 v3): §5.4 and Lemma 5.2 "Nyström helps" (p. 18–20), stated for Schatten
  norms and every unitarily invariant norm, proved by a block computation.
- HMT: Algorithm 4.1 (randomized range finder), for `rsvd`'s docstring.

**Citations** (keys `EpperlyWebber2026`, `TroppWebber2023`, `TroppYurtseverUdellCevher2017` enter
`docs/references.bib` in the first S0 PR; D13):

| statement | citation | relation to the printed statement |
|---|---|---|
| `obliqueProjector` | [EpperlyWebber2026, Lemma 5.1, proof]; [TroppYurtseverUdellCevher2017, (4.2), (4.3)]; [CamanoEpperlyMeyerTropp2025, §2.4] | there with a basis and full or equal rank; here total, every rank |
| error split (linear, Gram, Frobenius, gauge) | [EpperlyWebber2026, Lemma 5.1, (5.2)]; [CamanoEpperlyMeyerTropp2025, Lemma 2.6]; [TroppYurtseverUdellCevher2017, Lemmas A.3, A.4] | there a trace identity in a basis; here a matrix identity |
| `sketchAndSolve_eq_pinv_mul_add` | [EpperlyWebber2026, Lemma 5.1, (5.1)] | there in a factorization $\mathbf{A} = \mathbf{Q}\mathbf{R}$; here basis-free |
| `HasOrthonormalCols.sketchAndSolve_eq_add` | [TroppYurtseverUdellCevher2017, Lemma A.4]; [CamanoEpperlyMeyerTropp2025, Lemma 2.6] | there with a complement frame $\mathbf{Q}_\perp$ |
| `rsvd`, `generalizedNystrom`, `nystrom` | [HalkoMartinssonTropp2011, Algorithm 4.1]; [MartinssonTropp2020, Algorithm 8, (2.3), (14.1)]; [EpperlyWebber2026, Definitions 3.4, 4.1] | deterministic test matrices; sketch-orientation core |
| GN split | [EpperlyWebber2026, proof of Theorem 4.2]; [TroppYurtseverUdellCevher2017, Lemma A.3] | exact, with the rank hypothesis |
| Gram correspondence (4 statements, PSD forms) | [MartinssonTropp2020, Proposition 11.1, §14.2]; [EpperlyWebber2026, Fact 3.5]; [CamanoEpperlyMeyerTropp2025, Imported Theorem 2.4]; [TroppWebber2023, §5.4] | general factor and every norm; there $\mathbf{F} = \mathbf{A}^{1/2}$ or trace only |
| PSD facts, representation invariance | [MartinssonTropp2020, §2.7]; [EpperlyWebber2026, Fact 6.1(a), (b)] | range form |
| variational, monotone, superadditive | [MartinssonTropp2020, Corollary 11.2]; [EpperlyWebber2026, Fact 6.1(c), (d)] | superadditive with any nonnegative weights |
| Nyström helps | [TroppWebber2023, Lemma 5.2] | singular-value form; basis-free proof |

Gittens and Mahoney 2016 is cited through CEMT until its key is added (brief §9.2, nice to have).
**Result ids** (explore's `results.toml` has no low-rank entry, so all are new; D11):
`gram-correspondence` on `nystrom_conjTranspose_mul_self`, `conjTranspose_mul_self_sub_nystrom`,
`nuclearNorm_conjTranspose_mul_self_sub_nystrom`, `Matrix.PosSemidef.sub_nystrom_eq`;
`oblique-projection-error-split` on the Gram and Frobenius splits;
`sketch-and-solve-error-decomposition` on `sketchAndSolve_eq_pinv_mul_add` and the core-noise
lemma; `schur-complement-monotone`, `schur-complement-concave`, `nystrom-helps`. The variational
form is an instance of the existing `schur-complement-variational` and carries no id.

## 6. Cut, and why

- `_def` lemmas for `obliqueProjector`, `rsvd`, `sketchAndSolve`: the bodies are the formulas;
  `generalizedNystrom_def` and `nystrom_def` exist because their source formulas differ from the
  bodies.
- The single-view form $\mathbf{Y}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Y})^{+} =
  \mathbf{Q}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q})^{+}$ (brief §4.1 item 1): the projector-level
  `obliqueProjector_eq_of_range_eq` and `HasOrthonormalCols.generalizedNystrom_eq` are what the
  probabilistic proofs consume; the unmultiplied form has no consumer.
- The $\mathbf{Q}_\perp$ form of the second term,
  $\mathbf{Q}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q})^{+}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q}_\perp)\mathbf{Q}_\perp^{\mathsf{H}}\mathbf{B}$
  (review A9): S0 states it with the leading $\mathbf{Q}$ through the core form; the complement
  frame enters only in S6, where the Gaussian block law needs it (one rewrite with
  $\mathbf{Q}_\perp\mathbf{Q}_\perp^{\mathsf{H}} = \mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}}$).
- Hypothesis forms `A = Fᵀ * F` of the prototype: stated at `Fᴴ * F`; a user with `hA` rewrites.
- The spectral equality and the trace equality of the prototype: index `0` of the singular-value form,
  and the nuclear form with `Matrix.PosSemidef.nuclearNorm_eq_re_trace`.
- A gauge or Gram-form GN split and unsquared GN statements: D4 (GN is Frobenius); the projector
  level has them.
- Definitions for the Schur complement $\mathbf{H}/\mathbf{\Omega}$ and for the core noise: §5.3
  writes Schur complements without definitions (Q7).
- Restating `HasOrthonormalCols.frobNorm_sub_mul_sq` as "the core-form split": one spelling; its
  docstring gains the name (§3.6 item 4).
- A real-scalar twin of `obliqueProjector_smul_right`, a two-term superadditivity, homogeneity of
  `nystrom`: one-line corollaries with no consumer that cannot write them.
- A bridge to `Submodule.linearProjOfIsCompl`: no consumer (Q11).
- Loewner antitonicity of the inverse: exists (`Matrix.PosDef.inv_le_inv_of_le`).
- EW Lemma 5.8 (S10), the signed-permutation average (S4), a streaming model (brief §0.1).

## 7. Questions and decisions

Hard-to-reverse items are marked **(hard)**. None needs the maintainer under the brief's approval
rule except that Q1 is recorded for the checkpoint after S2b.

**Q1. D14, the orientation of the second argument (hard; decided here).** Decision: the sketch
orientation, `obliqueProjector X S := X * pinv (S * X) * S` with `S : Matrix k m 𝕜` on the left.
Reasons:
1. The Sketching predicates take the sketch: `IsSubspaceInjection S U a`. Under D2 they are applied
   to $\mathbf{\Omega}^{\mathsf{H}}$ and $\mathbf{\Psi}^{\mathsf{H}}$, so the predicate and the
   projector carry literally the same term (`IsSubspaceInjection Ψᴴ (A * Ω) a`,
   `obliqueProjector (A * Ω) Ψᴴ`, rank hypothesis `(Ψᴴ * (A * Ω)).rank`), with no
   `conjTranspose_conjTranspose` at each use (review A8).
2. Every Sketching law is a law of a sketch `Matrix k n 𝕜` (SRHT, CountSketch, sampling). In the
   test orientation each of those users writes `obliqueProjector X Sᴴ` and meets `Sᴴᴴ` whenever the
   definition unfolds; in the sketch orientation no user ever meets a double star in the core.
3. `sketchAndSolve` unfolds to the existing raw formula `pinv (S * A) * (S * Y)` of
   `IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le` literally (D1's promise that the Sketching
   statements keep their spelling holds only in this orientation), and the Solvers round's
   sketch-and-solve and sketch-and-precondition are in it (Woodruff; MT §10.3).
4. The literature is split: TYUC SIMAX (4.2) and Woodruff put the co-range sketch on the left
   ($\mathbf{\Psi}\mathbf{A}$, checked); EW, CEMT, MT and the manuscript write $\mathbf{\Psi}^{*}$.
   The named algorithm keeps D2's test matrix, so `generalizedNystrom A Ω Ψ` is the sources'
   $\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle$ and unfolds (`generalizedNystrom_def`) to
   their formula; the only place a reader of EW sees `Ψᴴ` as an argument is the core.
5. Smaller: every idempotent is `obliqueProjector P P`; `obliqueProjector X 1` is the orthogonal
   projector with no `ᴴ`.

Cost: Gaussian and Haar statements about a fixed `X` (S6 shape (a)) write `(Ψ ω)ᴴ` inside
`obliqueProjector`. Rework if reversed: every statement that mentions `obliqueProjector` or
`sketchAndSolve`, in S0 and in S2b, S6, S7. This is the sticky item of D1 (review answer 2).

**Q2. The rank hypothesis as a raw spelling, not a predicate (moderately hard).** Options:
(a) `(S * X).rank = X.rank`; (b) `Set.InjOn S.mulVec (LinearMap.range X.mulVecLin)`; (c) a named
predicate. Recommendation (a): it is EW Lemma 5.1's hypothesis verbatim, it is what the RandomMatrix
layer produces (`ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix` concludes a rank equation), it is
decidable by `Matrix.rank` arithmetic in examples, and (b) is one rewrite away
(`rank_mul_eq_iff_injOn`). (c) would bundle one equation and add an unfolding step at every
a.s. use; CONTRIBUTING §5.4's "a raw condition written twice is an interface" is met by the §5.3
row with its two bridges, as for `Function.Injective A.mulVec`. Rework if changed: the hypothesis
line of about 25 statements across S0, S6, S7.

**Q3. `sketchAndSolve A S B` with the sketch, matrix right-hand side (hard, with Q1).** The brief's
spelling `sketchAndSolve A Ψ B` with `Ψᴴ` inside follows D14 to `S`. Argument order (system,
sketch, right-hand side) matches `obliqueProjector X S`. A vector right-hand side is
`isLeastSquaresSolution_pinv_mulVec (S * A) (S *ᵥ b)` or a one-column `B`; no vector twin.

**Q4. A fourth file `Matrix/Factorizations/SketchedLowRank.lean` (not hard).** D12 named three files;
`rsvd` and `generalizedNystrom` in `Nystrom.lean` would give it 35 statements. Alternative: put them
in `ObliqueProjector.lean` (also over budget, and off its topic). The name is a topic, not a round;
`RangeFinder.lean` is avoided because S1's `LowRank/Structural/RangeFinder.lean` will exist.
Rework: a file move.

**Q5. `Oblique.lean`'s two-bases lemmas: restate and deprecate (not hard).** The `(Yᴴ * X)⁻¹`
spelling becomes a lemma (`obliqueProjector_of_isUnit`), so its six lemmas would be a second
spelling. They are restated on `obliqueProjector`, generalised where `pinv` allows (no injectivity
of `X` in `IsIdempotentElem.obliqueProjector_eq`; any widths in the frame norm), and the old names
get `@[deprecated]` for one release. No `v0.1` tag exists, so deletion would be allowed; the explorer is
built from releases and may list the old names, hence the deprecation. They have no users outside
the file.

**Q6. The Gram correspondence through `rsvd`, at `Fᴴ * F` (not hard).** Statements read
`nystrom (Fᴴ * F) Ω = (rsvd F Ω)ᴴ * rsvd F Ω`: the correspondence as a sentence ("Nyström of the
Gram matrix is the Gram matrix of the RSVD"), every factor, so kernel and Gram matrices need no
square root (brief §4.1 item 3). The maintainer's $\mathbf{A}^{1/2}\mathbf{P}\mathbf{A}^{1/2}$ is
`Matrix.PosSemidef.nystrom_eq`. The prototype's hypothesis form `(hA : A = Fᵀ * F)` is dropped
(rewrite first).

**Q7. No definitions for $\mathbf{H}/\mathbf{\Omega}$ or the core noise (not hard).** §5.3 writes
Schur complements as `C - Bᴴ * pinv A * B` and `D - C * A⁻¹ * B`; `H - nystrom H Ω` follows it.
Adding a definition later is additive.

**Q8. Superadditivity with arbitrary nonnegative weights (not hard).** It contains EW Fact 6.1(c)
(weights summing to one) and needs no extra hypothesis: through the variational form, a minimum of
a nonnegative combination is at least the combination of the minima. S4's group average is the case
of equal weights.

**Q9. Equivariance and Nyström helps are in S0 (not hard).** Not on the brief's S0 list. The
equivariance lemmas are the Matrix-layer half of S4's symmetrisation and of the reduction to a
diagonal $\mathbf{A}$, and belong with the definitions; TW Lemma 5.2 is listed among the brief's
item 3 companions. Removing them moves four plus two statements to S4 and S5.

**Q10. Selection Nyström keeps its submatrix spelling (not hard).** The four residual lemmas of
`Factorizations/Nystrom.lean` and `foldl_eliminationStep_eq_sub` stay in
`A.submatrix id e * pinv (A.submatrix e e) * A.submatrix e id` form (the §5.3 "rank-revealing
column selection" style, and what elimination produces); `nystrom_selectionMatrix` bridges. Restating
them on `nystrom` would touch the RPCholesky material the brief defers.

**Q11. No bridge to Mathlib's `Submodule.linearProjOfIsCompl` (not hard).** It is a map into the
subspace, needs the complement as data, and no S0 to S7 statement or Solvers consumer reads it.
Added on demand, in `ObliqueProjector.lean`.

**Q12. Size (information).** About 1300 lines against the brief's 900 (§4); the round total rises
by about 400 to about 7150. S0 remains one stage.

## 8. Amendments from the review (2026-10-15)

Review of this note (0 blocker, 3 major, 9 minor), all twelve amendments accepted by the
orchestrator, one corrected on inspection (A12(b) names the wrong Mathlib file, item 14); none
rejected. Q1 (D14) decided as drafted, Q3 with it; Q2 kept as (a) with the governing rule made
explicit; Q4 to Q12 accepted as recommended; nothing for the maintainer beyond Q1's place in the
record for the checkpoint after S2b (§7). The review verified, at every rank and shape including the
empty types, `A = 0`, `Ω = 0`, `S = 0`, rank-deficient `A * Ω` and Hermitian non-PSD inputs, every
statement of §3.1 to §3.7, the necessity of each hypothesis where the note says so, every cited
library lemma, the literature locators, the prototype ledger, and that measurability is not a gap
(`measurable_pinv`, `measurable_rangeProjector`). Where an item below contradicts §0 to §7, it
supersedes them; §3 stays as drafted. Skeletons: the files of item 15, every new proof `sorry`.

1. **Q1 decided: the sketch orientation** `obliqueProjector X S := X * pinv (S * X) * S`. The review
   finds it clearly dominant: every Sketching predicate and law is about a sketch `S : Matrix k n 𝕜`
   (D2), so the predicate's matrix and the core's second argument are the same term for every user,
   and `sketchAndSolve A S Y` unfolds to the existing `pinv (S * A) * (S * Y)`. The only cost is
   `(Ψ ω)ᴴ` inside S6's fixed-`X` statements, where `IsSubspaceInjection (Ψ ω)ᴴ X a` already carries
   the same term. **Q3** follows (forced by Q1; argument order system, sketch, right-hand side; no
   vector twin).
2. **Q2 kept as (a), `(S * X).rank = X.rank`, with the rule stated (A4).** §2 and Q2 misattribute
   the rule: "if you write a raw condition a second time, it is an interface" is CONTRIBUTING §1
   rule 2; §5.4 says "theorems take the interface, never the raw condition". The rule applied, for
   S0 and every later stage: *a single Mathlib-native equation or proposition (here `Matrix.rank`
   on both sides), with a §5.3 row and constructor bridges, is a spelling, as
   `Function.Injective A.mulVec` is for full column rank; a bundle of conditions, or a condition
   phrased through a library-specific construction, is a predicate once it recurs.* D5's
   optimality hypothesis (`Y.rank ≤ k ∧ frobNorm (C - Y) ≤ frobNorm (C - truncatedSVD C k)`, a
   conjunction through `truncatedSVD`) is on the predicate side, so its "more than three
   statements" threshold stands for S2a; the rank hypothesis (14 S0 statements with item 11, about 25 in
   the round) is on the spelling side, so the threshold does not apply to it. Q2's text reads so. A
   predicate wrapping the same equation can be added additively if S6 or S7 find themselves writing
   API lemmas about the hypothesis (the §5.4 trigger); the rework is then the hypothesis line of
   those statements.
3. **A1, the Mathlib-deviations entry** (replaces §1's "No deviation from Mathlib ... No entry"). The
   predicate stays Mathlib's `IsIdempotentElem`, but `obliqueProjector` is a departure of the kind of
   entry 5 (`rangeProjector` for `Submodule.starProjection`): Mathlib has projection along a
   complement and NLAlib's statements are written with another object. The justification is
   generality, not convenience. The other four definitions (`sketchAndSolve`, `rsvd`,
   `generalizedNystrom`, `nystrom`) are additions: Mathlib has no sketched least squares, low-rank
   approximation or Nyström approximation, so they join the list "Additions where Mathlib has
   nothing" (their existence as definitions is D1's decision, not the file's). The skeleton agent
   copies this entry into `docs/design/Mathlib-deviations.md` as §19 and adds the line
   "`obliqueProjector` (entry 19), `sketchAndSolve`, `rsvd`, `generalizedNystrom`, `nystrom`" to
   the additions paragraph, in the commit that adds the definitions:
   ```markdown
   ## 19. Oblique projectors from a basis and a sketch

   - **Mathlib.** `Submodule.projection p q h` (an endomorphism) and `Submodule.linearProjOfIsCompl`
     (a map into `p` through an injection), in `LinearAlgebra/Projection.lean`, project onto `p`
     along a complement `q` and take a proof `h : IsCompl p q`; `LinearMap.IsProj p f` is the
     predicate. The idempotent predicate `IsIdempotentElem` is used as Mathlib has it.
   - **NLAlib.** `obliqueProjector X S := X * pinv (S * X) * S`
     (`NLAlib/Matrix/Subspaces/ObliqueProjector.lean`), a total matrix-valued function of a basis
     `X : Matrix m r 𝕜` and a sketch `S : Matrix k m 𝕜` with no proof argument. It is always
     idempotent; under `(S * X).rank = X.rank` it projects onto `range X` along
     `{v | S *ᵥ v ⟂ range (S * X)}`.
   - **Why.** Generality, not convenience. (1) Every rank and shape: through `pinv` the formula is
     defined and idempotent for every `X` and `S`, it projects onto `range X` exactly under the
     rank hypothesis, and onto the smaller range of `X * (S * X)ᴴ` otherwise; Mathlib's projection
     exists only after an `IsCompl` proof. The probabilistic stages need the total form: they
     integrate `obliqueProjector X (Ψ ω)ᴴ` over every `ω`, including the null set where the rank
     hypothesis fails, and `measurable_pinv` makes it a random matrix, which a proof-carrying
     projection is not without a junk branch. (2) It is the matrix the algorithms compute:
     generalized Nyström, sketch-and-solve and the formulas of Tropp, Yurtsever, Udell and
     Cevher, Epperly and Webber, and Camaño, Epperly, Meyer and Tropp are literally
     $\mathbf{X}(\mathbf{S}\mathbf{X})^{+}\mathbf{S}$, and `generalizedNystrom_def` and
     `sketchAndSolve` unfold to them with no transport. (3) The complement is not a datum the user
     has: when `S` has more rows than `rank X` the kernel is the preimage under `S` of the
     orthogonal complement of `range (S * X)`, which is `ker S` only when
     `range (S * X) = range S`. Mathlib's form would require constructing that subspace and proving
     complementarity at every use, and it hides the sketch, which is the variable of every theorem
     (the injection hypothesis, the law of `S`).
   - **Bridge.** To the predicate: `isIdempotentElem_obliqueProjector` and
     `IsIdempotentElem.obliqueProjector_eq` (every idempotent is one). To Mathlib's projections:
     not stated, added on demand in the same file (`docs/design/LowRank-S0.md` §7 Q11); it would
     read `LinearMap.IsProj (LinearMap.range X.mulVecLin) (obliqueProjector X S).mulVecLin` under
     the rank hypothesis, a corollary of `range_obliqueProjector` and
     `obliqueProjector_mul_eq_self_of_range_le`.
   - **Cost.** A user holding `Submodule.projection` writes the bridge first. The §5.3 two-bases
     spelling `X * (Yᴴ * X)⁻¹ * Yᴴ` becomes a lemma (`obliqueProjector_of_isUnit`), and six
     `Oblique.lean` lemmas are deprecated for one release.
   - **Status: proposed** in LowRank S0 (`docs/design/LowRank-S0.md` §8 item 3), 2026-10-15; not
     approved by the maintainer.
   ```
4. **A2, residual bridges to the §5.3 spellings** (`SketchedLowRank.lean`, +2). Every S1 to S7
   statement writes the projection residual as `(1 - rangeProjector Y) * A` or names the output;
   the bridges keep one rewrite in one place:
   ```lean
   theorem sub_rsvd [DecidableEq m] (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
       A - rsvd A Ω = (1 - rangeProjector (A * Ω)) * A
   theorem sub_generalizedNystrom [DecidableEq m] (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
       (Ψ : Matrix m p 𝕜) :
       A - generalizedNystrom A Ω Ψ = (1 - obliqueProjector (A * Ω) Ψᴴ) * A
   ```
   Proofs `sub_mul`, `one_mul`; the GN split's proof route uses `sub_rsvd`. No `sub_nystrom`: at
   `Fᴴ * F` it is `conjTranspose_mul_self_sub_nystrom`, and for general `A` it is
   `sub_generalizedNystrom` after unfolding `nystrom`.
5. **A3, rank and range of the outputs** (+1 in `ObliqueProjector.lean`, +4 in
   `SketchedLowRank.lean`). The `rsvd` docstring's "rank at most $\lvert l \rvert$" and the range
   claim of the `obliqueProjector` docstring get lemmas (CONTRIBUTING §6), in the form
   `range_mulVecLin_le_iff_exists_mul` consumes:
   ```lean
   theorem range_obliqueProjector_le (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) :
       LinearMap.range (obliqueProjector X S).mulVecLin ≤ LinearMap.range X.mulVecLin
   theorem rank_rsvd_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) : (rsvd A Ω).rank ≤ (A * Ω).rank
   theorem range_rsvd_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
       LinearMap.range (rsvd A Ω).mulVecLin ≤ LinearMap.range (A * Ω).mulVecLin
   theorem rank_generalizedNystrom_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (Ψ : Matrix m p 𝕜) :
       (generalizedNystrom A Ω Ψ).rank ≤ (Ψᴴ * (A * Ω)).rank
   theorem range_generalizedNystrom_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (Ψ : Matrix m p 𝕜) :
       LinearMap.range (generalizedNystrom A Ω Ψ).mulVecLin ≤ LinearMap.range (A * Ω).mulVecLin
   ```
   Routes: `Matrix.rank_mul_le_left` with `rank_rangeProjector` and `rank_obliqueProjector`; ranges
   by `range_mulVecLin_le_iff_exists_mul` (the projector is `X * _`) and
   `range_mulVecLin_rangeProjector`. The bounds by `card l` and `card p` are Mathlib's
   `Matrix.rank_le_card_width` and `Matrix.rank_le_card_height` after these, not separate statements.
6. **A5, the `nystrom` docstring.** "A theorem's subject only for positive semidefinite
   $\mathbf{A}$" becomes: the order and exactness theorems take `A.PosSemidef`; the general-factor,
   selection and equivariance statements do not. §1's convention paragraph reads the same.
7. **A6, result ids.** Ids are defined by the `Result:` lines of docstrings; `results.toml` is
   optional metadata, so §5's "results.toml has no low-rank entry" is not the check. Existing ids
   beside S0: `sketch-and-solve-ls`, `sketch-and-precondition` (`Sketching/Properties/LeastSquares`),
   `subspace-injection`, `schur-complement-variational`, `schur-complement-psd`
   (`GeneralizedSchur`), `oblique-projection-norm` (`Oblique.lean`). The new ids do not collide.
   `oblique-projection-norm` moves to the two restated frame-norm lemmas
   (`HasOrthonormalCols.specNorm_obliqueProjector` and its `_mul_cos` twin) and leaves the
   deprecated ones. `sketch-and-solve-error-decomposition`'s docstring says it is the exact
   identity beside the bound `sketch-and-solve-ls`.
8. **A7, imports of `ObliqueProjector.lean`** (§4 file 2): add `Basic/OrthonormalBasis`
   (`exists_hasOrthonormalCols_range_eq`, indexed by `Fin X.rank`) and `Basic/Gram`
   (`mulVec_injective_iff_rank_eq`). §3.2's "nothing imports `Oblique.lean`" reads "nothing but the
   generated root `NLAlib.lean`", which is no cycle.
9. **A8, the deprecations of §3.2.** `mul_inv_mul_conjTranspose_mulVec_eq_zero` is deprecated
   without a named replacement (no users; the vector case is `Matrix.mulVec_mulVec` and the
   hypothesis, or the matrix form `obliqueProjector_mul_eq_zero_of_mul_eq_zero` at one column); no
   `mulVec` twin is added. `HasOrthonormalCols.specNorm_mul_inv_mul_conjTranspose` and its twin:
   the deprecation docstring says the replacement agrees with the old lemma where
   $\mathbf{V}^{\mathsf{H}}\mathbf{U}$ is invertible, and that where it is singular both sides of
   the old lemma are $0$ (Mathlib's inverse), a case the new lemma states with the pseudoinverse
   instead.
10. **A9, sketch-side invariance** (`ObliqueProjector.lean`, +1), added: the twin of
    `obliqueProjector_smul_right` for laws invariant under $\mathbf{\Psi} \mapsto
    \mathbf{\Psi}\mathbf{W}$ (Q1 reason 2 is about sketch users):
    ```lean
    theorem HasOrthonormalCols.obliqueProjector_mul_left [DecidableEq k] {k' : Type*} [Fintype k']
        {W : Matrix k' k 𝕜} (hW : HasOrthonormalCols W) (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) :
        obliqueProjector X (W * S) = obliqueProjector X S
    ```
    Proof: `HasOrthonormalCols.pinv_mul_left` and `hW`. The `obliqueProjector` docstring gains one
    clause: $\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$ is unchanged by $\mathbf{X} \mapsto
    \mathbf{X}\mathbf{M}$ for invertible $\mathbf{M}$ (under the rank hypothesis), by
    $\mathbf{S} \mapsto c\,\mathbf{S}$ for $c \ne 0$ and by $\mathbf{S} \mapsto \mathbf{W}\mathbf{S}$
    for $\mathbf{W}$ with orthonormal columns, but not by $\mathbf{S} \mapsto \mathbf{M}\mathbf{S}$
    for a general invertible $\mathbf{M}$, even under the rank hypothesis: it depends on
    $\mathbf{S}^{\mathsf{H}}\mathbf{S}$, not only on the row space of $\mathbf{S}$.
11. **A10, the `P_X` form of exactness** (`ObliqueProjector.lean`, +1), added beside
    `obliqueProjector_mul_self_iff`; the split's proof route uses it:
    ```lean
    theorem obliqueProjector_mul_rangeProjector (h : (S * X).rank = X.rank) :
        obliqueProjector X S * rangeProjector X = rangeProjector X
    ```
    Proof: `obliqueProjector_mul_eq_self_of_range_le` with `range_mulVecLin_rangeProjector`.
12. **A11, docstrings are LaTeX.** The skeleton writes every docstring's mathematics in LaTeX
    (CONTRIBUTING §6 item 5) with the table's notation: norms `\|\mathbf{A}\|_{\mathsf{F}}`,
    `\|\mathbf{A}\|_{\Phi}`, `\|\mathbf{x}\|`, never `\lVert … \rVert` (the drafts in §3, the
    sketch-and-solve and §3.7 docstrings among them, are converted); Lean names stay in backticks
    outside `$…$`. A conclusion with a fraction or longer than a line is displayed with `$$…$$`,
    including the gauge split and the GN split.
13. **Size** (amends §4 and Q12). `ObliqueProjector.lean` 27 statements, about 650 lines;
    `SketchedLowRank.lean` 17, about 340. S0 is about 1400 lines and 75 public declarations
    (27 + 3 + 17 + 16 + 6 + 4 in the Matrix layer, 2 in Sketching). A12(c): the 25-statement budget
    of §4 is not a CONTRIBUTING rule (only the 1000-line topic rule, §1 item 8 and §8 item 5); it
    was a planning figure, and the 27 of `ObliqueProjector.lean` stand. Q4's split of
    `SketchedLowRank.lean` from `Nystrom.lean` still holds on topic and length (41 statements
    together).
14. **A12, corrections of record.**
    (a) `Matrix.PosSemidef.dotProduct_mulVec_zero_iff` is in `Mathlib/Analysis/Matrix/Order.lean`.
    (b) Corrected on inspection: `CFC.sqrt_mul_sqrt_self` and `CFC.sqrt_nonneg` are defined in
        `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean`; `Abs.lean`
        only uses them.
    (c) See item 13.
    (d) §0's "Nyström helps" row: the comparison S5 wants is the lemma at `Ω := H * Ω₀`,
        `singularValues (H - nystrom H (H * Ω₀)) k ≤ singularValues (H - rsvd H Ω₀) k` through
        `sub_rsvd` (item 4), since `nystrom H (H * Ω₀)` is the Nyström approximation from the sample
        `H * Ω₀`; the S5 note states it.
    (e) Keys: `TroppWebber2023`, `EpperlyWebber2026`, `TroppYurtseverUdellCevher2017` and
        `GittensMahoney2016` are absent from `docs/references.bib`; the first three enter in the
        first S0 PR (D13).
    (f) Mathlib's `LinearMap.singularValues` has `sq_singularValues_of_lt` and nothing on
        $\mathbf{T}^{\dagger}\mathbf{T}$ itself; §3.6 item 1's "searched, none" stands.
15. **Files and statements for the skeleton** (§4's order and dependencies otherwise unchanged):
    `Matrix/Spectral/SingularValues.lean` 2, `Matrix/Norms/UnitarilyInvariant.lean` 1,
    `Matrix/Basic/Projector.lean` 1 (moved from `PrincipalAngles.lean`);
    `Matrix/Subspaces/ObliqueProjector.lean` 27 (new); `Matrix/Subspaces/Oblique.lean` 3 new,
    6 deprecated; `Matrix/Factorizations/SketchedLowRank.lean` 17 (new);
    `Matrix/Factorizations/Nystrom.lean` 16 new, 24 in the file;
    `Matrix/Factorizations/NystromOrder.lean` 6 (new); `Sketching/Properties/SubspaceEmbedding.lean`
    1 and `Sketching/Properties/LeastSquares.lean` 1, with the reproof of
    `frobNorm_sub_mul_pinv_mul_sq_le`; `Matrix/Spectral/ProjectedLowRank.lean` docstring only.
    The Mathlib-deviations entry of item 3 and the §5.3 rows of §1 go in with the definitions.

### Skeleton notes

Skeleton agent, 2026-10-15. All 75 statements are written and **proved; no `sorry` remains**.
Nothing is registered in `NLAlib.lean`. Each file was checked with `lake lean`; `check_refs.py`
and `check_latex.mjs` pass.

- **Files.** New: `Matrix/Subspaces/ObliqueProjector.lean` (27), `Matrix/Factorizations/SketchedLowRank.lean`
  (17), `Matrix/Factorizations/NystromOrder.lean` (6). Side files, because their homes are
  registered and would otherwise import unregistered modules: `Matrix/Factorizations/NystromGram.lean`
  (the 16 `Nystrom.lean` additions), `Matrix/Subspaces/ObliqueBases.lean` (the 3 `Oblique.lean`
  additions), `Sketching/Properties/LeastSquaresOblique.lean` (the `LeastSquares.lean` addition).
  Each says it merges into its home at the wrap-up. Proved in place: the two Gram singular-value
  lemmas (`SingularValues.lean`), the gauge equality (`UnitarilyInvariant.lean`),
  `HasOrthonormalCols.rangeProjector_mul` (moved public to `Basic/Projector.lean`, removed from
  `PrincipalAngles.lean`), `IsSubspaceInjection.rank_mul_eq` (`SubspaceEmbedding.lean`), and the
  §3.6 item 4 docstring of `ProjectedLowRank.lean`.
- **Deferred to the wrap-up.** The reproof of `IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le`
  from the split (it needs `LeastSquares.lean` to import `ObliqueProjector.lean`). The six
  deprecations in `Oblique.lean` are in place with message strings, not target names, since
  `Oblique.lean` cannot import `ObliqueProjector.lean` before registration; the merge of
  `ObliqueBases.lean` should switch them to `@[deprecated name]`. The §5.3 rows of §1 are not yet
  in CONTRIBUTING.
- **Statement changes.** `HasOrthonormalCols.generalizedNystrom_eq` became
  `generalizedNystrom_eq_mul_sketchAndSolve`: orthonormality of `Q` was unused (the identity holds
  for any `Q` with the range of `A * Ω`), and an unused hypothesis is not minimal.
  `frobNorm_sub_generalizedNystrom_sq` takes no `[DecidableEq m]`, and the four `CFC.sqrt`
  statements of `NystromGram.lean` take no `[DecidableEq n]` (`open scoped Classical in`, as in
  `Functions/AbsoluteValue.lean`): the linter reports the instance used only in proofs.
  `[Fintype _]` instances are on the declarations that need them.
- **Proof routes that differ from §3.** Range invariance (`obliqueProjector_eq_of_range_eq`) needs
  no orthonormal basis: $\mathbf{\Pi}_{\mathbf{X}}\mathbf{\Pi}_{\mathbf{X}'} =
  \mathbf{\Pi}_{\mathbf{X}'}$ by exactness, and the product collapses because
  $\mathbf{P}_{\mathbf{S}\mathbf{X}'} = \mathbf{P}_{\mathbf{S}\mathbf{X}}$; only the rank
  hypothesis on $\mathbf{X}$ is used. The PSD rank lemma goes through
  $\mathbf{A}^{1/2}$ and `Matrix.rank_conjTranspose_mul_self`. Superadditivity and Nyström helps
  are pointwise from the variational form.

### Placement refactor (2026-10-15)

- Amendment 2026-10-15 (maintainer): `sketchAndSolve`, `mul_sketchAndSolve`,
  `sketchAndSolve_eq_pinv_mul_add` and `HasOrthonormalCols.sketchAndSolve_eq_add` move from
  `Matrix/Subspaces/ObliqueProjector.lean` to `Matrix/Pseudoinverse/LeastSquares.lean` (their topic
  is least squares; `ObliqueProjector.lean` points to them), names unchanged;
  `rank_mul_eq_iff_injOn` moves to `ForMathlib/LinearAlgebra/Matrix/Rank.lean` as
  `Matrix.rank_mul_eq_iff_injOn` over any field (deprecated alias `NLAlib.rank_mul_eq_iff_injOn`),
  beside the formerly private row-space companion, now public as
  `Matrix.range_mulVecLin_conjTranspose_mul_eq_of_rank_eq`.
