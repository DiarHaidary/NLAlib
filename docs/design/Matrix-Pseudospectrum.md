# Closed pseudospectral characterizations

Design date: 2026-11-02. Scope: the complete original
`pseudospectrum-perturbation-equivalence` card, consolidated into one Matrix topic file.

## Objects and interfaces

No new definition, hypothesis interface, vocabulary row, constant, or Mathlib deviation is
introduced. Use `Matrix`, `spectrum`, `IsStarNormal`, `Matrix.rank`, `specNorm`, and
`singularValues` directly. The first four results use an `RCLike` field and arbitrary finite
indices. The least singular value has an explicit index `k` with `k + 1 = Fintype.card n`;
this condition already implies nonempty dimension. Normal spectral disks use complex scalars
and the existing Mathlib `IsStarNormal` interface. Their statement also covers empty indices.
The matrix, shift, and perturbation all belong to the same field. Thus the real instance covers
real shifts and real perturbations; it makes no claim about real or structured perturbations
producing a nonreal shift of a real matrix.

No set-valued pseudospectrum definition is needed: the equivalences rewrite the perturbation,
unit-residual, singular-value, and resolvent descriptions consumers already have. Closed radii
are intentional; the perturbation, residual, and normal-disk equivalences allow every real radius,
including zero (and are false on both sides for negative radii). The resolvent statement requires positive
radius and retains the eigenvalue disjunct because the total inverse is zero at singular inputs.

## Exact headline signatures

All declarations except the final dot-notation theorem are in `NLAlib`.

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_rank_le_one_and_mem_spectrum_add (A : Matrix n n 𝕜) (z : 𝕜)
    {k : ℕ} (hk : k + 1 = Fintype.card n) :
    ∃ E : Matrix n n 𝕜, E.rank ≤ 1 ∧ z ∈ spectrum 𝕜 (A + E) ∧
      specNorm E = singularValues (z • 1 - A) k ∧
      ∀ F : Matrix n n 𝕜, z ∈ spectrum 𝕜 (A + F) → specNorm E ≤ specNorm F

theorem exists_specNorm_le_and_mem_spectrum_add_iff (A : Matrix n n 𝕜) (z : 𝕜)
    {k : ℕ} (hk : k + 1 = Fintype.card n) (ε : ℝ) :
    (∃ E : Matrix n n 𝕜, specNorm E ≤ ε ∧ z ∈ spectrum 𝕜 (A + E)) ↔
      singularValues (z • 1 - A) k ≤ ε

theorem exists_norm_eq_one_and_norm_mulVec_le_iff (A : Matrix n n 𝕜) (z : 𝕜)
    {k : ℕ} (hk : k + 1 = Fintype.card n) (ε : ℝ) :
    (∃ v : n → 𝕜, ‖WithLp.toLp 2 v‖ = 1 ∧
      ‖WithLp.toLp 2 ((z • 1 - A) *ᵥ v)‖ ≤ ε) ↔
      singularValues (z • 1 - A) k ≤ ε

theorem singularValues_le_iff_mem_spectrum_or_le_specNorm_inv (A : Matrix n n 𝕜)
    (z : 𝕜) {k : ℕ} (hk : k + 1 = Fintype.card n) {ε : ℝ} (hε : 0 < ε) :
    singularValues (z • 1 - A) k ≤ ε ↔
      z ∈ spectrum 𝕜 A ∨ 1 / ε ≤ specNorm (z • 1 - A)⁻¹

theorem _root_.IsStarNormal.exists_specNorm_le_and_mem_spectrum_add_iff
    {A : Matrix n n ℂ} (hA : IsStarNormal A) (z : ℂ) (ε : ℝ) :
    (∃ E : Matrix n n ℂ, specNorm E ≤ ε ∧ z ∈ spectrum ℂ (A + E)) ↔
      ∃ μ ∈ spectrum ℂ A, ‖z - μ‖ ≤ ε
```

Each headline carries `Result: pseudospectrum-perturbation-equivalence`; the perturbation
equivalence is the primary description. The attained minimum includes rank zero when the
shift is already singular, hence the precise rank-at-most-one wording.

## Reuse and proof structure

Mathlib and the target library were searched first. No exact pseudospectrum characterization
was found. The reviewed development is mathematical scope and proof material, not an API
template. Exact overlaps are reused rather than copied:

* The lower bound transports
  `singularValues_last_le_specNorm_of_not_injective_add` from
  `Matrix/Pseudoinverse/ConditionNumber.lean`, applied to `z • 1 - A` and `-E`.
  Mathlib's `spectrum.mem_iff`, `Matrix.mulVec_injective_iff_isUnit`, and
  `Algebra.algebraMap_eq_smul_one` supply the bridge. It remains a private local transport.
  `isLeast_specNorm_not_injective_add` already owns generic distance-to-singularity; do not
  independently reprove that topic or publish another version.
* `exists_norm_eq_one_and_norm_mulVec_eq_singularValues` supplies the minimizing unit vector.
  The outer product of its shifted image with its conjugate has exactly the required norm by
  `specNorm_vecMulVec` and `EuclideanSpace.norm_toLp_star`, and rank at most one by
  `Matrix.rank_vecMulVec_le`. Spectrum membership follows directly from failure of injectivity.
* The residual equivalence uses `singularValues_last_mul_norm_le` and the same existing unit
  witness. The perturbation equivalence consumes the attained minimum and the lower bound.
* For the resolvent, `singularValues_last_pos_iff_injective` detects the singular case.
  `pinv_of_isUnit` and `specNorm_pinv_of_injective` already yield the inverse norm formula;
  no new public inverse-norm bridge is added.
* For normal disks, `isStarNormal_iff_exists_eq_mul_diagonal_mul_conjTranspose` supplies unitary
  diagonalization. Existing Bauer–Fike
  `exists_norm_sub_le_pseudoConditionNumber_mul_specNorm`,
  `HasOrthonormalCols.pseudoConditionNumber_eq_one`, and
  `mem_spectrum_of_mul_eq_mul_diagonal` give the forward direction. The converse is the
  scalar perturbation `(z - μ) • 1`, using `specNorm_smul`, `specNorm_one_le`, and Mathlib's
  `spectrum.add_mem_add_iff`. Nonemptiness needed internally follows from the nonzero
  eigenvector supplied by `exists_mulVec_eq_smul_of_mem_spectrum`.

Any local algebra or spectrum transport helper is private and proof-only. No supporting
module change is currently expected; any necessary shared addition requires a design amendment.

## Placement and consumers

`NLAlib/Matrix/Perturbation/Pseudospectrum.lean` contains the five headlines, ordered as above,
with private transport preceding them. It imports the specific existing least-singular-value,
condition-number, normal-matrix, residual, and eigenvector-pairing topic files as needed.
No separate resolvent file or aggregator is introduced.

The perturbation minimum is consumed by backward-error and eigenvalue sensitivity arguments.
The closed equivalence rewrites numerical least-singular-value certificates into perturbation
statements. The unit-residual equivalence supports approximate eigenpairs and Krylov residuals.
The resolvent form supports nonnormal spectral estimates while preserving singular endpoints.
The normal form specializes these descriptions to closed spectral disks without exposing a
chosen eigenbasis. These are prospective consumers; no downstream extension is in scope.

## Sources and exclusions

The original card and both proof files were read in `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`, using `estimation-krylov-19-reviewed`:
`NLAlib/Matrix/Perturbation/Pseudospectrum.lean` and `PseudospectrumResolvent.lean`.
The atlas points to the Pseudospectra Gateway's theorems I–IV; the proof files cite
Trefethen–Embree (2005), section 2. This port keeps all five clauses but replaces the source's
complex-only first four results, truncated dimension subtraction, raw normality, redundant
unit-vector and inverse lemmas, and two-file split with native interfaces and reuse.

Verified printed sources: `[EmbreeTrefethen2001, Definition, p. 583]` prints the closed
perturbation, singular-value, and residual equivalences. `[TrefethenEmbree2005, Theorem 2.1
and discussion, pp. 16–17]` gives the open-radius equivalences and rank-one construction;
the attained endpoint form here is stated explicitly. `[TrefethenEmbree2005, Theorem 2.2]`
gives normal spectral disks; the theorem here is the closed-radius variant, including zero.
No converse characterization of normality is claimed. Bibliography and root-import updates
belong to the integrating agent.

No open-radius twins, real/complex twins, pseudospectrum wrapper definition, new broad normal
or resolvent theory, targets, programs, or numerical constants are added.

## Review questions

The integrating agent approved the five signatures and one-file placement on 2026-11-02,
before proof implementation. There are no new interfaces to register.
