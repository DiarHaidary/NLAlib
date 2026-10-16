# Poly3: analytic Chebyshev approximation on an open ellipse

**Exact design approved by root and independent bounded review, 2026-10-16.** The user approved a generic
real-input f with compatible complex holomorphic extension F. Earlier full coefficient and
inclusive degree-N conventions remain fixed. Root GO authorizes sequential implementation, starting with the coefficient-owner extension.
Read CONTRIBUTING, PORT_POLYNOMIAL, Polynomial-Series and current status. The previously
approved available-agent fallback continues.

## 1. Scope and objects

Prove canonical coefficient decay, a reusable reconstruction criterion, and the exact geometric
error for the existing truncation. Preserve holomorphy and boundedness only on the OPEN ellipse;
do not impose continuity on its outer boundary. No interpolation theorem or exponential/Jackson
approximation is included. No real-part-only result or second analytic coefficient/truncation.

| Object/interface | Home and meaning | Bridge |
|---|---|---|
| `openBernsteinEllipse ρ` | Polynomial/Approximation/BernsteinEllipse, strict focal-distance sublevel set | Open-set theorem and membership of the closed real segment, including ±1 |
| Existing `chebyshevCoeff`, `chebyshevTrunc` | Poly2 canonical RCLike objects | Complex contour/Fourier representations are proof equalities, never new coefficient definitions |
| Existing `DifferentiableOn`, `Set.EqOn`, `Metric.IsUniformApproxOn` | Holomorphy, extension agreement and bound | Raw pointwise distance constructor already available; no holomorphy bundle |

Use the standard focal-distance definition for simple openness and transparent geometry.
Joukowski remains an inline expression in the annular membership bridge, not another public
object. The valid regime is ρ>1. The definition is total: at ρ=1 or nonpositive ρ it is empty;
for 0<ρ<1 it equals the ellipse for reciprocal parameter, without any theorem claiming validity
for an analytic approximation radius less than one.

```lean
namespace NLAlib
noncomputable def openBernsteinEllipse (ρ : ℝ) : Set ℂ :=
  {z : ℂ | ‖z - 1‖ + ‖z + 1‖ < ρ + ρ⁻¹}

theorem isOpen_openBernsteinEllipse (ρ : ℝ) :
    IsOpen (openBernsteinEllipse ρ)

theorem ofReal_mem_openBernsteinEllipse {ρ x : ℝ} (hρ : 1 < ρ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : (x : ℂ) ∈ openBernsteinEllipse ρ

theorem joukowski_mem_openBernsteinEllipse {ρ : ℝ} {w : ℂ} (hρ : 1 < ρ)
    (hw : ρ⁻¹ < ‖w‖ ∧ ‖w‖ < ρ) :
    (w + w⁻¹) / 2 ∈ openBernsteinEllipse ρ
end NLAlib
```

No closed-ellipse object or full annulus-image equivalence is needed publicly. The membership
bridge suffices for contour estimates. This representation avoids a generic open-mapping detour.

## 2. Refreshed search and actual proof routes

Search Mathlib → current NLAlib → prototype. Exact ellipse/Joukowski searches found no existing
object. Current Poly2 supplies the only coefficient and truncation; reuse without aliases.

* Geometry: focal-distance strict sublevel openness follows continuity of norms. For real
  x∈[−1,1], the focal sum is exactly two, strictly less than ρ+ρ⁻¹ for ρ>1; this includes ±1.
  For nonzero w, quadratic factorizations of J(w)±1 and the parallelogram identity give
  ‖J(w)−1‖+‖J(w)+1‖=‖w‖+‖w‖⁻¹. A private real inequality then proves annular membership.
  This bypasses branchpoint/inverse-function issues entirely. Full image equality is deferred
  because no consumer needs surjectivity. The focal definition is the standard same ellipse.
* Contour deformation: `Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`
  and `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const` provide the
  annular coefficient estimate. Apply at each 1<r<ρ and take r↑ρ; no outer boundary regularity.
* Fourier: `fourierCoeff_eq_intervalIntegral`,
  `hasSum_fourier_series_of_summable` and
  `has_pointwise_sum_fourier_series_of_summable` are existing Mathlib reconstruction APIs.
  The even cosine pullback identifies negative/positive frequency pairs with the full canonical
  coefficient. No independent Fourier uniqueness or convergence proof is planned.
* Generic transport: existing `RCLike.toComplex`, `norm_toComplex`, `continuous_toComplex` and
  injectivity transfer coefficients, summability, sums and metric errors. Its real-linear map and
  continuity give a continuous-linear integral bridge if needed; do not introduce another embedding.
* Generic norm bounds for T on a real segment follow `map_T` and upstream real bounds, as in
  Poly2's transport. Refreshed exact searches repeat per file before implementation.

## 3. File sequence and placement

1. Extend existing `Polynomial/Approximation/ChebyshevCoefficients.lean` first: the general
   zero-index bound and canonical toComplex bridge below, importing the existing generic metric
   interface and RCLike embedding. These are about canonical coefficients, not analyticity.
2. New `Polynomial/Approximation/BernsteinEllipse.lean`, about 150–250 lines: the geometric
   definition and three geometry facts above. Norm-factorization helpers remain private.
3. New `Polynomial/Approximation/ChebyshevSeries.lean`, about 250–450 lines: the canonical
   Fourier representation and reusable reconstruction criterion, with no analytic/ellipse import.
4. New `Polynomial/Approximation/AnalyticCoefficients.lean`, about 300–500 lines: positive-index
   analytic decay, importing Series for its genuine Fourier representation bridge and Geometry.
5. New `Polynomial/Approximation/AnalyticApproximation.lean`, about 200–350 lines: analytic
   truncation error and affine existence, consuming generic Series and AnalyticCoefficients.

This is four new files plus an owner extension. Series precedes AnalyticCoefficients because its
representation lemma is a shared mathematical bridge and has no analytic dependency; this avoids
an import cycle and duplicate private Fourier machinery. No scalar file imports Matrix or Krylov.

Keep individual proofs under about 80 lines using private helpers. Cross-file machinery may not
be exported merely to bypass private visibility. If shared generic circle infrastructure is truly
required, inventory exact reuse first and amend the design with its ForMathlib home before a new
public lemma or file. No stage-shaped helper dump is authorized. File budgets are estimates, not
permission to exceed 1000 lines or hide a new persistent interface.

## 4. Exact coefficient signatures

All declarations namespace NLAlib. The complex extension only identifies real-interval values;
f need not be globally continuous or have a holomorphic codomain structure. The existing metric
bound means exactly ‖F(z)‖≤M; its nonempty domain implies M≥0, so no redundant M≥0 is added.

```lean
variable {𝕜 : Type*} [RCLike 𝕜]

theorem norm_chebyshevCoeff_zero_le {f : ℝ → 𝕜} {M : ℝ}
    (hM : Metric.IsUniformApproxOn f (fun _ => 0) (Set.Icc (-1 : ℝ) 1) M) :
    ‖chebyshevCoeff f 0‖ ≤ M

theorem toComplex_chebyshevCoeff (f : ℝ → 𝕜) (k : ℕ) :
    RCLike.toComplex (chebyshevCoeff f k) =
      chebyshevCoeff (fun x => RCLike.toComplex (f x)) k

theorem norm_chebyshevCoeff_le_of_open_ellipse
    {f : ℝ → 𝕜} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun x => RCLike.toComplex (f x))
      (fun x : ℝ => F (x : ℂ)) (Set.Icc (-1 : ℝ) 1)) {k : ℕ} (hk : 0 < k) :
    ‖chebyshevCoeff f k‖ ≤ 2 * M / ρ ^ k
```

The zero bound needs no continuity, holomorphy or integrability premise:
`intervalIntegral.norm_integral_le_of_norm_le_const` bounds its total integral by πM.
Nonnegative M follows from the nonempty segment. Analytic consumers derive its pointwise
hypothesis from hExt, segment membership and the ellipse bound. Positive coefficients use the
contour radius estimate and limit. No analytic-zero twin is exported.

The toComplex bridge is unconditional, including nonintegrable weighted integrands. Use
`LinearIsometry.intervalIntegral_comp_comm` with the isometry from the EXISTING embedding;
conditional continuous-linear-map integral commutation is insufficient here. Its multiplication
and real-scalar preservation commute the remaining coefficient expression. This bridge is used
by both generic reconstruction and analytic coefficient decay, so it is public at the owner.

## 5. Reconstruction and approximation signatures

Propose the reusable reconstruction theorem under continuity and summable coefficient norms.
This uses existing hypotheses and supports later interpolation/Jackson, with little extra proof
over the analytic-only theorem: summability is precisely the Fourier convergence input. There
is no second public analytic reconstruction theorem; the error proof applies this criterion after
analytic decay establishes summability and hExt gives interval continuity.

The one additional representation bridge belongs to ChebyshevSeries. Locally activate existing Mathlib
`Polynomial.instTwoPiPos` (owner `Mathlib.Analysis.Polynomial.Fourier`); do not expose a redundant instance parameter or
add a global circle instance. The period of `fourier` is determined by its circle argument.

```lean
theorem fourierCoeff_cosinePullback_eq_chebyshevCoeff
    {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) (k : ℤ) :
    fourierCoeff (fun θ : AddCircle (2 * Real.pi) => f ((fourier 1 θ).re)) k =
      chebyshevCoeff f k.natAbs / (if k = 0 then 1 else 2)
```

This represents both positive and negative frequencies of the even cosine pullback using the
ONE coefficient; it is not another coefficient definition. AnalyticCoefficients uses it for
contour deformation, while Series uses it for reconstruction. Its complex-only codomain reflects
Mathlib's Fourier API; the unconditional canonical toComplex bridge supplies generic transport.
No circle-function object is defined publicly. Circle continuity/parity helpers remain private.

```lean
theorem hasSum_chebyshevCoeff_mul_eval_T
    {f : ℝ → 𝕜} (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hs : Summable (fun k : ℕ => ‖chebyshevCoeff f k‖)) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => chebyshevCoeff f k *
      (Polynomial.Chebyshev.T 𝕜 (k : ℤ)).eval (x : 𝕜)) (f x)

theorem isUniformApproxOn_chebyshevTrunc_of_open_ellipse
    {f : ℝ → 𝕜} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun x => RCLike.toComplex (f x))
      (fun x : ℝ => F (x : ℂ)) (Set.Icc (-1 : ℝ) 1)) (N : ℕ) :
    Metric.IsUniformApproxOn
      (fun x : ℝ => (chebyshevTrunc f N).eval (x : 𝕜)) f (Set.Icc (-1 : ℝ) 1)
      (2 * M / (ρ ^ N * (ρ - 1)))

theorem exists_degree_le_isUniformApproxOn_of_open_ellipse_interval
    {f : ℝ → 𝕜} {F : ℂ → ℂ} {a b ρ M : ℝ} (hab : a < b) (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => RCLike.toComplex (f (((b - a) * t + b + a) / 2)))
      (fun t : ℝ => F (t : ℂ)) (Set.Icc (-1 : ℝ) 1)) (N : ℕ) :
    ∃ p : 𝕜[X], p.degree ≤ (N : WithBot ℕ) ∧
      Metric.IsUniformApproxOn (fun x : ℝ => p.eval (x : 𝕜)) f (Set.Icc a b)
        (2 * M / (ρ ^ N * (ρ - 1)))
```

Affine transport is a short consumer: apply the canonical truncation to the pulled-back function,
then compose by the affine polynomial sending [a,b] to [−1,1]. No new affine-truncation object.
N=0 is included; the tail begins at N+1 and has exactly the denominator ρ^N(ρ−1).
M=0 is allowed and gives exact zero error. Reconstruction includes endpoints and arbitrary
RCLike values, not only real parts. No existence corollary on the unit interval duplicates the
explicit canonical theorem: users already have the truncation and its Poly2 degree bound.

## 6. Source verification and prototype relation

Verified primary source: official author/Chebfun ATAP Chapter 8,
https://raw.githubusercontent.com/chebfun/ATAP/master/chap8.m . Theorem 8.1 explicitly assumes
analyticity/boundedness on OPEN Eρ and proves a0≤M and positive ak≤2Mρ^(-k). Its proof first
uses a closed smaller annulus and then a radius limit. Theorem 8.2, Eq. (8.2), gives projection
error 2Mρ^(-N)/(ρ−1) for every N≥0. Cite Trefethen2019 with these verified theorem numbers;
no 2019 printed page is claimed from the local 2018 draft. Interpolation's factor4 is different
and deliberately outside this stage. Generic RCLike transport is a stated generalization.

Prototype files read: FunctionApproximation/{BernsteinEllipse,AnalyticCoefficients,AnalyticFourier,
AnalyticApproximation,ChebyshevCoefficients} and ForMathlib/Analysis/FourierCircle. Reuse contour/radius-limit mathematics, Fourier pairing and geometric-tail proofs. Replace
three coefficient spellings and real-part truncation by genuine representation bridges to Poly2.
Prototype reconstruction assumes analyticity; the continuity-plus-summability theorem abstracts
its actual Fourier convergence argument. Do not port unrelated circle/grid/Jackson helpers.

## 7. Risks, review and validation contract

Main risks are the Joukowski focal-norm identity, canonical contour normalization, absolute summability of the
paired integer Fourier series, and generic transport through the existing embedding. All have
identified upstream routes and the implemented signatures passed target/capped checks. No proof completion is inferred
from the source-complete prototype. Review the generic reconstruction scope and file budgets;
if the missing infrastructure becomes substantial, root assesses a smaller staged split before
new public machinery or weakened hypotheses. Do not add boundary continuity to ease the proof.
After root GO: one file at a time, refreshed searches and independent read-back, sequential capped
two-thread target/single-file checks, then one mechanical full-gate handoff with genuine mappings.
No commit/push or concurrent builds by the proof agent.

Review note: generic HasSum reflection later uses the embedding's isometry/inducing property,
not injectivity alone; `norm_toComplex` supplies the required isometry.

## Owner extension read-back (2026-10-16)

Exactly two public declarations were appended to ChebyshevCoefficients. The zeroth coefficient
norm is at most any Metric uniform norm bound M on the closed real segment, with no continuity,
analyticity or integrability assumption. The canonical coefficient commutes unconditionally with
the existing RCLike.toComplex embedding, including total-integral nonintegrability cases.
Imports added: existing RCLike.ToComplex and generic UniformApproximation; prior API/proofs
were preserved. The proof locally constructs the embedding's real linear isometry from
`norm_toComplex` and uses unconditional `LinearIsometry.intervalIntegral_comp_comm`.
Target build (2717 jobs) and capped Lean check passed without warnings; logs:
`/tmp/nlalib-poly3-checks/01-coefficient-bridges-build.log`, `01-coefficient-bridges-lean.log`.
Owner extension independently approved; geometry completed in the next step.

## Geometry read-back (2026-10-16)

Exactly four public declarations implement the focal-distance ellipse, its unconditional
openness, inclusion of the full closed segment for ρ>1, and strict Joukowski annulus membership.
Both endpoints are included with focal sum two strictly below ρ+ρ⁻¹. Three private algebra
helpers prove the radius inequality and Joukowski focal-norm identity through quadratic
factorizations; no open-mapping/branchpoint assumption or extra public object is needed.
No closed ellipse, public J or image-surjectivity equivalence was added. Fresh searches found
no upstream/current object overlap. Target build (1867 jobs) and capped Lean check passed
without warnings; logs `/tmp/nlalib-poly3-checks/02-ellipse-build.log`, `02-ellipse-lean.log`.
Owner extension independently approved; geometry independently approved. 

## Series read-back (2026-10-16)

Exactly two public declarations implement the reviewed dictionary and reconstruction signatures.
The dictionary covers every integer frequency: the index is natAbs and only the zero coefficient
escapes division by two. The generic reconstruction assumes only interval continuity and
summability of canonical coefficient norms, with endpoints recovered by arccos. Private proofs
use evenness, full-period reflection, Mathlib pointwise summable Fourier reconstruction and
positive/negative frequency pairing. Generic transport uses the existing unconditional coefficient
bridge and the embedding's linear isometry; HasSum is reflected by its inducing limit criterion
and finite-sum preservation, never by injectivity alone. No ellipse/analytic import, extra public
circle infrastructure or additional hypothesis was needed. The file has 304 lines and all proofs
are below the stage proof-length budget. Target build (2975 jobs) and capped Lean check passed
without warnings; logs `/tmp/nlalib-poly3-checks/03-series-build.log`, `03-series-lean.log`.
Owner extension/geometry independently approved; Series independently approved. 

## Analytic coefficient read-back (2026-10-16)

Exactly one public theorem proves the approved positive-index bound ‖a_k‖≤2M/ρ^k for generic
RCLike f and its compatible complex extension. Hypotheses remain open-ellipse holomorphy, the
shared Metric bound and EqOn agreement, with no added M≥0, continuity or integrability premise.
Private contour expressions are related to the public canonical Fourier dictionary. Deformation
uses each closed annulus 1≤‖w‖≤r<ρ inside the OPEN ellipse, then its exact norm estimate; the
limit r↑ρ retains the original radius without outer-boundary values. Generic transport uses the
unconditional canonical toComplex bridge and EqOn on cosine values. No analytic-zero twin or
public contour object/helper was added. All private proofs remain under 80 lines. Target build
(3009 jobs) and capped Lean check passed without warnings; logs:
`/tmp/nlalib-poly3-checks/04-analytic-coefficients-build.log`, `04-analytic-coefficients-lean.log`.
Files 1–3 independently approved; coefficient-decay independently approved. 

## Final approximation read-back and proof-stage handoff (2026-10-16)

The final two public statements match the exact reviewed signatures. The existing canonical
degree-N truncation approximates f uniformly on the closed segment with error
2M/(ρ^N(ρ−1)); affine pullback/composition gives a degree≤N polynomial on every a<b interval
with the same bound. Both are generic RCLike, include N=0 and M=0, and retain only open-ellipse
holomorphy, Metric boundedness and compatible-extension EqOn hypotheses. Generic reconstruction
and analytic coefficient decay establish the tail; Mathlib's geometric HasSum and norm-majorant
bound sum it exactly. Affine rescaling introduces no object or extra hypothesis. No duplicate
unit-interval existence or analytic reconstruction theorem was exported.
Target build (3033 jobs) and capped Lean check passed without warnings; logs:
`/tmp/nlalib-poly3-checks/05-analytic-approximation-build.log`, `05-analytic-approximation-lean.log`.

Proof work is complete: four new topic files plus the coefficient-owner extension, eleven public
declarations total (one geometric definition and ten theorems). All five proof steps have independent
approval, including final approximation and its proof-stage read-back. All five sequential target/capped checks passed
without warnings. No active build, sorry, strengthened hypothesis or unapproved public plumbing
API remains. Mechanical registration, approved vocabulary/deviation documentation, genuine
prototype mappings, full gates/reuse and extraction are handed off separately; their success and
any commit are not claimed here. The focal definition differs in invalid-parameter totalization
from the prototype annulus-image object, and full image equality was deliberately not claimed.

## Period-witness reuse amendment (2026-10-16)

Duplicate inspection and extraction exposed two generated public period-Fact declarations
from local instances in Series and AnalyticCoefficients. Making them private alone failed:
Lean's public Fourier statement cannot elaborate through a private instance. The reviewed final
solution reuses existing Mathlib `Polynomial.instTwoPiPos`, registered only locally by an
attribute in each file. Series imports its owner `Mathlib.Analysis.Polynomial.Fourier`, which
publicly imports AddCircle; AnalyticCoefficients receives it through Series. This modest scalar
dependency adds no upward layer import, global instance, new declaration or statement hypothesis.
The failed private-only approach is superseded; no duplicate witness is hidden or filtered.
The intended stage contribution remains eleven public declarations; refreshed extraction contains 3510 public declarations rather than the initial 3512. Prior proof bodies
and mathematical statements are unchanged.

Sequential affected-target builds (2981/3012 jobs) and capped single-file checks passed without
warnings. Final logs: `/tmp/nlalib-poly3-checks/06-period-reuse-series-{build,lean}.log` and
`06-period-reuse-coefficients-{build,lean}.log`. Mechanical revalidation and refreshed extraction passed as recorded below.

## Final mechanical validation (2026-10-16)

All five proof steps and eleven intended public declarations are independently approved: one
ellipse definition and ten theorems across four new modules plus the coefficient-owner extension.
Four root imports, one approved vocabulary row and an additions-not-deviation note are recorded.
Exactly two prototype approximation headlines receive genuine successor dispositions: unit-interval
existence becomes the constructive canonical-truncation bound, and affine existence generalizes
to RCLike norm/Metric error. Notes explicitly retain changed interfaces and focal-domain hypotheses.
All previous mappings, including the Poly2 coefficient, are unchanged. No ellipse object alias,
contour/real-part coefficient or truncation alias, or unproved image-set equivalence is claimed.

Final-source sequential two-thread full build passed (3907 jobs, zero warnings), both root checks
passed, audit checked 7398 declarations with zero violations, and 14 linters checked 5069 plus
2329 generated declarations with zero errors. Duplicate reporting found 4667 theorems and zero
classes after upstream period-witness reuse. References checked 56 keys/40 asymptotic forms;
constants checked 25 bounds; KaTeX checked 5516 docstrings/18168 spans. Eleven metadata tests
and all eleven reuse targets passed. Prior target/capped checks, including the affected-source
period amendment, passed. Logs: `/tmp/nlalib-poly3-checks`; the superseded initial public-witness
pass is kept separately in `initial-public-fact-pass`. No redundant browser or full-stage run.

Fresh extraction `/tmp/nlalib-poly3-explore.json` contains 313 modules/3510 public declarations,
exactly eleven above Poly2. All 313 source hashes match, all eleven targets are proved, and no
new generated public period witnesses remain. Strict unchanged Explorer build passes with
312 visible modules, 254 results and 172 enriched definitions; Rates remains 32 rows/nine guarantees/
three families. No Explorer/UI/Rate edits were made. The extraction records the pre-commit source
snapshot; root handles commit and restamp. No active validation process, validation-agent commit
or push remains.

The final read-back retains the original open-ellipse holomorphy, Metric boundedness and EqOn
extension interface, arbitrary RCLike values, endpoints and N=0/M=0. Zero-coefficient control is
generic; positive coefficients obey 2M/ρ^k; continuity plus coefficient summability reconstructs
f; the inclusive truncation has error 2M/(ρ^N(ρ−1)), with affine degree≤N existence as consumer.
No outer-boundary continuity, extra integrability premise or real-part-only approximation was
introduced. Primary Chapter 8 theorem numbers and the published-page verification limitation are
recorded above. The focal ellipse is intentionally total with reciprocal behavior for 0<ρ<1;
all analytic rates require ρ>1. Only annulus membership, not full image equality, is exported.
No proof edits were made by mechanical validation; the reviewed period-witness amendment was
performed and checked by the proof owner before the final full-gate rerun.
