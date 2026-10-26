# Design note: hidden-rotation lower bounds — the batched Krylov coupling, Shamir's $\Omega(\kappa\log(1/\varepsilon))$ and the two-pass $\Omega(k/\varepsilon)$ (stage LB-C)

Status: approved (APPROVE = a, OQ1–OQ10 all decided (a), 2026-10-26) and revised after the Fable
review `~/nlalib-harness/reports/Review-Fable-LBC-Design.md` (items 1–5: K7's proof plan and three
sub-lemma families, GZ2–GZ4 and KB2–KB3, the public stabilizer randomizer of `HiddenHaar.lean`,
SH6's constant, SH1's exponent; no approved statement changed except SH6, strengthened as item 4
asks). Branch `design/lbc` (worktree `~/nlalib-design-lbc`, from `origin/main` 79f8cc2). Decision
sheet: `~/nlalib-harness/state/decisions/LB-C.json`. Targets:
`~/nlalib-harness/pilot/lbc-targets.json` (57 statements).
Sources read in full: Shamir, *A Simple Complexity Lower Bound for Solving Ax=b*, arXiv:2609.10874v1
(LaTeX source; Theorem 1, Lemmas 1–4, §3.2–3.3); the research note
`~/nlalib-harness/reports/OP5-TwoPassMinimax.md` (harness commit 6398a6b: Theorems A, C,
Corollary B, Proposition E, Lemma C, gaps G1–G3, missing pieces M1–M5); the LB-A library on
`origin/main` (`NLAlib/LowerBounds/QueryModel/{Basic,Yao,DeferredDecision,HiddenHaar}.lean`,
`RandomMatrix/Haar/Stabilizer.lean`, `LowerBounds/LowRank/RangeRecovery.lean`) and its note
`docs/design/Probability-MatvecQueryModel.md`, with Fable's LB-A review items 3 and 6.

Checks on the skeleton (all run on this branch): `lake build --wfail NLAlib` succeeds (four new or
extended `NLAlib` modules, definitions only); `lake build NLAlibScaffold` gives exactly 57
`declaration uses sorry` warnings and nothing else; `scripts/check_rules.py --files` (0 errors;
the one warning, D7 on `IsMeasurable.truncate`, predates this stage), `check_refs.py`,
`check_constants.py`, `check_latex.mjs` (KaTeX) and both `mk_all --check` are clean;
`bin/check-skeleton --strict` (rule G3): 57 targets, 0 names missing an import, 0 unresolved; the
dispatcher's `locate` finds all 57 targets, which are exactly the sorried declarations. The
extraction-based name check (N1–N18) was not run; names for review are in §9.

## 0. Summary

| | |
|---|---|
| Framework (new) | the pass model `QueryAlgorithm.IsPassStructured` (+ `comapResponse`, `mapOutput`); the hidden-rotation oracle $\mathbf{x} \mapsto (\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$ and its simulation on `twoSidedMulVec U`; the conclusion interface `IsKrylovCoupling`; the **Krylov coupling theorem** K7: a $p$-pass algorithm's rotated output lies a.s. in $\mathcal{K}_{p+1}(\mathbf{D}, [\mathbf{U}^{\mathsf{H}}\mathbf{B}, \mathbf{G}])$, $\mathbf{G}$ standard Gaussian with one column per query and output column, independent of $\mathbf{U}^{\mathsf{H}}\mathbf{B}$ |
| First application | Shamir's Theorem 1 with explicit constants: $\kappa\log\frac{1}{4\varepsilon} \le 2(q + 1)$ for every randomized adaptive algorithm with $q$ products that solves every symmetric system with spectrum in $[-\kappa,-1]\cup[1,\kappa]$ to relative residual $\varepsilon$ w.p. $\ge 2/3$, in every dimension $n \ge 20(q+3)^2$ (SH5); Shamir's form $\kappa\log(1/\varepsilon) \le 4(q+1)$ for $\varepsilon \le e^{-4}$ (SH6); the strong-oracle, spectrum-known form (SH4); Lemmas 1, 2 (P4, P5), Lemma 3 (H1/H2 of LB-A), Lemma 4 (K7) |
| Second application | OP5 (complete, [derived]): two-pass $(1+\varepsilon)$ Frobenius rank-$k$ approximation needs $q > k/(6400\varepsilon)$ products (L7), one pass too (L8), and two-pass $(1+\varepsilon)\sigma_{k+1}$ spectral approximation needs $q > m/676 - k$, proportional to the dimension, for every $\varepsilon \le 0.1$ (L9); with the distributional Theorems A, C (L4, L5) and the Yao form B(i) (L6) |
| New definitions (in `NLAlib`, written, build `--wfail`) | `QueryAlgorithm.IsPassStructured`, `QueryAlgorithm.comapResponse`, `QueryAlgorithm.mapOutput` (in `LowerBounds/QueryModel/Basic.lean`); `hiddenRotationOracle`, `QueryAlgorithm.hiddenRotationDecode`, `QueryAlgorithm.hiddenRotationSimulation`, `IsKrylovCoupling` (new `LowerBounds/QueryModel/HiddenRotation.lean`); `IsChebyshevTwoIntervalSpectrum` (new `Polynomial/Chebyshev/TwoInterval.lean`); `equispacedLevelSpectrum` (new `LowerBounds/LowRank/FewPasses.lean`) |
| Statements | 57 sorried: S 31, M 23, L 2, H 1, in 10 scaffold files (§3) |
| What is new over LB-A | LB-A has the *invariance* (H2: given the transcript, $\mathbf{U}$ is Haar on the complement of what was revealed). New here: the pass predicate (OP5 M1); the reordering inside a pass is part of K7's proof (M2); the simulation with $\mathbf{D}$ (M3, Fable LB-A item 6); Gaussianization (M4: GZ1–GZ3, polar factor independent of the Gram matrix, also in a subspace; GZ4, the Haar frame law of a subspace); the degree bookkeeping (M5) — together the coupling K7 —, the two-interval Chebyshev certificate, the projected-$\chi^2$ tail, the level decomposition of Krylov residuals, and both applications |
| Kroó–Pinkus | not needed: Lemma 2 is proved with the explicit Chebyshev two-interval certificate (P1, P5), at most $q + 2$ points instead of $q + 1$ |
| Staging | one design, one skeleton; dispatch as two sub-stages by `--only`: **LB-C1** framework + Shamir (44 targets: Q*, Y3, K*, GZ1–GZ4, P1–P8, KB1–KB3, C1–C2, SH*), **LB-C2** LRA (13 targets: P9, L*), which needs only K7, K6, Q*, Y3 from C1 |
| Open questions | 10 (§10), each with a recommendation |

## 1. Scope

**In.** (i) A batched query model on the existing `QueryAlgorithm`: passes as a monotone map of
rounds, queries depending only on earlier passes; weaker-oracle and output maps. (ii) The
hidden-rotation oracle, its two-sided simulation on $\mathbf{U}$, and the Krylov coupling
theorem for every fixed $\mathbf{D} \in \mathbb{R}^{n\times n}$ (not necessarily symmetric or
diagonal), every fixed initial block $\mathbf{B}$, any output width, any number of passes —
stated so that linear systems, low-rank approximation and (later) matrix functions and trace
estimation consume the interface `IsKrylovCoupling` without the query model. (iii) The polynomial
side: the two-interval Chebyshev dual certificate and minimax value, Shamir's Lemmas 1 and 2,
equispaced finite differences; the hard-spectrum predicate and its existence. (iv) Shamir's
Theorem 1 (strong oracle, spectrum known; matrix–vector oracle; explicit constants). (v) OP5's
Theorem A, Corollary B(i), B(iii), Theorem C, in tail form with OP5's constants.

**Out** (§11, with what each needs): OP5 Proposition E ($p$ passes, constant $\asymp 4^{-p}$:
[derived], but its absolute constant $C$ is not explicit), the expectation forms of A and B(ii),
the EW Conjecture 7.1(b) rate corollary, the $\sqrt{\kappa}\log(1/\delta)$ corollary for
first-order methods on quadratics (needs a first-order oracle model), two-sided pair queries with
exact per-side budgets in the coupling, the non-symmetric $\mathbf{U}\mathbf{D}\mathbf{V}^{\mathsf{H}}$
(Golub–Kahan) coupling, trace / matrix-function applications, the `exists_forall_` asymptotic
forms (OQ6). Conjectures of OP5 ($\Theta(k/(p^2\varepsilon))$ for $p$ passes; the one-pass gap
$k/\varepsilon$ vs $k/\varepsilon^2$; the exact EW 7.1(b) factor) stay in the research note.

## 2. Objects

### 2.1 Passes (`NLAlib/LowerBounds/QueryModel/Basic.lean`, written)

```lean
structure IsPassStructured (alg : QueryAlgorithm Q R q β) (pass : ℕ → ℕ) : Prop where
  monotone : Monotone pass
  query_eq : ∀ i < q, ∀ h h' : Fin i → R,
    (∀ j : Fin i, pass j < pass i → h j = h' j) → alg.query i h = alg.query i h'
def comapResponse (f : R' → R) (alg : QueryAlgorithm Q R q β) : QueryAlgorithm Q R' q β
def mapOutput (g : β → β') (alg : QueryAlgorithm Q R q β) : QueryAlgorithm Q R q β'
```

A pass is a block of queries fixed before any of its responses — OP5's batch: "a batch's
coordinates are revealed before its products" is exactly `query_eq` applied to the hidden oracle,
whose response contains both. A $p$-pass algorithm is `IsPassStructured pass` plus
`∀ i < q, pass i < p` (a hypothesis, so `pass` may be any schedule; seeded families may use a
seed-dependent schedule, L6–L9). Bridges: `pass = 0` is `IsNonAdaptive` (Q25), `pass = id` is
every algorithm (Q24). The count of a pass is not a field: the coupling spends one Gaussian column
per round, so only the total $q$ matters. Fable's LB-A item 3 (budgets over unreachable
transcripts) does not arise: rounds are a fixed number $q$, and zero queries still consume a
column. Mathlib has no query model (searched for LB-A).

### 2.2 Hidden rotation and Krylov couplings (`NLAlib/LowerBounds/QueryModel/HiddenRotation.lean`, new, written)

```lean
def hiddenRotationOracle (U D : Matrix n n 𝕜) (x : n → 𝕜) : (n → 𝕜) × (n → 𝕜) :=
  ((U * D * Uᴴ) *ᵥ x, Uᴴ *ᵥ x)
def QueryAlgorithm.hiddenRotationSimulation (D : Matrix n n 𝕜)
    (alg : QueryAlgorithm (n → 𝕜) ((n → 𝕜) × (n → 𝕜)) q β) :
    QueryAlgorithm ((n → 𝕜) × (n → 𝕜)) ((n → 𝕜) × (n → 𝕜)) (2 * q) β
structure IsKrylovCoupling (μ) (D : Matrix n n ℝ) (s : ℕ) (G₀ : Ω → Matrix n c ℝ)
    (V : Ω → Matrix n k ℝ) (G : Ω → Matrix n c' ℝ) : Prop where
  hasLaw_gaussianMatrix : HasLaw G (gaussianMatrix n c') μ
  indepFun : IndepFun G₀ G μ
  ae_range_le : ∀ᵐ ω ∂μ, LinearMap.range (V ω).mulVecLin ≤
    blockKrylovSpace D (Matrix.fromCols (G₀ ω) (G ω)) s
```

The simulation is the Gram simulation with $\mathbf{D}$ in the odd rounds (round $2l$:
$(\mathbf{0}, \mathbf{x}_l) \mapsto \mathbf{U}^{\mathsf{H}}\mathbf{x}_l$; round $2l+1$:
$(\mathbf{D}\mathbf{v}_l, \mathbf{0}) \mapsto \mathbf{U}\mathbf{D}\mathbf{v}_l$), so H2 applies with
revealed vectors $\mathbf{v}_l$, $\mathbf{D}\mathbf{v}_l$ — exactly Shamir's $\mathcal{L}_t$. It is
a new definition next to `gramSimulation`, not a refactor of it (OQ8). `IsKrylovCoupling` is the
conclusion interface (§5.4 "a conclusion is an interface"): every application states its
Gaussian step against it and never sees the query model. Depth convention: `blockKrylovSpace D G s`
has $s$ blocks, $[\mathbf{G}, \mathbf{D}\mathbf{G}, \dots, \mathbf{D}^{s-1}\mathbf{G}]$; OP5 and the
maintainer's sketch index by degree ($\mathcal{K}_2 = \operatorname{span}(\mathbf{G},
\mathbf{D}\mathbf{G}, \mathbf{D}^2\mathbf{G})$ is our depth 3). The a.s. quantifier is needed:
$\mathbf{U}$ is orthogonal only almost surely.

### 2.3 Hard spectra

`IsChebyshevTwoIntervalSpectrum κ s M d` (`Polynomial/Chebyshev/TwoInterval.lean`, new, written):
every $d_i$ is one of $\pm\sqrt{\xi_j}$ ($\xi_j$ the Chebyshev extrema of $[1,\kappa^2]$ at degree
$\lfloor s/2\rfloor$), each taken at least $\frac{\lvert n\rvert}{4}\frac{\omega_j}{2\tau} + M$
times. It is the two-interval Chebyshev measure discretized with a margin — Shamir's
$m_s = \lceil N w_s\rceil + \lceil CT\rceil$, with $N = n/4$ and the explicit weights instead of
Kroó–Pinkus weights. A predicate plus an existence lemma (P8) rather than an explicit definition
(OQ4): the theorems take it as a hypothesis, and the headline SH5 hides it.

`equispacedLevelSpectrum k m p : k ⊕ (Fin (p+1) × m) → ℝ` (`LowerBounds/LowRank/FewPasses.lean`,
new, written): $p + 2$ on the head, $j + 1$ on tail level $j$; for $p = 2$ it is OP5's
$\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m, 3\mathbf{I}_m)$. Defined for all
$p$ so that Proposition E (deferred) reuses it; all statements here are at $p = 2$. The dimension
is the index type $k \oplus (\{0,1,2\}\times m)$, so the LRA lower bounds are stated in that
dimension $n = k + 3m$ (OQ5).

CONTRIBUTING §5.3 gets three rows (passes; hidden rotation and Krylov coupling; hard spectra), in
this commit. No Mathlib deviation (no Mathlib counterpart exists).

## 3. Statements

The exact Lean signatures are in the skeleton; each docstring has the statement in LaTeX, the
citation and a `Proof:` line; the targets file has a worker outline per declaration. Tables
list ids, difficulty, dependency wave and prerequisites.

### 3.1 Query model additions (Q14–Q25, Y3)

Q14–Q17: `run_comapResponse : (alg.comapResponse f).run O = alg.run (f ∘ O)`, `run_mapOutput`
and the history forms. Q18–Q21: measurability of both constructions (single and seeded).
Q22–Q23: they keep the pass structure. Q24 `isPassStructured_id`, Q25
`isPassStructured_zero_iff_isNonAdaptive`. Y3
`IsMeasurableFamily.exists_le_measureReal_run_mem_of_forall`: Yao's worst-case form with the
hypothesis only for the members `alg s` of the family. LB-A's Y2 quantifies over *all*
measurable deterministic algorithms, which is useless for a class bound (a two-pass lower bound
does not hold for adaptive algorithms); Y3 is the general form and Y2 its corollary.

### 3.2 The Krylov coupling (K1–K8, KB2–KB3, GZ1–GZ4)

**K7** `QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_of_hasLaw_haarFrame`:
hypotheses `hpass : alg.IsPassStructured pass`, `hp : ∀ i < q, pass i < p`, `alg.IsMeasurable`,
any `D : Matrix n n ℝ`, `B : Matrix n c ℝ`, `HasLaw U (haarFrame n n) μ`, an auxiliary
`HasLaw Z (gaussianMatrix n (Fin q ⊕ k)) μ` with `IndepFun U Z μ`; conclusion
`∃ G : Ω → Matrix n (Fin q ⊕ k) ℝ, IsKrylovCoupling μ D (p + 1) (fun ω => (U ω)ᴴ * B)
(fun ω => (U ω)ᴴ * alg.run (hiddenRotationOracle (U ω) D)) G`.

* Why an auxiliary $\mathbf{Z}$: the coupled Gaussian is built from $\mathbf{U}$ *and* fresh
  randomness (Shamir's $\mathbf{a}_t$, $R_t$; OP5's $\mathbf{H}$). Asking the space to carry it
  keeps the conclusion on the given $\Omega$ (no "there is an extension" in the statement);
  consumers whose event depends on $\mathbf{U}$ only extend $\Omega$ by a product in their proof
  (SH2, L4). OQ3.
* Why $\mathbf{B}$: for a linear system the algorithm knows $\mathbf{b}$, so $\mathbf{U}$ is
  revealed on $\mathbf{U}^{\mathsf{H}}\mathbf{b}$ from the start; the coupled $\mathbf{G}$ must be
  independent of $\mathbf{U}^{\mathsf{H}}\mathbf{b}$ (Shamir's $\mathbf{h}_s$ step needs it), which
  holds only if $\mathbf{U}^{\mathsf{H}}\mathbf{b}$ is put in the revealed space $\mathcal{L}_0$.
  $\mathbf{B}$ is fixed (deterministic); a random $\mathbf{b}$ independent of $\mathbf{U}$ is
  handled by freezing. The algorithm need not know $\mathbf{B}$.
* Depth: $\mathcal{L}_j \subseteq \mathcal{K}_{j+1}$ after pass $j$ (OP5 Lemma C(b)); the output
  is one more block with no products, so it lies in $\mathcal{L}_p + \operatorname{range}
  \mathbf{G}_{\mathrm{out}} \subseteq \mathcal{K}_{p+1}$. One query per pass ($p = q$) gives
  Shamir's Lemma 4 with a separate output: $\mathbf{D}\hat{\mathbf{v}} \in
  \mathbf{D}\mathcal{K}_{q+1}$, residual polynomials of degree $q + 1$ (his $T$ is our $q + 1$,
  since his output is his last query).
* Truth in degenerate cases: $q = 0$ (no passes needed, depth 1: the output is fixed, and lies in
  $\operatorname{range}[\mathbf{U}^{\mathsf{H}}\mathbf{B}, \mathbf{G}_{\mathrm{out}}]$ by the
  output step); $k$, $c$ empty; $\mathbf{D}$ arbitrary (no symmetry used: Shamir's induction never
  uses it); a pass wider than $\dim\mathcal{L}^{\perp}$ (the coupled block is then the fresh
  Gaussian block itself, whose compression spans $\mathcal{L}^{\perp}$ a.s.). Adaptivity inside
  a pass is excluded by `query_eq`; without it the degree grows per query (OP5 §3.2 "Where it
  would fail"), which is the $p = q$ case.
* Proof (revised after Fable's review, item 1; OP5 Lemma C with three repairs). It runs on an
  **augmented simulation** $\mathcal{A}^+$ against `twoSidedMulVec U` (a private definition in the
  proof), not on `hiddenRotationSimulation`'s interleaved order: (i) $\lvert c \rvert$ left rounds
  $(\mathbf{0}, \mathbf{B}\mathbf{e}_a)$ first — $\mathbf{U}^{\mathsf{H}}\mathbf{B}$ is not in H2's
  revealed set otherwise, and the stabilizer would not fix it; (ii) per pass, the left rounds of
  all its queries (the reordering M2, licensed by `query_eq`), then $b_j$ **dummy left rounds**
  for a frame $\mathbf{Q}_j$ of width $b_j$ in $(\mathbf{U}\mathcal{L}_j)^{\perp}$ that contains the
  new directions of the pass, then its right rounds; (iii) the output as a last pass with dummy
  rounds and no right rounds. The padding columns of $\mathbf{Q}_j$ must be revealed: a frame
  padded by unrevealed vectors makes $\mathbf{G}_{j+1}$ depend on $\mathbf{U}$ off
  $\mathcal{L}_{j+1}$ and breaks the Haar invariant (OP5's alternative, fresh Gaussian columns
  for the padding, needs a random frame width). Coupled block: tall pass ($b_j \le d_j =
  \dim\mathcal{L}_j^{\perp}$) $\mathbf{G}_j = (\mathbf{I} - \mathbf{E}_j)\mathbf{Z}_j +
  \mathbf{U}^{\mathsf{H}}\mathbf{Q}_j((\mathbf{E}_j\mathbf{Z}_j)^{\mathsf{H}}
  \mathbf{E}_j\mathbf{Z}_j)^{1/2}$ with $\mathbf{E}_j$ the projector onto $\mathcal{L}_j^{\perp}$;
  wide pass ($b_j > d_j$) $\mathbf{G}_j = \mathbf{Z}_j$ (Fable's $\mathbf{P}\mathbf{Z} +
  (\mathbf{U}^{\mathsf{H}}\mathbf{E})(\mathbf{E}_0^{\mathsf{H}}(\mathbf{I} - \mathbf{P})\mathbf{Z})$
  also works; any orthogonal map of $\mathcal{L}_j^{\perp}$ does, the identity included, since
  only $\operatorname{range}(\mathbf{E}_j\mathbf{G}_j) = \mathcal{L}_j^{\perp}$ is used). Law: H2's
  randomized form for $\mathcal{A}^+$ truncated before pass $j$, with the now public stabilizer
  randomizer `stabRand` (item 3), makes $\mathbf{U}^{\mathsf{H}}\mathbf{Q}_j$ conditionally a Haar
  frame of $\mathcal{L}_j^{\perp}$ (GZ4), and GZ3 turns it into a Gaussian block independent of
  the past; the depth count is KB2–KB3. Split: the stand-alone lemmas below are targets; K7
  keeps the query-model part (augmented algorithm and decoding, frame choice, law of one pass,
  depth induction, assembly) as private lemmas, H, about 600 lines; it starts on the escalation
  model (`--hard L,H`). The full plan is K7's docstring and its outline in the targets file.

**KB2** `blockKrylovSpace_le_of_range_le` (S): $\mathcal{K}_q(\mathbf{A}, \mathbf{B})$ depends on
$\mathbf{B}$ through its range only. **KB3** `sup_sup_map_mulVecLin_le_blockKrylovSpace_add_two`
(S): $\mathcal{L} \le \mathcal{K}_{s+1}$ and $\mathcal{V} \le \mathcal{L} + \operatorname{range}
\mathbf{B}$ give $\mathcal{L} + \mathcal{V} + \mathbf{A}\mathcal{V} \le \mathcal{K}_{s+2}$, one
pass of the depth count. Both in `Krylov/Basic/BlockSpace.lean`.

**GZ1** `indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix` (OP5's M4, in
`RandomMatrix/Haar/Uniqueness.lean`): for tall Gaussian $\mathbf{G}$ the polar factor and
$\mathbf{G}^{\mathsf{H}}\mathbf{G}$ are independent. False for wide $\mathbf{G}$ (the Gram matrix
fixes the row space), hence `card k ≤ card n`.

Fable's item 2 (K7 applies GZ1 to the compressed Gaussian on $\mathcal{L}_j^{\perp}$, of random
dimension) is met by both options: **GZ2**
`indepFun_polarFactor_mul_of_isStarProjection_of_hasLaw_gaussianMatrix` (M) is GZ1 for
$\mathbf{P}\mathbf{G}$ with an orthogonal projector of rank $\ge \lvert k \rvert$, proved from GZ1
in coordinates with the existing `HasOrthonormalCols.polarFactor_mul_left`
($\operatorname{polar}(\mathbf{Q}\mathbf{A}) = \mathbf{Q}\operatorname{polar}(\mathbf{A})$, already
in `Matrix/Factorizations/Polar.lean`, so no new lemma). **GZ4**
`eq_map_polarFactor_mul_of_forall_map_mul_left_eq` (M): a law on frames in
$\operatorname{range}\mathbf{E}$ invariant under the orthogonal maps fixing
$\operatorname{range}(\mathbf{I} - \mathbf{E})$ is the law of
$\operatorname{polar}(\mathbf{E}\mathbf{Z})$ — the coordinate-free Haar frame law of a subspace,
which is how K7 states "conditionally Haar on $\mathcal{L}_j^{\perp}$" without random coordinates.
**GZ3** `hasLaw_one_sub_mul_add_mul_sqrt_of_hasLaw_gaussianMatrix` (M): for $\mathbf{F}$ with that
law independent of a Gaussian $\mathbf{Y}$, $(\mathbf{I} - \mathbf{E})\mathbf{Y} +
\mathbf{F}((\mathbf{E}\mathbf{Y})^{\mathsf{H}}\mathbf{E}\mathbf{Y})^{1/2}$ is standard Gaussian:
the one-pass Gaussianization, with $\mathbf{E}$ fixed (K7 freezes the transcript). All three in
`RandomMatrix/Haar/Uniqueness.lean`, true for every projector (GZ4 is vacuous when no frame of
width $\lvert k \rvert$ fits).

**Amendment to `NLAlib/LowerBounds/QueryModel/HiddenHaar.lean`** (Fable item 3, done on this
branch): `stabRaw`, `stabRand`, `Measurable.stabRand` (was the private `Measurable.stabRand_comp`,
now `@[fun_prop]`), `stabRand_spec`, `ae_hasOrthonormalCols_stabRaw`, `measurable_stabRand_right`,
`map_mul_left_stabRand`, `map_mul_right_stabRand` are public with LaTeX docstrings; nothing else
changes and no statement changes.

K1 measurability of the oracle; K2–K4 the simulation runs the algorithm and is measurable; K5
monotone in depth; K6 no initial block; K8 the matrix–vector corollary (`comapResponse Prod.fst`).

### 3.3 Polynomials (P1–P9)

| id | statement (math) | source |
|---|---|---|
| P1 | $\deg p \le q$, $p(0) = 1$: $T_k(\frac{a'^2+a^2}{a'^2-a^2})^{-1} \le \sum_j \frac{\omega_j}{2}(\lvert p(\sqrt{\xi_j})\rvert^2 + \lvert p(-\sqrt{\xi_j})\rvert^2)$, $k = \lfloor q/2\rfloor$ | the step inside `norm_sub_mulVec_gmresIterate_chebyshevTwoIntervalMatrix`, made public |
| P2 | `residualMinimax ([-a',-a] ∪ [a,a']) q = T_{⌊q/2⌋}(·)⁻¹` | Greenbaum 1997 §3.1 |
| P3 | $e^{-4k/\kappa} \le T_k(\frac{\kappa^2+1}{\kappa^2-1})^{-1}$, $\kappa \ge 2$ | Shamir Lemma 1 proof |
| P4 | $e^{-2q/\kappa} \le$ `residualMinimax ([-κ,-1] ∪ [1,κ]) q` | **Shamir Lemma 1** (Result id) |
| P5 | at most $q + 2$ points of $S$, positive weights summing to 1, $\rho^2 \le \sum w\lvert p\rvert^2$ | **Shamir Lemma 2** (no Kroó–Pinkus) |
| P6–P8 | the hard-spectrum predicate: values in $S_\kappa$; $\frac{\lvert n\rvert}{4}T_k^{-2} \le \sum_t (m_t - M)p(t)^2$; existence when $4(s+2)(M+1) \le 3\lvert n\rvert$ | Shamir §3.3 eqs. (8)–(9) |
| P9 | $\sum_{j=0}^n (-1)^{n-j}\binom{n}{j}P(x + jh) = 0$ for $\deg P < n$ | Mathlib `fwdDiff` (two lemmas) |

Shamir's Lemma 2 has equality with $\rho_d$ and $\le d + 1$ points; P5 gets equality too (via P2)
with $\le q + 2$ points — irrelevant for every use (OQ7). P3's constant is Shamir's.

### 3.4 Gaussian and Krylov tools (KB1, C1, C2)

KB1 `exists_sum_eval_sq_mul_norm_sq_le_norm_sub_mulVec_sq` (`Krylov/Basic/BlockSpace.lean`): for
diagonal $\mathbf{D}$ and $\mathbf{x} \in \mathcal{K}_s(\mathbf{D}, [\mathbf{g}, \mathbf{G}])$ some
residual polynomial $r$ ($\deg r \le s$, $r(0) = 1$) has $\sum_t r(t)^2\|(\mathbf{I} -
\mathbf{P}_{\mathbf{G}_t})\mathbf{g}_t\|^2 \le \|\mathbf{g} - \mathbf{D}\mathbf{x}\|^2$ over the
levels $t$ — Shamir's decomposition, deterministic. C1/C2 (`RandomMatrix/Gaussian/Invariance.lean`):
$\mathbb{P}[\|\mathbf{P}\mathbf{g}\|^2 \le \beta r] \le e^{\frac r2(1-\beta+\log\beta)}$ for an
orthogonal projector of rank $\ge r$, fixed or independent of $\mathbf{g}$ — Shamir's eq. (10)
(Laurent–Massart for a projection; `LaurentMassart2000` added to the bibliography).

### 3.5 Shamir's theorem (SH1–SH6, `LowerBounds/Krylov/LinearSystems.lean`)

| id | statement | constants |
|---|---|---|
| SH1 | hard spectrum $\mathbf{d}$ (depth $s$, margin $M \ge \lvert c\rvert + 12(s+2)$), $\boldsymbol\xi$ uniform on the sphere $\perp$ Gaussian $\mathbf{G}$ ($c$ columns): $\mathbb{P}[\exists\mathbf{x} \in \mathcal{K}_s(\mathbf{D},[\boldsymbol\xi,\mathbf{G}]): \|\boldsymbol\xi - \mathbf{D}\mathbf{x}\| < \frac14 e^{-2s/\kappa}] \le \frac14$ | ours |
| SH2 | every measurable deterministic algorithm, every $\mathbf{b} \ne \mathbf{0}$, strong oracle, $q$ queries, $\mathbf{U}$ Haar: $\mathbb{P}[\|\mathbf{b} - \mathbf{A}\hat{\mathbf{x}}\| < \frac14 e^{-2(q+1)/\kappa}\|\mathbf{b}\|] \le \frac14$ | spectrum depth $q+1$, margin $13(q+3)$ |
| SH3 | randomized, every $\mathbf{b} \ne 0$: $\exists$ orthogonal $\mathbf{U}$ with failure probability $\ge \frac34$ | Yao Y2 |
| SH4 | strong oracle, spectrum known: success $\ge \frac23$ on all $\mathbf{U}$, $\mathbf{b}$ ⇒ $\kappa\log\frac1{4\varepsilon} \le 2(q+1)$ | |
| SH5 | **matrix–vector oracle**: success $\ge\frac23$ on every symmetric $\mathbf{A}$ with spectrum in $S_\kappa$ and every $\mathbf{b}$, $\lvert n\rvert \ge 20(q+3)^2$ ⇒ $\kappa\log\frac1{4\varepsilon} \le 2(q+1)$ | Result `linear-system-matvec-lower-bound` |
| SH6 | $\varepsilon \le e^{-4}$: $\kappa\log\frac1\varepsilon \le 4(q+1)$ | from SH5: $\le 2(q+1)/(1 - \log 4/4) < 3.07(q+1)$; Shamir leaves $c$, $C$ unspecified |

Deviations from the paper, all recorded in the docstrings: (a) every fixed $\mathbf{b} \ne 0$
instead of a Gaussian $\mathbf{b}$ (stronger; the event is scale invariant, so the uniform
direction $\mathbf{U}^{\mathsf{H}}\mathbf{b}/\|\mathbf{b}\|$ replaces the Gaussian) — $\mathbf{b} =
\mathbf{0}$ is excluded because $\hat{\mathbf{x}} = 0$ solves it; (b) a separate output (degree
$q + 1$); (c) explicit constants $\frac14$, success $\le\frac14$, $n \ge 20(q+3)^2$ in place of
Shamir's $\frac34$, $0.9$, $C^2T^2$ (we take $\beta = \frac12$, $2$ in the $\chi^2$ tails, $N =
n/4$, margin $12(s+2)$; arithmetic in SH1's docstring: tail $\le (s+2)e^{-1.1589(s+2)} +
e^{-0.153 n} \le 0.2$); (d) the "D revealed" clause is SH4's quantifier order (the predicate is a
hypothesis, the algorithm may depend on $\mathbf{d}$); (e) $\kappa \ge 2$ (Lemma 1's range) in
place of $\kappa \ge C$. The two-sided oracle $(\mathbf{A}\mathbf{x}, \mathbf{A}^{\mathsf{T}}\mathbf{x})$
of the paper equals $(\mathbf{A}\mathbf{x}, \mathbf{A}\mathbf{x})$ on the symmetric hard instances,
so SH5's one-sided statement is the paper's; separate per-side budgets are deferred (OQ9).
MINRES attains the rate on the same spectra (`Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_pow_div_two`),
so SH5 is sharp up to the constant — a pairing for the explorer's rates page.

### 3.6 Two-pass low-rank approximation (L0a–L9, `LowerBounds/LowRank/FewPasses.lean`)

Output format: a pair $(\mathbf{W}, \mathbf{M}) \in \mathbb{R}^{n\times k}\times\mathbb{R}^{k\times
n}$, approximation $\mathbf{W}\mathbf{M}$ (rank $\le \lvert k\rvert$ by construction; every rank-$k$
output factors so, and the coupling needs the $n\times k$ frame $\mathbf{W}$, not the $n\times n$
matrix, to spend only $k$ output columns). OQ5.

| id | statement | OP5 |
|---|---|---|
| L0a, L0b | optimum $14\lvert m\rvert$; $\sigma_k = 3$ | §1 |
| L1, L1s | $\|\mathbf{D} - \mathbf{W}\mathbf{M}\|_{\mathsf F}^2 \ge 14m + 7(k - t)$; $\|\cdot\|_2^2 \ge 16(k-t)/k$ | Step 1, (1), (1') |
| L2 | $s^2\mathbf{I} \preceq \mathbf{G}_j^{\mathsf H}\mathbf{G}_j$, $\|\mathbf{G}_h\|_2 \le S$, $\mathbf{z} \in \mathcal{K}_3(\mathbf{D},\mathbf{G})$ ⇒ $s^2\|\mathbf{z}_h\|^2 \le 19 S^2\|\mathbf{z}\|^2$ | Step 3, (2) |
| L3 | $\gamma > 2$, $k \le b$, $\gamma^2 b \le m$: $\mathbb{P}[\exists\mathbf{z} \in \mathcal{K}_3: \|\mathbf{z}_h\|^2 > \frac{171}{(\gamma-2)^2}\|\mathbf{z}\|^2] \le 4e^{-m/(2\gamma^2)}$ | Step 3, $\rho(\gamma) = 171/(\gamma-2)^2$: $19/36$ at 20, $19/64$ at 26 |
| L4 | **Theorem A** (deterministic, strong oracle, $\le 2$ passes, $400(q+k) \le m$): $\mathbb{P}[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf F}^2 < 14m + 3.3k] \le 4e^{-m/800}$ | Thm A |
| L5 | **Theorem C** ($676(q+k) \le m$, $k \ne \emptyset$): $\mathbb{P}[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_2^2 < \frac{45}{4}] \le 4e^{-m/1352}$ | Thm C |
| L6 | randomized two-pass (per-seed schedules), matrix–vector oracle: $\exists$ orthogonal $\mathbf{U}$, failure $\ge 1 - 4e^{-m/800}$ | Cor B(i), via Y3 |
| L7 | **headline**: $0<\varepsilon\le\min(\frac1{6500},\frac{k}{14000})$, $m = \lfloor k/(8\varepsilon)\rfloor$, success $\ge\frac12$ on every symmetric $\mathbf{A}$ ⇒ $q > k/(6400\varepsilon)$ | Cor B(i) (there $q \ge k/(3200\varepsilon) - k$, $\varepsilon \le 1/6400$) |
| L8 | one pass, same bound | Cor B(iii) |
| L9 | spectral: $m \ge 2812$, $\varepsilon \le 0.1$, success $\ge\frac12$ ⇒ $m < 676(q + k)$ | Thm C |

Constants check: L4: $7(k - \frac{19}{36}k) = \frac{119}{36}k = 3.305k > 3.3k$; L5:
$16(1 - \frac{19}{64}) = \frac{45}{4}$, $(1.1\cdot 3)^2 = 10.89 < 11.25$; L7: $\varepsilon \le 1/6500$
gives $\frac{k}{8\varepsilon} - 1 \ge 400(q+k)$ when $q \le \frac{k}{6400\varepsilon}$ (OP5's $1/6400$
misses the floor by one; hence $1/6500$), $m \ge 1750$ gives failure $\ge 1 - 4e^{-2.19} > 0.55$;
L9: $1 - 4e^{-2812/1352} > 0.5002$. The "$\ge 400(q+k)$" hypothesis of L4 counts
$\lvert\mathtt{Fin}\,q \oplus k\rvert = q + k$ coupled columns. Degenerate: $k$ empty in L4 (the
event is $\|\mathbf{A}\|_{\mathsf F}^2 < 14m$, false); L5, L7–L9 assume $k$ nonempty (with $k$
empty the spectral claim is false: $\|\mathbf{A}\|_2^2 = 9$). Two-sided products are covered since
$\mathbf{A}$ is symmetric (OP5 §4.5). The only part of OP5's labels used is **[derived]** (Theorems
A, C, Corollary B(i), (iii)); conjectures and **[open]** items are §11.

### 3.7 Full list


**LowerBounds/QueryModel/Yao.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| Y3 | `QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem_of_forall` | S | 0 | — |

**LowerBounds/QueryModel/Basic.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| Q14 | `QueryAlgorithm.history_comapResponse` | S | 0 | — |
| Q15 | `QueryAlgorithm.run_comapResponse` | S | 1 | history_comapResponse |
| Q16 | `QueryAlgorithm.history_mapOutput` | S | 0 | — |
| Q17 | `QueryAlgorithm.run_mapOutput` | S | 1 | history_mapOutput |
| Q18 | `QueryAlgorithm.IsMeasurable.comapResponse` | S | 0 | — |
| Q19 | `QueryAlgorithm.IsMeasurable.mapOutput` | S | 0 | — |
| Q20 | `QueryAlgorithm.IsMeasurableFamily.comapResponse` | S | 0 | — |
| Q21 | `QueryAlgorithm.IsMeasurableFamily.mapOutput` | S | 0 | — |
| Q22 | `QueryAlgorithm.IsPassStructured.comapResponse` | S | 0 | — |
| Q23 | `QueryAlgorithm.IsPassStructured.mapOutput` | S | 0 | — |
| Q24 | `QueryAlgorithm.isPassStructured_id` | S | 0 | — |
| Q25 | `QueryAlgorithm.isPassStructured_zero_iff_isNonAdaptive` | S | 0 | — |

**LowerBounds/QueryModel/HiddenRotation.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| K1 | `Measurable.hiddenRotationOracle` | S | 0 | — |
| K2 | `QueryAlgorithm.hiddenRotationDecode_history_hiddenRotationSimulation` | M | 0 | — |
| K3 | `QueryAlgorithm.run_hiddenRotationSimulation` | S | 1 | hiddenRotationDecode_history_hiddenRotationSimulation |
| K4 | `QueryAlgorithm.IsMeasurable.hiddenRotationSimulation` | S | 0 | — |
| K5 | `IsKrylovCoupling.mono` | S | 0 | — |
| K6 | `IsKrylovCoupling.ae_range_le_of_isEmpty` | S | 0 | — |
| K7 | `QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_of_hasLaw_haarFrame` | H | 3 | hiddenRotationDecode_history_hiddenRotationSimulation, run_hiddenRotationSimulation, hiddenRotationSimulation, blockKrylovSpace_le_of_range_le, sup_sup_map_mulVecLin_le_blockKrylovSpace_add_two, eq_map_polarFactor_mul_of_forall_map_mul_left_eq, hasLaw_one_sub_mul_add_mul_sqrt_of_hasLaw_gaussianMatrix |
| K8 | `QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_mulVec_of_hasLaw_haarFrame` | S | 4 | exists_isKrylovCoupling_of_hasLaw_haarFrame, run_comapResponse, comapResponse, comapResponse |

**RandomMatrix/Haar/Uniqueness.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| GZ1 | `indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix` | L | 0 | — |
| GZ2 | `indepFun_polarFactor_mul_of_isStarProjection_of_hasLaw_gaussianMatrix` | M | 1 | indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix |
| GZ4 | `eq_map_polarFactor_mul_of_forall_map_mul_left_eq` | M | 0 | — |
| GZ3 | `hasLaw_one_sub_mul_add_mul_sqrt_of_hasLaw_gaussianMatrix` | M | 2 | indepFun_polarFactor_mul_of_isStarProjection_of_hasLaw_gaussianMatrix |

**Polynomial/Chebyshev/TwoInterval.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| P1 | `inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq` | M | 0 | — |
| P2 | `residualMinimax_Icc_union_Icc` | M | 1 | inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq |
| P3 | `exp_neg_le_inv_eval_T_real` | S | 0 | — |
| P4 | `exp_neg_le_residualMinimax_Icc_union_Icc` | S | 2 | residualMinimax_Icc_union_Icc, exp_neg_le_inv_eval_T_real |
| P5 | `exists_residualMinimax_Icc_union_Icc_sq_le_sum_mul_norm_sq` | M | 2 | inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq, residualMinimax_Icc_union_Icc |
| P6 | `IsChebyshevTwoIntervalSpectrum.mem_Icc_union_Icc` | S | 0 | — |
| P7 | `IsChebyshevTwoIntervalSpectrum.inv_sq_le_sum_card_sub_mul_eval_sq` | M | 1 | inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq |
| P8 | `exists_isChebyshevTwoIntervalSpectrum` | M | 0 | — |

**Polynomial/Interpolation/DividedDifference.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| P9 | `sum_neg_one_pow_mul_choose_mul_eval_eq_zero` | S | 0 | — |

**Krylov/Basic/BlockSpace.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| KB1 | `exists_sum_eval_sq_mul_norm_sq_le_norm_sub_mulVec_sq` | M | 0 | — |
| KB2 | `blockKrylovSpace_le_of_range_le` | S | 0 | — |
| KB3 | `sup_sup_map_mulVecLin_le_blockKrylovSpace_add_two` | S | 0 | — |

**RandomMatrix/Gaussian/Invariance.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| C1 | `measureReal_norm_mulVec_sq_le_mul_le_of_hasLaw_gaussianVector` | M | 0 | — |
| C2 | `measureReal_norm_mulVec_sq_le_mul_le_of_hasLaw_gaussianVector_of_indepFun` | S | 1 | measureReal_norm_mulVec_sq_le_mul_le_of_hasLaw_gaussianVector |

**LowerBounds/Krylov/LinearSystems.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| SH1 | `IsChebyshevTwoIntervalSpectrum.measureReal_exists_norm_sub_mulVec_lt_le` | L | 2 | exists_sum_eval_sq_mul_norm_sq_le_norm_sub_mulVec_sq, measureReal_norm_mulVec_sq_le_mul_le_of_hasLaw_gaussianVector_of_indepFun, inv_sq_le_sum_card_sub_mul_eval_sq, exp_neg_le_inv_eval_T_real |
| SH2 | `IsChebyshevTwoIntervalSpectrum.measureReal_norm_sub_mulVec_lt_le_of_hasLaw_haarFrame` | M | 4 | exists_isKrylovCoupling_of_hasLaw_haarFrame, measureReal_exists_norm_sub_mulVec_lt_le, run_mapOutput, isPassStructured_id, hiddenRotationOracle |
| SH3 | `IsChebyshevTwoIntervalSpectrum.exists_le_measureReal_norm_sub_mulVec_ge` | S | 5 | measureReal_norm_sub_mulVec_lt_le_of_hasLaw_haarFrame, hiddenRotationOracle |
| SH4 | `IsChebyshevTwoIntervalSpectrum.mul_log_le_of_forall_le_measureReal` | S | 6 | exists_le_measureReal_norm_sub_mulVec_ge |
| SH5 | `mul_log_le_of_forall_le_measureReal_norm_sub_mulVec_le` | M | 7 | mul_log_le_of_forall_le_measureReal, exists_isChebyshevTwoIntervalSpectrum, mem_Icc_union_Icc, comapResponse, run_comapResponse |
| SH6 | `mul_log_le_four_mul_add_one_of_forall_le_measureReal_norm_sub_mulVec_le` | S | 8 | mul_log_le_of_forall_le_measureReal_norm_sub_mulVec_le |

**LowerBounds/LowRank/FewPasses.lean**

| id | declaration | diff | wave | depends on |
|---|---|---|---|---|
| L0a | `HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq` | M | 1 | le_frobNorm_diagonal_sub_mul_sq |
| L0b | `HasOrthonormalCols.singularValues_mul_diagonal_mul_card` | M | 0 | — |
| L1 | `le_frobNorm_diagonal_sub_mul_sq` | M | 0 | — |
| L1s | `le_specNorm_diagonal_sub_mul_sq` | M | 0 | — |
| L2 | `mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace` | M | 1 | sum_neg_one_pow_mul_choose_mul_eval_eq_zero |
| L3 | `measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix` | M | 2 | mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace |
| L4 | `QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame` | M | 4 | exists_isKrylovCoupling_of_hasLaw_haarFrame, ae_range_le_of_isEmpty, le_frobNorm_diagonal_sub_mul_sq, measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix, run_mapOutput, mapOutput, mapOutput, hiddenRotationOracle |
| L5 | `QueryAlgorithm.IsPassStructured.measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame` | M | 4 | exists_isKrylovCoupling_of_hasLaw_haarFrame, ae_range_le_of_isEmpty, le_specNorm_diagonal_sub_mul_sq, measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix, run_mapOutput, mapOutput, mapOutput, hiddenRotationOracle |
| L6 | `exists_le_measureReal_frobNorm_sub_mul_sq_ge` | M | 5 | measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame, exists_le_measureReal_run_mem_of_forall, run_comapResponse, comapResponse, comapResponse, hiddenRotationOracle |
| L7 | `div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le` | S | 6 | exists_le_measureReal_frobNorm_sub_mul_sq_ge, frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq |
| L8 | `div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one` | S | 7 | div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le |
| L9 | `lt_of_forall_le_measureReal_specNorm_sub_mul_le` | M | 5 | measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame, singularValues_mul_diagonal_mul_card, exists_le_measureReal_run_mem_of_forall, run_comapResponse, comapResponse, comapResponse, hiddenRotationOracle |

## 4. Map to the sources

| source | here |
|---|---|
| Shamir Thm 1 | SH5 (matrix–vector), SH4 (strong oracle, $\mathbf{D}$ known), SH6 (his form, explicit constant), SH2/SH3 (distributional / worst case) |
| Shamir Lemma 1 | P4 (via P2, P3) |
| Shamir Lemma 2 | P5 (explicit certificate P1; no Kroó–Pinkus) |
| Shamir Lemma 3 | LB-A H1 (`RandomMatrix/Haar/Stabilizer.lean`) |
| Shamir Lemma 4 | K7 with one query per pass; its proof uses H2 (randomized form, already cited to Lemma 4 in `HiddenHaar.lean`) |
| Shamir §3.3 (hard $\mathbf{D}$, eqs. (8)–(12)) | P6–P8, KB1, C1–C2, SH1 |
| Shamir §2, reduction to quadratics | deferred (§11) |
| OP5 Lemma C (+ M1–M5) | K7 (M1 = `IsPassStructured`, M2 inside K7, M3 = `hiddenRotationSimulation` K2–K4, M4 = GZ1–GZ4, M5 = KB2–KB3 and inside K7) |
| OP5 Step 1, Step 3, Lagrange | L1, L1s; L3; L2 + P9 |
| OP5 Thm A, Cor B(i), B(iii), Thm C | L4, L6–L7, L8, L5 + L9 |
| OP5 Cor B(ii), expectation forms, Prop E, §4.4 EW 7.1(b) | deferred |

## 5. Consumers

* `IsPassStructured`: every pass-specific bound (OP2 one-pass GN bound if it closes; Proposition E;
  Hutch++/non-adaptive trace bounds stated for $p$ passes); `isPassStructured_zero_iff_isNonAdaptive`
  links the existing `IsNonAdaptive` statements.
* `comapResponse`, `mapOutput`: every reduction between oracles and output formats (two-sided →
  one-sided on symmetric inputs, output post-processing), here SH5, L4, L6.
* K7 / `IsKrylovCoupling`: Shamir, OP5, and next Proposition E ($p$ passes, `equispacedLevelSpectrum
  k m p`), BN23-type spectral bounds, DEM-style bounds for matrix functions, trace estimation
  (needs the transcript form, §11).
* Y3: every class-restricted Yao argument (L6, L9; one-sided bounds).
* P1–P5: the two-interval MINRES worst case in `Krylov/LinearSystems/WorstCase.lean` should be
  re-proved from P1 (cleanup, not in this stage's targets).
* KB1, C1–C2: any Gaussian-Krylov residual bound (DEM, BN23).
* GZ1–GZ4: Gaussianization in any coupling; Haar frames of a subspace from Gaussian data.
* `stabRand` (now public): any further stabilizer-form argument on a revealed subspace.

## 6. Files and placement

New `NLAlib` files (definitions, written): `LowerBounds/QueryModel/HiddenRotation.lean` (oracle,
simulation, `IsKrylovCoupling`), `Polynomial/Chebyshev/TwoInterval.lean` (the predicate; P11
holds: imports only `NLAlib.Polynomial`), `LowerBounds/LowRank/FewPasses.lean` (the spectrum).
Addition to an existing file: `LowerBounds/QueryModel/Basic.lean` (three definitions, docstring
list updated).

Scaffold files (same paths as their `NLAlib` homes) and imports (G3; every name a `Proof:` line
cites elaborates in the file's import closure, checked by `bin/check-skeleton --strict`):

| scaffold file | ids | imports |
|---|---|---|
| `LowerBounds/QueryModel/Basic.lean` | Q14–Q25 | `NLAlib.LowerBounds.QueryModel.Basic` |
| `LowerBounds/QueryModel/Yao.lean` | Y3 | `NLAlib.LowerBounds.QueryModel.Yao` |
| `LowerBounds/QueryModel/HiddenRotation.lean` | K1–K8 | its NLAlib file, `…QueryModel.HiddenHaar`, `RandomMatrix.Gaussian.Invariance`, scaffold `Krylov.Basic.BlockSpace`, scaffold `…QueryModel.Basic`, scaffold `RandomMatrix.Haar.Uniqueness` |
| `RandomMatrix/Haar/Uniqueness.lean` | GZ1–GZ4 | `NLAlib.RandomMatrix.Haar.Uniqueness`, `Matrix.Basic.OrthonormalBasis`, `RandomMatrix.Gaussian.Invariance`, `RandomMatrix.Gaussian.Rank` |
| `Polynomial/Chebyshev/TwoInterval.lean` | P1–P8 | its NLAlib file, `Polynomial.Chebyshev.ResidualMinimax`, `ForMathlib.Algebra.Polynomial.Expand` |
| `Polynomial/Interpolation/DividedDifference.lean` | P9 | its NLAlib file, `Mathlib.Algebra.Group.ForwardDiff` |
| `Krylov/Basic/BlockSpace.lean` | KB1–KB3 | its NLAlib file, `Matrix.Basic.Projector` |
| `RandomMatrix/Gaussian/Invariance.lean` | C1, C2 | `Matrix.Basic.Projector`, `Probability.Distributions.ChiSquare`, its NLAlib file, `ForMathlib.Probability.Independence.Basic` |
| `LowerBounds/Krylov/LinearSystems.lean` | SH1–SH6 | `…QueryModel.Yao`, `RandomMatrix.Haar.Sphere`, scaffold BlockSpace, HiddenRotation, TwoInterval, Gaussian.Invariance |
| `LowerBounds/LowRank/FewPasses.lean` | L0a–L9 | its NLAlib file, scaffold Yao, `Matrix.Spectral.LowRank`, `RandomMatrix.Gaussian.ExtremeSingularValues`, scaffold HiddenRotation, scaffold DividedDifference |

Placement decisions (P10): the coupling is model-level, so `LowerBounds/QueryModel/`; Shamir's
theorem is a lower bound about linear systems, whose upper bounds (CG, MINRES, worst cases) live in
`Krylov/LinearSystems/`, so the new topic folder `LowerBounds/Krylov/` mirrors it (OQ1); the hard
spectrum's *Gaussian* analysis (SH1, L2, L3) stays with its lower bound because it is about that
instance only; the generic tools go to their topics (KB1 Krylov, C1–C2 Gaussian invariance — not
`Probability/Distributions/ChiSquare.lean`, which may not import the Gaussian invariance lemma of
layer 2 —, GZ1–GZ4 Haar uniqueness — not `Haar/Basic.lean`, which `Uniqueness` imports). Expected sizes:
HiddenRotation ≈ 900 lines with K7's proof (split off `HiddenRotationCoupling.lean` if it exceeds
1000; amendment then), LinearSystems ≈ 450, FewPasses ≈ 700.

## 7. Material

No prototype material (the prototype library has no query model). Proof material: LB-A's
`gramSimulation` lemmas (template for K2–K4), H2's randomized form (K7), Y2's proof (Y3),
`Krylov/LinearSystems/WorstCase.lean` (P1's even-part step), `chebyshevExtremum`/`chebyshevWeight`
and `inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq` (P1, P2, P5, P7),
`inv_eval_T_real_eq_two_mul_pow_div` (P3), `ExtremeSingularValues` Gordon tails (L3), the $\chi^2$
tails of `Probability/Distributions/ChiSquare.lean` (C1, SH1).

## 8. Mathlib search (pinned v4.33.1)

Forward differences: `fwdDiff_iter_eq_sum_shift`, `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`
(step 1 only; P9 composes with an affine map). Haar/Stiefel independence of polar factor and Gram
matrix: searched, none (GZ1). Query models, couplings, Krylov spaces of Gaussian blocks: none.
Chebyshev on two intervals: none (Mathlib has `Polynomial.Chebyshev.T` and extrema only).

## 9. Names for review

`IsPassStructured` (alternatives `IsBatched`, `HasPasses`); `comapResponse` (Mathlib's
`comap`/`map` reading); `hiddenRotationOracle`, `hiddenRotationSimulation`, `IsKrylovCoupling`;
`IsChebyshevTwoIntervalSpectrum`; `equispacedLevelSpectrum`. Theorem names follow N2–N3 with the
left side's head; the awkward ones are the inequality-first lower bounds
(`le_frobNorm_diagonal_sub_mul_sq`, `mul_log_le_of_forall_le_measureReal_norm_sub_mulVec_le`,
`div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le`), whose conclusions are pure arithmetic.
The extraction check (N1–N18) runs at clean-up.

## 10. Open questions (recommendations in bold; the decision sheet has them one line each)

All ten decided by the maintainer on 2026-10-26: **(a)** for each, as recommended (Fable: (a)
for each).

1. **Folder for Shamir** — (a) **`LowerBounds/Krylov/LinearSystems.lean`**, mirroring the upper
   bounds' `Krylov/LinearSystems/`; (b) `LowerBounds/LinearSystems/`; (c) `LowerBounds/Regression/`
   (where the sketch-and-solve bound is). (a): CONTRIBUTING's LowerBounds subfolders are named after
   the layer folders; the paired upper bounds are Krylov.
2. **Pass model** — (a) **predicate `IsPassStructured alg pass` on the existing `QueryAlgorithm`**
   (all LB-A API — transcripts, Yao, H2, measurability — applies unchanged); (b) a new
   `BlockQueryAlgorithm` with matrix-valued queries per pass. (b) duplicates the model.
3. **Coupling conclusion** — (a) **`∃ G` on the given space under an auxiliary Gaussian
   `Z ⊥ U`, packaged as `IsKrylovCoupling`**; (b) an explicit measurable coupling map
   $\Phi(\mathbf{U}, \mathbf{Z})$; (c) a statement on an existential extension of the space.
   (a) is usable with `exact`, needs no universe gymnastics; consumers extend by a product.
4. **Hard spectrum for linear systems** — (a) **predicate + existence lemma**; (b) an explicit
   definition `shamirSpectrum κ q n` (multiplicity bookkeeping in a `def`, junk below the dimension
   threshold); (c) `∃ d` inside each statement.
5. **LRA instance and output format** — (a) **dimension type `k ⊕ (Fin 3 × m)` and output
   `(W, M)` with `W : n × k`**, as OP5; (b) arbitrary `n` with an embedding (padding changes the
   optimum and needs an extra argument); (c) output an `n × n` matrix with a rank hypothesis (the
   coupling would spend $n$ Gaussian columns; needs a measurable factorization first).
6. **Constants** — (a) **explicit constants only (SH5/SH6, L7, L9), no `exists_forall_` forms**
   (B5 asks for them on sample-size results of the sketching kind; a lower bound with explicit
   constants gains nothing from $\exists c$); (b) add the asymptotic corollaries.
7. **Lemma 2** — (a) **explicit two-interval certificate, $\le q + 2$ points**; (b) formalize
   Kroó–Pinkus Theorem 2.3 ($\le q + 1$ points) as a general best-approximation characterization.
   (b) is a separate approximation-theory stage with no consumer here.
8. **Simulation** — (a) **new `hiddenRotationSimulation` next to `gramSimulation`**; (b) refactor
   `gramSimulation` as its $\mathbf{D} = \mathbf{I}$ case (Fable LB-A item 6; changes proved
   statements on main). Revisit when a third simulation appears.
9. **Two-sided pair queries / per-side budgets in the coupling** — (a) **defer** (symmetric hard
   instances make them equal to one-sided products; a split of pair rounds costs a factor 2 and is
   a reduction when a consumer needs it); (b) add a pair-splitting reduction now.
10. **Staging and dispatch** — (a) **one approval, dispatch LB-C1 (44 targets after the revision) then LB-C2 (13)**;
    (b) two separate approvals. The LRA part is complete per OP5 ([derived], no open step), so the
    maintainer's main-branch rule is met; it depends only on K6, K7, Q*, Y3.

## 11. Deferred, with what each needs

* OP5 Proposition E ($p$ passes, $c_p \asymp 4^{-p}$): an explicit absolute constant in place of
  $C$, the Lagrange constant $\binom{2p+2}{p+1} - 1$ (P9 gives the identity), Gordon tails as in L3;
  then a statement at general `p` on `equispacedLevelSpectrum k m p`.
* OP5 Corollary B(ii) and the expectation forms: $\mathbb{E}$ of the excess $\ge 3.3k\,\mathbb{P}(E)$
  (integrability of a bounded-below function of $\mathbf{U}$; Yao in expectation, which LB-A lacks).
* EW Conjecture 7.1(b) rate form (OP5 §4.4): a reduction from
  $(\boldsymbol\Omega, \mathbf{A}\boldsymbol\Omega, \mathbf{A}^{*}\mathbf{A}\boldsymbol\Omega)$
  algorithms to two-pass ones.
* Shamir's $\Omega(\sqrt\kappa\log(1/\delta))$ for first-order methods on quadratics: a
  first-order oracle model and the two-product simulation.
* Transcript-level coupling (for trace estimation and matrix functions, where the loss is not a
  function of an output subspace): K7's proof gives it; a statement form needs a design.
* Non-symmetric $\mathbf{U}\mathbf{D}\mathbf{V}^{\mathsf{H}}$ with two-sided queries (Golub–Kahan
  coupling: two Gaussian families, interleaved degrees); per-side budgets (OQ9).
* OP5 conjectures ($\tilde\Theta(k/(p^2\varepsilon))$, Christoffel-function instances) and the
  one-pass gap: research, not this stage.

## 12. Proof plan for dispatch

Waves (from `lbc-targets.json`, the longest dependency chain): wave 0, 30 independent targets
(Y3, Q14, Q16, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, K1, K2, K4, K5, K6, GZ1, GZ4, P1, P3, P6, P8, P9, KB1, KB2, KB3, C1, L0b, L1, L1s); then the chains P1→P2→{P4, P5},
P1→P7, C1→C2, K2→K3, GZ1→GZ2→GZ3, {K2–K4, KB2, KB3, GZ3, GZ4}→K7→{K8, SH2, L4, L5},
{KB1, C2, P7, P3}→SH1→SH2→SH3→SH4→SH5→SH6, P9→L2→L3→{L4, L5}→{L6, L9}, L6→L7→L8. Difficulties:
S 31, M 23, L 2 (GZ1, SH1), H 1 (K7). One dispatch for LB-C1 and LB-C2 together (the dependency
order serialises them; dependents may start on sorried dependencies), tag `lbc`, haiku first with
opus escalation, L and H on opus from the start (`--hard L,H`); failed L/H targets get Opus
continuation sessions, as S10's E8 and L1.

## 13. Literature

[Shamir2026] (arXiv:2609.10874, read in full from the LaTeX source); [DerezinskiEpperlyMeyer2026]
(context, cited by Shamir and LB-A); [Greenbaum1997, §3.1] (two-interval minimax, locator to
verify); [LaurentMassart2000, Lemma 1] (new bib entry); [Meckes2019, Ch. 1]; [Vershynin2018,
Cor. 7.3.3] (Gordon tails, via the library); Kroó–Pinkus 2010 (named in P5's docstring, not
cited: not used). The OP5 research note is the source for L*; its results are **[derived]**, not
refereed, and the docstrings say "No printed source" where a `Result:` id is attached (L7, L8).


## Implementation completion (2026-10-26)

All 57 targets are proved on `stage/lbc`, including K7, with the approved public statements
unchanged. The implementation exposes the left queries sequentially within each pass and delays
all right products until its left queries are exposed. Each nonzero residual is normalized as a
singleton frame; zero residuals use the original independent Gaussian column. The exposed
response itself makes each earlier coupled column reconstructible from a later transcript and
its original seed. Successive replacement of seed columns proves the full joint product law,
including independence of the initially revealed `Uᴴ * B`.

The fixed auxiliary schedule uses `|c| + 3 * p * q + |k|` slots, with unused slots and the
former frame slots equal to zero. These are proof-only two-sided queries to `U`; the original
algorithm still makes exactly its `q` matrix-vector queries. Each batch's right products add at
most one power of `D`, and the output block adds none, giving depth `p + 1`. No additional
dimension, rank or nonempty hypotheses were added.

The reusable probabilistic argument lives in
`NLAlib/LowerBounds/QueryModel/GaussianCoupling.lean`. The pass simulation, depth argument,
canonical coupling and arbitrary-probability-space transport live in `HiddenRotation.lean`.
The finished K7/K8 and all dependent lower bounds were moved out of the scaffold by D8.
