/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.Deflation
public import NLAlib.Matrix.Computation.NewtonSchulzSign
public import NLAlib.Matrix.Spectral.SingularValues
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Real.Sign

/-!
# Hermitian diagonalization by randomized spectral bisection

`NLAlib.eigh P N A R₀ ε θ s` computes an approximate diagonalization
$\mathbf{A} \approx \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$ of a Hermitian
$\mathbf{A}$ with $\|\mathbf{A}\|_2 \le R_0$ by randomized spectral bisection
([Shah2024, Algorithm 3]): at a node with window $R$, shift by a random $c$ of size at most
$R/\ell$, compute the sign of $\mathbf{A} - c\mathbf{I}$ by the Newton–Schulz iteration, the two
spectral projectors $\tfrac12(\mathbf{I} \pm \operatorname{sign})$, their ranks by a rounded trace,
orthonormal bases $\mathbf{Q}_\pm$ of their ranges by randomized deflation, and recurse on the
compressions $\mathbf{Q}_\pm^{\mathsf{H}}\mathbf{A}\mathbf{Q}_\pm \mp (R/2)\mathbf{I}$ with window
$(1/2 + 2/\ell)R$, tolerance $(1 - 1/\ell)\varepsilon$ and $\ell + 1$; a node stops when it has
size at most $1$ or $R \le \varepsilon R_0$.

The algorithm is a function of its primitives (`NLAlib.EighPrimitives`: a matrix multiplication,
a QR factorization, a rounding function and two samplers, each a black box with a contract of
`NLAlib/Matrix/Computation/Primitives.lean` and
`NLAlib/Matrix/Computation/EntrywiseRounding.lean`) and of a tree of ideal samples
`s : List Bool → NLAlib.EighSample N`: the node reached by the path `a` from the root uses
`s a`, a uniform seed for its shift and two Gaussian test matrices.
The step limits are explicit (`N` for each sign iteration, a recursion depth); its guarantee and
its probability are in the design note `docs/design/Eigensolvers-HermitianDiagonalization.md`.

Deviations from [Shah2024, Algorithm 3]: the compressions are stored as rounded Hermitian matrices
(the source leaves their symmetry implicit); $k_- = n - k_+$ (the source rounds both traces); the
scalar parameters $R$, $\varepsilon$, $\ell$ and the tolerances are exact reals; the deflation
tolerance has this library's constants.

## Main definitions

* `NLAlib.EighPrimitives`, `NLAlib.EighSample`, `NLAlib.leadingBlock`.
* `NLAlib.bisectionSignTol`, `NLAlib.bisectionDepth`.
* `NLAlib.EighStep`, `NLAlib.EighStep.IsSplit`, `NLAlib.eighStep`, `NLAlib.eighAux`, `NLAlib.eigh`.
* `NLAlib.EighNode`, `NLAlib.eighChild`, `NLAlib.eighNodeAt`: the recursion tree.
* `NLAlib.IsApproxDiagonalization`: the output guarantee.
* `NLAlib.IsEighGoodSample`: the good events of a node.

## Main results

The local and global guarantees are in the design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` (stage HDIAG).
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- The **primitives of the eigensolver**: a matrix multiplication, a QR factorization, a rounding
function, a uniform sampler (scale and ideal seed in $[-1, 1]$ to a computed shift) and a complex
normal sampler (ideal to computed sample). [Shah2024, Section 1.3]. -/
structure EighPrimitives where
  /-- Matrix multiplication. -/
  mm : MatMulMap ℂ
  /-- QR factorization. -/
  qr : QRMap ℂ
  /-- Rounding of a real number. -/
  fl : ℝ → ℝ
  /-- The uniform sampler. -/
  unif : ℝ → ℝ → ℝ
  /-- The complex normal sampler. -/
  normal : ℂ → ℂ

/-- The **ideal sample of a node**: a uniform seed $v \in [-1, 1]$ for the shift and two
$N \times N$ Gaussian test matrices, one for each spectral projector ($N$ the size of the root). -/
abbrev EighSample (N : ℕ) : Type :=
  ℝ × (Bool → Matrix (Fin N) (Fin N) ℂ)

/-- The **leading $k \times k$ block** of an $N \times N$ matrix, zero outside it when $k > N$. -/
def leadingBlock {N : ℕ} (k : ℕ) (G : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j => if h : (i : ℕ) < N ∧ (j : ℕ) < N then G ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- The **target accuracy of the sign and deflation steps** at a node of size $k$ with tolerance
$\varepsilon$, failure parameter $\rho$ and depth parameter $\ell$:
$$\beta = \frac{\eta\sqrt\rho}{36k\bigl(2\sqrt k + \sqrt{2\log(4/\rho)}\bigr)} \,, \qquad
\eta = \frac{(1 - 1/\ell)\varepsilon}{5\ell} \,.$$
[Shah2024, Algorithm 3, line 5], with this library's Gaussian constants. -/
noncomputable def bisectionSignTol (k : ℕ) (ε ρ : ℝ) (ℓ : ℕ) : ℝ :=
  (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) * √ρ /
    (36 * k * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ))))

/-- The **depth parameter at the root**, $\ell = \lceil \log_2(1/\varepsilon) \rceil + 5$.
[Shah2024, Section 4]. -/
noncomputable def bisectionDepth (ε : ℝ) : ℕ :=
  ⌈Real.logb 2 ε⁻¹⌉₊ + 5

/-- The **outcome of one node** of size $k$: a leaf with its output, a single child on the same
size (the spectrum lies on one side of the shift) with the side, the shifted matrix and the shift
to add back, or a split into a positive part of size $k_+$ and a negative part of size $k - k_+$
with the two computed bases, the two compressions and the shift. -/
inductive EighStep (k : ℕ) where
  /-- A leaf, with its output. -/
  | leaf (U : Matrix (Fin k) (Fin k) ℂ) (d : Fin k → ℝ)
  /-- One child: the side, the shifted matrix and the shift added back to its output. -/
  | shift (b : Bool) (A' : Matrix (Fin k) (Fin k) ℂ) (σ : ℝ)
  /-- Two children: the bases, the compressions and the shift. -/
  | split (kp : ℕ) (h : kp ≤ k) (Qp : Matrix (Fin k) (Fin kp) ℂ)
      (Qm : Matrix (Fin k) (Fin (k - kp)) ℂ) (Ap : Matrix (Fin kp) (Fin kp) ℂ)
      (Am : Matrix (Fin (k - kp)) (Fin (k - kp)) ℂ) (σ : ℝ)

/-- The step **splits into two children**: it is `NLAlib.EighStep.split`. -/
def EighStep.IsSplit {k : ℕ} : EighStep k → Prop
  | .split .. => True
  | _ => False

open Classical in
/-- **One node of randomized spectral bisection** on $\mathbf{A}$ of size $k$ with window $R$,
tolerance $\varepsilon$, depth parameter $\ell$ and ideal sample $(v, \mathbf{G}_{\pm})$, root
scale $R_0$, failure parameter $\rho$ and at most $N$ sign steps: a leaf
$(\mathbf{I}, \operatorname{Re}\operatorname{diag}\mathbf{A})$ for $k \le 1$, a leaf
$(\mathbf{I}, \mathbf{0})$ for $R \le \varepsilon R_0$; otherwise the computed shift
$c = \mathrm{unif}(R/\ell, v)$, $\mathbf{B}$ the Newton–Schulz sign of the rounded
$\mathbf{A} - c\mathbf{I}$ at accuracy `NLAlib.bisectionSignTol` and scale $2R$, the projectors
$\mathbf{P}_{\pm} = \tfrac12(\mathbf{I} \pm \mathbf{B})$ stored as rounded Hermitian matrices
(every entry rounded, so no exact halving is assumed), $k_+$ the rounded trace of
$\mathbf{P}_+$ rounded to an integer and capped at $k$; one child on
$\mathbf{A} \mp (R/2)\mathbf{I}$ when $k_+ \in \{k, 0\}$, and otherwise the deflated bases
$\mathbf{Q}_{\pm}$ of $\mathbf{P}_\pm$ and
the rounded Hermitian parts of $\mathbf{Q}_\pm^{\mathsf{H}}\mathbf{A}\mathbf{Q}_\pm \mp
(R/2)\mathbf{I}$. [Shah2024, Algorithm 3].
Algorithm: spectral-bisection -/
noncomputable def eighStep (P : EighPrimitives) (N signFuel : ℕ) (R₀ ρ : ℝ) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) ℂ) (R ε : ℝ) (ℓ : ℕ) (s : EighSample N) : EighStep k :=
  if k ≤ 1 then .leaf 1 fun i => RCLike.re (A i i)
  else if R ≤ ε * R₀ then .leaf 1 0
  else
    let c := P.unif (R / ℓ) s.1
    let Ash := roundDiag P.fl (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))
    let B := newtonSchulzSign P.mm P.fl (bisectionSignTol k ε ρ ℓ) (2 * R) signFuel Ash
    let Pp := roundHermitian P.fl ((2⁻¹ : ℝ) • (1 + B))
    let Pm := roundHermitian P.fl ((2⁻¹ : ℝ) • (1 - B))
    let kp := min k (round (roundedSum P.fl fun i => RCLike.re (Pp i i))).toNat
    if kp = k then .shift true (roundDiag P.fl (A - (R / 2) • (1 : Matrix (Fin k) (Fin k) ℂ)))
      (R / 2)
    else if kp = 0 then
      .shift false (roundDiag P.fl (A + (R / 2) • (1 : Matrix (Fin k) (Fin k) ℂ))) (-(R / 2))
    else
      let Qp := deflate P.mm P.qr P.normal kp Pp (leadingBlock k (s.2 true))
      let Qm := deflate P.mm P.qr P.normal (k - kp) Pm (leadingBlock k (s.2 false))
      .split kp (min_le_left _ _) Qp Qm
        (roundHermitian P.fl
          (hermitianPart (P.mm (P.mm Qpᴴ A) Qp) - (R / 2) • (1 : Matrix (Fin kp) (Fin kp) ℂ)))
        (roundHermitian P.fl (hermitianPart (P.mm (P.mm Qmᴴ A) Qm) +
          (R / 2) • (1 : Matrix (Fin (k - kp)) (Fin (k - kp)) ℂ)))
        (R / 2)

/-- **Randomized spectral bisection with recursion budget** $f$: unfold `NLAlib.eighStep` at the
root with the sample `s []`, recurse on the children with window $(1/2 + 2/\ell)R$, tolerance
$(1 - 1/\ell)\varepsilon$, depth parameter $\ell + 1$ and the samples of their subtrees, and
assemble $[\mathrm{mm}(\mathbf{Q}_+, \mathbf{U}_+)\ \mathrm{mm}(\mathbf{Q}_-, \mathbf{U}_-)]$ with
the rounded shifted eigenvalues. Junk value $(\mathbf{I}, \mathbf{0})$ when the budget is spent.
[Shah2024, Algorithm 3].
Algorithm: spectral-bisection -/
noncomputable def eighAux (P : EighPrimitives) (N signFuel : ℕ) (R₀ ρ : ℝ) :
    ℕ → {k : ℕ} → Matrix (Fin k) (Fin k) ℂ → ℝ → ℝ → ℕ → (List Bool → EighSample N) →
      Matrix (Fin k) (Fin k) ℂ × (Fin k → ℝ)
  | 0, _, _, _, _, _, _ => (1, 0)
  | f + 1, k, A, R, ε, ℓ, s =>
    match eighStep P N signFuel R₀ ρ A R ε ℓ (s []) with
    | .leaf U d => (U, d)
    | .shift b A' σ =>
      let r := eighAux P N signFuel R₀ ρ f A' ((2⁻¹ + 2 / (ℓ : ℝ)) * R)
        ((1 - 1 / (ℓ : ℝ)) * ε) (ℓ + 1) fun a => s (b :: a)
      (r.1, fun i => P.fl (r.2 i + σ))
    | .split kp h Qp Qm Ap Am σ =>
      let rp := eighAux P N signFuel R₀ ρ f Ap ((2⁻¹ + 2 / (ℓ : ℝ)) * R)
        ((1 - 1 / (ℓ : ℝ)) * ε) (ℓ + 1) fun a => s (true :: a)
      let rm := eighAux P N signFuel R₀ ρ f Am ((2⁻¹ + 2 / (ℓ : ℝ)) * R)
        ((1 - 1 / (ℓ : ℝ)) * ε) (ℓ + 1) fun a => s (false :: a)
      let e : Fin k ≃ Fin kp ⊕ Fin (k - kp) :=
        (finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm
      ((Matrix.fromCols (P.mm Qp rp.1) (P.mm Qm rm.1)).submatrix id e,
        fun i => Sum.elim (fun j => P.fl (rp.2 j + σ)) (fun j => P.fl (rm.2 j - σ)) (e i))

/-- **Randomized spectral bisection** $\mathsf{eigh}(\mathbf{A}, \varepsilon, \theta)$ for an
$n \times n$ matrix with scale $R_0$, at most $N$ steps per sign computation and the tree of ideal
samples `s`: `NLAlib.eighAux` at the root with window $R_0$, failure parameter
$\rho = \theta/(4n)$, depth parameter $\ell$ = `NLAlib.bisectionDepth` $\varepsilon$ and recursion
budget $\ell + 1$. [Shah2024, Section 4], the root call there with $R_0 = \|\mathbf{A}\|_2$.
Algorithm: spectral-bisection -/
noncomputable def eigh (P : EighPrimitives) (signFuel : ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R₀ ε θ : ℝ) (s : List Bool → EighSample n) :
    Matrix (Fin n) (Fin n) ℂ × (Fin n → ℝ) :=
  eighAux P n signFuel R₀ (θ / (4 * n)) (bisectionDepth ε + 1) A R₀ ε (bisectionDepth ε) s

/-- A **node of the recursion tree**: its size $k$, matrix, window $R$, tolerance $\varepsilon$ and
depth parameter $\ell$. -/
structure EighNode where
  /-- The size. -/
  k : ℕ
  /-- The matrix. -/
  A : Matrix (Fin k) (Fin k) ℂ
  /-- The window. -/
  R : ℝ
  /-- The tolerance. -/
  ε : ℝ
  /-- The depth parameter. -/
  ℓ : ℕ

/-- **The child of a node on side $b$** under the sample `s`: none at a leaf and on the absent
side of a one-child node, and otherwise the child node of `NLAlib.eighStep` with the next window,
tolerance and depth parameter. -/
noncomputable def eighChild (P : EighPrimitives) (N signFuel : ℕ) (R₀ ρ : ℝ) (x : EighNode)
    (s : EighSample N) (b : Bool) : Option EighNode :=
  match eighStep P N signFuel R₀ ρ x.A x.R x.ε x.ℓ s with
  | .leaf _ _ => none
  | .shift b' A' _ =>
    if b = b' then
      some ⟨x.k, A', (2⁻¹ + 2 / (x.ℓ : ℝ)) * x.R, (1 - 1 / (x.ℓ : ℝ)) * x.ε, x.ℓ + 1⟩
    else none
  | .split kp _ _ _ Ap Am _ =>
    if b then some ⟨kp, Ap, (2⁻¹ + 2 / (x.ℓ : ℝ)) * x.R, (1 - 1 / (x.ℓ : ℝ)) * x.ε, x.ℓ + 1⟩
    else some ⟨x.k - kp, Am, (2⁻¹ + 2 / (x.ℓ : ℝ)) * x.R, (1 - 1 / (x.ℓ : ℝ)) * x.ε, x.ℓ + 1⟩

/-- **The node at the path $a$** below the node $x$ with the tree of samples `s`: $x$ at the empty
path, and the node at the rest of the path below the child on side $b$ for a path $b :: a$, with
the samples of that subtree; none when the path leaves the tree. -/
noncomputable def eighNodeAt (P : EighPrimitives) (N signFuel : ℕ) (R₀ ρ : ℝ) :
    List Bool → EighNode → (List Bool → EighSample N) → Option EighNode
  | [], x, _ => some x
  | b :: a, x, s => (eighChild P N signFuel R₀ ρ x (s []) b).bind fun y =>
    eighNodeAt P N signFuel R₀ ρ a y fun a' => s (b :: a')

/-- `IsApproxDiagonalization A U d η κ`: **$\mathbf{U}\operatorname{diag}(\mathbf{d})
\mathbf{U}^{\mathsf{H}}$ is an approximate diagonalization of $\mathbf{A}$** with residual $\eta$
and a nearly unitary $\mathbf{U}$:
$\|\mathbf{A} - \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}\|_2 \le \eta$ and
every singular value of $\mathbf{U}$ lies in $[1 - \kappa, 1 + \kappa]$, in Loewner form
$(1 - \kappa)^2\mathbf{I} \preceq \mathbf{U}^{\mathsf{H}}\mathbf{U} \preceq
(1 + \kappa)^2\mathbf{I}$. The output guarantee of [Shah2024, Theorem 4.2]. -/
structure IsApproxDiagonalization {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℂ) (d : n → ℝ) (η κ : ℝ) : Prop where
  /-- The residual bound. -/
  specNorm_sub_le : specNorm (A - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) ≤ η
  /-- The lower singular value bound. -/
  smul_one_le : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ Uᴴ * U
  /-- The upper singular value bound. -/
  le_smul_one : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ)

/-- `IsEighGoodSample w x t y s`: **the good events of the node $y$ for its ideal sample**
$s = (v, \mathbf{G}_\pm)$, with the ideal shift $c' = (R/\ell)v$:
(I) the seed lies in $[-1, 1]$ (true almost surely) and every eigenvalue of $\mathbf{A}$ is
at distance at least $w$ from $c'$; (II) for each side
$\pm$ whose spectral projector $\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} -
c'\mathbf{I}))$ has rank $r$ with $0 < r < k$, and every orthonormal basis $\mathbf{V}$ of its
range, the leading $k \times k$ block $\mathbf{G}$ of $\mathbf{G}_\pm$ has
$\|\mathbf{G}\|_2 < t$ and $\sigma_{r-1}(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1) > x$, with
$\mathbf{G}_1$ its first $r$ columns. [Shah2024, Lemma 4.1], Events I and II there. -/
def IsEighGoodSample {N : ℕ} (w x t : ℝ) (y : EighNode) (s : EighSample N) : Prop :=
  (s.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∀ e ∈ spectrum ℝ y.A, w ≤ |e - y.R / y.ℓ * s.1|) ∧
    ∀ (b : Bool) (r : ℕ) (V : Matrix (Fin y.k) (Fin r) ℂ), 0 < r → r < y.k →
      HasOrthonormalCols V →
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + (if b then (1 : ℝ) else -1) •
        cfc Real.sign (y.A - (y.R / y.ℓ * s.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))) →
      specNorm (leadingBlock y.k (s.2 b)) < t ∧
        ∀ h : r ≤ y.k,
          x < singularValues (Vᴴ * (leadingBlock y.k (s.2 b)).submatrix id (Fin.castLE h)) (r - 1)

end NLAlib
