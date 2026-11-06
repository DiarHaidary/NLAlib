/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.Matrix.QRIteration.Ritz

/-!
# The shifting strategy $\mathrm{Sh}_{k,B}$ in exact arithmetic

The shifting strategy of [BanksGarzaVargasSrivastava2021, §4.2] as a mathematical rule on the
current Hessenberg iterate $\mathbf{H}$ and a list of $k = 2^m$ approximate Ritz values: if a
Ritz value is an eigenvalue, shift by it (the step then decouples exactly); otherwise try the
promising Ritz value $r$ of `NLAlib.findRitz`, then the exceptional shifts, a square grid on the
disk of radius $(2B)^{1/k}\theta\alpha\,\psi_k(\mathbf{H})$ about $r$, and take the first shift
$s$ whose degree $k$ step $(z - s)^k$ decouples exactly or reduces the potential by $1 - \gamma$.
The iteration `NLAlib.shqrIterate` repeats this with a Ritz-value oracle.

This is the exact iteration the convergence theorem is about, written as a definition so that
the theorem names one sequence; it is not an implementation (it compares exact real numbers and
decides equality of complex determinants). The finite-precision algorithm of
[BanksGarzaVargasSrivastava2022] is designed separately (design note
`docs/design/Eigensolvers-ShiftedQR.md`, §9).

## Main definitions

* `NLAlib.squareGrid`: the exceptional shifts, a square grid covering a disk.
* `NLAlib.exceptionalRadius`, `NLAlib.exceptionalSpacing`: the radius and relative spacing.
* `NLAlib.IsShiftSuccess`: a shift whose degree $k$ step decouples or reduces the potential.
* `NLAlib.shqrCandidates`, `NLAlib.shqrShift`, `NLAlib.shqrStep`, `NLAlib.shqrIterate`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- The **square grid** of $(m + 1)^2$ points $c + R\,(2i/m - 1) + R\,(2j/m - 1)\,\mathrm{i}$,
$0 \le i, j \le m$, with $m = \lceil\sqrt2/\varepsilon\rceil$: it covers the square of half-side
$R$ about $c$, so every point of the disk of radius $R$ about $c$ is within $\varepsilon R$ of a
grid point. An explicit $\varepsilon R$-net, in place of the maximal separated set of
[BanksGarzaVargasSrivastava2021, proof of Lemma 4.7]. -/
noncomputable def squareGrid (c : ℂ) (R ε : ℝ) : List ℂ :=
  (List.range (⌈Real.sqrt 2 / ε⌉₊ + 1)).flatMap fun i =>
    (List.range (⌈Real.sqrt 2 / ε⌉₊ + 1)).map fun j =>
      c + (R : ℂ) * ⟨2 * (i : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) - 1,
        2 * (j : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) - 1⟩

/-- The **radius of the exceptional disk**, $(2B)^{1/k}\theta\alpha\psi$, for degree $k$,
condition bound $B$, optimality $\theta$, promising parameter $\alpha$ and potential $\psi$.
[BanksGarzaVargasSrivastava2021, Lemma 4.7], line 1 of $\mathrm{Exc}$ there. -/
noncomputable def exceptionalRadius (k : ℕ) (B θ α ψ : ℝ) : ℝ :=
  (2 * B) ^ ((k : ℝ)⁻¹) * θ * α * ψ

/-- The **relative spacing of the exceptional shifts**,
$$\varepsilon = \Bigl(\frac{\rho}{(14B^4)^{1/k}\alpha^2\theta^2}\Bigr)^{k/(k-1)}\,,$$
with $\rho = (1 - \gamma)^2$ in exact arithmetic ($\rho = \xi(1 - \gamma)$ for a stagnation ratio
$\xi$ in finite precision). [BanksGarzaVargasSrivastava2021, Lemma 4.7], line 2 of
$\mathrm{Exc}$ there, with $12$ in place of $14$ for a net of $9/\varepsilon^2$ points; the
square grid has up to $12/\varepsilon^2$. -/
noncomputable def exceptionalSpacing (k : ℕ) (B θ α ρ : ℝ) : ℝ :=
  (ρ / ((14 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2)) ^ ((k : ℝ) / (k - 1))

/-- A shift $s$ is a **success** for the degree $k$ and rate $\gamma$ at $\mathbf{H}$ if the
degree $k$ step with shift polynomial $(z - s)^k$ gives a reduced matrix or reduces the
potential: $\psi_k(\widehat{\mathbf{H}}) \le (1 - \gamma)\psi_k(\mathbf{H})$. -/
def IsShiftSuccess (γ : ℝ) (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s : ℂ) : Prop :=
  IsDecoupled 0 (multiShiftedQRStep H (List.replicate k s)) ∨
    hessenbergPotential k (multiShiftedQRStep H (List.replicate k s)) ≤
      (1 - γ) * hessenbergPotential k H

/-- The **candidate shifts** of $\mathrm{Sh}_{k,B}$ at $\mathbf{H}$ for a list `ss` of $k = 2^m$
Ritz values: the promising Ritz value $r$ of `NLAlib.findRitz`, then the square grid of spacing
`NLAlib.exceptionalSpacing` $(\rho = (1 - \gamma)^2)$ on the disk of radius
`NLAlib.exceptionalRadius` about $r$. [BanksGarzaVargasSrivastava2021, §4.2], lines 1–4 of
$\mathrm{Sh}_{k,B}$ there. -/
noncomputable def shqrCandidates (B θ α γ : ℝ) (m : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) : List ℂ :=
  findRitz H m 1 ss ::
    squareGrid (findRitz H m 1 ss)
      (exceptionalRadius (2 ^ m) B θ α (hessenbergPotential (2 ^ m) H))
      (exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2))

/-- The **shift chosen by $\mathrm{Sh}_{k,B}$**, $k = 2^m$: the first Ritz value in `ss` that is
an eigenvalue of $\mathbf{H}$ if there is one; otherwise the first success among
`NLAlib.shqrCandidates` (the promising Ritz value $r$ first), and $r$ if none succeeds (which the
convergence theorem excludes). The first clause covers the case the paper sets aside, where the
shift polynomial is singular. [BanksGarzaVargasSrivastava2021, §4.2]. -/
noncomputable def shqrShift (B θ α γ : ℝ) (m : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) : ℂ :=
  match ss.find? (fun r => @decide ((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0)
      (Classical.propDecidable _)) with
  | some r => r
  | none =>
    ((shqrCandidates B θ α γ m H ss).find? fun s =>
        @decide (IsShiftSuccess γ (2 ^ m) H s) (Classical.propDecidable _)).getD
      (findRitz H m 1 ss)

/-- One **iteration of $\mathrm{Sh}_{k,B}$**, $k = 2^m$: the degree $k$ QR step with shift
polynomial $(z - s)^k$, $s$ the shift `NLAlib.shqrShift`.
[BanksGarzaVargasSrivastava2021, §4.2].
Algorithm: shifted-qr (specification) -/
noncomputable def shqrStep (B θ α γ : ℝ) (m : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  multiShiftedQRStep H (List.replicate (2 ^ m) (shqrShift B θ α γ m H ss))

/-- The **shifted QR iteration with strategy $\mathrm{Sh}_{k,B}$**: $\mathbf{H}_0$ given and
$\mathbf{H}_{t+1}$ the iteration `NLAlib.shqrStep` at $\mathbf{H}_t$ with the Ritz values
`ritz` $\mathbf{H}_t$ of an oracle (exact Ritz values, or any $\theta$-optimal ones).
[BanksGarzaVargasSrivastava2021, Theorem 1.6].
Algorithm: shifted-qr (specification) -/
noncomputable def shqrIterate (B θ α γ : ℝ) (m : ℕ)
    (ritz : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → List ℂ)
    (H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  | 0 => H₀
  | t + 1 => shqrStep B θ α γ m (shqrIterate B θ α γ m ritz H₀ t)
      (ritz (shqrIterate B θ α γ m ritz H₀ t))

end NLAlib
