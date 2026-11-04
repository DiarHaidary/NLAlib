/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.RoundingErrors
public import NLAlib.Computation.Model
public import NLAlib.Matrix.Computation.BLAS
public import NLAlib.Krylov.FinitePrecision.CGEnergyEstimator
public import proposals.krylov.CGDirectionUpdate

/-!
# Proposed concrete conjugate gradient program and implementation bridge

The exact target and program were approved on 2026-11-04; their full realization proof
and registration are in progress outside the library.
The canonical DSL program uses cached squared residuals, stored matrix entries and a fixed
operation order. No square root is computed. Status distinguishes a zero residual from a
nonpositive curvature; failed execution remains a separate outcome.

Design and approval boundary: `docs/design/Krylov-CG-Implementation.md`.

## Main definitions

* `NLAlib.cgProg`, `NLAlib.cgProg.compiled`: the concrete program.
* `NLAlib.cgCount`: componentwise upper operation bounds, including guarded stopping.
* `NLAlib.StoredEntriesConjugateGradient`: the exact target proposed for approval.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

/-- The canonical proposed CG program from zero. Declared buffers are input right-hand side,
output iterate, residual, direction, and one status cell. Matrix entries are read column-major
from ROM; all scratch is scoped. A zero cached squared residual sets positive status, while a
nonpositive curvature sets negative status. Zero status after the requested loop means budget
exhausted. Each subsequent loop iteration skips the body after either stop. -/
def cgProg {P ι VB VI : Type} (tag : P) (N q : IExp VI)
    (b x r p status : VB) : Builder P ι VB VI Unit := scope do
  let A ← alloc tag (N * N)
  let s ← alloc tag N
  let scalars ← alloc tag 9
  forRange (N * N) fun i => stmt (.rom tag ⟨A, .var i⟩ (.var i))
  ins (.lit tag ⟨scalars, 6⟩ 0)
  ins (.lit tag ⟨scalars, 7⟩ 1)
  ins (.un tag .neg ⟨scalars, 8⟩ ⟨scalars, 7⟩)
  ins (.copy tag ⟨status, 0⟩ ⟨scalars, 6⟩)
  forRange N fun i => ins (.lit tag ⟨x, .var i⟩ 0)
  copyv tag b 0 r 0 N
  copyv tag b 0 p 0 N
  dot tag ⟨scalars, 0⟩ r 0 r 0 N
  ifThenElse tag .eq ⟨scalars, 0⟩ ⟨scalars, 6⟩
    (ins (.copy tag ⟨status, 0⟩ ⟨scalars, 7⟩)) (pure ())
  forRange q fun _ => ifThenElse tag .eq ⟨status, 0⟩ ⟨scalars, 6⟩
    (do
      gemv tag N N A 0 p 0 s 0
      dot tag ⟨scalars, 2⟩ p 0 s 0 N
      ifThenElse tag .lt ⟨scalars, 6⟩ ⟨scalars, 2⟩ (do
        ins (.bin tag .div ⟨scalars, 3⟩ ⟨scalars, 0⟩ ⟨scalars, 2⟩)
        axpy tag ⟨scalars, 3⟩ p 0 x 0 N
        ins (.un tag .neg ⟨scalars, 5⟩ ⟨scalars, 3⟩)
        axpy tag ⟨scalars, 5⟩ s 0 r 0 N
        dot tag ⟨scalars, 1⟩ r 0 r 0 N
        ins (.bin tag .div ⟨scalars, 4⟩ ⟨scalars, 1⟩ ⟨scalars, 0⟩)
        forRange N fun i => do
          ins (.bin tag .mul ⟨scalars, 2⟩ ⟨scalars, 4⟩ ⟨p, .var i⟩)
          ins (.bin tag .add ⟨p, .var i⟩ ⟨r, .var i⟩ ⟨scalars, 2⟩)
        ins (.copy tag ⟨scalars, 0⟩ ⟨scalars, 1⟩)
        ifThenElse tag .eq ⟨scalars, 0⟩ ⟨scalars, 6⟩
          (ins (.copy tag ⟨status, 0⟩ ⟨scalars, 7⟩)) (pure ()))
        (ins (.copy tag ⟨status, 0⟩ ⟨scalars, 8⟩))) (pure ())

/-- The proposed CG tree compiled once at symbolic dimension and step budget. Its only five
free buffers are the declared input, three output vectors and status. The target is approved;
the tree awaits its full realization proof and
registration. -/
def cgProg.compiled {P ι : Type} (tag : P) : Prog P ι 1 5 :=
  (ProgFamily.compile fun _ _ N q h =>
    (cgProg tag N (q 0) (h 0) (h 1) (h 2) (h 3) (h 4)).run).get rfl

/-- The one compiled tree instantiates to the concrete builder at every dimension and
requested step budget; the program has no access to their values before instantiation. -/
theorem cgProg.toStmt_compiled {P ι : Type} (tag : P) (N q : ℕ) :
    (cgProg.compiled (ι := ι) tag).toStmt N ![q] =
      (cgProg tag (.const N) (.const q) 0 1 2 3 4).run := by
  rfl

/-- Componentwise operation upper bounds for the canonical program, including initialization,
all requested loop guards, and the maximal number of active steps. Early termination and
nonpositive-curvature rejection can lower individual counts. No square root, oracle call,
conversion or random draw is charged. -/
noncomputable def cgCount {P ι : Type} (tag : P) (N q : ℕ) : OpCount P ι :=
  Finsupp.single (.rom tag) (N ^ 2) +
  Finsupp.single (.bin tag .mul) (N + q * (N ^ 2 + 5 * N)) +
  Finsupp.single (.bin tag .add) (N + q * (N ^ 2 + 5 * N)) +
  Finsupp.single (.un tag .conj) (N + 2 * q * N) +
  Finsupp.single (.bin tag .div) (2 * q) +
  Finsupp.single (.un tag .neg) (q + 1) +
  Finsupp.single (.lit tag) (N + 3 + q * (N + 2)) +
  Finsupp.single (.cmp tag) (1 + 3 * q) +
  Finsupp.single (.copy tag) (2 * N + 2 * q + 2)

/-- The approved exact target, awaiting its full realization proof and registration.
Every real ROM matrix and right-hand
side gives a successful guarded run with one of three statuses. For an SPD ROM matrix, the
three output vectors equal the exact CG state after the requested budget, padded after zero
termination. Counts are componentwise upper bounds and cell memory includes the read-only
matrix, loaded matrix, inputs, outputs and scratch. No target registry has been changed. -/
def StoredEntriesConjugateGradient : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (tag : P),
    StoredEntries (𝕜 := ℝ) tag (cgProg.compiled (ι := ι) tag)
      (fun _ _ => True) (fun N _ => Fin N → ℝ)
      (fun N _ b => ![(Array.ofFn b).map some, Array.replicate N none,
        Array.replicate N none, Array.replicate N none, Array.replicate 1 none])
      (fun N _ => N ^ 2) (fun N q => cgCount tag N (q 0))
      (fun N _ p => if p = tag then 2 * N ^ 2 + 5 * N + 11 else 0)
      (fun N q b vals _ st =>
        let A : Matrix (Fin N) (Fin N) ℝ := fun i j => vals (i + N * j)
        ∃ status : ℝ, st.store.read tag 4 0 = some status ∧
          (status = 0 ∨ status = 1 ∨ status = -1) ∧
          Holds st.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
          (A.PosDef →
            Holds st.store tag 1 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).x i) ∧
            Holds st.store tag 2 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).r i) ∧
            Holds st.store tag 3 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).p i) ∧
            (status = 1 ↔ (cgState A b 0 (q 0)).r = 0) ∧ status ≠ -1))

/-- The implementation roundoff budget for the proposed stored CG program. For positive
matrix dimension, the input-only small-roundoff window ensures this controls every actual
kernel error. It is kept in this proposal until target approval. -/
noncomputable irreducible_def cgImplementationRoundoffBound (N : ℕ) (u : ℝ) : ℝ :=
  4 * (N : ℝ) ^ 2 * u

/-- The proposed dimension-dependent roundoff bound is nonnegative at nonnegative roundoff. -/
theorem cgImplementationRoundoffBound_nonneg (N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ cgImplementationRoundoffBound N u := by
  rw [cgImplementationRoundoffBound_def]
  positivity

/-- In positive dimension the proposed implementation bound dominates four times unit
roundoff; this also covers zero unit roundoff. -/
theorem four_mul_le_cgImplementationRoundoffBound {N : ℕ} (hN : 0 < N)
    {u : ℝ} (hu : 0 ≤ u) : 4 * u ≤ cgImplementationRoundoffBound N u := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [cgImplementationRoundoffBound_def]
  nlinarith [mul_nonneg (show 0 ≤ (N : ℝ) ^ 2 - 1 by nlinarith) hu]

private theorem cg_implementation_mul_le {N : ℕ} (hN : 0 < N) {u : ℝ} (hu : 0 ≤ u) :
    4 * (N : ℝ) * u ≤ cgImplementationRoundoffBound N u := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [cgImplementationRoundoffBound_def]
  nlinarith [mul_nonneg (show 0 ≤ (N : ℝ) ^ 2 - N by nlinarith) hu]

/-- The dot-product rounding factor is bounded by twice dimension times unit roundoff when
the proposed implementation budget is at most one hundredth. -/
theorem roundingFactor_le_two_mul_of_cgImplementationRoundoffBound_le {N : ℕ}
    (hN : 0 < N) {u : ℝ} (hu : 0 ≤ u)
    (hsmall : cgImplementationRoundoffBound N u ≤ 1 / 100) :
    Computation.roundingFactor N u ≤ 2 * N * u := by
  have hNu := (cg_implementation_mul_le hN hu).trans hsmall
  have hNu0 : 0 ≤ (N : ℝ) * u := by positivity
  have hden : 0 < 1 - (N : ℝ) * u := by linarith
  rw [Computation.roundingFactor, div_le_iff₀ hden]
  nlinarith [mul_nonneg hNu0 (show 0 ≤ 1 / 2 - (N : ℝ) * u by linarith)]

/-- The dense matvec spectral-error multiplier is bounded by the input-only proposed
implementation budget, including zero unit roundoff. -/
theorem roundingFactor_mul_sqrt_le_cgImplementationRoundoffBound {N : ℕ}
    (hN : 0 < N) {u : ℝ} (hu : 0 ≤ u)
    (hsmall : cgImplementationRoundoffBound N u ≤ 1 / 100) :
    Computation.roundingFactor N u * Real.sqrt N ≤
      cgImplementationRoundoffBound N u := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqrt : Real.sqrt N ≤ (N : ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith⟩
  have hγ := roundingFactor_le_two_mul_of_cgImplementationRoundoffBound_le hN hu hsmall
  calc
    Computation.roundingFactor N u * Real.sqrt N ≤ (2 * N * u) * N :=
      mul_le_mul hγ hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ ≤ cgImplementationRoundoffBound N u := by
      rw [cgImplementationRoundoffBound_def]
      nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) hu]

/-- The two-operation vector-update factor is bounded by the proposed input-only
implementation budget. -/
theorem roundingFactor_two_le_cgImplementationRoundoffBound {N : ℕ}
    (hN : 0 < N) {u : ℝ} (hu : 0 ≤ u)
    (hsmall : cgImplementationRoundoffBound N u ≤ 1 / 100) :
    Computation.roundingFactor 2 u ≤ cgImplementationRoundoffBound N u := by
  have h4u := four_mul_le_cgImplementationRoundoffBound hN hu
  have hden : 0 < 1 - (2 : ℝ) * u := by linarith
  have hγ : Computation.roundingFactor 2 u ≤ 4 * u := by
    rw [Computation.roundingFactor, Nat.cast_ofNat, div_le_iff₀ hden]
    nlinarith [mul_nonneg hu (show 0 ≤ 1 / 4 - u by linarith)]
  exact hγ.trans h4u

/-- The input-only CG horizon window implies the local implementation budget is at most
one hundred-thousandth. No measured trajectory or successful-run premise is needed. -/
theorem cgImplementationRoundoffBound_le_of_mul_le {N q : ℕ} (hq : 0 < q)
    {u κ : ℝ} (hu : 0 ≤ u) (hκ : 1 ≤ κ)
    (hsmall : (q : ℝ) ^ 2 * Real.sqrt q * cgImplementationRoundoffBound N u * κ ^ 2 ≤
      1 / 10 ^ 5) : cgImplementationRoundoffBound N u ≤ 1 / 10 ^ 5 := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : 1 ≤ (q : ℝ) ^ 2 := by nlinarith
  have hsqrt : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr hqr
  have hκ2 : 1 ≤ κ ^ 2 := by nlinarith
  have hprod : 1 ≤ (q : ℝ) ^ 2 * Real.sqrt q := by
    simpa only [one_mul] using mul_le_mul hq2 hsqrt (by norm_num) (by positivity)
  have hprod' : 1 ≤ ((q : ℝ) ^ 2 * Real.sqrt q) * κ ^ 2 := by
    simpa only [one_mul] using mul_le_mul hprod hκ2 (by norm_num) (by positivity)
  have h := mul_le_mul_of_nonneg_right hprod' (cgImplementationRoundoffBound_nonneg N hu)
  nlinarith

namespace CGImplementation

/-- The actual inline direction update computes the exact CG direction under exact semantics.
It preserves the residual and every other cell outside the direction and scratch, and has
two arithmetic operations per component with no additional memory. -/
theorem exec_cg_direction_update_of_sem_eq_exactSem
    {P ι : Type} [DecidableEq P] (I : Interp P ι ℝ (OpCount P ι)) (tag : P)
    (hsem : I.sem = exactSem)
    (st : St P ℝ (OpCount P ι)) (coeff tmp : Cell ℕ ℕ) (p r : ℕ) (n : IExp ℕ)
    (av : ℝ) (pv rv : ℕ → ℝ)
    (hc : st.store.read tag coeff.buf coeff.idx.eval = some av)
    (hp : ∀ i < n.eval, st.store.read tag p i = some (pv i))
    (hr : ∀ i < n.eval, st.store.read tag r i = some (rv i))
    (hpr : p ≠ r) (htp : tmp.buf ≠ p) (htr : tmp.buf ≠ r) (hcp : coeff.buf ≠ p)
    (htc : tmp.buf = coeff.buf → tmp.idx.eval ≠ coeff.idx.eval)
    (ht : ∃ w s, st.store.write tag tmp.buf tmp.idx.eval w = some s) :
    ∃ st', exec I (Builder.forRange n fun i => do
        Builder.ins (.bin tag .mul tmp coeff ⟨p, .var i⟩)
        Builder.ins (.bin tag .add ⟨p, .var i⟩ ⟨r, .var i⟩ tmp)).run st = some st' ∧
      st'.store.shape = st.store.shape ∧
      st' = { st with
        store := st'.store
        cnt := st.cnt + n.eval • (I.charge (.bin tag .mul) + I.charge (.bin tag .add)) } ∧
      (∀ q b j, (q ≠ tag ∨ b ≠ p ∨ n.eval ≤ j) →
        (q ≠ tag ∨ b ≠ tmp.buf ∨ j ≠ tmp.idx.eval) →
        st'.store.read q b j = st.store.read q b j) ∧
      ∀ i < n.eval, st'.store.read tag p i = some (rv i + av * pv i) := by
  have h : IsRelErrSem (fun _ => 0) (fun _ x => x) (fun _ _ => True) I.sem := by
    rw [hsem]
    exact isRelErrSem_exactSem
  obtain ⟨st', hrun, hshape, hstate, hframe, hout⟩ :=
    IsRelErrSem.exec_cg_direction_update I tag h st coeff tmp p r n av pv rv
      ⟨av, hc, rfl⟩ (fun i hi => ⟨pv i, hp i hi, rfl⟩)
      (fun i hi => ⟨rv i, hr i hi, rfl⟩) hpr htp htr hcp htc ht
  refine ⟨st', hrun, hshape, hstate, hframe, fun i hi => ?_⟩
  obtain ⟨w, v, hw, hmul, hadd⟩ := hout i hi
  obtain ⟨δ, hδ, hv⟩ := hmul
  obtain ⟨η, hη, he⟩ := hadd
  have hδ0 : δ = 0 := abs_eq_zero.mp (le_antisymm hδ (abs_nonneg _))
  have hη0 : η = 0 := abs_eq_zero.mp (le_antisymm hη (abs_nonneg _))
  have hv' : v = av * pv i := by simpa only [hδ0, add_zero, mul_one] using hv
  have he' : w = rv i + v := by simpa only [hη0, add_zero, mul_one] using he
  simpa only [he', hv'] using hw

end CGImplementation

end NLAlib
