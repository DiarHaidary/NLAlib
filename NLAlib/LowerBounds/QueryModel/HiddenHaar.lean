/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.QueryModel.Basic
public import NLAlib.RandomMatrix.Haar.Stabilizer

/-!
# Deferred decision for adaptive queries to a unitarily invariant matrix

An algorithm queries a matrix $\mathbf{X}$ with a right unitarily invariant law (Gaussian, Haar)
through `twoSidedMulVec`. Then $\mathbf{X}$ may be rotated on the right by any orthogonal matrix
that fixes what the transcript has revealed, chosen as a function of the transcript: the right parts
of the queries and the second components (products $\mathbf{X}^{\mathsf{H}}\mathbf{u}$) of the
responses. The joint law of transcript and matrix does not change. The proof randomizes with the
polar factor of a
Gaussian matrix compressed to the complement of the revealed vectors and inducts over the rounds.

## Main definitions

* `NLAlib.stabRand`: the stabilizer randomizer, a Haar element of the orthogonal matrices fixing a
  given range, built from a Gaussian matrix (with `NLAlib.map_mul_left_stabRand`,
  `NLAlib.map_mul_right_stabRand`); the Krylov coupling of the
  hidden-rotation lower bounds uses it.

## Main results

* `NLAlib.QueryAlgorithm.IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant`: the
  adaptive stabilizer form; the theorem of the same name with the suffix `_of_indepFun` is the
  form with a stabilizer that also depends on an independent variable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

variable {m n : Type*} [Fintype n] [DecidableEq n]

/-- The raw stabilizer randomizer of $\mathbf{V}$:
$\mathbf{P} + \operatorname{polar}(\mathbf{E}\mathbf{G}\mathbf{E})$ with $\mathbf{P}$ the
projector onto the range of $\mathbf{V}$ and $\mathbf{E} = \mathbf{I} - \mathbf{P}$. For a
Gaussian $\mathbf{G}$ it is almost surely orthogonal (`NLAlib.ae_hasOrthonormalCols_stabRaw`). -/
noncomputable def stabRaw {c : Type*} [Fintype c] (V : Matrix n c ℝ)
    (G : Matrix n n ℝ) : Matrix n n ℝ :=
  rangeProjector V + polarFactor ((1 - rangeProjector V) * G * (1 - rangeProjector V))

open scoped Classical in
/-- The **stabilizer randomizer** of $\mathbf{V}$: `stabRaw V G`, replaced by $\mathbf{I}$ when
it is not orthogonal. It is always orthogonal and fixes $\mathbf{V}$ (`NLAlib.stabRand_spec`), and
for a standard Gaussian $\mathbf{G}$ its law is invariant under left and right multiplication by
every orthogonal matrix fixing $\mathbf{V}$ (`NLAlib.map_mul_left_stabRand`,
`NLAlib.map_mul_right_stabRand`): it is a Haar element of the stabilizer of the range of
$\mathbf{V}$, the randomizer of the stabilizer form of deferred decision. -/
noncomputable def stabRand {c : Type*} [Fintype c] (V : Matrix n c ℝ)
    (G : Matrix n n ℝ) : Matrix n n ℝ :=
  if HasOrthonormalCols (stabRaw V G) then stabRaw V G else 1

/-- The stabilizer randomizer is jointly measurable in $\mathbf{V}$ and $\mathbf{G}$. -/
@[fun_prop]
theorem Measurable.stabRand {α : Type*} [MeasurableSpace α] {c : Type*} [Fintype c]
    {f : α → Matrix n c ℝ} {g : α → Matrix n n ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => stabRand (f a) (g a) := by
  have hP : Measurable fun a => rangeProjector (f a) := measurable_rangeProjector.comp hf
  have hE : Measurable fun a => 1 - rangeProjector (f a) := measurable_const.matrix_sub hP
  have hF : Measurable fun a => stabRaw (f a) (g a) :=
    hP.matrix_add (measurable_polarFactor.comp ((hE.matrix_mul hg).matrix_mul hE))
  exact Measurable.ite (hF isClosed_setOf_hasOrthonormalCols.measurableSet) hF measurable_const

/-- The stabilizer randomizer of $\mathbf{V}$ is orthogonal and fixes $\mathbf{V}$. -/
theorem stabRand_spec {c : Type*} [Fintype c] (V : Matrix n c ℝ) (G : Matrix n n ℝ) :
    HasOrthonormalCols (stabRand V G) ∧ stabRand V G * V = V := by
  unfold stabRand
  split_ifs with h
  · refine ⟨h, ?_⟩
    rw [stabRaw, Matrix.add_mul, rangeProjector_mul_self, polarFactor_eq_pinv_sqrt_mul (_ * _)]
    simp only [Matrix.mul_assoc, one_sub_rangeProjector_mul_self, Matrix.mul_zero, add_zero]
  · exact ⟨hasOrthonormalCols_one, Matrix.one_mul V⟩

/-- An orthogonal matrix fixing `V`, its adjoint fixes it too. -/
private theorem conjTranspose_mul_eq_self_of_mul_eq_self {c : Type*} {V : Matrix n c ℝ}
    {s : Matrix n n ℝ} (hs : HasOrthonormalCols s) (hsV : s * V = V) : sᴴ * V = V := by
  conv_lhs => rw [← hsV]
  rw [← Matrix.mul_assoc, hs.conjTranspose_mul_self, Matrix.one_mul]

/-- An orthogonal matrix fixing `V` commutes with the projector onto its range and with its
complement. -/
private theorem mul_rangeProjector_of_mul_eq {c : Type*} [Fintype c] {V : Matrix n c ℝ}
    {s : Matrix n n ℝ} (hs : HasOrthonormalCols s) (hsV : s * V = V) :
    s * rangeProjector V = rangeProjector V ∧ rangeProjector V * s = rangeProjector V ∧
      s * (1 - rangeProjector V) = (1 - rangeProjector V) * s := by
  have h1 : s * rangeProjector V = rangeProjector V := by
    rw [← mul_pinv, ← Matrix.mul_assoc, hsV]
  have h2 : rangeProjector V * s = rangeProjector V := by
    have h : sᴴ * rangeProjector V = rangeProjector V := by
      rw [← mul_pinv, ← Matrix.mul_assoc, conjTranspose_mul_eq_self_of_mul_eq_self hs hsV]
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      conjTranspose_rangeProjector] using congrArg Matrix.conjTranspose h
  refine ⟨h1, h2, ?_⟩
  rw [Matrix.mul_sub, Matrix.sub_mul, h1, h2, Matrix.mul_one, Matrix.one_mul]

/-- Left multiplication by an orthogonal `s` fixing `V` moves inside the raw randomizer. -/
private theorem mul_stabRaw {c : Type*} [Fintype c] {V : Matrix n c ℝ} {s : Matrix n n ℝ}
    (hs : HasOrthonormalCols s) (hsV : s * V = V) (G : Matrix n n ℝ) :
    s * stabRaw V G = stabRaw V (s * G) := by
  obtain ⟨h1, -, hE⟩ := mul_rangeProjector_of_mul_eq hs hsV
  rw [stabRaw, stabRaw, Matrix.mul_add, h1, ← hs.polarFactor_mul_left, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hE, Matrix.mul_assoc _ s G]

/-- Right multiplication by an orthogonal `s` fixing `V` moves inside the raw randomizer. -/
private theorem stabRaw_mul {c : Type*} [Fintype c] {V : Matrix n c ℝ} {s : Matrix n n ℝ}
    (hs : HasOrthonormalCols s) (hsV : s * V = V) (G : Matrix n n ℝ) :
    stabRaw V G * s = stabRaw V (G * s) := by
  obtain ⟨-, h2, hE⟩ := mul_rangeProjector_of_mul_eq hs hsV
  rw [stabRaw, stabRaw, Matrix.add_mul, h2, ← hs.conjTranspose.polarFactor_mul_right,
    Matrix.mul_assoc _ (1 - rangeProjector V), ← hE, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ G s]

/-- The raw randomizer is orthogonal when `P + E G E` is invertible. -/
private theorem hasOrthonormalCols_stabRaw_of_isUnit {c : Type*} [Fintype c] (V : Matrix n c ℝ)
    (G : Matrix n n ℝ)
    (hG : IsUnit (rangeProjector V + (1 - rangeProjector V) * G * (1 - rangeProjector V))) :
    HasOrthonormalCols (stabRaw V G) := by
  set P := rangeProjector V with hPdef
  set E : Matrix n n ℝ := 1 - P with hEdef
  set A := E * G * E with hAdef
  have hP : IsStarProjection P := isStarProjection_rangeProjector V
  have hE : IsStarProjection E := hP.one_sub
  have hPh : Pᴴ = P := hP.isSelfAdjoint.star_eq
  have hEh : Eᴴ = E := hE.isSelfAdjoint.star_eq
  have hPE : P * E = 0 := hP.isIdempotentElem.mul_one_sub_self
  have hEP : E * P = 0 := hP.isIdempotentElem.one_sub_mul_self
  have hAh : Aᴴ = E * Gᴴ * E := by
    rw [hAdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hEh, Matrix.mul_assoc]
  have hEA : E * Aᴴ = Aᴴ := by
    rw [hAh, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE.isIdempotentElem.eq]
  have hPU : P * polarFactor A = 0 := by
    simp only [polarFactor, hAdef, ← Matrix.mul_assoc, hPE, Matrix.zero_mul]
  have hUP : (polarFactor A)ᴴ * P = 0 := by
    rw [← hPh, ← Matrix.conjTranspose_mul, hPU, Matrix.conjTranspose_zero]
  -- the range projector of `Aᴴ` is `E`
  obtain ⟨N, hN⟩ := hG.exists_left_inv
  have hN' : (P + A)ᴴ * Nᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hN, Matrix.conjTranspose_one]
  have hEM : E * (P + A)ᴴ = Aᴴ := by
    rw [Matrix.conjTranspose_add, hPh, Matrix.mul_add, hEP, zero_add, hEA]
  set Q := rangeProjector Aᴴ with hQdef
  have hQE : Q * E = E := by
    calc Q * E = Q * (E * (P + A)ᴴ) * Nᴴ := by
          rw [Matrix.mul_assoc Q, Matrix.mul_assoc E, hN', Matrix.mul_one]
      _ = E := by rw [hEM, rangeProjector_mul_self, ← hEM, Matrix.mul_assoc, hN', Matrix.mul_one]
  have hEQ : E * Q = Q := by rw [hQdef, ← mul_pinv, ← Matrix.mul_assoc, hEA]
  have hQh : Qᴴ = Q := conjTranspose_rangeProjector _
  have hQ : Q = E :=
    calc Q = (E * Q)ᴴ := by rw [hEQ, hQh]
      _ = E := by rw [Matrix.conjTranspose_mul, hQh, hEh, hQE]
  rw [hasOrthonormalCols_iff, stabRaw, ← hPdef, ← hEdef, Matrix.conjTranspose_add, hPh,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hP.isIdempotentElem.eq, hPU, hUP,
    conjTranspose_polarFactor_mul_self, ← hQdef, hQ, hEdef]
  abel

/-- For a standard Gaussian $\mathbf{G}$, the raw randomizer is almost surely orthogonal:
$\mathbf{P} + \mathbf{E}\mathbf{G}\mathbf{E}$ is almost surely invertible, its determinant being
a nonzero polynomial in the entries of $\mathbf{G}$. -/
theorem ae_hasOrthonormalCols_stabRaw {c : Type*} [Fintype c] (V : Matrix n c ℝ) :
    ∀ᵐ G ∂gaussianMatrix n n, HasOrthonormalCols (stabRaw V G) := by
  set P := rangeProjector V with hPdef
  set E : Matrix n n ℝ := 1 - P with hEdef
  -- `det (P + E G E)` is a polynomial in the entries of `G`, equal to `1` at `G = 1`
  let Y : Matrix n n (MvPolynomial (n × n) ℝ) := P.map MvPolynomial.C +
    E.map MvPolynomial.C * Matrix.mvPolynomialX n n ℝ * E.map MvPolynomial.C
  have heval : ∀ G : Matrix n n ℝ,
      MvPolynomial.eval (Function.uncurry G) Y.det = (P + E * G * E).det := by
    intro G
    have hC : ∀ B : Matrix n n ℝ,
        (B.map MvPolynomial.C).map (MvPolynomial.eval (Function.uncurry G)) = B := fun B => by
      ext i j
      simp
    have hX : (Matrix.mvPolynomialX n n ℝ).map (MvPolynomial.eval (Function.uncurry G)) = G := by
      ext i j
      simp [Matrix.mvPolynomialX_apply, Function.uncurry]
    rw [RingHom.map_det]
    simp only [Y, map_add, map_mul, RingHom.mapMatrix_apply, hC, hX]
  have hp : Y.det ≠ 0 := by
    intro h0
    have hEE : E * E = E := (isStarProjection_one_sub_rangeProjector V).isIdempotentElem.eq
    have h := heval 1
    rw [h0, map_zero, Matrix.mul_one, hEE, hEdef, add_sub_cancel, Matrix.det_one] at h
    exact zero_ne_one h
  have hU := hasLaw_uncurry_of_hasLaw_gaussianMatrix (HasLaw.id (μ := gaussianMatrix n n))
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hae : ∀ᵐ x ∂gaussianVector (n × n), MvPolynomial.eval x Y.det ≠ 0 :=
    ae_eval_ne_zero_of_ne_zero hp
  rw [← hU.map_eq] at hae
  filter_upwards [ae_of_ae_map hU.aemeasurable hae] with G hG
  rw [id, heval] at hG
  exact hasOrthonormalCols_stabRaw_of_isUnit V G
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hG))

/-- The stabilizer randomizer of a fixed $\mathbf{V}$ is measurable in $\mathbf{G}$. -/
theorem measurable_stabRand_right {c : Type*} [Fintype c] (V : Matrix n c ℝ) :
    Measurable (stabRand V) :=
  Measurable.stabRand measurable_const measurable_id

/-- Left multiplication by an orthogonal $\mathbf{s}$ fixing $\mathbf{V}$ keeps the law of the
stabilizer randomizer of a standard Gaussian matrix. -/
theorem map_mul_left_stabRand {c : Type*} [Fintype c] (V : Matrix n c ℝ)
    {s : Matrix n n ℝ} (hs : HasOrthonormalCols s) (hsV : s * V = V) :
    ((gaussianMatrix n n).map (stabRand V)).map (s * ·) =
      (gaussianMatrix n n).map (stabRand V) := by
  have hm := measurable_stabRand_right V
  have hl : Measurable fun x : Matrix n n ℝ => s * x := by fun_prop
  rw [Measure.map_map hl hm]
  conv_rhs => rw [← IsLeftUnitarilyInvariant.map_mul_left_eq_self (ν := gaussianMatrix n n) s hs,
    Measure.map_map hm hl]
  refine Measure.map_congr ?_
  filter_upwards [ae_hasOrthonormalCols_stabRaw V] with G hG'
  have hsG : HasOrthonormalCols (stabRaw V (s * G)) := mul_stabRaw hs hsV G ▸ hs.mul hG'
  simp only [Function.comp_apply, stabRand, if_pos hG', if_pos hsG, mul_stabRaw hs hsV]

/-- Right multiplication by an orthogonal $\mathbf{s}$ fixing $\mathbf{V}$ keeps the law of the
stabilizer randomizer of a standard Gaussian matrix. -/
theorem map_mul_right_stabRand {c : Type*} [Fintype c] (V : Matrix n c ℝ)
    {s : Matrix n n ℝ} (hs : HasOrthonormalCols s) (hsV : s * V = V) :
    ((gaussianMatrix n n).map (stabRand V)).map (· * s) =
      (gaussianMatrix n n).map (stabRand V) := by
  have hm := measurable_stabRand_right V
  have hl : Measurable fun x : Matrix n n ℝ => x * s := by fun_prop
  rw [Measure.map_map hl hm]
  conv_rhs => rw [← IsRightUnitarilyInvariant.map_mul_right_eq_self (ν := gaussianMatrix n n) s hs,
    Measure.map_map hm hl]
  refine Measure.map_congr ?_
  filter_upwards [ae_hasOrthonormalCols_stabRaw V] with G hG'
  have hsG : HasOrthonormalCols (stabRaw V (G * s)) := stabRaw_mul hs hsV G ▸ hG'.mul hs
  simp only [Function.comp_apply, stabRand, if_pos hG', if_pos hsG, stabRaw_mul hs hsV]

omit [DecidableEq n] in
/-- A matrix fixes `[V g]` exactly when it fixes `V` and `g`. -/
private theorem mul_fromCols_replicateCol_eq_iff {c : Type*} {V : Matrix n c ℝ}
    {g : n → ℝ} {L : Matrix n n ℝ} :
    L * Matrix.fromCols V (Matrix.replicateCol Unit g) =
        Matrix.fromCols V (Matrix.replicateCol Unit g) ↔ L * V = V ∧ L *ᵥ g = g := by
  rw [Matrix.mul_fromCols, Matrix.fromCols_ext_iff, ← Matrix.replicateCol_mulVec]
  refine and_congr_right fun _ => ⟨fun h => funext fun i => congrFun (congrFun h i) (), ?_⟩
  intro h
  rw [h]

/-- An orthogonal matrix fixing a vector, its adjoint fixes it too. -/
private theorem conjTranspose_mulVec_eq_of_mulVec_eq {L : Matrix n n ℝ}
    (hL : HasOrthonormalCols L) {g : n → ℝ} (h : L *ᵥ g = g) : Lᴴ *ᵥ g = g := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, hL.conjTranspose_mul_self, Matrix.one_mulVec]

/-- One left query on the stabilizer: for `R` the randomizer of `V` and `s` measurable,
orthogonal, fixing `V` and its argument, `(Rᴴ g, R)` has the law of `(Rᴴ g, R s(Rᴴ g))`. -/
private theorem map_left_query_stabRand {c : Type*} [Fintype c] (V : Matrix n c ℝ) (g : n → ℝ)
    {s : (n → ℝ) → Matrix n n ℝ} (hsm : Measurable s) (hso : ∀ b, HasOrthonormalCols (s b))
    (hsV : ∀ b, s b * V = V) (hsb : ∀ b, s b *ᵥ b = b) :
    ((gaussianMatrix n n).map (stabRand V)).map (fun M => (Mᴴ *ᵥ g, M)) =
      ((gaussianMatrix n n).map (stabRand V)).map (fun M => (Mᴴ *ᵥ g, M * s (Mᴴ *ᵥ g))) := by
  set γ := gaussianMatrix n n
  set V' := Matrix.fromCols V (Matrix.replicateCol Unit g)
  have hR := measurable_stabRand_right V
  have hL := measurable_stabRand_right V'
  -- left multiplication by the randomizer `L` of `[V g]` keeps the law of `R`
  have h1 : (γ.prod γ).map (fun p => stabRand V' p.1 * stabRand V p.2) = γ.map (stabRand V) := by
    conv_rhs => rw [← (by simp : (γ.prod γ).map Prod.snd = γ), Measure.map_map hR measurable_snd]
    refine Measure.map_prod_eq_of_forall_map_eq (F := fun t z => stabRand V' t * stabRand V z)
      (G := fun _ z => stabRand V z) (by fun_prop) (by fun_prop) fun t => ?_
    obtain ⟨ho, hV'⟩ := stabRand_spec V' t
    have hl : Measurable fun x : Matrix n n ℝ => stabRand V' t * x := by fun_prop
    rw [← map_mul_left_stabRand V ho (mul_fromCols_replicateCol_eq_iff.1 hV').1,
      Measure.map_map hl hR]
    rfl
  have hLg : ∀ t, (stabRand V' t)ᴴ *ᵥ g = g := fun t =>
    conjTranspose_mulVec_eq_of_mulVec_eq (stabRand_spec V' t).1
      (mul_fromCols_replicateCol_eq_iff.1 (stabRand_spec V' t).2).2
  have hφ₁ : Measurable fun M : Matrix n n ℝ => (Mᴴ *ᵥ g, M) := by fun_prop
  have hφ₂ : Measurable fun M : Matrix n n ℝ => (Mᴴ *ᵥ g, M * s (Mᴴ *ᵥ g)) := by fun_prop
  have hLR : Measurable fun p : Matrix n n ℝ × Matrix n n ℝ => stabRand V' p.1 * stabRand V p.2 :=
    by fun_prop
  rw [← h1, Measure.map_map hφ₁ hLR, Measure.map_map hφ₂ hLR]
  simp only [Function.comp_def, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, hLg]
  -- freeze `R = r`; then `L r s = L u r` with `u = r s rᴴ` fixing `[V g]`
  rw [← Measure.prod_swap, Measure.map_map _ measurable_swap, Measure.map_map _ measurable_swap]
  rotate_left
  · fun_prop
  · fun_prop
  refine Measure.map_prod_eq_of_forall_map_eq
    (F := fun t z => ((stabRand V t)ᴴ *ᵥ g, stabRand V' z * stabRand V t))
    (G := fun t z => ((stabRand V t)ᴴ *ᵥ g,
      stabRand V' z * stabRand V t * s ((stabRand V t)ᴴ *ᵥ g))) (by fun_prop) (by fun_prop)
    fun t => ?_
  obtain ⟨hr, hrV⟩ := stabRand_spec V t
  set r := stabRand V t
  set b := rᴴ *ᵥ g
  set u := r * s b * rᴴ
  have hu : HasOrthonormalCols u := (hr.mul (hso b)).mul hr.conjTranspose
  have huV' : u * V' = V' := by
    refine mul_fromCols_replicateCol_eq_iff.2 ⟨?_, ?_⟩
    · rw [Matrix.mul_assoc, conjTranspose_mul_eq_self_of_mul_eq_self hr hrV, Matrix.mul_assoc, hsV,
        hrV]
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hsb, Matrix.mulVec_mulVec,
        hr.mul_conjTranspose_self, Matrix.one_mulVec]
  have hfun : (fun z => (b, stabRand V' z * r * s b)) =
      (fun M => (b, M * r)) ∘ (· * u) ∘ stabRand V' := by
    funext z
    simp only [Function.comp_apply, u, Matrix.mul_assoc, hr.conjTranspose_mul_self, Matrix.mul_one]
  have hmr : Measurable fun M : Matrix n n ℝ => (b, M * r) := by fun_prop
  have hmu : Measurable fun M : Matrix n n ℝ => M * u := by fun_prop
  rw [hfun]
  calc γ.map (fun z => (b, stabRand V' z * r))
      = (γ.map (stabRand V')).map (fun M => (b, M * r)) := by rw [Measure.map_map hmr hL]; rfl
    _ = ((γ.map (stabRand V')).map (· * u)).map (fun M => (b, M * r)) := by
      rw [map_mul_right_stabRand V' hu huV']
    _ = _ := by rw [Measure.map_map hmr hmu, Measure.map_map (hmr.comp hmu) hL]; rfl

/-- One pair query on the stabilizer: for `R` the randomizer of `V` and `s` measurable,
orthogonal, fixing `V`, `w` and the second component of its argument, `((R w, Rᴴ g), R)` has the
law of `((R w, Rᴴ g), R s(R w, Rᴴ g))`. -/
private theorem map_pair_query_stabRand {c : Type*} [Fintype c] (V : Matrix n c ℝ)
    (w g : n → ℝ) {s : (n → ℝ) × (n → ℝ) → Matrix n n ℝ} (hsm : Measurable s)
    (hso : ∀ p, HasOrthonormalCols (s p)) (hsV : ∀ p, s p * V = V) (hsw : ∀ p, s p *ᵥ w = w)
    (hsb : ∀ p, s p *ᵥ p.2 = p.2) :
    ((gaussianMatrix n n).map (stabRand V)).map (fun M => ((M *ᵥ w, Mᴴ *ᵥ g), M)) =
      ((gaussianMatrix n n).map (stabRand V)).map
        (fun M => ((M *ᵥ w, Mᴴ *ᵥ g), M * s (M *ᵥ w, Mᴴ *ᵥ g))) := by
  set γ := gaussianMatrix n n
  set V' := Matrix.fromCols V (Matrix.replicateCol Unit w)
  have hR := measurable_stabRand_right V
  have hL := measurable_stabRand_right V'
  -- right multiplication by the randomizer `L` of `[V w]` keeps the law of `R`
  have h1 : (γ.prod γ).map (fun p => stabRand V p.2 * stabRand V' p.1) = γ.map (stabRand V) := by
    conv_rhs => rw [← (by simp : (γ.prod γ).map Prod.snd = γ), Measure.map_map hR measurable_snd]
    refine Measure.map_prod_eq_of_forall_map_eq (F := fun t z => stabRand V z * stabRand V' t)
      (G := fun _ z => stabRand V z) (by fun_prop) (by fun_prop) fun t => ?_
    obtain ⟨ho, hV'⟩ := stabRand_spec V' t
    have hl : Measurable fun x : Matrix n n ℝ => x * stabRand V' t := by fun_prop
    rw [← map_mul_right_stabRand V ho (mul_fromCols_replicateCol_eq_iff.1 hV').1,
      Measure.map_map hl hR]
    rfl
  have hLw : ∀ t, stabRand V' t *ᵥ w = w := fun t =>
    (mul_fromCols_replicateCol_eq_iff.1 (stabRand_spec V' t).2).2
  have hRL : Measurable fun p : Matrix n n ℝ × Matrix n n ℝ => stabRand V p.2 * stabRand V' p.1 :=
    by fun_prop
  have hψ₁ : Measurable fun M : Matrix n n ℝ => ((M *ᵥ w, Mᴴ *ᵥ g), M) := by fun_prop
  have hψ₂ : Measurable fun M : Matrix n n ℝ => ((M *ᵥ w, Mᴴ *ᵥ g), M * s (M *ᵥ w, Mᴴ *ᵥ g)) :=
    by fun_prop
  rw [← h1, Measure.map_map hψ₁ hRL, Measure.map_map hψ₂ hRL]
  simp only [Function.comp_def, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, hLw]
  -- freeze `R = r` and apply the left query lemma to `L` with the vector `rᴴ g`
  rw [← Measure.prod_swap, Measure.map_map _ measurable_swap, Measure.map_map _ measurable_swap]
  rotate_left
  · fun_prop
  · fun_prop
  refine Measure.map_prod_eq_of_forall_map_eq
    (F := fun t z => ((stabRand V t *ᵥ w, (stabRand V' z)ᴴ *ᵥ ((stabRand V t)ᴴ *ᵥ g)),
      stabRand V t * stabRand V' z))
    (G := fun t z => ((stabRand V t *ᵥ w, (stabRand V' z)ᴴ *ᵥ ((stabRand V t)ᴴ *ᵥ g)),
      stabRand V t * stabRand V' z *
        s (stabRand V t *ᵥ w, (stabRand V' z)ᴴ *ᵥ ((stabRand V t)ᴴ *ᵥ g))))
    (by fun_prop) (by fun_prop) fun t => ?_
  set r := stabRand V t
  set a := r *ᵥ w
  have hleft := map_left_query_stabRand V' (rᴴ *ᵥ g) (s := fun b => s (a, b)) (by fun_prop)
    (fun b => hso _) (fun b => mul_fromCols_replicateCol_eq_iff.2 ⟨hsV _, hsw _⟩)
    (fun b => hsb (a, b))
  have hκ : Measurable fun q : (n → ℝ) × Matrix n n ℝ => ((a, q.1), r * q.2) := by fun_prop
  have h2 := congrArg (Measure.map fun q : (n → ℝ) × Matrix n n ℝ => ((a, q.1), r * q.2)) hleft
  have hφ₁ : Measurable fun M : Matrix n n ℝ => (Mᴴ *ᵥ (rᴴ *ᵥ g), M) := by fun_prop
  have hφ₂ : Measurable fun M : Matrix n n ℝ =>
      (Mᴴ *ᵥ (rᴴ *ᵥ g), M * s (a, Mᴴ *ᵥ (rᴴ *ᵥ g))) := by fun_prop
  rw [Measure.map_map hκ hφ₁, Measure.map_map hκ hφ₂, Measure.map_map (hκ.comp hφ₁) hL,
    Measure.map_map (hκ.comp hφ₂) hL] at h2
  simpa only [Function.comp_def, Matrix.mul_assoc] using h2

/-- The vectors of `ℝⁿ` revealed by a history of length `i`: the right parts of the queries and
the second components of the responses. -/
private def revealed {m : Type*} {β : Type*} {q : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) q β) (i : ℕ)
    (h : Fin i → (m → ℝ) × (n → ℝ)) : Matrix n (Fin i ⊕ Fin i) ℝ :=
  Matrix.fromCols ((alg.truncate i).rightQueryMatrix h) (Matrix.of fun r j => (h j).2 r)

/-- The invariant of the induction, for histories of length `i`, as an identity of laws. -/
private def StabInvariant {m : Type*} [Fintype m] {β : Type*} {q : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) q β)
    (ν : Measure (Matrix m n ℝ)) (i : ℕ) : Prop :=
  ∀ S : (Fin i → (m → ℝ) × (n → ℝ)) → Matrix n n ℝ, Measurable S →
    (∀ h, HasOrthonormalCols (S h)) → (∀ h, S h * revealed alg i h = revealed alg i h) →
    ν.map (fun x => (alg.history (twoSidedMulVec x) i, x)) =
      ν.map (fun x => (alg.history (twoSidedMulVec x) i, x * S (alg.history (twoSidedMulVec x) i)))

/-- The invariant holds for the empty history, by right unitary invariance of `ν`. -/
private theorem stabInvariant_zero [Fintype m] {β : Type*} {q : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) q β)
    (ν : Measure (Matrix m n ℝ)) [IsRightUnitarilyInvariant ν] : StabInvariant alg ν 0 := by
  intro S _ hSo _
  have hc : Measurable fun x : Matrix m n ℝ => ((Fin.elim0 : Fin 0 → (m → ℝ) × (n → ℝ)), x) :=
    by fun_prop
  have hr : Measurable fun x : Matrix m n ℝ => x * S Fin.elim0 := by fun_prop
  calc ν.map (fun x => (alg.history (twoSidedMulVec x) 0, x))
      = (ν.map (fun x => x * S Fin.elim0)).map
          (fun x => ((Fin.elim0 : Fin 0 → (m → ℝ) × (n → ℝ)), x)) := by
        rw [IsRightUnitarilyInvariant.map_mul_right_eq_self _ (hSo _)]
        rfl
    _ = _ := by
        rw [Measure.map_map hc hr]
        rfl

omit [Fintype n] [DecidableEq n] in
/-- The revealed vectors are measurable in the history. -/
private theorem measurable_revealed {m : Type*} {β : Type*} [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) q β}
    (halg : alg.IsMeasurable) {i : ℕ} (hi : i ≤ q) : Measurable (revealed alg i) := by
  have hQ := (halg.truncate hi).measurable_rightQueryMatrix (𝕜 := ℝ)
  refine measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun k => ?_
  rcases k with j | j
  · simp only [revealed, Matrix.fromCols_apply_inl]
    exact (measurable_pi_apply j).comp ((measurable_pi_apply r).comp hQ)
  · simp only [revealed, Matrix.fromCols_apply_inr, Matrix.of_apply]
    exact (measurable_pi_apply r).comp (measurable_snd.comp (measurable_pi_apply j))

omit [DecidableEq n] in
/-- A matrix fixing what a history of length `i + 1` reveals fixes what its first `i` entries
reveal, the right part of query `i` and the second component of response `i`. -/
private theorem mul_revealed_eq_of_mul_revealed_snoc_eq {m : Type*} {β : Type*} {q : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) q β) {i : ℕ}
    (h : Fin i → (m → ℝ) × (n → ℝ)) (r : (m → ℝ) × (n → ℝ)) {M : Matrix n n ℝ}
    (hM : M * revealed alg (i + 1) (Fin.snoc h r) = revealed alg (i + 1) (Fin.snoc h r)) :
    M * revealed alg i h = revealed alg i h ∧ M *ᵥ (alg.query i h).1 = (alg.query i h).1 ∧
      M *ᵥ r.2 = r.2 := by
  set A' := revealed alg (i + 1) (Fin.snoc h r)
  have hcol : ∀ k, M *ᵥ (fun x => A' x k) = fun x => A' x k := fun k => funext fun x => by
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (congrFun hM x) k
  have hsnoc : ∀ {k} (hk : k ≤ i + 1) (hk' : k ≤ i),
      (fun l : Fin k => (Fin.snoc h r : Fin (i + 1) → _) (Fin.castLE hk l)) =
        fun l => h (Fin.castLE hk' l) := fun hk hk' => funext fun l => by
    rw [show Fin.castLE hk l = Fin.castSucc (Fin.castLE hk' l) from Fin.ext rfl, Fin.snoc_castSucc]
  have hA : ∀ x k, revealed alg i h x k = A' x (Sum.map Fin.castSucc Fin.castSucc k) := by
    rintro x (j | j)
    · simp only [A', revealed, Matrix.fromCols_apply_inl, Sum.map_inl]
      simp only [QueryAlgorithm.rightQueryMatrix, QueryAlgorithm.queries, Matrix.of_apply]
      rw [← hsnoc _ j.isLt.le]
      rfl
    · simp only [A', revealed, Matrix.fromCols_apply_inr, Sum.map_inr, Matrix.of_apply,
        Fin.snoc_castSucc]
  refine ⟨?_, ?_, ?_⟩
  · ext x k
    have := congrFun (hcol (Sum.map Fin.castSucc Fin.castSucc k)) x
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, hA, this]
  · have := hcol (Sum.inl (Fin.last i))
    have hq : (fun x => A' x (Sum.inl (Fin.last i))) = (alg.query i h).1 := by
      funext x
      simp only [A', revealed, Matrix.fromCols_apply_inl, QueryAlgorithm.rightQueryMatrix,
        QueryAlgorithm.queries, Matrix.of_apply]
      exact congrArg (fun z => (alg.query i z).1 x) (hsnoc _ le_rfl)
    rwa [hq] at this
  · have := hcol (Sum.inr (Fin.last i))
    have hq : (fun x => A' x (Sum.inr (Fin.last i))) = r.2 := by
      funext x
      simp only [A', revealed, Matrix.fromCols_apply_inr, Matrix.of_apply, Fin.snoc_last]
    rwa [hq] at this

/-- The invariant at `i`, randomized over the stabilizer of what the history reveals. -/
private theorem map_history_eq_map_mul_stabRand {m : Type*} [Fintype m] {β : Type*}
    [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) q β} (halg : alg.IsMeasurable)
    (ν : Measure (Matrix m n ℝ)) [IsProbabilityMeasure ν] {i : ℕ} (hi : i ≤ q)
    (ih : StabInvariant alg ν i) :
    ν.map (fun x => (alg.history (twoSidedMulVec x) i, x)) =
      ((gaussianMatrix n n).prod ν).map (fun p => (alg.history (twoSidedMulVec p.2) i,
        p.2 * stabRand (revealed alg i (alg.history (twoSidedMulVec p.2) i)) p.1)) := by
  set γ := gaussianMatrix n n
  have hH := halg.measurable_history (O := twoSidedMulVec)
    (Measurable.twoSidedMulVec measurable_fst measurable_snd) hi
  have hVr := measurable_revealed halg hi
  have hφ : Measurable fun x : Matrix m n ℝ => (alg.history (twoSidedMulVec x) i, x) := by
    fun_prop
  have hH₂ : Measurable fun p : Matrix n n ℝ × Matrix m n ℝ =>
      alg.history (twoSidedMulVec p.2) i := hH.comp measurable_snd
  conv_lhs => rw [← (by simp : (γ.prod ν).map Prod.snd = ν), Measure.map_map hφ measurable_snd]
  refine Measure.map_prod_eq_of_forall_map_eq
    (F := fun _ x => (alg.history (twoSidedMulVec x) i, x))
    (G := fun g x => (alg.history (twoSidedMulVec x) i,
      x * stabRand (revealed alg i (alg.history (twoSidedMulVec x) i)) g))
    (by fun_prop) (by fun_prop) fun g => ?_
  exact ih (fun h => stabRand (revealed alg i h) g) (by fun_prop)
    (fun h => (stabRand_spec _ g).1) (fun h => (stabRand_spec _ g).2)

/-- The step of the induction for a frozen history `h` and matrix `x`: the pair query lemma on
the stabilizer of what `h` reveals, pushed forward by `M ↦ x M`. -/
private theorem map_snoc_mul_stabRand {m : Type*} [Fintype m] {β : Type*} {q : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) q β) {i : ℕ}
    {S : (Fin (i + 1) → (m → ℝ) × (n → ℝ)) → Matrix n n ℝ} (hSm : Measurable S)
    (hSo : ∀ h, HasOrthonormalCols (S h))
    (hSV : ∀ h, S h * revealed alg (i + 1) h = revealed alg (i + 1) h)
    (h : Fin i → (m → ℝ) × (n → ℝ)) (x : Matrix m n ℝ) :
    (gaussianMatrix n n).map (fun g =>
      ((Fin.snoc h (twoSidedMulVec (x * stabRand (revealed alg i h) g) (alg.query i h)) :
        Fin (i + 1) → (m → ℝ) × (n → ℝ)), x * stabRand (revealed alg i h) g)) =
    (gaussianMatrix n n).map (fun g =>
      ((Fin.snoc h (twoSidedMulVec (x * stabRand (revealed alg i h) g) (alg.query i h)) :
        Fin (i + 1) → (m → ℝ) × (n → ℝ)), x * stabRand (revealed alg i h) g *
          S (Fin.snoc h
            (twoSidedMulVec (x * stabRand (revealed alg i h) g) (alg.query i h))))) := by
  set V := revealed alg i h
  set w := (alg.query i h).1
  set u := (alg.query i h).2
  have hsm : Measurable fun p : (n → ℝ) × (n → ℝ) =>
      S (Fin.snoc h (x *ᵥ p.1, p.2) : Fin (i + 1) → (m → ℝ) × (n → ℝ)) := by fun_prop
  have hfix := fun p : (n → ℝ) × (n → ℝ) =>
    mul_revealed_eq_of_mul_revealed_snoc_eq alg h (x *ᵥ p.1, p.2) (hSV _)
  have hpair := map_pair_query_stabRand V w (xᴴ *ᵥ u) hsm (fun p => hSo _)
    (fun p => (hfix p).1) (fun p => (hfix p).2.1) (fun p => (hfix p).2.2)
  have hκ : Measurable fun q : ((n → ℝ) × (n → ℝ)) × Matrix n n ℝ =>
      ((Fin.snoc h (x *ᵥ q.1.1, q.1.2) : Fin (i + 1) → (m → ℝ) × (n → ℝ)), x * q.2) := by
    fun_prop
  have hφ₁ : Measurable fun M : Matrix n n ℝ => ((M *ᵥ w, Mᴴ *ᵥ (xᴴ *ᵥ u)), M) := by fun_prop
  have hφ₂ : Measurable fun M : Matrix n n ℝ => ((M *ᵥ w, Mᴴ *ᵥ (xᴴ *ᵥ u)),
      M * S (Fin.snoc h (x *ᵥ (M *ᵥ w), Mᴴ *ᵥ (xᴴ *ᵥ u)))) := by fun_prop
  have hR := measurable_stabRand_right V
  have h2 := congrArg (Measure.map fun q : ((n → ℝ) × (n → ℝ)) × Matrix n n ℝ =>
    ((Fin.snoc h (x *ᵥ q.1.1, q.1.2) : Fin (i + 1) → (m → ℝ) × (n → ℝ)), x * q.2)) hpair
  rw [Measure.map_map hκ hφ₁, Measure.map_map hκ hφ₂, Measure.map_map (hκ.comp hφ₁) hR,
    Measure.map_map (hκ.comp hφ₂) hR] at h2
  have htw : ∀ M : Matrix n n ℝ,
      twoSidedMulVec (x * M) (alg.query i h) = (x *ᵥ (M *ᵥ w), Mᴴ *ᵥ (xᴴ *ᵥ u)) := fun M => by
    simp only [twoSidedMulVec, Matrix.mulVec_mulVec, Matrix.conjTranspose_mul, w, u]
  simp only [htw]
  simpa only [Function.comp_def, Matrix.mul_assoc] using h2

/-- The induction step: the invariant for histories of length `i` gives it for `i + 1`. -/
private theorem stabInvariant_succ [Fintype m] {β : Type*} [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) q β} (halg : alg.IsMeasurable)
    (ν : Measure (Matrix m n ℝ)) [IsProbabilityMeasure ν] {i : ℕ} (hi : i < q)
    (ih : StabInvariant alg ν i) : StabInvariant alg ν (i + 1) := by
  intro S hSm hSo hSV
  have hH := halg.measurable_history (O := twoSidedMulVec)
    (Measurable.twoSidedMulVec measurable_fst measurable_snd) hi.le
  have hVr := measurable_revealed halg hi.le
  have hQ := halg.measurable_query i hi
  -- the next history, from the history and the matrix
  set nx : (Fin i → (m → ℝ) × (n → ℝ)) → Matrix m n ℝ → (Fin (i + 1) → (m → ℝ) × (n → ℝ)) :=
    fun h x => Fin.snoc h (twoSidedMulVec x (alg.query i h))
  have hnx : Measurable fun p : (Fin i → (m → ℝ) × (n → ℝ)) × Matrix m n ℝ => nx p.1 p.2 :=
    Measurable.finSnoc measurable_fst (Measurable.twoSidedMulVec measurable_snd
      (hQ.comp measurable_fst))
  have hΨ₁ : Measurable fun p : (Fin i → (m → ℝ) × (n → ℝ)) × Matrix m n ℝ =>
      (nx p.1 p.2, p.2) := by fun_prop
  have hΨ₂ : Measurable fun p : (Fin i → (m → ℝ) × (n → ℝ)) × Matrix m n ℝ =>
      (nx p.1 p.2, p.2 * S (nx p.1 p.2)) := by fun_prop
  have hφ : Measurable fun x : Matrix m n ℝ => (alg.history (twoSidedMulVec x) i, x) := by
    fun_prop
  have hH₁ : Measurable fun p : Matrix m n ℝ × Matrix n n ℝ =>
      alg.history (twoSidedMulVec p.1) i := hH.comp measurable_fst
  have hH₂ : Measurable fun p : Matrix n n ℝ × Matrix m n ℝ =>
      alg.history (twoSidedMulVec p.2) i := hH.comp measurable_snd
  have hRand : Measurable fun p : Matrix n n ℝ × Matrix m n ℝ =>
      (alg.history (twoSidedMulVec p.2) i,
        p.2 * stabRand (revealed alg i (alg.history (twoSidedMulVec p.2) i)) p.1) := by fun_prop
  have hY : Measurable fun p : Matrix m n ℝ × Matrix n n ℝ => (alg.history (twoSidedMulVec p.1) i,
      p.1 * stabRand (revealed alg i (alg.history (twoSidedMulVec p.1) i)) p.2) := by fun_prop
  have hhist : ∀ x : Matrix m n ℝ, alg.history (twoSidedMulVec x) (i + 1) =
      nx (alg.history (twoSidedMulVec x) i) x := fun x => rfl
  simp only [hhist]
  have e₁ : ν.map (fun x => (nx (alg.history (twoSidedMulVec x) i) x, x)) =
      (ν.map fun x => (alg.history (twoSidedMulVec x) i, x)).map fun p => (nx p.1 p.2, p.2) := by
    rw [Measure.map_map hΨ₁ hφ]
    rfl
  have e₂ : ν.map (fun x => (nx (alg.history (twoSidedMulVec x) i) x,
      x * S (nx (alg.history (twoSidedMulVec x) i) x))) =
      (ν.map fun x => (alg.history (twoSidedMulVec x) i, x)).map
        fun p => (nx p.1 p.2, p.2 * S (nx p.1 p.2)) := by
    rw [Measure.map_map hΨ₂ hφ]
    rfl
  rw [e₁, e₂, map_history_eq_map_mul_stabRand halg ν hi.le ih, Measure.map_map hΨ₁ hRand,
    Measure.map_map hΨ₂ hRand]
  -- freeze the matrix `x` and apply the pair query lemma on the stabilizer of `V(h)`
  rw [← Measure.prod_swap, Measure.map_map (hΨ₁.comp hRand) measurable_swap,
    Measure.map_map (hΨ₂.comp hRand) measurable_swap]
  refine Measure.map_prod_eq_of_forall_map_eq
    (F := fun x g => (nx (alg.history (twoSidedMulVec x) i)
      (x * stabRand (revealed alg i (alg.history (twoSidedMulVec x) i)) g),
        x * stabRand (revealed alg i (alg.history (twoSidedMulVec x) i)) g))
    (G := fun x g => (nx (alg.history (twoSidedMulVec x) i)
      (x * stabRand (revealed alg i (alg.history (twoSidedMulVec x) i)) g),
        x * stabRand (revealed alg i (alg.history (twoSidedMulVec x) i)) g *
          S (nx (alg.history (twoSidedMulVec x) i)
            (x * stabRand (revealed alg i (alg.history (twoSidedMulVec x) i)) g))))
    (hΨ₁.comp hY :) (hΨ₂.comp hY :) fun x => ?_
  exact map_snoc_mul_stabRand alg hSm hSo hSV _ x

/-- **Adaptive deferred decision for a unitarily invariant law, stabilizer form**: let the law
$\nu$ of $\mathbf{X} \in \mathbb{R}^{m \times n}$ be right unitarily invariant (Gaussian, Haar)
and $\tau$ the transcript of a measurable algorithm making `q` adaptive pair queries
$(\mathbf{w}, \mathbf{u})$ to `twoSidedMulVec X` (products $\mathbf{X}\mathbf{w}$ and
$\mathbf{X}^{\mathsf{H}}\mathbf{u}$). Let $\mathbf{S}(\tau)$ be an orthogonal matrix chosen
measurably from the transcript that fixes every vector of $\mathbb{R}^n$ the transcript reveals:
the right parts $\mathbf{w}_i$ of the queries (`QueryAlgorithm.rightQueryMatrix`) and the second
components $\mathbf{X}^{\mathsf{H}}\mathbf{u}_i$ of the responses. Then $(\tau, \mathbf{X})$ has
the law of $(\tau, \mathbf{X}\mathbf{S}(\tau))$; the rotated matrix gives the same transcript, by
`QueryAlgorithm.transcript_eq_of_forall_apply_queries_eq`.
[DerezinskiEpperlyMeyer2026, Theorem 3.1]; [Shamir2026, Lemma 4]; there for a Haar orthogonal
matrix with the oracles $\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$,
$\mathbf{A}^{\mathsf{H}}\mathbf{x}$ and $(\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$,
each a two-sided query sequence to $\mathbf{U}$; here for every right unitarily invariant law.
The hypotheses quantify over every `τ`, also those no run produces; for a one-sided algorithm the
second components of actual transcripts vanish, and `S` may be anything off them that is
measurable and orthogonal. -/
theorem QueryAlgorithm.IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant
    [Fintype m] [IsProbabilityMeasure μ] {β : Type*} [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) q β} (halg : alg.IsMeasurable)
    {ν : Measure (Matrix m n ℝ)} [IsRightUnitarilyInvariant ν] {X : Ω → Matrix m n ℝ}
    (hX : HasLaw X ν μ) {S : (Fin q → (m → ℝ) × (n → ℝ)) → Matrix n n ℝ} (hSm : Measurable S)
    (hSo : ∀ τ, HasOrthonormalCols (S τ))
    (hSq : ∀ τ, S τ * alg.rightQueryMatrix τ = alg.rightQueryMatrix τ)
    (hSr : ∀ τ, S τ * Matrix.of (fun r j => (τ j).2 r) = Matrix.of fun r j => (τ j).2 r) :
    IdentDistrib (fun ω => (alg.transcript (twoSidedMulVec (X ω)), X ω))
      (fun ω => (alg.transcript (twoSidedMulVec (X ω)),
        X ω * S (alg.transcript (twoSidedMulVec (X ω))))) μ μ := by
  have hν : IsProbabilityMeasure ν := hX.map_eq ▸ Measure.isProbabilityMeasure_map hX.aemeasurable
  have key : ∀ i ≤ q, StabInvariant alg ν i := by
    intro i
    induction i with
    | zero => exact fun _ => stabInvariant_zero alg ν
    | succ i ih => exact fun hi => stabInvariant_succ halg ν hi (ih (Nat.le_of_succ_le hi))
  have h := key q le_rfl S hSm hSo fun τ => by
    rw [revealed, Matrix.mul_fromCols]
    exact congrArg₂ Matrix.fromCols (hSq τ) (hSr τ)
  have hH := halg.measurable_history (O := twoSidedMulVec)
    (Measurable.twoSidedMulVec measurable_fst measurable_snd) (le_refl q)
  have hφ₁ : Measurable fun x : Matrix m n ℝ => (alg.history (twoSidedMulVec x) q, x) := by
    fun_prop
  have hφ₂ : Measurable fun x : Matrix m n ℝ =>
      (alg.history (twoSidedMulVec x) q, x * S (alg.history (twoSidedMulVec x) q)) := by fun_prop
  refine ⟨hφ₁.comp_aemeasurable hX.aemeasurable, hφ₂.comp_aemeasurable hX.aemeasurable, ?_⟩
  calc μ.map (fun ω => (alg.transcript (twoSidedMulVec (X ω)), X ω))
      = (μ.map X).map fun x => (alg.history (twoSidedMulVec x) q, x) :=
        (AEMeasurable.map_map_of_aemeasurable hφ₁.aemeasurable hX.aemeasurable).symm
    _ = (μ.map X).map fun x =>
          (alg.history (twoSidedMulVec x) q, x * S (alg.history (twoSidedMulVec x) q)) := by
        rw [hX.map_eq]
        exact h
    _ = _ := AEMeasurable.map_map_of_aemeasurable hφ₂.aemeasurable hX.aemeasurable

namespace QueryAlgorithm

/-- **Adaptive deferred decision for a unitarily invariant law, randomized stabilizer form**: the
stabilizer form `QueryAlgorithm.IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant`
with an orthogonal matrix $\mathbf{S}(\tau, Z)$ that also depends on a variable $Z$ independent
of $\mathbf{X}$ and, for every value of $Z$, fixes what the transcript $\tau$ reveals. Then
$(\tau, \mathbf{X})$ has the law of $(\tau, \mathbf{X}\mathbf{S}(\tau, Z))$. With
$\mathbf{S}(\tau, Z)$ Haar on the orthogonal matrices fixing the revealed vectors, this is the
form used in Shamir's Lemma 4: given $\tau$, $\mathbf{X}$ may be rotated by an independent Haar
element of that stabilizer.
[Shamir2026, Lemma 4]; there for a Haar orthogonal matrix and the oracle
$(\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$; here for every right unitarily
invariant law and any measurable randomized stabilizer. -/
theorem IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant_of_indepFun
    [Fintype m] [IsProbabilityMeasure μ] {β : Type*} [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) q β} (halg : alg.IsMeasurable)
    {ν : Measure (Matrix m n ℝ)} [IsRightUnitarilyInvariant ν] {X : Ω → Matrix m n ℝ}
    (hX : HasLaw X ν μ) {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ} (hZ : AEMeasurable Z μ)
    (hXZ : IndepFun X Z μ) {S : (Fin q → (m → ℝ) × (n → ℝ)) → ζ → Matrix n n ℝ}
    (hSm : Measurable (Function.uncurry S)) (hSo : ∀ τ z, HasOrthonormalCols (S τ z))
    (hSq : ∀ τ z, S τ z * alg.rightQueryMatrix τ = alg.rightQueryMatrix τ)
    (hSr : ∀ τ z, S τ z * Matrix.of (fun r j => (τ j).2 r) = Matrix.of fun r j => (τ j).2 r) :
    IdentDistrib (fun ω => (alg.transcript (twoSidedMulVec (X ω)), X ω))
      (fun ω => (alg.transcript (twoSidedMulVec (X ω)),
        X ω * S (alg.transcript (twoSidedMulVec (X ω))) (Z ω))) μ μ := by
  have hτ : Measurable fun x : Matrix m n ℝ => alg.transcript (twoSidedMulVec x) :=
    halg.measurable_transcript (Measurable.twoSidedMulVec measurable_fst measurable_snd)
  -- Freeze `Z = z`: for fixed `z` this is the stabilizer form with `S (·) z`.
  have h := hXZ.symm.identDistrib_prodMk_of_forall_map_eq hZ hX.aemeasurable
    (F := fun _ x => (alg.transcript (twoSidedMulVec x), x))
    (G := fun z x =>
      (alg.transcript (twoSidedMulVec x), x * S (alg.transcript (twoSidedMulVec x)) z))
    ((hτ.comp measurable_snd).prodMk measurable_snd)
    ((hτ.comp measurable_snd).prodMk (measurable_snd.matrix_mul
      (hSm.comp ((hτ.comp measurable_snd).prodMk measurable_fst)))) fun z => ?_
  · exact h.comp measurable_snd
  have hz := halg.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant hX
    (S := fun τ => S τ z) (hSm.comp (measurable_id.prodMk measurable_const))
    (fun τ => hSo τ z) (fun τ => hSq τ z) (fun τ => hSr τ z)
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable ?_ hX.aemeasurable]
  · exact hz.map_eq
  exact (hτ.prodMk (measurable_id.matrix_mul
    (hSm.comp (hτ.prodMk measurable_const)))).aemeasurable

end QueryAlgorithm

end NLAlib
