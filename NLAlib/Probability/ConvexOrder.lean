/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import NLAlib.ForMathlib.Probability.Kernel.Composition.IntegralCompProd
public import NLAlib.Probability.Distributions.UniformInjection

/-!
# Convex order from a barycenter, and Hoeffding's comparison

A random vector $Y$ dominates $X$ in convex order when $\mathbb{E} f(X) \le \mathbb{E} f(Y)$ for
every convex $f$. The easy direction of Strassen's theorem gives it from a coupling in which $X$ is
the conditional barycenter of $Y$: if a Markov kernel $\kappa$ moves the law $\mu$ of the first
variable to $\kappa \circ \mu$ and $\int Y \, d\kappa(a) = X(a)$, Jensen's inequality in each fibre
and integration in $a$ give the comparison
(`ConvexOn.integral_comp_le_integral_comp_of_integral_eq`, in
`NLAlib.ForMathlib.Probability.Kernel.Composition.IntegralCompProd`). Its main instance, proved
here, is **Hoeffding's comparison**: a population sum $\sum_j \mathbf{a}_{\iota(j)}$ over a
uniformly random injection $\iota : k \to n$ (sampling without replacement) is dominated in convex
order by the same sum over $\lvert k \rvert$ i.i.d. uniform indices (sampling with replacement)
(`ConvexOn.integral_uniformOn_injective_le_integral_pi`). Through one convex function each, it
transfers every exponential-moment tail of sampling with replacement to sampling without
replacement; the matrix Chernoff tails without replacement are the first consumer
(`NLAlib.Probability.MatrixConcentration.ChernoffWithoutReplacement`).

The values lie in any real Banach space, and $f$ is convex and continuous on a closed convex set
$s$ holding the values (the positive semidefinite cone for $\operatorname{tr} e^{\theta \cdot}$,
which is convex only on Hermitian matrices). Hoeffding's comparison is stated with Mathlib objects
only and declared in the `ConvexOn` namespace for dot notation; it uses the library's API for
uniform injections (`NLAlib.Probability.Distributions.UniformInjection`), so it stays here.


## Main results

* `ConvexOn.integral_uniformOn_injective_le_integral_pi`: Hoeffding's comparison of sampling
  without and with replacement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NLAlib

variable {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {s : Set E} {f : E → ℝ}

section Hoeffding

/-! ### Hoeffding's pattern kernel

For $\lvert k \rvert \le \lvert n \rvert$ every map $J : k \to n$ factors as $e_J \circ \pi_J$ with
$e_J$ injective and $\pi_J : k \to k$ (its pattern). The pattern kernel sends an injection
$\iota$ to the law of $\iota \circ \tau \circ \pi_J$ for $\tau$ uniform on the permutations of $k$
and $J$ uniform on $k \to n$, independent. Averaging over $\tau$ makes its barycenter
$\sum_j \mathbf{a}_{\iota(j)}$ (whatever the patterns); averaging the injection over the
permutations of $n$ makes its composition with the uniform injection uniform on $k \to n$. -/

open Equiv Function

variable {k n : Type*} [Fintype k] [Fintype n]

/-- For $\lvert k \rvert \le \lvert n \rvert$, every map $J : k \to n$ is $e \circ \pi$ for an
injection $e$ and a map $\pi : k \to k$. -/
private theorem exists_embedding_comp_eq (hk : Fintype.card k ≤ Fintype.card n) (J : k → n) :
    ∃ (e : k ↪ n) (π : k → k), ⇑e ∘ π = J := by
  classical
  obtain ⟨T, hJT, -, hT⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (Finset.univ.image J)) (Finset.card_image_le.trans_eq Finset.card_univ)
    (by rwa [Finset.card_univ])
  let φ : k ≃ T := Fintype.equivOfCardEq (by rw [Fintype.card_coe, hT])
  refine ⟨⟨fun j => (φ j : n), Subtype.val_injective.comp φ.injective⟩,
    fun j => φ.symm ⟨J j, hJT (Finset.mem_image_of_mem J (Finset.mem_univ j))⟩, ?_⟩
  funext j
  simp

/-- Averaging over the permutations of the sample: for every $\pi : k \to k$,
$\sum_\tau \sum_j g(\tau(\pi(j))) = \lvert k \rvert! \sum_l g(l)$. -/
private theorem sum_perm_sum_apply_comp [DecidableEq k] {M : Type*} [AddCommMonoid M]
    (g : k → M) (π : k → k) :
    ∑ τ : Perm k, ∑ j, g (τ (π j)) = (Fintype.card k).factorial • ∑ l, g l := by
  rcases isEmpty_or_nonempty k with _ | ⟨⟨m⟩⟩
  · simp
  have h (m' : k) : ∑ τ : Perm k, g (τ m') = ∑ τ : Perm k, g (τ m) := by
    refine Eq.trans ?_ (Equiv.sum_comp (Equiv.mulRight (swap m m')) fun τ : Perm k => g (τ m))
    simp [Perm.mul_apply]
  calc ∑ τ : Perm k, ∑ j, g (τ (π j)) = ∑ j, ∑ τ : Perm k, g (τ (π j)) := Finset.sum_comm
    _ = ∑ m' : k, ∑ τ : Perm k, g (τ m') := by simp only [h]
    _ = ∑ τ : Perm k, ∑ m', g (τ m') := Finset.sum_comm
    _ = ∑ _τ : Perm k, ∑ l, g l := by simp only [Equiv.sum_comp]
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]

/-- Averaging over the permutations of the population: for an injection $e : k \to n$,
$\lvert k \hookrightarrow n \rvert \sum_\sigma h(\sigma \circ e)
= \lvert n \rvert! \sum_\iota h(\iota)$, the last sum over the injections. -/
private theorem card_mul_sum_perm_comp [DecidableEq n] (h : (k → n) → ℝ) (e : k ↪ n) :
    (Fintype.card (k ↪ n) : ℝ) * ∑ σ : Perm n, h (σ ∘ e) =
      (Fintype.card n).factorial * ∑ ι : k ↪ n, h ι := by
  have hc (e' : k ↪ n) : ∑ σ : Perm n, h (σ ∘ e') = ∑ σ : Perm n, h (σ ∘ e) := by
    obtain ⟨σ₀, hσ₀⟩ := Perm.exists_smul_eq_embedding e e'
    refine Eq.trans ?_ (Equiv.sum_comp (Equiv.mulRight σ₀) fun σ : Perm n => h (σ ∘ e))
    refine Finset.sum_congr rfl fun σ _ => congrArg h ?_
    funext j
    simp [← hσ₀, Function.Embedding.smul_apply, Perm.smul_def]
  calc (Fintype.card (k ↪ n) : ℝ) * ∑ σ : Perm n, h (σ ∘ e)
      = ∑ e' : k ↪ n, ∑ σ : Perm n, h (σ ∘ e') := by
        rw [Finset.sum_congr rfl fun e' _ => hc e', Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
    _ = ∑ σ : Perm n, ∑ e' : k ↪ n, h (σ ∘ e') := Finset.sum_comm
    _ = ∑ _σ : Perm n, ∑ ι : k ↪ n, h ι := Finset.sum_congr rfl fun σ _ =>
        (Equiv.embeddingCongr (Equiv.refl k) σ).sum_comp fun ι : k ↪ n => h ι
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

/-- The counting identity behind the marginal of the pattern kernel: summing
$g(\iota \circ \tau \circ \pi_J)$ over injections $\iota$, permutations $\tau$ of $k$ and maps
$J$ gives $\lvert k \rvert! \, \lvert k \hookrightarrow n \rvert \sum_J g(J)$, when
$e_J \circ \pi_J = J$ with $e_J$ injective. -/
private theorem sum_embedding_sum_comp [DecidableEq k] (π : (k → n) → k → k)
    (e : (k → n) → k ↪ n) (he : ∀ J, ⇑(e J) ∘ π J = J) (g : (k → n) → ℝ) :
    ∑ ι : k ↪ n, ∑ p : Perm k × (k → n), g (ι ∘ p.1 ∘ π p.2) =
      (Fintype.card k).factorial * (Fintype.card (k ↪ n) * ∑ J, g J) := by
  classical
  have hτ (τ : Perm k) (J : k → n) : ∑ ι : k ↪ n, g (ι ∘ τ ∘ π J) = ∑ ι : k ↪ n, g (ι ∘ π J) :=
    (Equiv.embeddingCongr τ.symm (Equiv.refl n)).sum_comp fun ι : k ↪ n => g (ι ∘ π J)
  have hσ (J : k → n) : ((Fintype.card n).factorial : ℝ) * ∑ ι : k ↪ n, g (ι ∘ π J) =
      Fintype.card (k ↪ n) * ∑ σ : Perm n, g (σ ∘ J) := by
    refine (card_mul_sum_perm_comp (fun x => g (x ∘ π J)) (e J)).symm.trans ?_
    refine congrArg _ (Finset.sum_congr rfl fun σ _ => ?_)
    rw [Function.comp_assoc, he]
  have hperm (σ : Perm n) : ∑ J : k → n, g (σ ∘ J) = ∑ J, g J :=
    ((Equiv.refl k).arrowCongr σ).sum_comp g
  have hJ : ∑ J, ∑ ι : k ↪ n, g (ι ∘ π J) = Fintype.card (k ↪ n) * ∑ J, g J := by
    have h0 : ((Fintype.card n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    refine mul_left_cancel₀ h0 ?_
    rw [Finset.mul_sum, Finset.sum_congr rfl fun J _ => hσ J, ← Finset.mul_sum, Finset.sum_comm]
    simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
    ring
  calc ∑ ι : k ↪ n, ∑ p : Perm k × (k → n), g (ι ∘ p.1 ∘ π p.2)
      = ∑ τ : Perm k, ∑ J, ∑ ι : k ↪ n, g (ι ∘ τ ∘ π J) := by
        rw [Finset.sum_comm, Fintype.sum_prod_type]
    _ = ∑ _τ : Perm k, ∑ J, ∑ ι : k ↪ n, g (ι ∘ π J) := by simp only [hτ]
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, hJ, nsmul_eq_mul]

variable [MeasurableSpace n] [MeasurableSingletonClass n]

/-- Hoeffding's pattern kernel: $\iota$ goes to the law of $\iota \circ \tau \circ \pi_J$ for
$\tau$ uniform on the permutations of $k$ and $J$ uniform on $k \to n$, independent. -/
private noncomputable def patternKernel [DecidableEq k] (π : (k → n) → k → k) :
    Kernel (k → n) (k → n) :=
  Kernel.ofFunOfCountable fun ι => (Fintype.card (Perm k × (k → n)) : ℝ≥0∞)⁻¹ •
    ∑ p : Perm k × (k → n), Measure.dirac (ι ∘ p.1 ∘ π p.2)

/-- Unfolding the pattern kernel. -/
private theorem patternKernel_apply [DecidableEq k] (π : (k → n) → k → k) (ι : k → n) :
    patternKernel π ι = (Fintype.card (Perm k × (k → n)) : ℝ≥0∞)⁻¹ •
      ∑ p : Perm k × (k → n), Measure.dirac (ι ∘ p.1 ∘ π p.2) :=
  rfl

/-- The pattern kernel is Markov. -/
private theorem isMarkovKernel_patternKernel [DecidableEq k] [Nonempty (k → n)]
    (π : (k → n) → k → k) : IsMarkovKernel (patternKernel π) := by
  refine ⟨fun ι => ⟨?_⟩⟩
  rw [patternKernel_apply, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)

/-- Integral against the pattern kernel, as an average. -/
private theorem integral_patternKernel [DecidableEq k] (π : (k → n) → k → k) (ι : k → n)
    (G : (k → n) → E) :
    ∫ J, G J ∂patternKernel π ι = (Fintype.card (Perm k × (k → n)) : ℝ)⁻¹ •
      ∑ p : Perm k × (k → n), G (ι ∘ p.1 ∘ π p.2) := by
  rw [patternKernel_apply, integral_smul_measure,
    integral_finsetSum_measure fun _ _ => Integrable.of_finite]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **Barycenter of the pattern kernel**: whatever the patterns, the mean of
$\sum_j \mathbf{a}_{J(j)}$ under the pattern kernel at $\iota$ is $\sum_j \mathbf{a}_{\iota(j)}$. -/
private theorem integral_sum_patternKernel [DecidableEq k] [Nonempty (k → n)]
    (π : (k → n) → k → k) (A : n → E) (ι : k → n) :
    ∫ J, ∑ j, A (J j) ∂patternKernel π ι = ∑ j, A (ι j) := by
  have h1 (J : k → n) : ∑ τ : Perm k, ∑ j, A ((ι ∘ τ ∘ π J) j) =
      (Fintype.card k).factorial • ∑ l, A (ι l) :=
    sum_perm_sum_apply_comp (fun l => A (ι l)) (π J)
  rw [integral_patternKernel, Fintype.sum_prod_type, Finset.sum_comm,
    Finset.sum_congr rfl fun J _ => h1 J, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul (R := ℝ) (Fintype.card (k → n)),
    ← Nat.cast_smul_eq_nsmul (R := ℝ) (Fintype.card k).factorial, smul_smul, smul_smul,
    Fintype.card_prod, Fintype.card_perm, Nat.cast_mul, mul_comm ((Fintype.card k).factorial : ℝ),
    mul_assoc, inv_mul_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
      (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))), one_smul]

/-- Integral against the uniform law on injections, as an average over the injections. -/
private theorem integral_uniformOn_injective (F : (k → n) → ℝ) :
    ∫ ι, F ι ∂uniformOn {ι : k → n | Injective ι} =
      (Fintype.card (k ↪ n) : ℝ)⁻¹ * ∑ ι : k ↪ n, F ι := by
  classical
  have hmass (ι : k → n) : (uniformOn {ι : k → n | Injective ι}).real {ι} =
      if Injective ι then (Fintype.card (k ↪ n) : ℝ)⁻¹ else 0 := by
    split_ifs with h
    · rw [measureReal_def, uniformOn_injective_singleton h, Fintype.card_embedding_eq,
        ENNReal.toReal_inv, ENNReal.toReal_natCast]
    · rw [measureReal_def, uniformOn, cond_apply (Set.toFinite _).measurableSet,
        Set.inter_singleton_eq_empty.2 h]
      simp
  rw [integral_fintype Integrable.of_finite]
  simp only [hmass, smul_eq_mul, ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum,
    Finset.sum_subtype (p := Injective) _ (fun ι => by simp)]
  exact congrArg _ ((Equiv.subtypeInjectiveEquivEmbedding k n).sum_comp fun ι : k ↪ n => F ι)

/-- Integral against the uniform law on maps $k \to n$, as an average. -/
private theorem integral_pi_uniformOn_univ [DecidableEq k] (G : (k → n) → ℝ) :
    ∫ J, G J ∂Measure.pi (fun _ : k => uniformOn (Set.univ : Set n)) =
      (Fintype.card (k → n) : ℝ)⁻¹ * ∑ J, G J := by
  rw [← uniformOn_pi, Set.pi_univ, integral_fintype Integrable.of_finite, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [measureReal_def, uniformOn_univ, Measure.count_singleton, smul_eq_mul, ENNReal.toReal_div]
  simp

/-- **Marginal of the pattern kernel**: composed with the uniform law on injections it gives the
uniform law on $k \to n$, in integral form. -/
private theorem integral_comp_patternKernel [DecidableEq k] [Nonempty (k → n)]
    (π : (k → n) → k → k) (e : (k → n) → k ↪ n) (he : ∀ J, ⇑(e J) ∘ π J = J)
    (g : (k → n) → ℝ) :
    ∫ J, g J ∂(patternKernel π ∘ₘ uniformOn {ι : k → n | Injective ι}) =
      (Fintype.card (k → n) : ℝ)⁻¹ * ∑ J, g J := by
  classical
  have := isMarkovKernel_patternKernel (n := n) π
  have hD : (Fintype.card (k ↪ n) : ℝ) ≠ 0 := by
    have : Nonempty (k ↪ n) := ⟨e (Classical.arbitrary _)⟩
    exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hN : (Fintype.card (k → n) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hk : ((Fintype.card k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [Measure.integral_comp Integrable.of_finite, integral_uniformOn_injective]
  simp only [integral_patternKernel, smul_eq_mul]
  rw [← Finset.mul_sum, sum_embedding_sum_comp π e he g, Fintype.card_prod, Fintype.card_perm,
    Nat.cast_mul]
  field_simp

end Hoeffding

/-- **Hoeffding's comparison**: a population sum sampled without replacement is dominated in
convex order by the same sum sampled with replacement. For a population
$\mathbf{a} : n \to E$ in a real Banach space, $\lvert k \rvert \le \lvert n \rvert$, and $f$
convex and continuous on a closed set $s$ holding every with-replacement sum
$\sum_j \mathbf{a}_{J(j)}$,
$$\mathbb{E}_{\iota} f\Bigl(\sum_j \mathbf{a}_{\iota(j)}\Bigr) \le
\mathbb{E}_{J} f\Bigl(\sum_j \mathbf{a}_{J(j)}\Bigr) \,,$$
$\iota : k \to n$ a uniform injection, $J$ a vector of $\lvert k \rvert$ i.i.d. uniform indices.
[Hoeffding1963, Theorem 4] (there scalar, $f$ continuous and convex); [GrossNesme2010, Section D]
(there a finite set in a vector space and $f$ convex on its convex hull, applied to matrices).
Here any real Banach space and any $f$ convex and continuous on a closed convex $s$; the hypothesis
$\lvert k \rvert \le \lvert n \rvert$ is needed since otherwise the left side is $0$ and a convex
$f$ may be negative. Proof: the kernel form with a private kernel that composes the injection
with a random pattern $k \to k$ whose law is invariant under permutations of $k$ (the barycenter
is the injective sum) and whose composition with a uniform injection is uniform on $k \to n$.
The statement is that of the prototype's `integral_uniform_subset_convex_le_iid` (there on subsets,
`PMF`, `Fin k` and $s$ the whole space); the proof is new, the pattern kernel and two permutation
averages replacing the prototype's explicit coupling and conditional weights.
Result: hoeffding-sampling-without-replacement -/
theorem _root_.ConvexOn.integral_uniformOn_injective_le_integral_pi {k n : Type*} [Fintype k]
    [Fintype n] [MeasurableSpace n] [MeasurableSingletonClass n] (hf : ConvexOn ℝ s f)
    (hfc : ContinuousOn f s) (hs : IsClosed s) (hk : Fintype.card k ≤ Fintype.card n) (A : n → E)
    (hA : ∀ J : k → n, ∑ j, A (J j) ∈ s) :
    ∫ ι, f (∑ j, A (ι j)) ∂uniformOn {ι : k → n | Function.Injective ι} ≤
      ∫ J, f (∑ j, A (J j)) ∂Measure.pi fun _ : k => uniformOn (Set.univ : Set n) := by
  classical
  obtain ⟨e₀⟩ := Function.Embedding.nonempty_of_card_le hk
  have : Nonempty (k → n) := ⟨e₀⟩
  choose e π he using exists_embedding_comp_eq hk
  have := isMarkovKernel_patternKernel (n := n) π
  calc ∫ ι, f (∑ j, A (ι j)) ∂uniformOn {ι : k → n | Function.Injective ι}
      ≤ ∫ J, f (∑ j, A (J j)) ∂(patternKernel π ∘ₘ uniformOn {ι : k → n | Function.Injective ι}) :=
        hf.integral_comp_le_integral_comp_of_integral_eq hfc hs
          (ae_of_all _ fun _ => Integrable.of_finite) (ae_of_all _ fun _ => ae_of_all _ hA)
          (ae_of_all _ fun ι => integral_sum_patternKernel π A ι) Integrable.of_finite
          Integrable.of_finite
    _ = _ := by rw [integral_comp_patternKernel π e he, integral_pi_uniformOn_univ]

end NLAlib
