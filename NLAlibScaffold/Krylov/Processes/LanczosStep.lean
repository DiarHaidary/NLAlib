/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.RoundingErrors
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2
public import NLAlibScaffold.Krylov.Processes.LanczosProgramTree

/-!
# One step of the Lanczos program in the standard model

One step of `NLAlib.lanczosStepWith` under `NLAlib.Computation.IsRelErrSem`, for any product
`mv` meeting a normwise matvec specification (`NLAlib.LanczosMvSpec`), succeeds and has the local
errors of the kernels (`NLAlib.LanczosStepErr`): the product, the two `axpy` updates
($\gamma_2$), the inner product ($\gamma_N$) and the normalisation ($u$, near unit length
$\gamma_{N+4}$). The tools are a frame relation on stores (`NLAlib.StoreFrame`) and decoded
vectors and cells (`NLAlib.DecVec`, `NLAlib.DecCell`). Design:
`docs/design/Krylov-LanczosRounding.md` (§2.2).

## Main definitions

* `NLAlib.LanczosStepErr`: the local errors of one computed step.
* `NLAlib.LanczosMvSpec`: a normwise specification of the product of the program.

## Main results

* `NLAlib.abs_norm_sq_sub_one_le_of_relErr_normalize`: a computed normalisation is nearly unit.
* `NLAlib.exec_lanczosStepWith`: one step.
-/

@[expose] public section

open Finset
open scoped Matrix

namespace NLAlib

open Computation Builder

/-! ### Norm helpers -/

/-- An entrywise bound gives a bound of the Euclidean norm. -/
theorem norm_toLp_le_of_abs_le {N : ℕ} {x y : Fin N → ℝ} (h : ∀ i, |x i| ≤ y i) :
    ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (sum_le_sum fun i _ => ?_)
  simp only [Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) ((h i).trans (le_abs_self _)) 2

/-- Entrywise relative errors bounded by $\gamma$ have norm at most $\gamma\|\mathbf{x}\|$. -/
theorem norm_toLp_mul_le {N : ℕ} {x θ : Fin N → ℝ} {γ : ℝ} (hγ : 0 ≤ γ)
    (h : ∀ i, |θ i| ≤ γ) : ‖WithLp.toLp 2 (fun i => x i * θ i)‖ ≤ γ * ‖WithLp.toLp 2 x‖ := by
  calc _ ≤ ‖WithLp.toLp 2 (γ • fun i => |x i|)‖ := norm_toLp_le_of_abs_le fun i => by
        rw [abs_mul, Pi.smul_apply, smul_eq_mul, mul_comm γ]
        exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
    _ = γ * ‖WithLp.toLp 2 x‖ := by
        rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hγ]
        congr 1
        simp [EuclideanSpace.norm_eq]

/-- $mu < 1$ from $nu < 1$ for $m \le n$, $u \ge 0$. -/
theorem cast_mul_lt_one_of_le {u : ℝ} {m n : ℕ} (hu : 0 ≤ u) (hmn : m ≤ n)
    (h : (n : ℝ) * u < 1) : (m : ℝ) * u < 1 :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hu) h

/-! ### Store frames and decoded vectors -/

section Store

variable {P K : Type} [DecidableEq P]

/-- **A store frame**: `s'` has the shape of `s` and, at tag `p`, the cells of `s` outside the
region `A` (buffer, index). -/
def StoreFrame (p : P) (s s' : Store P K) (A : ℕ → ℕ → Prop) : Prop :=
  s'.shape = s.shape ∧ ∀ b i, ¬ A b i → s'.read p b i = s.read p b i

/-- The block of `n` cells of buffer `b` from offset `off`. -/
def StoreBlock (b off n : ℕ) : ℕ → ℕ → Prop := fun b' i => b' = b ∧ off ≤ i ∧ i < off + n

/-- **A decoded vector**: the $N$ cells of buffer `b` from `off` hold words decoding to
$\mathbf{x}$ at tag `p`. -/
def DecVec (s : Store P K) (p : P) (dec : P → K → ℝ) (b off : ℕ) {N : ℕ} (x : Fin N → ℝ) :
    Prop :=
  ∀ i : Fin N, ∃ w, s.read p b (off + i) = some w ∧ dec p w = x i

/-- **A decoded cell**: cell `i` of buffer `b` holds a word decoding to $x$ at tag `p`. -/
def DecCell (s : Store P K) (p : P) (dec : P → K → ℝ) (b i : ℕ) (x : ℝ) : Prop :=
  ∃ w, s.read p b i = some w ∧ dec p w = x

variable {p : P} {dec : P → K → ℝ} {s s' s'' : Store P K} {A B : ℕ → ℕ → Prop}

theorem StoreFrame.refl (s : Store P K) (A : ℕ → ℕ → Prop) : StoreFrame p s s A :=
  ⟨rfl, fun _ _ _ => rfl⟩

theorem StoreFrame.trans (h : StoreFrame p s s' A) (h' : StoreFrame p s' s'' B) :
    StoreFrame p s s'' fun b i => A b i ∨ B b i :=
  ⟨h'.1.trans h.1, fun b i hb => (h'.2 b i fun hB => hb (Or.inr hB)).trans
    (h.2 b i fun hA => hb (Or.inl hA))⟩

theorem StoreFrame.mono (h : StoreFrame p s s' A) (hAB : ∀ b i, A b i → B b i) :
    StoreFrame p s s' B :=
  ⟨h.1, fun b i hb => h.2 b i fun hA => hb (hAB b i hA)⟩

theorem storeFrame_of_write {b i : ℕ} {v : K} (h : s.write p b i v = some s') :
    StoreFrame p s s' (StoreBlock b i 1) :=
  ⟨Store.shape_of_write_eq_some h, fun b' i' hb' => Store.read_of_write_eq_some_of_ne h (by
    by_cases hb : b' = b
    · exact Or.inr fun hi => hb' ⟨hb, by omega, by omega⟩
    · exact Or.inl hb)⟩

theorem storeFrame_of_writeBlock {b off : ℕ} {xs : Array K}
    (h : s.writeBlock p b off xs = some s') : StoreFrame p s s' (StoreBlock b off xs.size) :=
  ⟨Store.shape_of_writeBlock_eq_some h, fun b' i' hb' =>
    Store.read_of_writeBlock_eq_some_of_ne h (by
      by_cases hb : b' = b
      · exact Or.inr (by by_contra hc; exact hb' ⟨hb, by omega, by omega⟩)
      · exact Or.inl hb)⟩

theorem DecVec.frame {N b off : ℕ} {x : Fin N → ℝ} (h : DecVec s p dec b off x)
    (hf : StoreFrame p s s' A) (hA : ∀ i < N, ¬ A b (off + i)) : DecVec s' p dec b off x :=
  fun i => by rw [hf.2 _ _ (hA i i.2)]; exact h i

theorem DecCell.frame {b i : ℕ} {x : ℝ} (h : DecCell s p dec b i x) (hf : StoreFrame p s s' A)
    (hA : ¬ A b i) : DecCell s' p dec b i x := by
  rw [DecCell, hf.2 _ _ hA]; exact h

theorem DecVec.of_writeBlock {N b off : ℕ} {W : ℕ → K}
    (h : s.writeBlock p b off ((List.range N).toArray.map W) = some s') :
    DecVec s' p dec b off fun i : Fin N => dec p (W i) := fun i =>
  ⟨W i, by rw [Store.read_of_writeBlock_eq_some_of_lt h (by simp)]; simp, rfl⟩

theorem DecCell.of_write {b i : ℕ} {v : K} (h : s.write p b i v = some s') :
    DecCell s' p dec b i (dec p v) :=
  ⟨v, Store.read_of_write_eq_some h, rfl⟩

theorem exists_write_of_shape {S : Array (P × ℕ)} (hs : s.shape = S) {b i n : ℕ}
    (hb : S[b]? = some (p, n)) (hi : i < n) (v : K) : ∃ s', s.write p b i v = some s' :=
  Store.exists_write_eq_some_of_getElem?_shape v (hs ▸ hb) hi

end Store


/-! ### Normalisation -/

/-- **A computed normalisation is nearly unit** (pure real): if $\mathbf{z} \ne \mathbf{0}$,
$s = \sum_i z_i^2(1 + \eta_i)$ with each $1 + \eta_i$ a product of $n$ factors
$(1 + \delta)^{\pm 1}$, $\lvert \delta \rvert \le u$ (a computed
$\mathbf{z}^{\mathsf{T}}\mathbf{z}$, `NLAlib.Computation.IsRoundingProduct`),
$\beta = \sqrt{s}\,(1 + \sigma)$ with $\lvert\sigma\rvert \le u$,
$v_i = (z_i/\beta)(1 + \delta_i)$ with $\lvert\delta_i\rvert \le u$, $0 \le u$ and
$(n + 4)u < 1$, then $s > 0$, $\beta > 0$ and
$\lvert\lVert\mathbf{v}\rVert^2 - 1\rvert \le \gamma_{n+4}$: $\lVert\mathbf{v}\rVert^2$ is the
ratio of a weighted mean of $(1 + \delta_i)^2$ (two factors) to a weighted mean of
$1 + \eta_i$ ($n$ factors) times $(1 + \sigma)^2$ (two), $n + 4$ factors in all
[Higham2002, Lemmas 3.1 and 3.3]. -/
theorem abs_norm_sq_sub_one_le_of_relErr_normalize {n : ℕ} {u s β : ℝ} {z v : Fin n → ℝ}
    {η δ : Fin n → ℝ} {σ : ℝ} (hu : 0 ≤ u) (hn : ((n + 4 : ℕ) : ℝ) * u < 1) (hz : z ≠ 0)
    (hη : ∀ i, IsRoundingProduct u n (η i)) (hs : s = ∑ i, z i * z i * (1 + η i))
    (hσ : |σ| ≤ u) (hβ : β = √s * (1 + σ)) (hδ : ∀ i, |δ i| ≤ u)
    (hv : ∀ i, v i = z i / β * (1 + δ i)) :
    0 < s ∧ 0 < β ∧ |‖WithLp.toLp 2 v‖ ^ 2 - 1| ≤ roundingFactor (n + 4) u := by
  have hu1 : u < 1 := by
    have : (1 : ℝ) * u ≤ ((n + 4 : ℕ) : ℝ) * u := by gcongr; norm_cast; omega
    linarith
  have hZ : 0 < ∑ i, z i * z i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
    exact (mul_self_pos.mpr hi).trans_le
      (single_le_sum (fun j _ => mul_self_nonneg (z j)) (mem_univ i))
  obtain ⟨η', hη', hsη⟩ := exists_isRoundingProduct_sum_mul_one_add_eq hu hu1 univ
    (fun i => z i * z i) η (fun i _ => mul_self_nonneg _) (fun i _ => hη i)
  have h1η : 0 < 1 + η' :=
    (pow_pos (by linarith) n).trans_le ((isRoundingProduct_iff hu hu1).mp hη').1
  have hs' : s = (∑ i, z i * z i) * (1 + η') := hs.trans hsη
  have hspos : 0 < s := by rw [hs']; positivity
  have h1σ : 0 < 1 + σ := by linarith [neg_abs_le σ]
  have hβpos : 0 < β := by rw [hβ]; exact mul_pos (Real.sqrt_pos.mpr hspos) h1σ
  refine ⟨hspos, hβpos, ?_⟩
  have hδ2 := fun i => (isRoundingProduct_one_of_abs_le (hδ i)).mul
    (isRoundingProduct_one_of_abs_le (hδ i))
  obtain ⟨φ, hφ, hφeq⟩ := exists_isRoundingProduct_sum_mul_one_add_eq hu hu1 univ
    (fun i => z i * z i) _ (fun i _ => mul_self_nonneg _) (fun i _ => hδ2 i)
  have hβsq : β ^ 2 = s * (1 + σ) ^ 2 := by rw [hβ, mul_pow, Real.sq_sqrt hspos.le]
  have hsum : ∑ i, v i ^ 2 =
      (∑ i, z i * z i * (1 + ((1 + δ i) * (1 + δ i) - 1))) / β ^ 2 := by
    rw [sum_div]
    refine sum_congr rfl fun i _ => ?_
    rw [hv]
    field_simp
    ring
  have key : ‖WithLp.toLp 2 v‖ ^ 2 = (1 + φ) / ((1 + η') * (1 + σ) * (1 + σ)) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [hsum, hφeq, hβsq, hs', div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hR := hφ.div ((hη'.mul (isRoundingProduct_one_of_abs_le hσ)).mul
    (isRoundingProduct_one_of_abs_le hσ))
  rw [show 2 + (n + 1 + 1) = n + 4 by omega] at hR
  simp only [add_sub_cancel] at hR
  rw [key]
  exact hR.abs_le hn

/-- **The facts of a computed normalisation** $\beta = \mathrm{fl}(\sqrt{\mathbf{z}^{\mathsf{T}}
\mathbf{z}})$, $\mathbf{v} = \mathbf{z}/\beta$ unless $\beta = 0$ (then $\mathbf{v} =
\mathbf{z}$): $\beta \ge 0$, $\beta = 0$ exactly when $\mathbf{z} = \mathbf{0}$, then
$\mathbf{v} = \mathbf{0}$; otherwise $\mathbf{v}$ is nearly unit; and
$\|\beta\mathbf{v} - \mathbf{z}\| \le u\|\mathbf{z}\|$. -/
theorem facts_of_relErr_normalize {n : ℕ} {u s β σ : ℝ} {z v η : Fin n → ℝ} (hu : 0 ≤ u)
    (hn : ((n + 4 : ℕ) : ℝ) * u < 1) (hη : ∀ i, IsRoundingProduct u n (η i))
    (hs : s = ∑ i, z i * z i * (1 + η i)) (hσ : |σ| ≤ u) (hβ : β = √s * (1 + σ))
    (hv0 : β = 0 → v = z) (hv : β ≠ 0 → ∀ i, ∃ δ : ℝ, |δ| ≤ u ∧ v i = z i / β * (1 + δ)) :
    0 ≤ β ∧ (z = 0 → β = 0) ∧ (β = 0 → v = 0) ∧
      (β ≠ 0 → |‖WithLp.toLp 2 v‖ ^ 2 - 1| ≤ roundingFactor (n + 4) u) ∧
      ‖WithLp.toLp 2 (β • v - z)‖ ≤ u * ‖WithLp.toLp 2 z‖ ∧ (z ≠ 0 → 0 < β) := by
  by_cases hz : z = 0
  · have hs0 : s = 0 := by simp [hs, hz]
    have hβ0 : β = 0 := by simp [hβ, hs0]
    have hv' := hv0 hβ0
    refine ⟨hβ0.ge, fun _ => hβ0, fun _ => hv'.trans hz, fun h => absurd hβ0 h, ?_,
      fun h => absurd hz h⟩
    simp [hβ0, hz]
  obtain ⟨-, hβpos, -⟩ := abs_norm_sq_sub_one_le_of_relErr_normalize hu hn hz hη hs hσ hβ
    (δ := fun _ => 0) (v := fun i => z i / β * (1 + 0)) (fun _ => by simpa using hu)
    (fun _ => rfl)
  choose δ hδ hvδ using hv hβpos.ne'
  obtain ⟨-, -, hunit⟩ := abs_norm_sq_sub_one_le_of_relErr_normalize hu hn hz hη hs hσ hβ hδ hvδ
  refine ⟨hβpos.le, fun h => absurd h hz, fun h => absurd h hβpos.ne', fun _ => hunit, ?_,
    fun _ => hβpos⟩
  have heq : β • v - z = fun i => z i * δ i := by
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hvδ i]
    field_simp
    ring
  rw [heq]
  exact norm_toLp_mul_le hu hδ

/-! ### The local errors of one step -/

/-- **The local errors of one computed Lanczos step** from $\mathbf{v}$ (previous vector
$\mathbf{v}_0$, coefficient $\beta_0$) through the product $\mathbf{u}$, the updates
$\mathbf{w}$, $\mathbf{z}$ and the coefficient $\alpha$ to $\beta$ and the next vector
$\mathbf{v}_2$: the product has error at most $c\|\mathbf{v}\|$, the two updates relative
errors $g_2$, the inner product $g_N$, the normalisation $u$; $\beta \ge 0$ vanishes when
$\mathbf{z}$ does; on breakdown $\mathbf{v}_2 = \mathbf{0}$, and otherwise $\mathbf{v}_2$ is
nearly unit, $\lvert\|\mathbf{v}_2\|^2 - 1\rvert \le \gamma$. The clauses of
`NLAlib.LanczosRun` for one step, with one bound per kernel. -/
structure LanczosStepErr {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (c g₂ gN u γ : ℝ)
    (v₀ v : Fin N → ℝ) (β₀ : ℝ) (uv w z : Fin N → ℝ) (α β : ℝ) (v₂ : Fin N → ℝ) : Prop where
  /-- The product. -/
  norm_u_sub_le : ‖WithLp.toLp 2 (uv - H *ᵥ v)‖ ≤ c * ‖WithLp.toLp 2 v‖
  /-- The first update. -/
  norm_w_sub_le : ‖WithLp.toLp 2 (w - (uv - β₀ • v₀))‖ ≤
    g₂ * (‖WithLp.toLp 2 uv‖ + |β₀| * ‖WithLp.toLp 2 v₀‖)
  /-- The inner product. -/
  abs_α_sub_le : |α - v ⬝ᵥ w| ≤ gN * ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 w‖
  /-- The second update. -/
  norm_z_sub_le : ‖WithLp.toLp 2 (z - (w - α • v))‖ ≤
    g₂ * (‖WithLp.toLp 2 w‖ + |α| * ‖WithLp.toLp 2 v‖)
  /-- The normalisation. -/
  norm_smul_sub_le : ‖WithLp.toLp 2 (β • v₂ - z)‖ ≤ u * ‖WithLp.toLp 2 z‖
  /-- The coefficient is nonnegative. -/
  β_nonneg : 0 ≤ β
  /-- The coefficient vanishes with the unnormalised vector. -/
  β_eq_zero : z = 0 → β = 0
  /-- Breakdown leaves the zero vector. -/
  v_eq_zero : β = 0 → v₂ = 0
  /-- Nearly unit next vector. -/
  abs_norm_sq_sub_one_le : β ≠ 0 → |‖WithLp.toLp 2 v₂‖ ^ 2 - 1| ≤ γ

/-! ### The pieces of a step -/

section Pieces

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C) {p : P}
  {u : P → ℝ} {dec : P → K → ℝ}

theorem DecVec.nat {s : Store P K} {b off N : ℕ} {x : Fin N → ℝ} (h : DecVec s p dec b off x) :
    ∀ i < N, ∃ w, s.read p b (off + i) = some w ∧ dec p w = vecSeq x i := fun i hi => by
  obtain ⟨w, hw, hd⟩ := h ⟨i, hi⟩
  exact ⟨w, hw, by rw [hd, vecSeq, dif_pos hi]⟩

/-- **Negate a coefficient, then `axpy`**: `s[0] ← -s[src]`, then
$\mathbf{y} \leftarrow s_0\mathbf{x} + \mathbf{y}$ on two disjoint slots of `W`. The new
$\mathbf{y}'$ is $\mathbf{y} - a\mathbf{x}$ up to $\gamma_2(\|\mathbf{y}\| +
\lvert a\rvert\|\mathbf{x}\|)$. -/
theorem exec_neg_axpy (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hu : 2 * u p < 1)
    (st : St P K C) {S : Array (P × ℕ)} (hsh : st.store.shape = S) {W sb : ℕ} (src X Y : IExp ℕ)
    {N : ℕ} {x y : Fin N → ℝ} {a : ℝ} (hWs : W ≠ sb) (hS : S[sb]? = some (p, 4))
    (hXY : X.eval + N ≤ Y.eval ∨ Y.eval + N ≤ X.eval) (ha : DecCell st.store p dec sb src.eval a)
    (hx : DecVec st.store p dec W X.eval x) (hy : DecVec st.store p dec W Y.eval y) :
    ∃ (st' : St P K C) (y' : Fin N → ℝ), (∀ f, exec I (ins (.un p .neg ⟨sb, 0⟩ ⟨sb, src⟩) >>=
        fun _ => axpy p ⟨sb, 0⟩ W X W Y (.const N) >>= f).run st = exec I (f ()).run st') ∧
      StoreFrame p st.store st'.store
        (fun b i => StoreBlock sb 0 1 b i ∨ StoreBlock W Y.eval N b i) ∧
      DecVec st'.store p dec W Y.eval y' ∧
      ‖WithLp.toLp 2 (y' - (y - a • x))‖ ≤
        roundingFactor 2 (u p) * (‖WithLp.toLp 2 y‖ + |a| * ‖WithLp.toLp 2 x‖) := by
  obtain ⟨wa, hwa, hda⟩ := ha
  obtain ⟨z, hz, hdz⟩ := h.neg p wa
  obtain ⟨s₁, hs₁⟩ := exists_write_of_shape hsh hS (by norm_num : 0 < 4) z
  obtain ⟨st₁, h₁, hst₁⟩ := exec_ins_un I (st := st) (dst := ⟨sb, 0⟩) (x := ⟨sb, src⟩) hwa hz hs₁
  have hf₁ := storeFrame_of_write hs₁
  rw [← hst₁] at hf₁
  have hn : ∀ i, ¬ StoreBlock sb 0 1 W i := fun _ hb => hWs hb.1
  obtain ⟨st₂, Wv, h₂, hb₂, hW⟩ := IsRelErrSem.exec_axpy I p st₁ h ⟨sb, 0⟩ W X W Y (.const N)
    (-a) (vecSeq x) (vecSeq y) hu ⟨z, by rw [hst₁]; exact Store.read_of_write_eq_some hs₁,
      by rw [hdz, hda]⟩ ((hx.frame hf₁ fun _ _ => hn _).nat) ((hy.frame hf₁ fun _ _ => hn _).nat)
    (fun h' => absurd h'.symm hWs) (fun _ i hi j hj he => by
      simp only [IExp.eval_const] at hi hj; omega)
  have hf₂ := storeFrame_of_writeBlock hb₂
  simp only [Array.size_map, List.size_toArray, List.length_range, IExp.eval_const] at hf₂
  refine ⟨st₂, fun i => dec p (Wv i), fun f => ?_, (hf₁.trans hf₂), DecVec.of_writeBlock hb₂, ?_⟩
  · rw [exec_bind_of_exec_eq_some I h₁ (seqShape_ins _),
      exec_bind_of_exec_eq_some I h₂ (seqShape_axpy _ _ _ _ _ _ _)]
  · have hu0 : 0 ≤ u p := h.nonneg trivial
    have hγ0 : 0 ≤ roundingFactor 2 (u p) := roundingFactor_nonneg hu0 (by exact_mod_cast hu)
    have huγ : u p ≤ roundingFactor 2 (u p) := (le_roundingFactor_one hu0 (by linarith)).trans
      (roundingFactor_le_roundingFactor hu0 (by norm_num) (by exact_mod_cast hu))
    have hW' : ∀ i : Fin N, ∃ θ δ : ℝ, |θ| ≤ roundingFactor 2 (u p) ∧ |δ| ≤ u p ∧
        dec p (Wv i) = -a * x i * (1 + θ) + y i * (1 + δ) := fun i => by
      simpa [vecSeq_fin] using hW i (by simp)
    choose θ δ hθ hδ hWe using hW'
    have heq : (fun i : Fin N => dec p (Wv i)) - (y - a • x) =
        (fun i : Fin N => (-a * x i) * θ i) + fun i => y i * δ i := by
      ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hWe]; ring
    rw [heq, WithLp.toLp_add]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_toLp_mul_le (x := fun i => -a * x i) hγ0 hθ
    have h2 := norm_toLp_mul_le (x := y) hu0 hδ
    have h3 : ‖WithLp.toLp 2 (fun i => -a * x i)‖ = |a| * ‖WithLp.toLp 2 x‖ := by
      rw [show (fun i => -a * x i) = (-a) • x from rfl, WithLp.toLp_smul, norm_smul,
        Real.norm_eq_abs, abs_neg]
    rw [h3] at h1
    nlinarith [norm_nonneg (WithLp.toLp 2 y), abs_nonneg a, norm_nonneg (WithLp.toLp 2 x)]

theorem sum_range_extendZero {N : ℕ} (f : ℝ → ℝ → ℝ) (x y : Fin N → ℝ) :
    ∑ i ∈ range N, f (vecSeq x i) (vecSeq y i) = ∑ i : Fin N, f (x i) (y i) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => f (vecSeq x i) (vecSeq y i))]
  simp [vecSeq_fin]

/-- Cauchy–Schwarz on absolute values: $\sum_i \lvert x_i\rvert\lvert y_i\rvert \le
\|\mathbf{x}\|\|\mathbf{y}\|$. -/
theorem sum_abs_mul_abs_le_norm {N : ℕ} (x y : Fin N → ℝ) :
    ∑ i, |x i| * |y i| ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
  have h := EuclideanSpace.abs_dotProduct_le_norm (fun i => |x i|) (fun i => |y i|)
  have hn : ∀ z : Fin N → ℝ, ‖WithLp.toLp 2 (fun i => |z i|)‖ = ‖WithLp.toLp 2 z‖ := fun z => by
    simp [EuclideanSpace.norm_eq]
  rw [hn, hn] at h
  exact (le_abs_self _).trans h

/-- **The inner product of two slots, into a cell**: `s[0] ← xᴴy` by `dot`, `re`, then a copy
into `aC`; the copied $a$ is $\mathbf{x}^{\mathsf{T}}\mathbf{y}$ up to
$\gamma_N\|\mathbf{x}\|\|\mathbf{y}\|$. -/
theorem exec_dot_re_copy (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hN : (N : ℝ) * u p < 1) (st : St P K C)
    {S : Array (P × ℕ)} (hsh : st.store.shape = S) {W sb : ℕ} (X Y : IExp ℕ) (aC : Cell ℕ ℕ)
    {x y : Fin N → ℝ} (hWs : W ≠ sb) (hS : S[sb]? = some (p, 4)) {na : ℕ}
    (haC : S[aC.buf]? = some (p, na)) (haCi : aC.idx.eval < na) (haCs : aC.buf ≠ sb)
    (hx : DecVec st.store p dec W X.eval x) (hy : DecVec st.store p dec W Y.eval y) :
    ∃ (st' : St P K C) (a : ℝ), (∀ f, exec I (dot p ⟨sb, 0⟩ W X W Y (.const N) >>=
        fun _ => ins (.un p .re ⟨sb, 0⟩ ⟨sb, 0⟩) >>= fun _ => ins (.copy p aC ⟨sb, 0⟩) >>=
        f).run st = exec I (f ()).run st') ∧
      StoreFrame p st.store st'.store
        (fun b i => StoreBlock sb 0 1 b i ∨ StoreBlock aC.buf aC.idx.eval 1 b i) ∧
      DecCell st'.store p dec aC.buf aC.idx.eval a ∧ DecCell st'.store p dec sb 0 a ∧
      |a - x ⬝ᵥ y| ≤ roundingFactor N (u p) * ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
  obtain ⟨z0, -⟩ := h.lit_ok p 0 trivial
  obtain ⟨st₁, w₁, h₁, hw₁, hb₁⟩ := IsRelErrSem.exec_dot_abs_sum_mul_sub_le I p st h hz ⟨sb, 0⟩
    W X W Y (.const N) (vecSeq x) (vecSeq y) hN hx.nat hy.nat (fun h' => absurd h'.symm hWs)
    (fun h' => absurd h'.symm hWs) ⟨z0, exists_write_of_shape hsh hS (by norm_num) z0⟩
  have hf₁ := storeFrame_of_write hw₁
  obtain ⟨w₂, hw₂, hd₂⟩ := h.re p w₁
  obtain ⟨s₂, hs₂⟩ := exists_write_of_shape (hf₁.1.trans hsh) hS (by norm_num : 0 < 4) w₂
  obtain ⟨st₂, h₂, hst₂⟩ := exec_ins_un I (st := st₁) (dst := ⟨sb, 0⟩) (x := ⟨sb, 0⟩)
    (Store.read_of_write_eq_some hw₁) hw₂ hs₂
  have hf₂ := storeFrame_of_write hs₂
  rw [← hst₂] at hf₂
  obtain ⟨s₃, hs₃⟩ := exists_write_of_shape ((hf₁.trans hf₂).1.trans hsh) haC haCi w₂
  obtain ⟨st₃, h₃, hst₃⟩ := exec_ins_copy I (st := st₂) (dst := aC) (src := ⟨sb, 0⟩)
    (by rw [hst₂]; exact Store.read_of_write_eq_some hs₂) hs₃
  have hf₃ := storeFrame_of_write hs₃
  rw [← hst₃] at hf₃
  refine ⟨st₃, dec p w₁, fun f => ?_, ((hf₁.trans hf₂).trans hf₃).mono fun b i hb => ?_,
    ⟨w₂, by rw [hst₃]; exact Store.read_of_write_eq_some hs₃, hd₂⟩,
    ⟨w₂, by rw [hst₃, Store.read_of_write_eq_some_of_ne hs₃ (Or.inl haCs.symm), hst₂]
            exact Store.read_of_write_eq_some hs₂, hd₂⟩, ?_⟩
  · rw [exec_bind_of_exec_eq_some I h₁ (seqShape_dot _ _ _ _ _ _ _),
      exec_bind_of_exec_eq_some I h₂ (seqShape_ins _),
      exec_bind_of_exec_eq_some I h₃ (seqShape_ins _)]
  · rcases hb with (hb | hb) | hb
    · exact Or.inl hb
    · exact Or.inl hb
    · exact Or.inr hb
  · simp only [IExp.eval_const, sum_range_extendZero (fun a b => a * b),
      sum_range_extendZero (fun a b => |a| * |b|)] at hb₁
    rw [abs_sub_comm]
    calc _ ≤ _ := hb₁
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (sum_abs_mul_abs_le_norm x y)
          (roundingFactor_nonneg (h.nonneg trivial) hN)

/-- **The breakdown test and the normalisation**: if `s[c]` decodes to $\beta$, `s[3]` to $0$
and the slot at `off` holds $\mathbf{z}$, the conditional leaves $\mathbf{z}$ when
$\beta = 0$ and otherwise divides it by $\beta$ (`rscl`, one rounding per entry). -/
theorem exec_ifThenElse_rscl (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C)
    {W sb : ℕ} (c off : IExp ℕ) {N : ℕ} {z : Fin N → ℝ} {β : ℝ} (hWs : W ≠ sb)
    (hc : DecCell st.store p dec sb c.eval β) (h3 : DecCell st.store p dec sb 3 0)
    (hzv : DecVec st.store p dec W off.eval z) :
    ∃ (st' : St P K C) (v : Fin N → ℝ), exec I (ifThenElse p .eq ⟨sb, c⟩ ⟨sb, 3⟩ (pure ())
        (rscl p ⟨sb, c⟩ W off (.const N))).run st = some st' ∧
      StoreFrame p st.store st'.store (StoreBlock W off.eval N) ∧
      DecVec st'.store p dec W off.eval v ∧ (β = 0 → v = z) ∧
      (β ≠ 0 → ∀ i, ∃ δ : ℝ, |δ| ≤ u p ∧ v i = z i / β * (1 + δ)) := by
  obtain ⟨wc, hwc, hdc⟩ := hc
  obtain ⟨w3, hw3, hd3⟩ := h3
  have hcmp : cmpStep I p .eq ⟨sb, c⟩ ⟨sb, 3⟩ st =
      some (decide (β = 0), { st with cnt := st.cnt + I.charge (.cmp p) }) := by
    simp only [cmpStep]
    rw [show (⟨sb, c⟩ : Cell ℕ ℕ).idx.eval = c.eval from rfl, hwc,
      show (⟨sb, 3⟩ : Cell ℕ ℕ).idx.eval = 3 from rfl, hw3]
    simp [h.cmp_eq, hdc, hd3]
  have hrun : (ifThenElse (ι := ι) p .eq ⟨sb, c⟩ ⟨sb, 3⟩ (pure ())
      (rscl p ⟨sb, c⟩ W off (.const N))).run = .seq (.ite p .eq ⟨sb, c⟩ ⟨sb, 3⟩ .skip
        (rscl p ⟨sb, c⟩ W off (.const N)).run) .skip := rfl
  rw [hrun, exec_seq_skip, exec_ite, hcmp, Option.bind_some]
  by_cases hβ : β = 0
  · rw [show decide (β = 0) = true from decide_eq_true hβ, if_pos rfl]
    exact ⟨_, z, exec_skip I _, StoreFrame.refl _ _, hzv, fun _ => rfl, fun h' => absurd hβ h'⟩
  rw [show decide (β = 0) = false from decide_eq_false hβ, if_neg Bool.false_ne_true]
  obtain ⟨st', Wv, h', hb', hW⟩ := IsRelErrSem.exec_rscl I p
    { st with cnt := st.cnt + I.charge (.cmp p) } h ⟨sb, c⟩ W off (.const N) β
    (vecSeq z) hβ ⟨wc, hwc, hdc⟩ hzv.nat (fun h'' => absurd h''.symm hWs)
  have hf := storeFrame_of_writeBlock hb'
  simp only [Array.size_map, List.size_toArray, List.length_range, IExp.eval_const] at hf
  refine ⟨st', fun i => dec p (Wv i), h', hf, DecVec.of_writeBlock hb', fun h'' => absurd h'' hβ,
    fun _ i => ?_⟩
  simpa [vecSeq_fin] using hW i (by simp)

/-- **The computed norm of a vector**: `s[2] ← xᴴx` by `dot`, then `s[d] ← √s[2]`
($d \in \{1, 2\}$); the result is $\sqrt{\sum_i x_i^2(1 + \eta_i)}\,(1 + \sigma)$, each
$1 + \eta_i$ a product of $N$ rounding errors and $\lvert\sigma\rvert \le u$. -/
theorem exec_dot_sqrt (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hu1 : u p < 1) (st : St P K C)
    {S : Array (P × ℕ)} (hsh : st.store.shape = S) {X sb : ℕ} (xo d : IExp ℕ)
    {x : Fin N → ℝ} (hXs : X ≠ sb) (hS : S[sb]? = some (p, 4)) (hd : 1 ≤ d.eval ∧ d.eval ≤ 2)
    (hx : DecVec st.store p dec X xo.eval x) :
    ∃ (st' : St P K C) (η : Fin N → ℝ) (σ β : ℝ), (∀ f, exec I (dot p ⟨sb, 2⟩ X xo X xo
        (.const N) >>= fun _ => ins (.un p .sqrt ⟨sb, d⟩ ⟨sb, 2⟩) >>= f).run st =
        exec I (f ()).run st') ∧
      StoreFrame p st.store st'.store (StoreBlock sb 1 2) ∧ DecCell st'.store p dec sb d.eval β ∧
      (∀ i, IsRoundingProduct (u p) N (η i)) ∧ |σ| ≤ u p ∧
      β = √(∑ i, x i * x i * (1 + η i)) * (1 + σ) := by
  obtain ⟨z0, -⟩ := h.lit_ok p 0 trivial
  obtain ⟨st₁, w₁, h₁, hw₁, η, hη, hd₁⟩ :=
    IsRelErrSem.exec_dot_eq_sum_mul_one_add_isRoundingProduct I p st h hz ⟨sb, 2⟩ X xo X xo
      (.const N) (vecSeq x) (vecSeq x) hx.nat hx.nat (fun h' => absurd h'.symm hXs)
      (fun h' => absurd h'.symm hXs) ⟨z0, exists_write_of_shape hsh hS (by norm_num) z0⟩
  have hf₁ := storeFrame_of_write hw₁
  have hsum : dec p w₁ = ∑ i : Fin N, x i * x i * (1 + η i) := by
    rw [hd₁, IExp.eval_const, ← Fin.sum_univ_eq_sum_range (fun i => vecSeq x i * vecSeq x i *
      (1 + η i))]
    simp [vecSeq_fin]
  have hu0 : 0 ≤ u p := h.nonneg trivial
  have hnn : 0 ≤ dec p w₁ := by
    rw [hsum]
    refine sum_nonneg fun i _ => mul_nonneg (mul_self_nonneg _) ?_
    have := ((isRoundingProduct_iff hu0 hu1).mp (hη i (by simp))).1
    exact (pow_nonneg (by linarith) _).trans this
  obtain ⟨w₂, hw₂⟩ := h.sqrt_ok p w₁ hnn
  obtain ⟨σ, hσ, hd₂⟩ := h.sqrt_err p w₁ w₂ hw₂
  obtain ⟨s₂, hs₂⟩ := exists_write_of_shape (hf₁.1.trans hsh) hS (by omega : d.eval < 4) w₂
  obtain ⟨st₂, h₂, hst₂⟩ := exec_ins_un I (st := st₁) (dst := ⟨sb, d⟩) (x := ⟨sb, 2⟩)
    (Store.read_of_write_eq_some hw₁) hw₂ hs₂
  have hf₂ := storeFrame_of_write hs₂
  rw [← hst₂] at hf₂
  refine ⟨st₂, fun i => η i, σ, dec p w₂, fun f => ?_, (hf₁.trans hf₂).mono fun b i hb => ?_,
    ⟨w₂, by rw [hst₂]; exact Store.read_of_write_eq_some hs₂, rfl⟩, fun i => hη i (by simp), hσ,
    by rw [hd₂, hsum]⟩
  · rw [exec_bind_of_exec_eq_some I h₁ (seqShape_dot _ _ _ _ _ _ _),
      exec_bind_of_exec_eq_some I h₂ (seqShape_ins _)]
  · rcases hb with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
    · have h1' : 2 ≤ i := h1
      have h2' : i < 2 + 1 := h2
      exact ⟨rfl, by omega, by omega⟩
    · exact ⟨rfl, by omega, by omega⟩

/-- **The normalisation of a step**: `s[2] ← zᴴz`, `s[1] ← √s[2]`, a copy into `bC`, then the
breakdown test and `rscl` on the slot at `Z`; the facts of `NLAlib.facts_of_relErr_normalize`. -/
theorem exec_normalize_step (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hN : ((N + 4 : ℕ) : ℝ) * u p < 1) (st : St P K C)
    {S : Array (P × ℕ)} (hsh : st.store.shape = S) {W sb : ℕ} (Z : IExp ℕ) (bC : Cell ℕ ℕ)
    {z : Fin N → ℝ} (hWs : W ≠ sb) (hS : S[sb]? = some (p, 4)) {nb : ℕ}
    (hbC : S[bC.buf]? = some (p, nb)) (hbCi : bC.idx.eval < nb) (hbs : bC.buf ≠ sb)
    (hbW : bC.buf ≠ W) (hzv : DecVec st.store p dec W Z.eval z)
    (h3 : DecCell st.store p dec sb 3 0) :
    ∃ (st' : St P K C) (v : Fin N → ℝ) (β : ℝ), exec I (dot p ⟨sb, 2⟩ W Z W Z (.const N) >>=
        fun _ => ins (.un p .sqrt ⟨sb, 1⟩ ⟨sb, 2⟩) >>= fun _ => ins (.copy p bC ⟨sb, 1⟩) >>=
        fun _ => ifThenElse p .eq ⟨sb, 1⟩ ⟨sb, 3⟩ (pure ())
          (rscl p ⟨sb, 1⟩ W Z (.const N))).run st = some st' ∧
      StoreFrame p st.store st'.store (fun b i => StoreBlock W Z.eval N b i ∨
        StoreBlock sb 1 2 b i ∨ StoreBlock bC.buf bC.idx.eval 1 b i) ∧
      DecVec st'.store p dec W Z.eval v ∧ DecCell st'.store p dec bC.buf bC.idx.eval β ∧
      DecCell st'.store p dec sb 1 β ∧ 0 ≤ β ∧ (z = 0 → β = 0) ∧ (β = 0 → v = 0) ∧
      (β ≠ 0 → |‖WithLp.toLp 2 v‖ ^ 2 - 1| ≤ roundingFactor (N + 4) (u p)) ∧
      ‖WithLp.toLp 2 (β • v - z)‖ ≤ u p * ‖WithLp.toLp 2 z‖ := by
  have hu0 : 0 ≤ u p := h.nonneg trivial
  have hu1 : u p < 1 := by
    simpa using cast_mul_lt_one_of_le (m := 1) hu0 (by omega) hN
  obtain ⟨st₁, η, σ, β, h₁, hf₁, hβ₁, hη, hσ, hβ⟩ := exec_dot_sqrt I h hz hu1 st hsh Z 1 hWs hS
    ⟨le_rfl, by norm_num⟩ hzv
  obtain ⟨wβ, hwβ, hdβ⟩ := hβ₁
  obtain ⟨s₂, hs₂⟩ := exists_write_of_shape (hf₁.1.trans hsh) hbC hbCi wβ
  obtain ⟨st₂, h₂, hst₂⟩ := exec_ins_copy I (st := st₁) (dst := bC) (src := ⟨sb, 1⟩) hwβ hs₂
  have hf₂ := storeFrame_of_write hs₂
  rw [← hst₂] at hf₂
  have hf₁₂ := hf₁.trans hf₂
  have hβ₂ : DecCell st₂.store p dec sb 1 β :=
    DecCell.frame ⟨wβ, hwβ, hdβ⟩ hf₂ fun hb => hbs hb.1.symm
  obtain ⟨st₃, v, h₃, hf₃, hv₃, hv0, hv⟩ := exec_ifThenElse_rscl I h st₂ 1 Z hWs hβ₂
    (h3.frame hf₁₂ fun hb => by rcases hb with ⟨-, -, h'⟩ | ⟨h', -⟩ <;> omega)
    (hzv.frame hf₁₂ fun i _ hb => by
      rcases hb with ⟨h', -⟩ | ⟨h', -⟩
      · exact hWs h'
      · exact hbW h'.symm)
  obtain ⟨hβ0, hzβ, hβv, hunit, hδ, -⟩ := facts_of_relErr_normalize hu0 hN hη rfl hσ hβ hv0 hv
  refine ⟨st₃, v, β, ?_, (hf₁₂.trans hf₃).mono fun b i hb => ?_, hv₃,
    DecCell.frame ⟨wβ, by rw [hst₂]; exact Store.read_of_write_eq_some hs₂, hdβ⟩ hf₃
      fun hb => hbW hb.1,
    hβ₂.frame hf₃ fun hb => hWs hb.1.symm, hβ0, hzβ, hβv, hunit, hδ⟩
  · rw [(h₁ _), exec_bind_of_exec_eq_some I h₂ (seqShape_ins _), h₃]
  · rcases hb with (hb | hb) | hb
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hb)
    · exact Or.inl hb

/-- **A normwise specification of a matrix-vector product** `mv W src dst` of the Lanczos
program: it emits one statement, and from any state whose buffer `R` (the read-only data, such
as a stored matrix) is as in `s₀` and whose slot at `src` of `W` holds $\mathbf{x}$, it
succeeds, writes the slot at `dst` (disjoint from `src`, writable) and nothing else, with a
decoded result $\mathbf{y}$, $\|\mathbf{y} - \mathbf{H}\mathbf{x}\| \le
c\|\mathbf{x}\|$. -/
def LanczosMvSpec (I : Interp P ι K C) (mv : ℕ → IExp ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (p : P) (dec : P → K → ℝ) (R : ℕ) (s₀ : Store P K) {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) : Prop :=
  (∀ W src dst, SeqShape (mv W src dst)) ∧
  ∀ (st : St P K C) (W : ℕ) (src dst : IExp ℕ) (x : Fin N → ℝ), R ≠ W →
    (∀ i, st.store.read p R i = s₀.read p R i) →
    (src.eval + N ≤ dst.eval ∨ dst.eval + N ≤ src.eval) →
    DecVec st.store p dec W src.eval x →
    (∀ i < N, ∃ v s₁, st.store.write p W (dst.eval + i) v = some s₁) →
    ∃ (st' : St P K C) (y : Fin N → ℝ), exec I (mv W src dst).run st = some st' ∧
      StoreFrame p st.store st'.store (StoreBlock W dst.eval N) ∧
      DecVec st'.store p dec W dst.eval y ∧
      ‖WithLp.toLp 2 (y - H *ᵥ x)‖ ≤ c * ‖WithLp.toLp 2 x‖

theorem not_storeBlock_of_ne {b b' off n i : ℕ} (h : b' ≠ b) : ¬ StoreBlock b off n b' i :=
  fun hb => h hb.1

theorem not_storeBlock_of_disjoint {W a b N i : ℕ} (h : a + N ≤ b ∨ b + N ≤ a) (hi : i < N) :
    ¬ StoreBlock W b N W (a + i) := fun ⟨_, h1, h2⟩ => by rcases h with h | h <;> omega

/-- **The updates of a step**: the product into the slot at `nxt`, then
$\mathbf{w} \leftarrow \mathbf{u} - \beta_0\mathbf{v}_0$, $\alpha \leftarrow
\mathbf{v}^{\mathsf{T}}\mathbf{w}$ (copied into `aC`) and
$\mathbf{z} \leftarrow \mathbf{w} - \alpha\mathbf{v}$, all in that slot, with the bounds of
`NLAlib.LanczosStepErr`. -/
theorem exec_lanczos_update (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hN : ((N + 4 : ℕ) : ℝ) * u p < 1)
    {mv : ℕ → IExp ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit} {R : ℕ} {s₀ : Store P K}
    {H : Matrix (Fin N) (Fin N) ℝ} {c : ℝ} (hmv : LanczosMvSpec I mv p dec R s₀ H c)
    (st : St P K C) {S : Array (P × ℕ)} (hsh : st.store.shape = S)
    (hR : ∀ i, st.store.read p R i = s₀.read p R i) {W sb : ℕ} (cur prev nxt : IExp ℕ)
    (aC : Cell ℕ ℕ) (hWs : W ≠ sb) (hRW : R ≠ W) (hS : S[sb]? = some (p, 4)) {nW : ℕ}
    (hSW : S[W]? = some (p, nW)) (hnxt : nxt.eval + N ≤ nW) {na : ℕ}
    (haC : S[aC.buf]? = some (p, na)) (haCi : aC.idx.eval < na) (haCs : aC.buf ≠ sb)
    (haW : aC.buf ≠ W) (hcn : cur.eval + N ≤ nxt.eval ∨ nxt.eval + N ≤ cur.eval)
    (hpn : prev.eval + N ≤ nxt.eval ∨ nxt.eval + N ≤ prev.eval) {x y : Fin N → ℝ} {b₀ : ℝ}
    (hx : DecVec st.store p dec W cur.eval x) (hy : DecVec st.store p dec W prev.eval y)
    (hb₀ : DecCell st.store p dec sb 1 b₀) :
    ∃ (st' : St P K C) (uv w zv : Fin N → ℝ) (α : ℝ), (∀ f, exec I (mv W cur nxt >>=
        fun _ => ins (.un p .neg ⟨sb, 0⟩ ⟨sb, 1⟩) >>=
        fun _ => axpy p ⟨sb, 0⟩ W prev W nxt (.const N) >>=
        fun _ => dot p ⟨sb, 0⟩ W cur W nxt (.const N) >>=
        fun _ => ins (.un p .re ⟨sb, 0⟩ ⟨sb, 0⟩) >>= fun _ => ins (.copy p aC ⟨sb, 0⟩) >>=
        fun _ => ins (.un p .neg ⟨sb, 0⟩ ⟨sb, 0⟩) >>=
        fun _ => axpy p ⟨sb, 0⟩ W cur W nxt (.const N) >>= f).run st =
          exec I (f ()).run st') ∧
      StoreFrame p st.store st'.store (fun b i => StoreBlock W nxt.eval N b i ∨
        StoreBlock sb 0 1 b i ∨ StoreBlock aC.buf aC.idx.eval 1 b i) ∧
      DecVec st'.store p dec W nxt.eval zv ∧ DecCell st'.store p dec aC.buf aC.idx.eval α ∧
      ‖WithLp.toLp 2 (uv - H *ᵥ x)‖ ≤ c * ‖WithLp.toLp 2 x‖ ∧
      ‖WithLp.toLp 2 (w - (uv - b₀ • y))‖ ≤
        roundingFactor 2 (u p) * (‖WithLp.toLp 2 uv‖ + |b₀| * ‖WithLp.toLp 2 y‖) ∧
      |α - x ⬝ᵥ w| ≤ roundingFactor N (u p) * ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 w‖ ∧
      ‖WithLp.toLp 2 (zv - (w - α • x))‖ ≤
        roundingFactor 2 (u p) * (‖WithLp.toLp 2 w‖ + |α| * ‖WithLp.toLp 2 x‖) := by
  have hu2 : ((2 : ℕ) : ℝ) * u p < 1 := cast_mul_lt_one_of_le (h.nonneg trivial) (by omega) hN
  have huN : (N : ℝ) * u p < 1 := cast_mul_lt_one_of_le (h.nonneg trivial) (by omega) hN
  obtain ⟨z0, -⟩ := h.lit_ok p 0 trivial
  obtain ⟨st₁, uv, h₁, hf₁, hu₁, hb₁⟩ := hmv.2 st W cur nxt x hRW hR hcn hx
    fun i hi => ⟨z0, exists_write_of_shape hsh hSW (by omega) z0⟩
  have hn₁ := fun i (hi : i < N) => not_storeBlock_of_disjoint (W := W) hcn hi
  obtain ⟨st₂, w, h₂, hf₂, hw₂, hb₂⟩ := exec_neg_axpy I h hu2 st₁ (hf₁.1.trans hsh) 1 prev nxt
    hWs hS hpn (hb₀.frame hf₁ (not_storeBlock_of_ne hWs.symm))
    (hy.frame hf₁ fun i hi => not_storeBlock_of_disjoint hpn hi) hu₁
  have hf₁₂ := hf₁.trans hf₂
  have hx₂ : DecVec st₂.store p dec W cur.eval x := hx.frame hf₁₂ fun i hi hb => by
    rcases hb with hb | hb | hb
    · exact hn₁ i hi hb
    · exact hWs hb.1
    · exact hn₁ i hi hb
  obtain ⟨st₃, α, h₃, hf₃, hα₃, hα₃', hb₃⟩ := exec_dot_re_copy I h hz huN st₂
    (hf₁₂.1.trans hsh) cur nxt aC hWs hS haC haCi haCs hx₂ hw₂
  have hn₃ : ∀ off i, ¬ (StoreBlock sb 0 1 W i ∨ StoreBlock aC.buf off 1 W i) := fun off i hb => by
    rcases hb with hb | hb
    · exact hWs hb.1
    · exact haW hb.1.symm
  obtain ⟨st₄, zv, h₄, hf₄, hz₄, hb₄⟩ := exec_neg_axpy I h hu2 st₃ (hf₃.1.trans (hf₁₂.1.trans hsh))
    0 cur nxt hWs hS hcn hα₃' (hx₂.frame hf₃ fun i _ => hn₃ _ _)
    (hw₂.frame hf₃ fun i _ => hn₃ _ _)
  refine ⟨st₄, uv, w, zv, α, fun f => ?_, ((hf₁₂.trans hf₃).trans hf₄).mono fun b i hb => ?_, hz₄,
    hα₃.frame hf₄ fun hb => by
      rcases hb with hb | hb
      · exact haCs hb.1
      · exact haW hb.1, hb₁, hb₂, hb₃, hb₄⟩
  · rw [exec_bind_of_exec_eq_some I h₁ (hmv.1 _ _ _), h₂, h₃, h₄]
  · rcases hb with (((hb | hb | hb) | hb | hb) | hb | hb)
    · exact Or.inl hb
    · exact Or.inr (Or.inl hb)
    · exact Or.inl hb
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hb)
    · exact Or.inr (Or.inl hb)
    · exact Or.inl hb

/-- **One step of the Lanczos program** (`NLAlib.lanczosStepWith`) in the standard model: from
$\mathbf{v}$ in the slot at `cur`, $\mathbf{v}_0$ in the slot at `prev`, $\beta_0$ in `s[1]`
and $0$ in `s[3]`, the step succeeds, writes only the slot at `nxt`, `s[0..2]`, `aC` and `bC`,
leaves $\mathbf{v}_2$ in the slot at `nxt`, $\alpha$ in `aC`, $\beta$ in `bC` and `s[1]`,
and the step has the local errors of `NLAlib.LanczosStepErr`. -/
theorem exec_lanczosStepWith (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hN : ((N + 4 : ℕ) : ℝ) * u p < 1)
    {mv : ℕ → IExp ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit} {R : ℕ} {s₀ : Store P K}
    {H : Matrix (Fin N) (Fin N) ℝ} {c : ℝ} (hmv : LanczosMvSpec I mv p dec R s₀ H c)
    (st : St P K C) {S : Array (P × ℕ)} (hsh : st.store.shape = S)
    (hR : ∀ i, st.store.read p R i = s₀.read p R i) {W sb : ℕ} (cur prev nxt : IExp ℕ)
    (aC bC : Cell ℕ ℕ) (hWs : W ≠ sb) (hRW : R ≠ W) (hS : S[sb]? = some (p, 4)) {nW : ℕ}
    (hSW : S[W]? = some (p, nW)) (hnxt : nxt.eval + N ≤ nW) {na nb : ℕ}
    (haC : S[aC.buf]? = some (p, na)) (haCi : aC.idx.eval < na) (haCs : aC.buf ≠ sb)
    (haW : aC.buf ≠ W) (hbC : S[bC.buf]? = some (p, nb)) (hbCi : bC.idx.eval < nb)
    (hbs : bC.buf ≠ sb) (hbW : bC.buf ≠ W) (hab : aC.buf ≠ bC.buf)
    (hcn : cur.eval + N ≤ nxt.eval ∨ nxt.eval + N ≤ cur.eval)
    (hpn : prev.eval + N ≤ nxt.eval ∨ nxt.eval + N ≤ prev.eval) {x y : Fin N → ℝ} {b₀ : ℝ}
    (hx : DecVec st.store p dec W cur.eval x) (hy : DecVec st.store p dec W prev.eval y)
    (hb₀ : DecCell st.store p dec sb 1 b₀) (h3 : DecCell st.store p dec sb 3 0) :
    ∃ (st' : St P K C) (uv w zv v : Fin N → ℝ) (α β : ℝ),
      exec I (lanczosStepWith mv p (.const N) W cur prev nxt sb aC bC).run st = some st' ∧
      StoreFrame p st.store st'.store (fun b i => StoreBlock W nxt.eval N b i ∨
        StoreBlock sb 0 3 b i ∨ StoreBlock aC.buf aC.idx.eval 1 b i ∨
        StoreBlock bC.buf bC.idx.eval 1 b i) ∧
      DecVec st'.store p dec W nxt.eval v ∧ DecCell st'.store p dec aC.buf aC.idx.eval α ∧
      DecCell st'.store p dec bC.buf bC.idx.eval β ∧ DecCell st'.store p dec sb 1 β ∧
      LanczosStepErr H c (roundingFactor 2 (u p)) (roundingFactor N (u p)) (u p)
        (roundingFactor (N + 4) (u p)) y x b₀ uv w zv α β v := by
  obtain ⟨st₁, uv, w, zv, α, h₁, hf₁, hz₁, hα₁, hb₁, hb₂, hb₃, hb₄⟩ := exec_lanczos_update I h hz
    hN hmv st hsh hR cur prev nxt aC hWs hRW hS hSW hnxt haC haCi haCs haW hcn hpn hx hy hb₀
  obtain ⟨st₂, v, β, h₂, hf₂, hv₂, hβ₂, hβ₂', hβ0, hzβ, hβv, hunit, hδ⟩ := exec_normalize_step I h
    hz hN st₁ (hf₁.1.trans hsh) nxt bC hWs hS hbC hbCi hbs hbW hz₁
    (h3.frame hf₁ fun hb => by
      rcases hb with ⟨h', -⟩ | ⟨-, -, h'⟩ | ⟨h', -⟩
      · exact hWs h'.symm
      · omega
      · exact haCs h'.symm)
  refine ⟨st₂, uv, w, zv, v, α, β, ?_, (hf₁.trans hf₂).mono fun b i hb => ?_, hv₂,
    hα₁.frame hf₂ fun hb => by
      rcases hb with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
      · exact haW h'
      · exact haCs h'
      · exact hab h', hβ₂, hβ₂',
    ⟨hb₁, hb₂, hb₃, hb₄, hδ, hβ0, hzβ, hβv, hunit⟩⟩
  · unfold lanczosStepWith
    rw [h₁ _, h₂]
  · rcases hb with (hb | ⟨rfl, -, h'⟩ | hb) | hb | ⟨rfl, h', h''⟩ | hb
    · exact Or.inl hb
    · exact Or.inr (Or.inl ⟨rfl, Nat.zero_le _, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl hb))
    · exact Or.inl hb
    · exact Or.inr (Or.inl ⟨rfl, Nat.zero_le _, by omega⟩)
    · exact Or.inr (Or.inr (Or.inr hb))

end Pieces

end NLAlib
