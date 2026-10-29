/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Computation.Exact
public import NLAlibScaffold.Krylov.LinearSystems.CGTridiagonal
public import NLAlibScaffold.Krylov.Processes.LanczosStep

/-!
# The conjugate gradient program

The Hestenes–Stiefel conjugate gradient method from $\mathbf{x}_0 = \mathbf{0}$ as a program, in
the order of `NLAlib.cgStep`: from $\mathbf{x}$, $\mathbf{r}$, $\mathbf{p}$ and
$\nu = \|\mathbf{r}\|^2$ (computed),
$$\mathbf{s} \leftarrow \mathbf{A}\mathbf{p},\quad \mu \leftarrow \mathbf{p}^{\mathsf{H}}\mathbf{s}\
(\texttt{dot}),\quad \gamma \leftarrow \nu/\mu,\quad
\mathbf{x} \leftarrow \mathbf{x} + \gamma\mathbf{p},\quad
\mathbf{r} \leftarrow \mathbf{r} - \gamma\mathbf{s}\ (\texttt{axpy}),$$
$$\nu' \leftarrow \mathbf{r}^{\mathsf{H}}\mathbf{r}\ (\texttt{dot}),\quad
\delta \leftarrow \nu'/\nu,\quad
\mathbf{p}' \leftarrow \mathbf{r};\ \mathbf{p}' \leftarrow \delta\mathbf{p} + \mathbf{p}'\
(\texttt{copy}, \texttt{axpy}),\quad \nu \leftarrow \nu' .$$
The stopping test is the exact comparison $\nu = 0$ before each step: the run stops when the
computed squared residual norm is exactly zero, and the remaining output cells are written $0$
(the junk values $0^{-1} = 0$ of `NLAlib.cgStep`). There is no test on $\mu$: in the standard
model $\mu > 0$ at every step taken is a theorem under a smallness hypothesis
(`NLAlib.CGRun.norm_r_le_two_mul_norm_p`, `NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc`).
The product is a parameter `mv`, an oracle call (`NLAlib.cgProg`) or `gemv` on a stored matrix
(`NLAlib.cgDenseProg`). Memory: five slots of length $N$ ($\mathbf{x}$, $\mathbf{r}$,
$\mathbf{s}$ and two rotating direction slots) and seven scalars.

Research branch `research/hscg-fp`. Design: `docs/design/research/Krylov-CGRounding.md` (§1).

## Main definitions

* `NLAlib.cgStepWith`, `NLAlib.cgProgWith`, `NLAlib.cgProg`, `NLAlib.cgDenseProg`.

## Main results

* `NLAlib.exec_cgProg_exactInterp`: in exact arithmetic the program computes `NLAlib.cgState`.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

open Computation Builder

variable {P ι VB VI : Type}

/-- **One conjugate gradient step** with the product `mv W src dst`: slots of `W` at $0$
($\mathbf{x}$), $N$ ($\mathbf{r}$), $2N$ ($\mathbf{s}$), `pc` (the current direction) and `pn`
(the next one); scalars `sc[0]` $= \nu$, `sc[1]` $= \mu$, `sc[2]` $= \gamma$, `sc[4]` $= \nu'$,
`sc[5]` $= \delta$, `sc[6]` $= -\gamma$. Writes $\gamma$, $\delta$, $\nu'$ into the three output
cells. -/
def cgStepWith (mv : VB → IExp VI → IExp VI → Builder P ι VB VI Unit) (p : P)
    (N : IExp VI) (W : VB) (pc pn : IExp VI) (sc : VB)
    (gamCell delCell nuCell : Cell VB VI) : Builder P ι VB VI Unit := do
  mv W pc (2 * N)
  dot p ⟨sc, 1⟩ W pc W (2 * N) N
  ins (.bin p .div ⟨sc, 2⟩ ⟨sc, 0⟩ ⟨sc, 1⟩)
  ins (.copy p gamCell ⟨sc, 2⟩)
  axpy p ⟨sc, 2⟩ W pc W 0 N
  ins (.un p .neg ⟨sc, 6⟩ ⟨sc, 2⟩)
  axpy p ⟨sc, 6⟩ W (2 * N) W N N
  dot p ⟨sc, 4⟩ W N W N N
  ins (.bin p .div ⟨sc, 5⟩ ⟨sc, 4⟩ ⟨sc, 0⟩)
  ins (.copy p delCell ⟨sc, 5⟩)
  copyv p W N W pn N
  axpy p ⟨sc, 5⟩ W pc W pn N
  ins (.copy p ⟨sc, 0⟩ ⟨sc, 4⟩)
  ins (.copy p nuCell ⟨sc, 0⟩)

/-- **Conjugate gradients**, $q$ steps from $\mathbf{x}_0 = \mathbf{0}$, product `mv`: input
$\mathbf{b}$ (buffer `b`), outputs $\mathbf{x}_k$ (`X`), $\gamma_0, \dots, \gamma_{q-1}$ (`gam`),
$\delta_0, \dots, \delta_{q-1}$ (`del`) and $\nu_0, \dots, \nu_q$ (`nu`). A step whose computed
$\nu$ is exactly $0$ is skipped and writes zeros. -/
def cgProgWith (mv : VB → IExp VI → IExp VI → Builder P ι VB VI Unit) (p : P)
    (N q : IExp VI) (b X gam del nu : VB) : Builder P ι VB VI Unit := do
  let W ← alloc p (5 * N)
  let sc ← alloc p 7
  ins (.lit p ⟨sc, 3⟩ 0)
  forRange N fun i => ins (.lit p ⟨W, .var i⟩ 0)
  copyv p b 0 W N N
  copyv p b 0 W (3 * N) N
  dot p ⟨sc, 0⟩ b 0 b 0 N
  ins (.copy p ⟨nu, 0⟩ ⟨sc, 0⟩)
  forRange q fun j =>
    ifThenElse p .eq ⟨sc, 0⟩ ⟨sc, 3⟩
      (do
        ins (.lit p ⟨gam, .var j⟩ 0)
        ins (.lit p ⟨del, .var j⟩ 0)
        ins (.lit p ⟨nu, .var j + 1⟩ 0))
      (cgStepWith mv p N W (3 * N + N * (.var j % 2)) (3 * N + N * ((.var j + 1) % 2)) sc
        ⟨gam, .var j⟩ ⟨del, .var j⟩ ⟨nu, .var j + 1⟩)
  copyv p W 0 X 0 N

/-- **Matrix-free conjugate gradients**: the product is one oracle call of `o`. -/
def cgProg (p : P) (o : ι) (N q : IExp VI) (b X gam del nu : VB) : Builder P ι VB VI Unit :=
  cgProgWith (fun W src dst => stmt (.apply o p W dst W src 1)) p N q b X gam del nu

/-- **Dense conjugate gradients**: the product is `gemv` on the $N \times N$ matrix stored
column-major in buffer `A`. -/
def cgDenseProg (p : P) (N q : IExp VI) (A b X gam del nu : VB) : Builder P ι VB VI Unit :=
  cgProgWith (fun W src dst => gemv p N N A 0 W src W dst) p N q b X gam del nu

variable [DecidableEq P] {𝕜 : Type} [RCLike 𝕜]

section CGKernels

variable (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
  (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (st : St P 𝕜 (OpCount P ι))

omit [RCLike 𝕜] in
/-- A block update is a store frame of its block. -/
private theorem cg_frame {s s' : Store P 𝕜} {b off n : ℕ} {f : ℕ → 𝕜}
    (u : BlockUpd p s s' b off n f) : StoreFrame p s s' (StoreBlock b off n) :=
  ⟨u.1, fun b' i h => u.2.2 b' i fun hb => by
    subst hb
    by_contra hc
    exact h ⟨rfl, by omega, by omega⟩⟩

include hI hc in
private theorem cg_exec_dot {dst : Cell ℕ ℕ} {x : ℕ} {xo : IExp ℕ} {y : ℕ} {yo n : IExp ℕ} {L : ℕ}
    {xs ys : ℕ → 𝕜} (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hy : ∀ i < n.eval, st.store.read p y (yo.eval + i) = some (ys i))
    (hdx : dst.buf ≠ x) (hdy : dst.buf ≠ y) (hs : st.store.shape[dst.buf]? = some (p, L))
    (hd : dst.idx.eval < L) :
    ∃ st', exec I (dot p dst x xo y yo n).run st = some st' ∧ BlockUpd p st.store st'.store
      dst.buf dst.idx.eval 1 fun _ => ∑ i ∈ Finset.range n.eval, star (xs i) * ys i := by
  obtain ⟨s₁, h₁⟩ := Store.exists_write_eq_some_of_getElem?_shape
    (∑ i ∈ Finset.range n.eval, star (xs i) * ys i) hs hd
  obtain ⟨st', h, hst, -⟩ := exec_dot I hI hc p st dst x xo y yo n xs ys hx hy
    (fun h => absurd h hdx) (fun h => absurd h hdy) s₁ h₁
  exact ⟨st', h, hst ▸ blockUpd_of_write h₁⟩

include hI hc in
private theorem cg_exec_axpy {a : Cell ℕ ℕ} {x : ℕ} {xo : IExp ℕ} {y : ℕ} {yo n : IExp ℕ} {L : ℕ}
    {av : 𝕜} {xs ys : ℕ → 𝕜} (ha : st.store.read p a.buf a.idx.eval = some av)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hy : ∀ i < n.eval, st.store.read p y (yo.eval + i) = some (ys i)) (hay : a.buf ≠ y)
    (hxy : x = y → xo.eval + n.eval ≤ yo.eval ∨ yo.eval + n.eval ≤ xo.eval)
    (hs : st.store.shape[y]? = some (p, L)) (hn : yo.eval + n.eval ≤ L) :
    ∃ st', exec I (axpy p a x xo y yo n).run st = some st' ∧ BlockUpd p st.store st'.store
      y yo.eval n.eval fun i => av * xs i + ys i := by
  obtain ⟨s₁, h₁⟩ := exists_writeBlock_map_range (fun i => av * xs i + ys i) hs hn
  obtain ⟨st', h, hst, -⟩ := exec_axpy I hI hc p st a x xo y yo n av xs ys ha hx hy
    (fun h => absurd h hay) (fun h i hi j hj he => by have := hxy h; omega) s₁ h₁
  exact ⟨st', h, hst ▸ blockUpd_of_writeBlock h₁⟩

omit [RCLike 𝕜] in
include hc in
private theorem cg_exec_copyv {x : ℕ} {xo : IExp ℕ} {y : ℕ} {yo n : IExp ℕ} {L : ℕ} {xs : ℕ → 𝕜}
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hxy : x = y → xo.eval + n.eval ≤ yo.eval ∨ yo.eval + n.eval ≤ xo.eval)
    (hs : st.store.shape[y]? = some (p, L)) (hn : yo.eval + n.eval ≤ L) :
    ∃ st', exec I (copyv p x xo y yo n).run st = some st' ∧ BlockUpd p st.store st'.store
      y yo.eval n.eval xs := by
  obtain ⟨s₁, h₁⟩ := exists_writeBlock_map_range xs hs hn
  obtain ⟨st', h, hst, -⟩ := exec_copyv I hc p st x xo y yo n xs hx
    (fun h i hi j hj he => by have := hxy h; omega) s₁ h₁
  exact ⟨st', h, hst ▸ blockUpd_of_writeBlock h₁⟩

omit [RCLike 𝕜] in
private theorem cg_exec_un {u : UnOp} {dst x : Cell ℕ ℕ} {a v : 𝕜} {L : ℕ}
    (hx : st.store.read p x.buf x.idx.eval = some a) (hv : I.sem.un p u a = some v)
    (hs : st.store.shape[dst.buf]? = some (p, L)) (hd : dst.idx.eval < L) :
    ∃ st', exec I (ins (ι := ι) (.un p u dst x)).run st = some st' ∧
      BlockUpd p st.store st'.store dst.buf dst.idx.eval 1 fun _ => v := by
  obtain ⟨s₁, h₁⟩ := Store.exists_write_eq_some_of_getElem?_shape v hs hd
  exact ⟨_, (exec_seq_instr_un I hx hv h₁).trans (exec_skip I _), blockUpd_of_write h₁⟩

omit [RCLike 𝕜] in
private theorem cg_exec_copy {dst x : Cell ℕ ℕ} {v : 𝕜} {L : ℕ}
    (hx : st.store.read p x.buf x.idx.eval = some v)
    (hs : st.store.shape[dst.buf]? = some (p, L)) (hd : dst.idx.eval < L) :
    ∃ st', exec I (ins (ι := ι) (.copy p dst x)).run st = some st' ∧
      BlockUpd p st.store st'.store dst.buf dst.idx.eval 1 fun _ => v := by
  obtain ⟨s₁, h₁⟩ := Store.exists_write_eq_some_of_getElem?_shape v hs hd
  exact ⟨_, (exec_seq_instr_copy I hx h₁).trans (exec_skip I _), blockUpd_of_write h₁⟩

include hI in
private theorem cg_exec_lit {dst : Cell ℕ ℕ} {L : ℕ}
    (hs : st.store.shape[dst.buf]? = some (p, L)) (hd : dst.idx.eval < L) :
    ∃ st', exec I (ins (ι := ι) (.lit p dst 0)).run st = some st' ∧
      BlockUpd p st.store st'.store dst.buf dst.idx.eval 1 fun _ => 0 := by
  obtain ⟨s₁, h₁⟩ := Store.exists_write_eq_some_of_getElem?_shape (0 : 𝕜) hs hd
  have hv : I.sem.lit p (0 : ℚ) = some (0 : 𝕜) := by rw [hI]; simp [exactSem]
  exact ⟨_, (exec_seq_instr_lit I hv h₁).trans (exec_skip I _), blockUpd_of_write h₁⟩

include hI in
private theorem cg_exec_div {dst x y : Cell ℕ ℕ} {a c : 𝕜} {L : ℕ} (hc0 : c ≠ 0)
    (hx : st.store.read p x.buf x.idx.eval = some a)
    (hy : st.store.read p y.buf y.idx.eval = some c)
    (hs : st.store.shape[dst.buf]? = some (p, L)) (hd : dst.idx.eval < L) :
    ∃ st', exec I (ins (ι := ι) (.bin p .div dst x y)).run st = some st' ∧
      BlockUpd p st.store st'.store dst.buf dst.idx.eval 1 fun _ => a / c := by
  obtain ⟨s₁, h₁⟩ := Store.exists_write_eq_some_of_getElem?_shape (a / c) hs hd
  have hv : I.sem.bin p .div a c = some (a / c) := by rw [hI]; simp [exactSem, hc0]
  exact ⟨_, (exec_seq_instr_bin I hx hy hv h₁).trans (exec_skip I _), blockUpd_of_write h₁⟩

include hI in
private theorem cg_exec_ite_eq {x y : Cell ℕ ℕ} {a c : 𝕜} (t e : Stmt P ι ℕ ℕ)
    (hx : st.store.read p x.buf x.idx.eval = some a)
    (hy : st.store.read p y.buf y.idx.eval = some c) :
    exec I (.ite p .eq x y t e) st = if a = c then
      exec I t { st with cnt := st.cnt + I.charge (.cmp p) } else
      exec I e { st with cnt := st.cnt + I.charge (.cmp p) } := by
  rw [exec_ite]
  simp only [cmpStep, hx, hy, Option.bind_some, hI, exactSem, Option.map_some]
  by_cases h : a = c <;> simp [h]

include hI in
/-- A loop of zero literals into cells `i < n` of buffer `W`. -/
private theorem cg_exec_forRange_lit {W L : ℕ} {n : IExp ℕ}
    (hs : st.store.shape[W]? = some (p, L)) (hn : n.eval ≤ L) :
    ∃ st', exec I (forRange (ι := ι) n fun i => ins (.lit p ⟨W, .var i⟩ 0)).run st =
      some st' ∧ BlockUpd p st.store st'.store W 0 n.eval fun _ => 0 := by
  rw [show (forRange (ι := ι) n fun i => ins (.lit p ⟨W, .var i⟩ 0)).run =
    .seq (.loop n fun i => (ins (.lit p ⟨W, .var i⟩ 0)).run) .skip from rfl, exec_seq_skip]
  refine exists_exec_loop_eq_some_of_forall I
    (fun i st' => BlockUpd p st.store st'.store W 0 i fun _ => 0)
    ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ _ => rfl⟩ fun i hi st' u => ?_
  obtain ⟨st'', h, u'⟩ := cg_exec_lit I hI p st' (dst := ⟨W, .var i⟩) (by rw [u.1]; exact hs)
    (by simp only [IExp.eval_var]; omega)
  simp only [IExp.eval_var] at u'
  exact ⟨st'', h, u.snoc (by rw [zero_add]; exact u')⟩

end CGKernels

section CGApply

omit [DecidableEq P] in
private theorem cg_flatten_mul_unflatten {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (v : Fin N → 𝕜) :
    flatten (A * unflatten N 1 ((List.range (N * 1)).toArray.map (vecSeq v))) =
      (List.range N).toArray.map (vecSeq (A *ᵥ v)) := by
  apply Array.ext
  · simp [size_flatten]
  · intro t h1 h2
    simp only [Array.size_map, List.size_toArray, List.length_range] at h2
    have hN : 0 < N := by omega
    simp only [flatten, Array.getElem_map, List.getElem_toArray, List.getElem_range,
      Nat.mod_eq_of_lt h2, Nat.div_eq_of_lt h2, Nat.zero_lt_one, and_self, h2, dite_true,
      vecSeq]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, unflatten, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp [Array.getD_eq_getD_getElem?, vecSeq, k.2]

/-- An oracle call `dst ← A src` on two disjoint blocks of length $N$ of one buffer `W`. -/
private theorem cg_exec_apply {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ) (o : ι)
    (p : P) (st : St P 𝕜 (OpCount P ι)) {W L : ℕ} {dOff sOff : IExp ℕ} {v : Fin N → 𝕜}
    (hs : st.store.shape[W]? = some (p, L)) (hd : dOff.eval + N ≤ L)
    (hdisj : dOff.eval + N ≤ sOff.eval ∨ sOff.eval + N ≤ dOff.eval)
    (hv : ∀ i < N, st.store.read p W (sOff.eval + i) = some (vecSeq v i)) :
    ∃ st', exec (exactInterp (fun _ => A) ξ) (stmt (.apply o p W dOff W sOff 1)).run st =
      some st' ∧ BlockUpd p st.store st'.store W dOff.eval N (vecSeq (A *ᵥ v)) := by
  obtain ⟨s₁, h₁⟩ := exists_writeBlock_map_range (vecSeq (A *ᵥ v)) hs hd
  refine ⟨{ st with store := s₁, cnt := st.cnt + (Finsupp.single (OpKind.load p o) 1 +
    (1 : IExp ℕ).eval • Finsupp.single (OpKind.matvec p o) 1) }, ?_, blockUpd_of_writeBlock h₁⟩
  rw [show (stmt (ι := ι) (.apply o p W dOff W sOff 1)).run = .seq (.apply o p W dOff W sOff 1)
    .skip from rfl, exec_seq_skip, exec]
  have hh : (exactInterp (P := P) (fun _ => A) ξ).height o * (1 : IExp ℕ).eval = N * 1 := rfl
  rw [hh, if_pos (Or.inr (by omega)), Store.readBlock_eq_some_map_range (vecSeq v)
    (fun i hi => hv i (by omega)), Option.bind_some]
  change (matOracle A 1 _).bind _ = _
  rw [matOracle, if_pos (by simp), Option.bind_some, cg_flatten_mul_unflatten, h₁]
  rfl

end CGApply

section CGVectors

variable {N : ℕ}

private theorem cg_vecSeq_smul_add (a : 𝕜) (x y : Fin N → 𝕜) (i : ℕ) :
    a * vecSeq x i + vecSeq y i = vecSeq (a • x + y) i := by
  unfold vecSeq
  split_ifs <;> simp

private theorem cg_sum_range_star_mul (x y : Fin N → 𝕜) :
    ∑ i ∈ Finset.range N, star (vecSeq x i) * vecSeq y i = star x ⬝ᵥ y := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => star (vecSeq x i) * vecSeq y i) N]
  simp [vecSeq, dotProduct]

/-- In exact CG, $\mathbf{p}_j^{\mathsf{H}}\mathbf{r}_j = \|\mathbf{r}_j\|^2$ (the line
search, by induction). -/
private theorem cg_star_p_dotProduct_r {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.PosDef)
    (b : Fin N → 𝕜) (j : ℕ) :
    star (cgState A b 0 j).p ⬝ᵥ (cgState A b 0 j).r =
      ((‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 : ℝ) : 𝕜) := by
  induction j with
  | zero => exact EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq _
  | succ j ih =>
    set S := cgState A b 0 j with hS
    have h0 : star S.p ⬝ᵥ (cgStep A S).r = 0 := by
      by_cases hp : S.p = 0
      · simp [hp]
      have hQ := hA.re_quadForm_pos hp
      have hq : star S.p ⬝ᵥ (A *ᵥ S.p) = (RCLike.re (quadForm A S.p) : 𝕜) :=
        (hA.isHermitian.coe_re_quadForm _).symm
      change star S.p ⬝ᵥ (S.r - ((‖WithLp.toLp 2 S.r‖ ^ 2 / RCLike.re (quadForm A S.p) : ℝ) :
        𝕜) • (A *ᵥ S.p)) = 0
      rw [dotProduct_sub, dotProduct_smul, hq, ih, smul_eq_mul, ← RCLike.ofReal_mul,
        div_mul_cancel₀ _ hQ.ne', sub_self]
    change star ((cgStep A S).r + ((‖WithLp.toLp 2 (cgStep A S).r‖ ^ 2 /
      ‖WithLp.toLp 2 S.r‖ ^ 2 : ℝ) : 𝕜) • S.p) ⬝ᵥ (cgStep A S).r = _
    rw [star_add, add_dotProduct, star_smul, smul_dotProduct, h0, smul_zero, add_zero]
    exact EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq _

/-- In exact CG on a positive definite matrix a nonzero residual has a nonzero direction. -/
private theorem cg_p_ne_zero {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.PosDef) (b : Fin N → 𝕜)
    {j : ℕ} (hr : (cgState A b 0 j).r ≠ 0) : (cgState A b 0 j).p ≠ 0 := by
  intro hp
  have h := cg_star_p_dotProduct_r hA b j
  rw [hp, star_zero, zero_dotProduct, ← EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq]
    at h
  exact hr (dotProduct_star_self_eq_zero.1 h.symm)

/-- The squared norm in $\Bbbk$ vanishes only at zero. -/
private theorem cg_coe_norm_sq_ne_zero {x : Fin N → 𝕜} (hx : x ≠ 0) :
    ((‖WithLp.toLp 2 x‖ ^ 2 : ℝ) : 𝕜) ≠ 0 := by
  rw [← EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq]
  exact fun h => hx (dotProduct_star_self_eq_zero.1 h)

end CGVectors

section CGPhases

/-- A cell outside a block, by arithmetic. -/
local macro "cg_out" : tactic => `(tactic| (simp only [StoreBlock, IExp.eval_zero, IExp.eval_one,
  IExp.eval_ofNat, IExp.eval_const, IExp.eval_add, IExp.eval_mul, IExp.eval_var] <;> omega))

/-- The product, the curvature and the step length of a CG step: $\mathbf{s} = \mathbf{A}
\mathbf{p}$ in slot `2N`, then $\gamma = \nu/\mathbf{p}^{\mathsf{H}}\mathbf{s}$ into `s[2]` and
into `gC`. -/
private theorem cg_exec_phaseA {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ) (o : ι)
    (p : P) (st : St P 𝕜 (OpCount P ι)) (pv : Fin N → 𝕜) (ν : 𝕜) {W s Lg : ℕ} {pc : IExp ℕ}
    {gC : Cell ℕ ℕ} (hW : st.store.shape[W]? = some (p, 5 * N))
    (hs : st.store.shape[s]? = some (p, 7)) (hg : st.store.shape[gC.buf]? = some (p, Lg))
    (hgi : gC.idx.eval < Lg) (hWs : W ≠ s) (hgW : gC.buf ≠ W) (hgs : gC.buf ≠ s)
    (hpc : 3 * N ≤ pc.eval ∧ pc.eval + N ≤ 5 * N) (hμ : star pv ⬝ᵥ (A *ᵥ pv) ≠ 0)
    (hp : ∀ i < N, st.store.read p W (pc.eval + i) = some (vecSeq pv i))
    (hν : st.store.read p s 0 = some ν) :
    ∃ st' : St P 𝕜 (OpCount P ι),
      StoreFrame p st.store st'.store (fun b i => StoreBlock W (2 * N) N b i ∨
        StoreBlock s 1 2 b i ∨ StoreBlock gC.buf gC.idx.eval 1 b i) ∧
      (∀ i < N, st'.store.read p W (2 * N + i) = some (vecSeq (A *ᵥ pv) i)) ∧
      st'.store.read p s 2 = some (ν / (star pv ⬝ᵥ (A *ᵥ pv))) ∧
      st'.store.read p gC.buf gC.idx.eval = some (ν / (star pv ⬝ᵥ (A *ᵥ pv))) ∧
      ∀ R : Builder P ι ℕ ℕ Unit, exec (exactInterp (fun _ => A) ξ)
        (stmt (.apply o p W (2 * .const N) W pc 1) >>= fun _ =>
          dot p ⟨s, 1⟩ W pc W (2 * .const N) (.const N) >>= fun _ =>
          ins (.bin p .div ⟨s, 2⟩ ⟨s, 0⟩ ⟨s, 1⟩) >>= fun _ =>
          ins (.copy p gC ⟨s, 2⟩) >>= fun _ => R).run st =
        exec (exactInterp (fun _ => A) ξ) R.run st' := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  obtain ⟨st1, h1, u1⟩ := cg_exec_apply A ξ o p st (dOff := 2 * .const N) (sOff := pc) hW
    (by simp; omega) (by simp; omega) hp
  replace u1 : BlockUpd p st.store st1.store W (2 * N) N (vecSeq (A *ᵥ pv)) := u1
  have f1 := cg_frame p u1
  obtain ⟨st2, h2, u2⟩ := cg_exec_dot I rfl (fun _ => rfl) p st1 (dst := ⟨s, 1⟩) (x := W)
    (xo := pc) (y := W) (yo := 2 * .const N) (n := .const N)
    (fun i (hi : i < N) => by rw [f1.2 _ _ ?_]; exacts [hp i hi, by cg_out])
    (fun i hi => by exact u1.read_in hi)
    hWs.symm hWs.symm (by rw [u1.1]; exact hs) (by norm_num)
  replace u2 : BlockUpd p st1.store st2.store s 1 1 fun _ => star pv ⬝ᵥ (A *ᵥ pv) :=
    u2.congr fun _ _ => cg_sum_range_star_mul pv (A *ᵥ pv)
  have f2 := cg_frame p u2
  obtain ⟨st3, h3, u3⟩ := cg_exec_div I rfl p st2 (dst := ⟨s, 2⟩) (x := ⟨s, 0⟩) (y := ⟨s, 1⟩)
    hμ (by rw [f2.2 _ _ ?_, f1.2 _ _ ?_]; exacts [hν, by cg_out, by cg_out])
    (u2.read_in (i := 0) Nat.one_pos) (by rw [u2.1, u1.1]; exact hs) (by norm_num)
  replace u3 : BlockUpd p st2.store st3.store s 2 1 fun _ => ν / (star pv ⬝ᵥ (A *ᵥ pv)) := u3
  have f3 := cg_frame p u3
  obtain ⟨st4, h4, u4⟩ := cg_exec_copy I p st3 (dst := gC) (x := ⟨s, 2⟩)
    (u3.read_in (i := 0) Nat.one_pos) (by rw [u3.1, u2.1, u1.1]; exact hg) hgi
  have f4 := cg_frame p u4
  refine ⟨st4, ((f1.trans f2).trans (f3.trans f4)).mono fun b i h => by
      simp only [StoreBlock] at h ⊢; omega,
    fun i hi => ?_, ?_, by simpa using u4.read_in (i := 0) Nat.one_pos, fun R => ?_⟩
  · rw [f4.2 _ _ ?_, f3.2 _ _ ?_, f2.2 _ _ ?_]
    exacts [u1.read_in hi, by cg_out, by cg_out, by cg_out]
  · rw [f4.2 _ _ ?_]
    exacts [u3.read_in (i := 0) Nat.one_pos, by cg_out]
  · rw [exec_bind_of_exec_eq_some I h1 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h2 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h3 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h4 ⟨_, fun _ => rfl⟩]

variable (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
  (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (st : St P 𝕜 (OpCount P ι))

include hI hc in
/-- The iterate and residual updates of a CG step and the coefficient:
$\mathbf{x} \leftarrow \mathbf{x} + \gamma\mathbf{p}$, $\mathbf{r} \leftarrow \mathbf{r} -
\gamma\mathbf{s}$, $\nu' = \mathbf{r}^{\mathsf{H}}\mathbf{r}$ into `s[4]`, $\delta = \nu'/\nu$
into `s[5]` and into `dC`. -/
private theorem cg_exec_phaseB {N : ℕ} (xv rv pv sv : Fin N → 𝕜) (γ ν : 𝕜) {W s Ld : ℕ}
    {pc : IExp ℕ} {dC : Cell ℕ ℕ} (hW : st.store.shape[W]? = some (p, 5 * N))
    (hs : st.store.shape[s]? = some (p, 7)) (hd : st.store.shape[dC.buf]? = some (p, Ld))
    (hdi : dC.idx.eval < Ld) (hWs : W ≠ s) (hdW : dC.buf ≠ W) (hds : dC.buf ≠ s)
    (hpc : 3 * N ≤ pc.eval ∧ pc.eval + N ≤ 5 * N) (hν0 : ν ≠ 0)
    (hx : ∀ i < N, st.store.read p W (0 + i) = some (vecSeq xv i))
    (hr : ∀ i < N, st.store.read p W (N + i) = some (vecSeq rv i))
    (hp : ∀ i < N, st.store.read p W (pc.eval + i) = some (vecSeq pv i))
    (hsv : ∀ i < N, st.store.read p W (2 * N + i) = some (vecSeq sv i))
    (hγ : st.store.read p s 2 = some γ) (hν : st.store.read p s 0 = some ν) :
    ∃ st' : St P 𝕜 (OpCount P ι),
      StoreFrame p st.store st'.store (fun b i => StoreBlock W 0 (2 * N) b i ∨
        StoreBlock s 4 3 b i ∨ StoreBlock dC.buf dC.idx.eval 1 b i) ∧
      (∀ i < N, st'.store.read p W (0 + i) = some (vecSeq (γ • pv + xv) i)) ∧
      (∀ i < N, st'.store.read p W (N + i) = some (vecSeq ((-γ) • sv + rv) i)) ∧
      st'.store.read p s 4 = some (star ((-γ) • sv + rv) ⬝ᵥ ((-γ) • sv + rv)) ∧
      st'.store.read p s 5 = some (star ((-γ) • sv + rv) ⬝ᵥ ((-γ) • sv + rv) / ν) ∧
      st'.store.read p dC.buf dC.idx.eval =
        some (star ((-γ) • sv + rv) ⬝ᵥ ((-γ) • sv + rv) / ν) ∧
      ∀ R : Builder P ι ℕ ℕ Unit, exec I
        (axpy p ⟨s, 2⟩ W pc W 0 (.const N) >>= fun _ =>
          ins (.un p .neg ⟨s, 6⟩ ⟨s, 2⟩) >>= fun _ =>
          axpy p ⟨s, 6⟩ W (2 * .const N) W (.const N) (.const N) >>= fun _ =>
          dot p ⟨s, 4⟩ W (.const N) W (.const N) (.const N) >>= fun _ =>
          ins (.bin p .div ⟨s, 5⟩ ⟨s, 4⟩ ⟨s, 0⟩) >>= fun _ =>
          ins (.copy p dC ⟨s, 5⟩) >>= fun _ => R).run st = exec I R.run st' := by
  set r' := (-γ) • sv + rv
  obtain ⟨st1, h1, u1⟩ := cg_exec_axpy I hI hc p st (a := ⟨s, 2⟩) (x := W) (xo := pc) (y := W)
    (yo := 0) (n := .const N) hγ hp hx hWs.symm (fun _ => by simp; omega) hW (by simp; omega)
  replace u1 : BlockUpd p st.store st1.store W 0 N (vecSeq (γ • pv + xv)) :=
    u1.congr fun i _ => cg_vecSeq_smul_add _ _ _ i
  have f1 := cg_frame p u1
  obtain ⟨st2, h2, u2⟩ := cg_exec_un I p st1 (dst := ⟨s, 6⟩) (x := ⟨s, 2⟩) (u := .neg)
    (by rw [f1.2 _ _ ?_]; exacts [hγ, by cg_out]) (by rw [hI]; rfl) (by rw [u1.1]; exact hs)
    (by norm_num)
  replace u2 : BlockUpd p st1.store st2.store s 6 1 fun _ => -γ := u2
  have f2 := cg_frame p u2
  obtain ⟨st3, h3, u3⟩ := cg_exec_axpy I hI hc p st2 (a := ⟨s, 6⟩) (x := W) (xo := 2 * .const N)
    (y := W) (yo := .const N) (n := .const N) (u2.read_in (i := 0) Nat.one_pos)
    (fun i (hi : i < N)
    => by rw [f2.2 _ _ ?_, f1.2 _ _ ?_]; exacts [hsv i hi, by cg_out, by cg_out])
    (fun i (hi : i < N)
    => by rw [f2.2 _ _ ?_, f1.2 _ _ ?_]; exacts [hr i hi, by cg_out, by cg_out]) hWs.symm
    (fun _ => by simp; omega) (by rw [u2.1, u1.1]; exact hW) (by simp; omega)
  replace u3 : BlockUpd p st2.store st3.store W N N (vecSeq r') :=
    u3.congr fun i _ => cg_vecSeq_smul_add _ _ _ i
  have f3 := cg_frame p u3
  obtain ⟨st4, h4, u4⟩ := cg_exec_dot I hI hc p st3 (dst := ⟨s, 4⟩) (x := W) (xo := .const N)
    (y := W) (yo := .const N) (n := .const N) (fun i hi => u3.read_in hi)
    (fun i hi => u3.read_in hi) hWs.symm hWs.symm (by rw [u3.1, u2.1, u1.1]; exact hs)
    (by norm_num)
  replace u4 : BlockUpd p st3.store st4.store s 4 1 fun _ => star r' ⬝ᵥ r' :=
    u4.congr fun _ _ => cg_sum_range_star_mul r' r'
  have f4 := cg_frame p u4
  obtain ⟨st5, h5, u5⟩ := cg_exec_div I hI p st4 (dst := ⟨s, 5⟩) (x := ⟨s, 4⟩) (y := ⟨s, 0⟩)
    hν0 (u4.read_in (i := 0) Nat.one_pos) (by
      rw [f4.2 _ _ ?_, f3.2 _ _ ?_, f2.2 _ _ ?_,
        f1.2 _ _ ?_]; exacts [hν, by cg_out, by cg_out, by cg_out, by cg_out])
        (by rw [u4.1, u3.1, u2.1, u1.1]; exact hs)
    (by norm_num)
  replace u5 : BlockUpd p st4.store st5.store s 5 1 fun _ => star r' ⬝ᵥ r' / ν := u5
  have f5 := cg_frame p u5
  obtain ⟨st6, h6, u6⟩ := cg_exec_copy I p st5 (dst := dC) (x := ⟨s, 5⟩)
    (u5.read_in (i := 0) Nat.one_pos) (by rw [u5.1, u4.1, u3.1, u2.1, u1.1]; exact hd) hdi
  have f6 := cg_frame p u6
  refine ⟨st6, (((f1.trans f2).trans (f3.trans f4)).trans (f5.trans f6)).mono fun b i h => by
      simp only [StoreBlock] at h ⊢; omega, fun i hi => ?_, fun i hi => ?_, ?_, ?_,
    by simpa using u6.read_in (i := 0) Nat.one_pos, fun R => ?_⟩
  · rw [f6.2 _ _ ?_, f5.2 _ _ ?_, f4.2 _ _ ?_,
      f3.2 _ _ ?_, f2.2 _ _ ?_]
    exacts [u1.read_in hi, by cg_out, by cg_out, by cg_out, by cg_out, by cg_out]
  · rw [f6.2 _ _ ?_, f5.2 _ _ ?_, f4.2 _ _ ?_]
    exacts [u3.read_in hi, by cg_out, by cg_out, by cg_out]
  · rw [f6.2 _ _ ?_, f5.2 _ _ ?_]
    exacts [u4.read_in (i := 0) Nat.one_pos, by cg_out, by cg_out]
  · rw [f6.2 _ _ ?_]
    exacts [u5.read_in (i := 0) Nat.one_pos, by cg_out]
  · rw [exec_bind_of_exec_eq_some I h1 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h2 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h3 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h4 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h5 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h6 ⟨_, fun _ => rfl⟩]

include hI hc in
/-- The direction update of a CG step: $\mathbf{p}' = \mathbf{r} + \delta\mathbf{p}$ in slot
`pn`, $\nu \leftarrow \nu'$ in `s[0]` and into `nC`. -/
private theorem cg_exec_phaseC {N : ℕ} (rv pv : Fin N → 𝕜) (δ ν' : 𝕜) {W s Ln : ℕ}
    {pc pn : IExp ℕ} {nC : Cell ℕ ℕ} (hW : st.store.shape[W]? = some (p, 5 * N))
    (hs : st.store.shape[s]? = some (p, 7)) (hn : st.store.shape[nC.buf]? = some (p, Ln))
    (hni : nC.idx.eval < Ln) (hWs : W ≠ s) (hnW : nC.buf ≠ W) (hns : nC.buf ≠ s)
    (hpc : 3 * N ≤ pc.eval ∧ pc.eval + N ≤ 5 * N) (hpn : 3 * N ≤ pn.eval ∧ pn.eval + N ≤ 5 * N)
    (hcn : pc.eval + N ≤ pn.eval ∨ pn.eval + N ≤ pc.eval)
    (hr : ∀ i < N, st.store.read p W (N + i) = some (vecSeq rv i))
    (hp : ∀ i < N, st.store.read p W (pc.eval + i) = some (vecSeq pv i))
    (hδ : st.store.read p s 5 = some δ) (hν' : st.store.read p s 4 = some ν') :
    ∃ st' : St P 𝕜 (OpCount P ι),
      StoreFrame p st.store st'.store (fun b i => StoreBlock W pn.eval N b i ∨
        StoreBlock s 0 1 b i ∨ StoreBlock nC.buf nC.idx.eval 1 b i) ∧
      (∀ i < N, st'.store.read p W (pn.eval + i) = some (vecSeq (δ • pv + rv) i)) ∧
      st'.store.read p s 0 = some ν' ∧ st'.store.read p nC.buf nC.idx.eval = some ν' ∧
      exec I (copyv p W (.const N) W pn (.const N) >>= fun _ =>
          axpy p ⟨s, 5⟩ W pc W pn (.const N) >>= fun _ =>
          ins (.copy p ⟨s, 0⟩ ⟨s, 4⟩) >>= fun _ => ins (.copy p nC ⟨s, 0⟩)).run st = some st' := by
  obtain ⟨st1, h1, u1⟩ := cg_exec_copyv I hc p st (x := W) (xo := .const N) (y := W) (yo := pn)
    (n := .const N) hr (fun _ => by simp; omega) hW (by simp; omega)
  replace u1 : BlockUpd p st.store st1.store W pn.eval N (vecSeq rv) := u1
  have f1 := cg_frame p u1
  obtain ⟨st2, h2, u2⟩ := cg_exec_axpy I hI hc p st1 (a := ⟨s, 5⟩) (x := W) (xo := pc) (y := W)
    (yo := pn) (n := .const N) (by rw [f1.2 _ _ ?_]; exacts [hδ, by cg_out])
    (fun i (hi : i < N) => by rw [f1.2 _ _ ?_]; exacts [hp i hi, by cg_out])
    (fun i hi => u1.read_in hi)
    hWs.symm (fun _ => by simp; omega) (by rw [u1.1]; exact hW) (by simp; omega)
  replace u2 : BlockUpd p st1.store st2.store W pn.eval N (vecSeq (δ • pv + rv)) :=
    u2.congr fun i _ => cg_vecSeq_smul_add _ _ _ i
  have f2 := cg_frame p u2
  obtain ⟨st3, h3, u3⟩ := cg_exec_copy I p st2 (dst := ⟨s, 0⟩) (x := ⟨s, 4⟩)
    (by rw [f2.2 _ _ ?_, f1.2 _ _ ?_]; exacts [hν', by cg_out, by cg_out])
    (by rw [u2.1, u1.1]; exact hs)
    (by norm_num)
  replace u3 : BlockUpd p st2.store st3.store s 0 1 fun _ => ν' := u3
  have f3 := cg_frame p u3
  obtain ⟨st4, h4, u4⟩ := cg_exec_copy I p st3 (dst := nC) (x := ⟨s, 0⟩)
    (u3.read_in (i := 0) Nat.one_pos) (by rw [u3.1, u2.1, u1.1]; exact hn) hni
  have f4 := cg_frame p u4
  refine ⟨st4, ((f1.trans f2).trans (f3.trans f4)).mono fun b i h => by
      simp only [StoreBlock] at h ⊢; omega, fun i hi => ?_, ?_,
    by simpa using u4.read_in (i := 0) Nat.one_pos, ?_⟩
  · rw [f4.2 _ _ ?_, f3.2 _ _ ?_]
    exacts [u2.read_in hi, by cg_out, by cg_out]
  · rw [f4.2 _ _ ?_]
    exacts [u3.read_in (i := 0) Nat.one_pos, by cg_out]
  · rw [exec_bind_of_exec_eq_some I h1 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h2 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h3 ⟨_, fun _ => rfl⟩]
    exact h4

end CGPhases

section CGStepExact

/-- A cell outside a block, by arithmetic. -/
local macro "cg_out" : tactic => `(tactic| (simp only [StoreBlock, IExp.eval_zero, IExp.eval_one,
  IExp.eval_ofNat, IExp.eval_const, IExp.eval_add, IExp.eval_mul, IExp.eval_var] <;> omega))

/-- The step length of a CG step as the program computes it, for Hermitian $\mathbf{A}$. -/
private theorem cg_gamma_eq {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (S : CGState 𝕜 (Fin N)) :
    ((‖WithLp.toLp 2 S.r‖ ^ 2 : ℝ) : 𝕜) / (star S.p ⬝ᵥ (A *ᵥ S.p)) = (cgAlpha A S : 𝕜) := by
  rw [show star S.p ⬝ᵥ (A *ᵥ S.p) = quadForm A S.p from rfl, ← hA.coe_re_quadForm,
    ← RCLike.ofReal_div]
  rfl

/-- **One step of the CG program computes `NLAlib.cgStep`** in exact arithmetic, from a state
with $\mathbf{r} \ne \mathbf{0}$ and $\mathbf{p} \ne \mathbf{0}$: slots $0$, $N$, `pc` hold
$\mathbf{x}$, $\mathbf{r}$, $\mathbf{p}$ and `s[0]` $= \|\mathbf{r}\|^2$; the run writes the
next state into slots $0$, $N$, `pn`, $\|\mathbf{r}'\|^2$ into `s[0]` and the three outputs. -/
private theorem cg_exec_step {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.PosDef)
    (ξ : Dist → ℕ → ℝ) (o : ι) (p : P) (st : St P 𝕜 (OpCount P ι)) (S : CGState 𝕜 (Fin N))
    {W s Lg Ld Ln : ℕ} {pc pn : IExp ℕ} {gC dC nC : Cell ℕ ℕ}
    (hW : st.store.shape[W]? = some (p, 5 * N)) (hs : st.store.shape[s]? = some (p, 7))
    (hg : st.store.shape[gC.buf]? = some (p, Lg)) (hgi : gC.idx.eval < Lg)
    (hd : st.store.shape[dC.buf]? = some (p, Ld)) (hdi : dC.idx.eval < Ld)
    (hn : st.store.shape[nC.buf]? = some (p, Ln)) (hni : nC.idx.eval < Ln)
    (hWs : W ≠ s) (hgW : gC.buf ≠ W) (hgs : gC.buf ≠ s) (hdW : dC.buf ≠ W) (hds : dC.buf ≠ s)
    (hnW : nC.buf ≠ W) (hns : nC.buf ≠ s) (hgd : gC.buf ≠ dC.buf) (hgn : gC.buf ≠ nC.buf)
    (hdn : dC.buf ≠ nC.buf)
    (hpc : 3 * N ≤ pc.eval ∧ pc.eval + N ≤ 5 * N) (hpn : 3 * N ≤ pn.eval ∧ pn.eval + N ≤ 5 * N)
    (hcn : pc.eval + N ≤ pn.eval ∨ pn.eval + N ≤ pc.eval)
    (hx : ∀ i < N, st.store.read p W (0 + i) = some (vecSeq S.x i))
    (hr : ∀ i < N, st.store.read p W (N + i) = some (vecSeq S.r i))
    (hp : ∀ i < N, st.store.read p W (pc.eval + i) = some (vecSeq S.p i))
    (hν : st.store.read p s 0 = some ((‖WithLp.toLp 2 S.r‖ ^ 2 : ℝ) : 𝕜))
    (hr0 : S.r ≠ 0) (hp0 : S.p ≠ 0) :
    ∃ st', exec (exactInterp (fun _ => A) ξ) (cgStepWith
        (fun W src dst => stmt (.apply o p W dst W src 1)) p (.const N) W pc pn s gC dC nC).run
        st = some st' ∧
      StoreFrame p st.store st'.store (fun b i => b = W ∨ (b = s ∧ i ≠ 3) ∨
        (b = gC.buf ∧ i = gC.idx.eval) ∨ (b = dC.buf ∧ i = dC.idx.eval) ∨
        (b = nC.buf ∧ i = nC.idx.eval)) ∧
      (∀ i < N, st'.store.read p W (0 + i) = some (vecSeq (cgStep A S).x i)) ∧
      (∀ i < N, st'.store.read p W (N + i) = some (vecSeq (cgStep A S).r i)) ∧
      (∀ i < N, st'.store.read p W (pn.eval + i) = some (vecSeq (cgStep A S).p i)) ∧
      st'.store.read p s 0 = some ((‖WithLp.toLp 2 (cgStep A S).r‖ ^ 2 : ℝ) : 𝕜) ∧
      st'.store.read p gC.buf gC.idx.eval = some (cgAlpha A S : 𝕜) ∧
      st'.store.read p dC.buf dC.idx.eval = some ((‖WithLp.toLp 2 (cgStep A S).r‖ ^ 2 /
        ‖WithLp.toLp 2 S.r‖ ^ 2 : ℝ) : 𝕜) ∧
      st'.store.read p nC.buf nC.idx.eval =
        some ((‖WithLp.toLp 2 (cgStep A S).r‖ ^ 2 : ℝ) : 𝕜) := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  have hμ : star S.p ⬝ᵥ (A *ᵥ S.p) ≠ 0 := by
    rw [show star S.p ⬝ᵥ (A *ᵥ S.p) = quadForm A S.p from rfl]
    exact (hA.quadForm_pos hp0).ne'
  obtain ⟨st3, fA, sA, γA, gA, hA'⟩ := cg_exec_phaseA A ξ o p st S.p _ hW hs hg hgi hWs hgW hgs
    hpc hμ hp hν
  rw [cg_gamma_eq hA.isHermitian] at γA gA
  obtain ⟨st9, fB, xB, rB, νB, δB, dB, hB⟩ := cg_exec_phaseB I rfl (fun _ => rfl) p st3 S.x S.r
    S.p (A *ᵥ S.p) (cgAlpha A S : 𝕜) _ (by rw [fA.1]; exact hW) (by rw [fA.1]; exact hs)
    (by rw [fA.1]; exact hd) hdi hWs hdW hds hpc (cg_coe_norm_sq_ne_zero hr0)
    (fun i (hi : i < N) => by rw [fA.2 _ _ ?_]; exacts [hx i hi, by cg_out])
    (fun i (hi : i < N) => by rw [fA.2 _ _ ?_]; exacts [hr i hi, by cg_out])
    (fun i (hi : i < N) => by rw [fA.2 _ _ ?_]; exacts [hp i hi, by cg_out]) sA γA
    (by rw [fA.2 _ _ ?_]; exacts [hν, by cg_out])
  have hr' : (-(cgAlpha A S : 𝕜)) • (A *ᵥ S.p) + S.r = (cgStep A S).r := by
    rw [neg_smul, neg_add_eq_sub]; rfl
  have hν' : star (cgStep A S).r ⬝ᵥ (cgStep A S).r =
      ((‖WithLp.toLp 2 (cgStep A S).r‖ ^ 2 : ℝ) : 𝕜) :=
    EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq _
  rw [hr'] at rB νB δB dB
  rw [hν', ← RCLike.ofReal_div] at δB dB
  rw [hν'] at νB
  obtain ⟨st13, fC, pC, sC, nC', hC⟩ := cg_exec_phaseC I rfl (fun _ => rfl) p st9 (cgStep A S).r
    S.p _ _ (by rw [fB.1, fA.1]; exact hW) (by rw [fB.1, fA.1]; exact hs)
    (by rw [fB.1, fA.1]; exact hn) hni hWs hnW hns hpc hpn hcn rB
    (fun i (hi : i < N)
    => by rw [fB.2 _ _ ?_, fA.2 _ _ ?_]; exacts [hp i hi, by cg_out, by cg_out]) δB νB
  refine ⟨st13, (hA' _).trans ((hB _).trans hC), ((fA.trans fB).trans fC).mono
      fun b i h => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, sC, ?_, ?_, nC'⟩
  · rcases h with ((h | h | h) | (h | h | h)) | (h | h | h) <;> obtain ⟨rfl, h1, h2⟩ := h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩)))
  · rw [fC.2 _ _ ?_, cgStep_x, add_comm S.x]; exacts [xB i hi, by cg_out]
  · rw [fC.2 _ _ ?_]; exacts [rB i hi, by cg_out]
  · rw [pC i hi, add_comm]; rfl
  · rw [fC.2 _ _ ?_, fB.2 _ _ ?_]; exacts [gA, by cg_out, by cg_out]
  · rw [fC.2 _ _ ?_]; exacts [dB, by cg_out]

end CGStepExact

section CGProgram

omit [RCLike 𝕜] [DecidableEq P] in
private theorem cg_run_ifThenElse (p : P) (c : CmpOp) (x y : Cell ℕ ℕ)
    (t e : Builder P ι ℕ ℕ Unit) :
    (ifThenElse p c x y t e).run = .seq (.ite p c x y t.run e.run) .skip := rfl

omit [DecidableEq P] in
/-- A CG step from a zero residual keeps the iterate and the residual. -/
private theorem cg_step_of_r_eq_zero {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    {S : CGState 𝕜 (Fin N)} (h : S.r = 0) :
    (cgStep A S).x = S.x ∧ (cgStep A S).r = 0 ∧ cgAlpha A S = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cgStep, cgAlpha, h]

/-- The loop invariant of the CG program before step `j`, with the buffers of the program
(`2`, `3`, `4` the outputs, `5` the slots, `6` the scalars). The direction slot is meaningful
only while the residual is nonzero. -/
private def CgInv {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (b : Fin N → 𝕜) (p : P)
    (sh : Array (P × ℕ)) (j : ℕ) (st : St P 𝕜 (OpCount P ι)) : Prop :=
  st.store.shape = sh ∧
  (∀ i < N, st.store.read p 5 (0 + i) = some (vecSeq (cgState A b 0 j).x i)) ∧
  (∀ i < N, st.store.read p 5 (N + i) = some (vecSeq (cgState A b 0 j).r i)) ∧
  ((cgState A b 0 j).r ≠ 0 → ∀ i < N,
    st.store.read p 5 (3 * N + N * (j % 2) + i) = some (vecSeq (cgState A b 0 j).p i)) ∧
  st.store.read p 6 0 = some ((‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 : ℝ) : 𝕜) ∧
  st.store.read p 6 3 = some 0 ∧
  (∀ k < j, st.store.read p 2 k = some (cgAlpha A (cgState A b 0 k) : 𝕜) ∧
    st.store.read p 3 k = some ((‖WithLp.toLp 2 (cgState A b 0 (k + 1)).r‖ ^ 2 /
      ‖WithLp.toLp 2 (cgState A b 0 k).r‖ ^ 2 : ℝ) : 𝕜)) ∧
  ∀ k ≤ j, st.store.read p 4 k = some ((‖WithLp.toLp 2 (cgState A b 0 k).r‖ ^ 2 : ℝ) : 𝕜)

/-- A skipped iteration (zero residual) keeps the invariant. -/
private theorem cg_inv_skip {N q : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (b : Fin N → 𝕜)
    (ξ : Dist → ℕ → ℝ) (p : P) (sh : Array (P × ℕ)) (hg : sh[2]? = some (p, q))
    (hd : sh[3]? = some (p, q)) (hn : sh[4]? = some (p, q + 1)) {j : ℕ} (hj : j < q)
    (st : St P 𝕜 (OpCount P ι)) (h : CgInv A b p sh j st) (hr0 : (cgState A b 0 j).r = 0) :
    ∃ st', exec (exactInterp (ι := ι) (fun _ => A) ξ) (ins (.lit p ⟨2, .var j⟩ 0) >>= fun _ =>
      ins (.lit p ⟨3, .var j⟩ 0) >>= fun _ => ins (.lit p ⟨4, .var j + 1⟩ 0)).run st =
        some st' ∧ CgInv A b p sh (j + 1) st' := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  obtain ⟨hsh, hx, hr, -, hν, h3, hold, hnu⟩ := h
  obtain ⟨hx', hr', hα⟩ := cg_step_of_r_eq_zero A hr0
  obtain ⟨st1, h1, u1⟩ := cg_exec_lit I rfl p st (dst := ⟨2, .var j⟩) (by rw [hsh]; exact hg) hj
  obtain ⟨st2, h2, u2⟩ := cg_exec_lit I rfl p st1 (dst := ⟨3, .var j⟩)
    (by rw [u1.1, hsh]; exact hd) hj
  obtain ⟨st3, h3', u3⟩ := cg_exec_lit I rfl p st2 (dst := ⟨4, .var j + 1⟩)
    (by rw [u2.1, u1.1, hsh]; exact hn) (by simp; omega)
  replace u1 : BlockUpd p st.store st1.store 2 j 1 fun _ => 0 := u1
  replace u2 : BlockUpd p st1.store st2.store 3 j 1 fun _ => 0 := u2
  replace u3 : BlockUpd p st2.store st3.store 4 (j + 1) 1 fun _ => 0 := u3
  have hrd : ∀ b' i, b' ≠ 2 → b' ≠ 3 → b' ≠ 4 → st3.store.read p b' i = st.store.read p b' i :=
    fun b' i h2 h3 h4 => by rw [u3.read_ne h4, u2.read_ne h3, u1.read_ne h2]
  have hS : cgState A b 0 (j + 1) = cgStep A (cgState A b 0 j) := rfl
  refine ⟨st3, by rw [exec_bind_of_exec_eq_some I h1 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h2 ⟨_, fun _ => rfl⟩]; exact h3',
    ⟨by rw [u3.1, u2.1, u1.1, hsh], fun i hi => ?_, fun i hi => ?_, fun h' => ?_, ?_, ?_,
      fun k hk => ?_, fun k hk => ?_⟩⟩
  · rw [hrd _ _ (by norm_num) (by norm_num) (by norm_num), hS, hx']; exact hx i hi
  · rw [hrd _ _ (by norm_num) (by norm_num) (by norm_num), hS, hr', ← hr0]; exact hr i hi
  · exact absurd hr' h'
  · rw [hrd _ _ (by norm_num) (by norm_num) (by norm_num), hS, hr', ← hr0]; exact hν
  · rw [hrd _ _ (by norm_num) (by norm_num) (by norm_num)]; exact h3
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · refine ⟨?_, ?_⟩
      · rw [u3.read_ne (by norm_num), u2.read_ne (by norm_num), u1.read_out (by omega)]
        exact (hold k hk).1
      · rw [u3.read_ne (by norm_num), u2.read_out (by omega), u1.read_ne (by norm_num)]
        exact (hold k hk).2
    · refine ⟨?_, ?_⟩
      · rw [u3.read_ne (by norm_num), u2.read_ne (by norm_num)]
        simpa [hα] using u1.read_in (i := 0) Nat.one_pos
      · rw [u3.read_ne (by norm_num)]
        simpa [hS, hr', hr0] using u2.read_in (i := 0) Nat.one_pos
  · rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_iff.mpr hk) with hk | rfl
    · rw [u3.read_out (by omega), u2.read_ne (by norm_num), u1.read_ne (by norm_num)]
      exact hnu k (Nat.lt_succ_iff.mp hk)
    · simpa [hS, hr'] using u3.read_in (i := 0) Nat.one_pos

/-- One iteration of the loop of the CG program keeps the invariant. -/
private theorem cg_inv_step {N q : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.PosDef)
    (b : Fin N → 𝕜) (ξ : Dist → ℕ → ℝ) (o : ι) (p : P) (sh : Array (P × ℕ))
    (hg : sh[2]? = some (p, q)) (hd : sh[3]? = some (p, q)) (hn : sh[4]? = some (p, q + 1))
    (hW : sh[5]? = some (p, 5 * N)) (hs : sh[6]? = some (p, 7)) {j : ℕ} (hj : j < q)
    (st : St P 𝕜 (OpCount P ι)) (h : CgInv A b p sh j st) :
    ∃ st', exec (exactInterp (fun _ => A) ξ) (ifThenElse p .eq ⟨6, 0⟩ ⟨6, 3⟩
      (ins (.lit p ⟨2, .var j⟩ 0) >>= fun _ =>
        ins (.lit p ⟨3, .var j⟩ 0) >>= fun _ => ins (.lit p ⟨4, .var j + 1⟩ 0))
      (cgStepWith (fun W src dst => stmt (.apply o p W dst W src 1)) p (.const N) 5
        (3 * .const N + .const N * (.var j % 2)) (3 * .const N + .const N * ((.var j + 1) % 2))
        6 ⟨2, .var j⟩ ⟨3, .var j⟩ ⟨4, .var j + 1⟩)).run st = some st' ∧
      CgInv A b p sh (j + 1) st' := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  rw [cg_run_ifThenElse, exec_seq_skip, cg_exec_ite_eq I rfl p st _ _ h.2.2.2.2.1 h.2.2.2.2.2.1]
  by_cases hr0 : (cgState A b 0 j).r = 0
  · rw [if_pos (by simp [hr0])]
    exact cg_inv_skip b ξ p sh hg hd hn hj _ h hr0
  rw [if_neg (cg_coe_norm_sq_ne_zero hr0)]
  obtain ⟨hsh, hx, hr, hp, hν, h3, hold, hnu⟩ := h
  have hm : (j % 2 = 0 ∧ (j + 1) % 2 = 1) ∨ (j % 2 = 1 ∧ (j + 1) % 2 = 0) := by omega
  obtain ⟨st', hst, fS, xS, rS, pS, νS, gS, dS, nS⟩ := cg_exec_step hA ξ o p
    { st with cnt := st.cnt + I.charge (.cmp p) } (cgState A b 0 j) (W := 5) (s := 6)
    (pc := 3 * .const N + .const N * (.var j % 2))
    (pn := 3 * .const N + .const N * ((.var j + 1) % 2))
    (gC := ⟨2, .var j⟩) (dC := ⟨3, .var j⟩) (nC := ⟨4, .var j + 1⟩)
    (by rw [hsh]; exact hW) (by rw [hsh]; exact hs) (by rw [hsh]; exact hg) hj
    (by rw [hsh]; exact hd) hj (by rw [hsh]; exact hn) (by simp; omega) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat, IExp.eval_const,
      IExp.eval_mod, IExp.eval_var]; rcases hm with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> omega)
    (by simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat, IExp.eval_const,
      IExp.eval_mod, IExp.eval_var]
        rcases hm with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> omega)
    (by simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat, IExp.eval_const,
      IExp.eval_mod, IExp.eval_var]
        rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> omega)
    hx hr (hp hr0) hν hr0 (cg_p_ne_zero hA b hr0)
  refine ⟨st', hst, ⟨fS.1.trans hsh, xS, rS, fun _ => pS, νS, ?_, fun k hk => ?_,
    fun k hk => ?_⟩⟩
  · rw [fS.2 6 3 (by simp)]; exact h3
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · refine ⟨?_, ?_⟩
      · rw [fS.2 2 k (by simp; omega)]; exact (hold k hk).1
      · rw [fS.2 3 k (by simp; omega)]; exact (hold k hk).2
    · exact ⟨gS, dS⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_iff.mpr hk) with hk | rfl
    · rw [fS.2 4 k (by simp; omega)]; exact hnu k (Nat.lt_succ_iff.mp hk)
    · exact nS

end CGProgram

section CGMain

/-- **The start of the CG program**: from buffer `0` holding $\mathbf{b}$, the invariant at
step $0$ (slots $0$, $N$, $3N$ hold $\mathbf{0}$, $\mathbf{b}$, $\mathbf{b}$, `s[0]` $=
\|\mathbf{b}\|^2$, `s[3]` $= 0$, `nu[0]` $= \|\mathbf{b}\|^2$). -/
private theorem cg_exec_init {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (b : Fin N → 𝕜)
    (ξ : Dist → ℕ → ℝ) (p : P) (q : ℕ) (st : St P 𝕜 (OpCount P ι))
    (hn : st.store.shape[4]? = some (p, q + 1)) (hW : st.store.shape[5]? = some (p, 5 * N))
    (hs : st.store.shape[6]? = some (p, 7))
    (hb : ∀ i < N, st.store.read p 0 (0 + i) = some (vecSeq b i)) :
    ∃ st' : St P 𝕜 (OpCount P ι), CgInv A b p st.store.shape 0 st' ∧
      ∀ R : Builder P ι ℕ ℕ Unit, exec (exactInterp (fun _ => A) ξ)
        (ins (.lit p ⟨6, 3⟩ 0) >>= fun _ =>
          forRange (.const N) (fun i => ins (.lit p ⟨5, .var i⟩ 0)) >>= fun _ =>
          copyv p 0 0 5 (.const N) (.const N) >>= fun _ =>
          copyv p 0 0 5 (3 * .const N) (.const N) >>= fun _ =>
          dot p ⟨6, 0⟩ 0 0 0 0 (.const N) >>= fun _ =>
          ins (.copy p ⟨4, 0⟩ ⟨6, 0⟩) >>= fun _ => R).run st =
        exec (exactInterp (fun _ => A) ξ) R.run st' := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  obtain ⟨st1, h1, u1⟩ := cg_exec_lit I rfl p st (dst := ⟨6, 3⟩) hs (show 3 < 7 by norm_num)
  replace u1 : BlockUpd p st.store st1.store 6 3 1 fun _ => 0 := u1
  obtain ⟨st2, h2, u2⟩ := cg_exec_forRange_lit I rfl p st1 (W := 5) (n := .const N)
    (by rw [u1.1]; exact hW) (by simp only [IExp.eval_const]; omega)
  replace u2 : BlockUpd p st1.store st2.store 5 0 N fun _ => 0 := u2
  have hb2 : ∀ i < N, st2.store.read p 0 (0 + i) = some (vecSeq b i) := fun i hi => by
    rw [u2.read_ne (by norm_num), u1.read_ne (by norm_num)]; exact hb i hi
  obtain ⟨st3, h3, u3⟩ := cg_exec_copyv I (fun _ => rfl) p st2 (x := 0) (xo := 0) (y := 5)
    (yo := .const N) (n := .const N) hb2 (fun h => absurd h (by norm_num))
    (by rw [u2.1, u1.1]; exact hW) (by simp; omega)
  replace u3 : BlockUpd p st2.store st3.store 5 N N (vecSeq b) := u3
  obtain ⟨st4, h4, u4⟩ := cg_exec_copyv I (fun _ => rfl) p st3 (x := 0) (xo := 0) (y := 5)
    (yo := 3 * .const N) (n := .const N)
    (fun i hi => by rw [u3.read_ne (by norm_num)]; exact hb2 i hi)
    (fun h => absurd h (by norm_num)) (by rw [u3.1, u2.1, u1.1]; exact hW) (by simp; omega)
  replace u4 : BlockUpd p st3.store st4.store 5 (3 * N) N (vecSeq b) := u4
  have hb4 : ∀ i < N, st4.store.read p 0 (0 + i) = some (vecSeq b i) := fun i hi => by
    rw [u4.read_ne (by norm_num), u3.read_ne (by norm_num)]; exact hb2 i hi
  obtain ⟨st5, h5, u5⟩ := cg_exec_dot I rfl (fun _ => rfl) p st4 (dst := ⟨6, 0⟩) (x := 0)
    (xo := 0) (y := 0) (yo := 0) (n := .const N) hb4 hb4 (by norm_num) (by norm_num)
    (by rw [u4.1, u3.1, u2.1, u1.1]; exact hs) (by norm_num)
  replace u5 : BlockUpd p st4.store st5.store 6 0 1 fun _ => ((‖WithLp.toLp 2 b‖ ^ 2 : ℝ) : 𝕜) :=
    u5.congr fun _ _ => (cg_sum_range_star_mul b b).trans
      (EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq b)
  obtain ⟨st6, h6, u6⟩ := cg_exec_copy I p st5 (dst := ⟨4, 0⟩) (x := ⟨6, 0⟩)
    (u5.read_in (i := 0) Nat.one_pos) (by rw [u5.1, u4.1, u3.1, u2.1, u1.1]; exact hn)
    (by norm_num)
  replace u6 : BlockUpd p st5.store st6.store 4 0 1 fun _ => ((‖WithLp.toLp 2 b‖ ^ 2 : ℝ) : 𝕜) :=
    u6
  have h0 : cgState A b 0 0 = ⟨0, b, b⟩ := by simp [cgState]
  have hW6 : ∀ i, st6.store.read p 5 i = st4.store.read p 5 i := fun i => by
    rw [u6.read_ne (by norm_num), u5.read_ne (by norm_num)]
  refine ⟨st6, ⟨by rw [u6.1, u5.1, u4.1, u3.1, u2.1, u1.1], fun i hi => ?_, fun i hi => ?_,
    fun _ i hi => ?_, ?_, ?_, fun k hk => absurd hk (Nat.not_lt_zero k), fun k hk => ?_⟩,
    fun R => ?_⟩
  · rw [hW6, u4.read_out (by omega), u3.read_out (by omega), u2.read_in hi, h0]
    simp [vecSeq]
  · rw [hW6, u4.read_out (by omega), u3.read_in hi, h0]
  · rw [hW6, h0, show 3 * N + N * (0 % 2) + i = 3 * N + i by simp, u4.read_in hi]
  · rw [u6.read_ne (by norm_num), h0]; exact u5.read_in (i := 0) Nat.one_pos
  · rw [u6.read_ne (by norm_num), u5.read_out (by norm_num), u4.read_ne (by norm_num),
      u3.read_ne (by norm_num), u2.read_ne (by norm_num)]
    exact u1.read_in (i := 0) Nat.one_pos
  · obtain rfl : k = 0 := by omega
    rw [h0]; exact u6.read_in (i := 0) Nat.one_pos
  · rw [exec_bind_of_exec_eq_some I h1 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h2 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h3 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h4 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h5 ⟨_, fun _ => rfl⟩,
      exec_bind_of_exec_eq_some I h6 ⟨_, fun _ => rfl⟩]

/-- The outputs of the CG program in a store: `X` (buffer 1), `gam`, `del`, `nu` (buffers
2, 3, 4). -/
private def CgOut {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (b : Fin N → 𝕜) (p : P) (q : ℕ)
    (s : Store P 𝕜) : Prop :=
  (∀ i < N, s.read p 1 (0 + i) = some (vecSeq (cgState A b 0 q).x i)) ∧
  (∀ k < q, s.read p 2 k = some (cgAlpha A (cgState A b 0 k) : 𝕜) ∧
    s.read p 3 k = some ((‖WithLp.toLp 2 (cgState A b 0 (k + 1)).r‖ ^ 2 /
      ‖WithLp.toLp 2 (cgState A b 0 k).r‖ ^ 2 : ℝ) : 𝕜)) ∧
  ∀ k ≤ q, s.read p 4 k = some ((‖WithLp.toLp 2 (cgState A b 0 k).r‖ ^ 2 : ℝ) : 𝕜)

omit [RCLike 𝕜] in
private theorem cg_exec_forRange_bind (I : Interp P ι 𝕜 (OpCount P ι)) {n : IExp ℕ}
    {body : ℕ → Builder P ι ℕ ℕ Unit} {st st₁ : St P 𝕜 (OpCount P ι)}
    (h : exec I (.loop n fun i => (body i).run) st = some st₁) {f : Unit → Builder P ι ℕ ℕ Unit} :
    exec I (forRange n body >>= f).run st = exec I (f ()).run st₁ := by
  rw [exec_run_bind I (b := forRange n body) (X := .loop n fun i => (body i).run) (fun _ => rfl),
    show (forRange n body).run =
    .seq (.loop n fun i => (body i).run) .skip from rfl, exec_seq_skip, h, Option.bind_some]

/-- The CG program after its two allocations. -/
private theorem cg_exec_inner {N q : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.PosDef)
    (b : Fin N → 𝕜) (ξ : Dist → ℕ → ℝ) (o : ι) (p : P) (st : St P 𝕜 (OpCount P ι))
    (hX : st.store.shape[1]? = some (p, N)) (hg : st.store.shape[2]? = some (p, q))
    (hd : st.store.shape[3]? = some (p, q)) (hn : st.store.shape[4]? = some (p, q + 1))
    (hW : st.store.shape[5]? = some (p, 5 * N)) (hs : st.store.shape[6]? = some (p, 7))
    (hb : ∀ i < N, st.store.read p 0 (0 + i) = some (vecSeq b i)) :
    ∃ st', exec (exactInterp (fun _ => A) ξ)
        (ins (.lit p ⟨6, 3⟩ 0) >>= fun _ =>
          forRange (.const N) (fun i => ins (.lit p ⟨5, .var i⟩ 0)) >>= fun _ =>
          copyv p 0 0 5 (.const N) (.const N) >>= fun _ =>
          copyv p 0 0 5 (3 * .const N) (.const N) >>= fun _ =>
          dot p ⟨6, 0⟩ 0 0 0 0 (.const N) >>= fun _ =>
          ins (.copy p ⟨4, 0⟩ ⟨6, 0⟩) >>= fun _ =>
          (forRange (.const q) fun j => ifThenElse p .eq ⟨6, 0⟩ ⟨6, 3⟩
            (ins (.lit p ⟨2, .var j⟩ 0) >>= fun _ =>
              ins (.lit p ⟨3, .var j⟩ 0) >>= fun _ => ins (.lit p ⟨4, .var j + 1⟩ 0))
            (cgStepWith (fun W src dst => stmt (.apply o p W dst W src 1)) p (.const N) 5
              (3 * .const N + .const N * (.var j % 2))
              (3 * .const N + .const N * ((.var j + 1) % 2)) 6 ⟨2, .var j⟩ ⟨3, .var j⟩
              ⟨4, .var j + 1⟩)) >>= fun _ =>
          copyv p 5 0 1 0 (.const N)).run st =
          some st' ∧ st'.store.shape = st.store.shape ∧ CgOut A b p q st'.store := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  obtain ⟨st1, inv0, h1⟩ := cg_exec_init A b ξ p q st hn hW hs hb
  obtain ⟨st2, h2, inv⟩ := exists_exec_loop_eq_some_of_forall I (n := .const q)
    (fun j st' => CgInv (ι := ι) A b p st.store.shape j st') inv0
    (fun j hj st' h => cg_inv_step hA b ξ o p _ hg hd hn hW hs hj st' h)
  obtain ⟨hshq, hxq, -, -, -, -, holdq, hnuq⟩ := inv
  obtain ⟨st3, h3, u3⟩ := cg_exec_copyv I (fun _ => rfl) p st2 (x := 5) (xo := 0) (y := 1)
    (yo := 0) (n := .const N) hxq (fun h => absurd h (by norm_num)) (by rw [hshq]; exact hX)
    (by simp)
  replace u3 : BlockUpd p st2.store st3.store 1 0 N (vecSeq (cgState A b 0 q).x) := u3
  refine ⟨st3, ?_, by rw [u3.1, hshq], fun i hi => u3.read_in hi, fun k hk => ?_,
    fun k hk => ?_⟩
  · rw [h1, cg_exec_forRange_bind I h2]
    exact h3
  · rw [u3.read_ne (by norm_num), u3.read_ne (by norm_num)]; exact holdq k hk
  · rw [u3.read_ne (by norm_num)]; exact hnuq k hk

private theorem cg_CgOut_pop {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} {b : Fin N → 𝕜} {p : P}
    {q : ℕ} {s : Store P 𝕜} (hs : 5 < s.size) (h : CgOut A b p q s) : CgOut A b p q s.pop := by
  refine ⟨fun i hi => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [Store.read_pop_of_lt (by omega)]; exact h.1 i hi
  · rw [Store.read_pop_of_lt (by omega), Store.read_pop_of_lt (by omega)]; exact h.2.1 k hk
  · rw [Store.read_pop_of_lt (by omega)]; exact h.2.2 k hk

private theorem cg_exec_cgProg {N : ℕ} (q : ℕ) {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.PosDef)
    (b : Fin N → 𝕜) (ξ : Dist → ℕ → ℝ) (o : ι) (p : P) (st : St P 𝕜 (OpCount P ι))
    (hsz : st.store.size = 5) (hX : st.store.shape[1]? = some (p, N))
    (hg : st.store.shape[2]? = some (p, q)) (hd : st.store.shape[3]? = some (p, q))
    (hn : st.store.shape[4]? = some (p, q + 1))
    (hb : ∀ i < N, st.store.read p 0 (0 + i) = some (vecSeq b i)) :
    ∃ st', exec (exactInterp (fun _ => A) ξ)
        (cgProg p o (.const N) (.const q) 0 1 2 3 4).run st = some st' ∧
      CgOut A b p q st'.store := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  unfold cgProg cgProgWith
  rw [run_alloc_bind]
  refine exec_alloc_of I fun st₁ h₁ => ?_
  simp only [hsz, run_alloc_bind]
  refine exec_alloc_of I (Q := fun s => CgOut A b p q s.pop) fun st₂ h₂ => ?_
  have h6 : st₁.store.size = 6 := by rw [h₁, Array.size_push, hsz]
  rw [h6]
  have hsh : ∀ k < 5, st₂.store.shape[k]? = st.store.shape[k]? := fun k hk => by
    rw [h₂, Store.getElem?_shape_push_of_lt (s := st₁.store) _ (by omega), h₁,
      Store.getElem?_shape_push_of_lt (s := st.store) _ (by omega)]
  have hW : st₂.store.shape[5]? = some (p, 5 * N) := by
    rw [h₂, Store.getElem?_shape_push_of_lt (s := st₁.store) _ (by omega), h₁]
    simpa [hsz] using Store.getElem?_shape_push_size st.store p (5 * N)
  have hs : st₂.store.shape[6]? = some (p, 7) := by
    rw [h₂, ← h6, Store.getElem?_shape_push_size]
    rfl
  have hb₂ : ∀ i < N, st₂.store.read p 0 (0 + i) = some (vecSeq b i) := fun i hi => by
    rw [h₂, Store.read_push_of_lt (s := st₁.store) (by omega), h₁,
      Store.read_push_of_lt (s := st.store) (by omega)]
    exact hb i hi
  obtain ⟨st₃, h₃, sh₃, out₃⟩ := cg_exec_inner hA b ξ o p st₂
    (by rw [hsh 1 (by norm_num)]; exact hX) (by rw [hsh 2 (by norm_num)]; exact hg)
    (by rw [hsh 3 (by norm_num)]; exact hd) (by rw [hsh 4 (by norm_num)]; exact hn) hW hs hb₂
  have h7 : st₃.store.size = 7 := by
    rw [Store.size_eq_of_shape_eq sh₃, h₂, Array.size_push, h6]
  exact ⟨st₃, h₃, cg_CgOut_pop (by simp [h7]) (cg_CgOut_pop (by omega) out₃)⟩

end CGMain

/-- **The conjugate gradient program computes the Hestenes–Stiefel recurrence** in exact
arithmetic: for positive definite $\mathbf{A}$ and every $\mathbf{b}$, the run succeeds,
`X` holds $\mathbf{x}_q$ of `NLAlib.cgState A b 0` (which is `NLAlib.cgIterate A b 0 q`,
`Matrix.PosDef.cgState_x_eq`), `gam[j]` $= \gamma_j$ (`NLAlib.cgAlpha`), `del[j]` $=
\|\mathbf{r}_{j+1}\|^2/\|\mathbf{r}_j\|^2$ and `nu[j]` $= \|\mathbf{r}_j\|^2$. Past the grade the
recurrence is frozen at the solution and the program skips, both writing $0$.
[HestenesStiefel1952, (3:1)].
Proof: loop invariant over the five slots (the rotation of the direction slots as in
`NLAlib.exec_lanczosBasisProg_exactInterp`); the division by $\mu = \mathbf{p}^{\mathsf{H}}
\mathbf{A}\mathbf{p} > 0$ succeeds because $\mathbf{p}_j \ne \mathbf{0}$ whenever
$\mathbf{r}_j \ne \mathbf{0}$ (`CGRecurrence.lean`, private `r_eq_zero_of_p_eq_zero`).
Difficulty: moderate (about 600 lines, mostly store bookkeeping). -/
theorem exec_cgProg_exactInterp (p : P) (o : ι) {N : ℕ} (q : ℕ)
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.PosDef) (b : Fin N → 𝕜) (ξ : Dist → ℕ → ℝ) :
    ∃ st', exec (exactInterp (fun _ => A) ξ)
        (cgProg p o (.const N) (.const q) 0 1 2 3 4).run
        (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate N none,
          Array.replicate q none, Array.replicate q none, Array.replicate (q + 1) none]) =
        some st' ∧
      (∀ i : Fin N, st'.store.read p 1 i = some ((cgState A b 0 q).x i)) ∧
      (∀ j < q, st'.store.read p 2 j = some (cgAlpha A (cgState A b 0 j) : 𝕜)) ∧
      (∀ j < q, st'.store.read p 3 j =
        some ((‖WithLp.toLp 2 (cgState A b 0 (j + 1)).r‖ ^ 2 /
          ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 : ℝ) : 𝕜)) ∧
      (∀ j ≤ q, st'.store.read p 4 j =
        some ((‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 : ℝ) : 𝕜)) := by
  obtain ⟨st', h, out⟩ := cg_exec_cgProg q hA b ξ o p
    (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate N none,
      Array.replicate q none, Array.replicate q none, Array.replicate (q + 1) none])
    (by simp [inputState]) (by simp [inputState, Store.getElem?_shape])
    (by simp [inputState, Store.getElem?_shape]) (by simp [inputState, Store.getElem?_shape])
    (by simp [inputState, Store.getElem?_shape])
    (fun i hi => by simp [inputState, Store.read, vecSeq, hi])
  refine ⟨st', h, fun i => ?_, fun j hj => (out.2.1 j hj).1, fun j hj => (out.2.1 j hj).2,
    out.2.2⟩
  simpa [vecSeq_fin] using out.1 i i.2

end NLAlib
