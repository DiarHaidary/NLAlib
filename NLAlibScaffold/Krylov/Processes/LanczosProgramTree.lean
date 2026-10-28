/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Computation.Exact
public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# The Lanczos program

The symmetric Lanczos process as a program, in Paige's ordering A(1) [Paige1976], the order of
`NLAlib.lanczosStep`: from $\mathbf{v}_j$ (slot `cur`), $\mathbf{v}_{j-1}$ (slot `prev`) and
$\beta_{j-1}$,
$$\mathbf{u} \leftarrow \mathbf{H}\mathbf{v}_j,\quad
\mathbf{w} \leftarrow \mathbf{u} - \beta_{j-1}\mathbf{v}_{j-1}\ (\texttt{axpy}),\quad
\alpha_j \leftarrow \mathbf{v}_j^{\mathsf{H}}\mathbf{w}\ (\texttt{dot}),\quad
\mathbf{z} \leftarrow \mathbf{w} - \alpha_j\mathbf{v}_j\ (\texttt{axpy}),$$
$$s \leftarrow \mathbf{z}^{\mathsf{H}}\mathbf{z}\ (\texttt{dot}),\quad \beta_j \leftarrow \sqrt{s},
\quad \mathbf{v}_{j+1} \leftarrow \mathbf{z}/\beta_j\ (\texttt{rscl, one division per entry})
\text{ unless } \beta_j = 0 .$$
All of $\mathbf{u}, \mathbf{w}, \mathbf{z}, \mathbf{v}_{j+1}$ live in one slot; three slots of
length $N$ rotate ($j \bmod 3$). The breakdown test is the exact comparison $\beta_j = 0$ (the
test `if z_j = 0` of [Chen, Algorithm 1]); on breakdown
the slot keeps $\mathbf{z}$ (which is then $\mathbf{0}$ in exact and in standard-model
arithmetic) and the loop continues, so every later output is $0$, as in the library's total
recursion `NLAlib.lanczosState` (junk value $0^{-1} = 0$). The matrix-vector product is a
parameter `mv`: an oracle call (`NLAlib.lanczosBasisProg`, the matrix-free model) or the `gemv`
kernel on a stored matrix (`NLAlib.lanczosBasisDenseProg`).

The program body is the one of `docs/design/Computation.md` §5 (D15), with the product
abstracted and the basis written to $N(q+1)$ cells (the next vector too, which the stability
analysis needs). Design: `docs/design/Krylov-LanczosRounding.md` (§1).

## Main definitions

* `NLAlib.lanczosStepWith`, `NLAlib.lanczosInit`, `NLAlib.lanczosBasisProgWith`.
* `NLAlib.lanczosBasisProg`, `NLAlib.lanczosBasisDenseProg`.

## Main results

* `NLAlib.exec_lanczosBasisProg_exactInterp`: in exact arithmetic the program computes
  `NLAlib.lanczosState`.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

open Computation Builder

variable {P ι VB VI : Type}

/-- **One Lanczos step** from slot `cur` (the previous vector in slot `prev`, $\beta_{j-1}$ in
`s[1]`, a literal zero in `s[3]`) into slot `nxt`, with the matrix-vector product `mv W src dst`:
writes $\alpha_j$ into `alphaCell`, $\beta_j$ into `betaCell` and into `s[1]`, and
$\mathbf{v}_{j+1}$ into slot `nxt` (left unnormalised when $\beta_j$ computes to $0$). -/
def lanczosStepWith (mv : VB → IExp VI → IExp VI → Builder P ι VB VI Unit) (p : P)
    (N : IExp VI) (W : VB) (cur prev nxt : IExp VI) (s : VB) (alphaCell betaCell : Cell VB VI) :
    Builder P ι VB VI Unit := do
  mv W cur nxt
  ins (.un p .neg ⟨s, 0⟩ ⟨s, 1⟩)
  axpy p ⟨s, 0⟩ W prev W nxt N
  dot p ⟨s, 0⟩ W cur W nxt N
  ins (.un p .re ⟨s, 0⟩ ⟨s, 0⟩)
  ins (.copy p alphaCell ⟨s, 0⟩)
  ins (.un p .neg ⟨s, 0⟩ ⟨s, 0⟩)
  axpy p ⟨s, 0⟩ W cur W nxt N
  dot p ⟨s, 2⟩ W nxt W nxt N
  ins (.un p .sqrt ⟨s, 1⟩ ⟨s, 2⟩)
  ins (.copy p betaCell ⟨s, 1⟩)
  ifThenElse p .eq ⟨s, 1⟩ ⟨s, 3⟩ (pure ()) (rscl p ⟨s, 1⟩ W nxt N)

/-- **The start**: slot 0 holds $\mathbf{b}/\|\mathbf{b}\|$ (computed as `dot`, `sqrt`, `rscl`;
$\mathbf{b}$ itself if $\|\mathbf{b}\|$ computes to $0$), slot 2 holds zero,
`s[1]` $= \beta_0 = 0$ and `s[3]` $= 0$. -/
def lanczosInit (p : P) (N : IExp VI) (b : VB) (W s : VB) : Builder P ι VB VI Unit := do
  ins (.lit p ⟨s, 3⟩ 0)
  forRange N fun i => ins (.lit p ⟨W, 2 * N + .var i⟩ 0)
  copyv p b 0 W 0 N
  dot p ⟨s, 2⟩ b 0 b 0 N
  ins (.un p .sqrt ⟨s, 2⟩ ⟨s, 2⟩)
  ifThenElse p .eq ⟨s, 2⟩ ⟨s, 3⟩ (pure ()) (rscl p ⟨s, 2⟩ W 0 N)
  ins (.lit p ⟨s, 1⟩ 0)

/-- **Lanczos with the basis**, $q$ steps, product `mv`: inputs $\mathbf{b}$ (buffer `b`),
outputs $\alpha_1, \dots, \alpha_q$ (`alpha`), $\beta_1, \dots, \beta_q$ (`beta`) and
$\mathbf{v}_1, \dots, \mathbf{v}_{q+1}$ (`Q`, $N \times (q + 1)$ column-major); memory $3N + 4$
besides the inputs and outputs. -/
def lanczosBasisProgWith (mv : VB → IExp VI → IExp VI → Builder P ι VB VI Unit) (p : P)
    (N q : IExp VI) (b alpha beta Q : VB) : Builder P ι VB VI Unit := do
  let W ← alloc p (3 * N)
  let s ← alloc p 4
  lanczosInit p N b W s
  forRange q fun j => do
    copyv p W (N * (.var j % 3)) Q (N * .var j) N
    lanczosStepWith mv p N W (N * (.var j % 3)) (N * ((.var j + 2) % 3))
      (N * ((.var j + 1) % 3)) s ⟨alpha, .var j⟩ ⟨beta, .var j⟩
  copyv p W (N * (q % 3)) Q (N * q) N

/-- **Matrix-free Lanczos with the basis**: the product is one oracle call of `o`. -/
def lanczosBasisProg (p : P) (o : ι) (N q : IExp VI) (b alpha beta Q : VB) :
    Builder P ι VB VI Unit :=
  lanczosBasisProgWith (fun W src dst => stmt (.apply o p W dst W src 1)) p N q b alpha beta Q

/-- **Dense Lanczos with the basis**: the product is `gemv` on the $N \times N$ matrix stored
column-major in buffer `H`. -/
def lanczosBasisDenseProg (p : P) (N q : IExp VI) (H b alpha beta Q : VB) :
    Builder P ι VB VI Unit :=
  lanczosBasisProgWith (fun W src dst => gemv p N N H 0 W src W dst) p N q b alpha beta Q

/-! ### Builders that run one statement, then the rest -/

section Seq

variable {K C : Type}

/-- A builder that emits one statement before its continuation. -/
def SeqShape (b : Builder P ι ℕ ℕ Unit) : Prop := ∃ X, ∀ k, ContT.run b k = .seq X (k ())

theorem seqShape_stmt (s : Stmt P ι ℕ ℕ) : SeqShape (stmt s) := ⟨s, fun _ => rfl⟩

theorem seqShape_ins (i : Instr P ℕ ℕ) : SeqShape (ι := ι) (ins i) := ⟨_, fun _ => rfl⟩

theorem seqShape_named (name : String) (args : List (Arg ℕ ℕ)) (b : Builder P ι ℕ ℕ Unit) :
    SeqShape (named name args b) := ⟨_, fun _ => rfl⟩

theorem seqShape_forRange (n : IExp ℕ) (body : ℕ → Builder P ι ℕ ℕ Unit) :
    SeqShape (forRange n body) := ⟨_, fun _ => rfl⟩

theorem seqShape_ifThenElse (p : P) (c : CmpOp) (x y : Cell ℕ ℕ)
    (t e : Builder P ι ℕ ℕ Unit) : SeqShape (ifThenElse p c x y t e) := ⟨_, fun _ => rfl⟩

theorem seqShape_axpy (p : P) (a : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) :
    SeqShape (ι := ι) (axpy p a x xo y yo n) := ⟨_, fun _ => rfl⟩

theorem seqShape_dot (p : P) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) :
    SeqShape (ι := ι) (dot p dst x xo y yo n) := ⟨_, fun _ => rfl⟩

theorem seqShape_copyv (p : P) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) :
    SeqShape (ι := ι) (copyv p x xo y yo n) := ⟨_, fun _ => rfl⟩

theorem seqShape_rscl (p : P) (a : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) :
    SeqShape (ι := ι) (rscl p a x xo n) := ⟨_, fun _ => rfl⟩

theorem seqShape_gemv (p : P) (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (y : ℕ) (yo : IExp ℕ) : SeqShape (ι := ι) (gemv p m n A ao x xo y yo) := ⟨_, fun _ => rfl⟩

variable [DecidableEq P] [AddMonoid C] (I : Interp P ι K C)

/-- The run of a builder of one statement, then `f`. -/
theorem exec_bind_of_seqShape {b : Builder P ι ℕ ℕ Unit} (hb : SeqShape b)
    (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C) :
    exec I (b >>= f).run st = (exec I b.run st).bind (exec I (f ()).run) := by
  obtain ⟨X, hX⟩ := hb; exact exec_run_bind I hX f st

/-- A successful first statement: the run of the rest from its final state. -/
theorem exec_bind_of_exec_eq_some {b : Builder P ι ℕ ℕ Unit} {st st' : St P K C}
    (h : exec I b.run st = some st') (hb : SeqShape b) (f : Unit → Builder P ι ℕ ℕ Unit) :
    exec I (b >>= f).run st = exec I (f ()).run st' := by
  rw [exec_bind_of_seqShape I hb, h, Option.bind_some]

variable {p : P} {st : St P K C}

/-- The run of a unary instruction. -/
theorem exec_ins_un {o : UnOp} {dst x : Cell ℕ ℕ} {a v : K} {s : Store P K}
    (hx : st.store.read p x.buf x.idx.eval = some a) (hv : I.sem.un p o a = some v)
    (hw : st.store.write p dst.buf dst.idx.eval v = some s) :
    ∃ st', exec I (ins (ι := ι) (.un p o dst x)).run st = some st' ∧ st'.store = s :=
  ⟨_, (exec_seq_instr_un I hx hv hw).trans (exec_skip I _), rfl⟩

/-- The run of a copy. -/
theorem exec_ins_copy {dst src : Cell ℕ ℕ} {v : K} {s : Store P K}
    (hx : st.store.read p src.buf src.idx.eval = some v)
    (hw : st.store.write p dst.buf dst.idx.eval v = some s) :
    ∃ st', exec I (ins (ι := ι) (.copy p dst src)).run st = some st' ∧ st'.store = s :=
  ⟨_, (exec_seq_instr_copy I hx hw).trans (exec_skip I _), rfl⟩

/-- The run of a literal. -/
theorem exec_ins_lit {dst : Cell ℕ ℕ} {q : ℚ} {v : K} {s : Store P K}
    (hv : I.sem.lit p q = some v) (hw : st.store.write p dst.buf dst.idx.eval v = some s) :
    ∃ st', exec I (ins (ι := ι) (.lit p dst q)).run st = some st' ∧ st'.store = s :=
  ⟨_, (exec_seq_instr_lit I hv hw).trans (exec_skip I _), rfl⟩


/-- The run of an allocation, for a postcondition on the popped store. -/
theorem exec_alloc_of {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C}
    {Q : Store P K → Prop} (h' : ∀ st₁ : St P K C,
      st₁.store = st.store.push (p, Array.replicate len.eval none) →
      ∃ st₂ : St P K C, exec I (body st.store.size) st₁ = some st₂ ∧ Q st₂.store.pop) :
    ∃ st' : St P K C, exec I (.alloc p len body) st = some st' ∧ Q st'.store := by
  obtain ⟨st₂, h₂, hQ⟩ := h' { st with
      store := st.store.push (p, Array.replicate len.eval none)
      cur := Function.update st.cur p (st.cur p + len.eval)
      peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval))
      curW := st.curW + len.eval * I.width p
      peakW := max st.peakW (st.curW + len.eval * I.width p) } rfl
  exact ⟨_, by rw [exec_alloc, h₂]; rfl, hQ⟩

omit [DecidableEq P] [AddMonoid C] in
theorem run_alloc_bind (p : P) (len : IExp ℕ) (f : ℕ → Builder P ι ℕ ℕ Unit) :
    (Builder.alloc p len >>= f).run = .alloc p len fun b => (f b).run := rfl

/-- Two distinct slots of length $N$ do not overlap. -/
theorem slot_disjoint (N : ℕ) {a b : ℕ} (hab : a ≠ b) : N * a + N ≤ N * b ∨ N * b + N ≤ N * a := by
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact Or.inl (by nlinarith)
  · exact Or.inr (by nlinarith)

end Seq

variable {𝕜 : Type} [RCLike 𝕜] [DecidableEq P]

section StoreFrames

variable {K : Type}

/-- A vector of `Fin N` as a sequence, zero past its end. -/
def vecSeq {N : ℕ} [Zero K] (v : Fin N → K) (i : ℕ) : K := if h : i < N then v ⟨i, h⟩ else 0

/-- The sequence of a vector agrees with it on `Fin N`. -/
theorem vecSeq_fin {N : ℕ} [Zero K] (v : Fin N → K) (i : Fin N) : vecSeq v i = v i := by
  simp [vecSeq, i.2]

/-- `s'` is `s` with the cells `off, …, off + n - 1` of buffer `b` at tag `p` set to
`f 0, …, f (n - 1)`: same shape, the new values, and every other read at tag `p` kept. -/
def BlockUpd (p : P) (s s' : Store P K) (b off n : ℕ) (f : ℕ → K) : Prop :=
  s'.shape = s.shape ∧ (∀ i < n, s'.read p b (off + i) = some (f i)) ∧
    ∀ b' i, (b' = b → i < off ∨ off + n ≤ i) → s'.read p b' i = s.read p b' i

namespace BlockUpd

variable {p : P} {s s' : Store P K} {b off n : ℕ} {f : ℕ → K}

/-- The new values of a block update. -/
theorem read_in (u : BlockUpd p s s' b off n f) {i : ℕ} (hi : i < n) :
    s'.read p b (off + i) = some (f i) := u.2.1 i hi

/-- A block update keeps every other buffer. -/
theorem read_ne (u : BlockUpd p s s' b off n f) {b' i : ℕ} (h : b' ≠ b) :
    s'.read p b' i = s.read p b' i := u.2.2 b' i fun h' => absurd h' h

/-- A block update keeps every cell outside the block. -/
theorem read_out (u : BlockUpd p s s' b off n f) {b' i : ℕ} (h : i < off ∨ off + n ≤ i) :
    s'.read p b' i = s.read p b' i := u.2.2 b' i fun _ => h

/-- A block update followed by an update of the next cell is a longer block update. -/
theorem snoc {s₂ : Store P K} (u : BlockUpd p s s' b off n f)
    (u' : BlockUpd p s' s₂ b (off + n) 1 fun _ => f n) : BlockUpd p s s₂ b off (n + 1) f := by
  refine ⟨u'.1.trans u.1, fun i hi => ?_, fun b' i h => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [u'.read_out (by omega), u.read_in hi]
    · simpa using u'.read_in (i := 0) (by omega)
  · by_cases hb : b' = b
    · rw [u'.read_out (by have := h hb; omega), u.read_out (by have := h hb; omega)]
    · rw [u'.read_ne hb, u.read_ne hb]

/-- A block update with values equal inside the block. -/
theorem congr {g : ℕ → K} (u : BlockUpd p s s' b off n f) (h : ∀ i < n, f i = g i) :
    BlockUpd p s s' b off n g :=
  ⟨u.1, fun i hi => (u.read_in hi).trans (congrArg some (h i hi)), u.2.2⟩

end BlockUpd

/-- A block write of `(List.range n).toArray.map f` is a block update. -/
theorem blockUpd_of_writeBlock {p : P} {s s' : Store P K} {b off n : ℕ} {f : ℕ → K}
    (h : s.writeBlock p b off ((List.range n).toArray.map f) = some s') :
    BlockUpd p s s' b off n f := by
  refine ⟨Store.shape_of_writeBlock_eq_some h, fun i hi => ?_, fun b' i hb => ?_⟩
  · rw [Store.read_of_writeBlock_eq_some_of_lt h (by simpa using hi)]
    simp [hi]
  · refine Store.read_of_writeBlock_eq_some_of_ne h ?_
    by_cases hbb : b' = b
    · simpa using Or.inr (hb hbb)
    · exact Or.inl hbb

/-- A cell write is a block update of length one. -/
theorem blockUpd_of_write {p : P} {s s' : Store P K} {b i : ℕ} {v : K}
    (h : s.write p b i v = some s') : BlockUpd p s s' b i 1 fun _ => v := by
  refine ⟨Store.shape_of_write_eq_some h, fun k hk => ?_, fun b' k hb => ?_⟩
  · obtain rfl : k = 0 := by omega
    exact Store.read_of_write_eq_some h
  · refine Store.read_of_write_eq_some_of_ne h ?_
    by_cases hbb : b' = b
    · exact Or.inr (by have := hb hbb; omega)
    · exact Or.inl hbb

/-- A block write succeeds inside a buffer of its tag, as the shape gives it. -/
theorem exists_writeBlock_map_range {p : P} {s : Store P K} {b off n L : ℕ} (f : ℕ → K)
    (hs : s.shape[b]? = some (p, L)) (hn : off + n ≤ L) :
    ∃ s', s.writeBlock p b off ((List.range n).toArray.map f) = some s' :=
  Store.exists_writeBlock_eq_some_of_write fun j hj =>
    ⟨f j, Store.exists_write_eq_some_of_getElem?_shape (f j) hs (by
      simp only [Array.size_map, List.size_toArray, List.length_range] at hj; omega)⟩

end StoreFrames

section Kernels

variable (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
  (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (st : St P 𝕜 (OpCount P ι))

include hI hc in
private theorem lz_exec_dot {dst : Cell ℕ ℕ} {x : ℕ} {xo : IExp ℕ} {y : ℕ} {yo n : IExp ℕ} {L : ℕ}
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
private theorem lz_exec_axpy {a : Cell ℕ ℕ} {x : ℕ} {xo : IExp ℕ} {y : ℕ} {yo n : IExp ℕ} {L : ℕ}
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

include hI hc in
private theorem lz_exec_rscl {a : Cell ℕ ℕ} {x : ℕ} {xo n : IExp ℕ} {L : ℕ} {av : 𝕜} {xs : ℕ → 𝕜}
    (hav : av ≠ 0) (ha : st.store.read p a.buf a.idx.eval = some av)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i)) (hax : a.buf ≠ x)
    (hs : st.store.shape[x]? = some (p, L)) (hn : xo.eval + n.eval ≤ L) :
    ∃ st', exec I (rscl p a x xo n).run st = some st' ∧ BlockUpd p st.store st'.store
      x xo.eval n.eval fun i => xs i / av := by
  obtain ⟨s₁, h₁⟩ := exists_writeBlock_map_range (fun i => xs i / av) hs hn
  obtain ⟨st', h, hst, -⟩ := exec_rscl I hI hc p st a x xo n av xs hav ha hx
    (fun h => absurd h hax) s₁ h₁
  exact ⟨st', h, hst ▸ blockUpd_of_writeBlock h₁⟩

omit [RCLike 𝕜] in
include hc in
private theorem lz_exec_copyv {x : ℕ} {xo : IExp ℕ} {y : ℕ} {yo n : IExp ℕ} {L : ℕ} {xs : ℕ → 𝕜}
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
private theorem lz_exec_un {u : UnOp} {dst x : Cell ℕ ℕ} {a v : 𝕜} {L : ℕ}
    (hx : st.store.read p x.buf x.idx.eval = some a) (hv : I.sem.un p u a = some v)
    (hs : st.store.shape[dst.buf]? = some (p, L)) (hd : dst.idx.eval < L) :
    ∃ st', exec I (ins (ι := ι) (.un p u dst x)).run st = some st' ∧
      BlockUpd p st.store st'.store dst.buf dst.idx.eval 1 fun _ => v := by
  obtain ⟨s₁, h₁⟩ := Store.exists_write_eq_some_of_getElem?_shape v hs hd
  exact ⟨_, (exec_seq_instr_un I hx hv h₁).trans (exec_skip I _), blockUpd_of_write h₁⟩

omit [RCLike 𝕜] in
private theorem lz_exec_copy {dst x : Cell ℕ ℕ} {v : 𝕜} {L : ℕ}
    (hx : st.store.read p x.buf x.idx.eval = some v)
    (hs : st.store.shape[dst.buf]? = some (p, L)) (hd : dst.idx.eval < L) :
    ∃ st', exec I (ins (ι := ι) (.copy p dst x)).run st = some st' ∧
      BlockUpd p st.store st'.store dst.buf dst.idx.eval 1 fun _ => v := by
  obtain ⟨s₁, h₁⟩ := Store.exists_write_eq_some_of_getElem?_shape v hs hd
  exact ⟨_, (exec_seq_instr_copy I hx h₁).trans (exec_skip I _), blockUpd_of_write h₁⟩

include hI in
private theorem lz_exec_lit {dst : Cell ℕ ℕ} {L : ℕ}
    (hs : st.store.shape[dst.buf]? = some (p, L)) (hd : dst.idx.eval < L) :
    ∃ st', exec I (ins (ι := ι) (.lit p dst 0)).run st = some st' ∧
      BlockUpd p st.store st'.store dst.buf dst.idx.eval 1 fun _ => 0 := by
  obtain ⟨s₁, h₁⟩ := Store.exists_write_eq_some_of_getElem?_shape (0 : 𝕜) hs hd
  have hv : I.sem.lit p (0 : ℚ) = some (0 : 𝕜) := by rw [hI]; simp [exactSem]
  exact ⟨_, (exec_seq_instr_lit I hv h₁).trans (exec_skip I _), blockUpd_of_write h₁⟩

include hI in
private theorem lz_exec_ite_eq {x y : Cell ℕ ℕ} {a c : 𝕜} (t e : Stmt P ι ℕ ℕ)
    (hx : st.store.read p x.buf x.idx.eval = some a)
    (hy : st.store.read p y.buf y.idx.eval = some c) :
    exec I (.ite p .eq x y t e) st = if a = c then
      exec I t { st with cnt := st.cnt + I.charge (.cmp p) } else
      exec I e { st with cnt := st.cnt + I.charge (.cmp p) } := by
  rw [exec_ite]
  simp only [cmpStep, hx, hy, Option.bind_some, hI, exactSem, Option.map_some]
  by_cases h : a = c <;> simp [h]

include hI in
/-- A loop of zero literals into cells `off + i` of buffer `W`, `i < n`. -/
private theorem lz_exec_forRange_lit {W off L : ℕ} {n : IExp ℕ} {o : IExp ℕ} (ho : o.eval = off)
    (hs : st.store.shape[W]? = some (p, L)) (hn : off + n.eval ≤ L) :
    ∃ st', exec I (forRange (ι := ι) n fun i => ins (.lit p ⟨W, o + .var i⟩ 0)).run st =
      some st' ∧ BlockUpd p st.store st'.store W off n.eval fun _ => 0 := by
  rw [show (forRange (ι := ι) n fun i => ins (.lit p ⟨W, o + .var i⟩ 0)).run =
    .seq (.loop n fun i => (ins (.lit p ⟨W, o + .var i⟩ 0)).run) .skip from rfl, exec_seq_skip]
  refine exists_exec_loop_eq_some_of_forall I
    (fun i st' => BlockUpd p st.store st'.store W off i fun _ => 0)
    ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ _ => rfl⟩ fun i hi st' u => ?_
  obtain ⟨st'', h, u'⟩ := lz_exec_lit I hI p st' (dst := ⟨W, o + .var i⟩) (by rw [u.1]; exact hs)
    (by simp only [IExp.eval_add, IExp.eval_var, ho]; omega)
  simp only [IExp.eval_add, IExp.eval_var, ho] at u'
  exact ⟨st'', h, u.snoc u'⟩

end Kernels

section Apply

omit [DecidableEq P] in
private theorem lz_flatten_mul_unflatten {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (v : Fin N → 𝕜) :
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
private theorem lz_exec_apply {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ) (o : ι)
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
  rw [matOracle, if_pos (by simp), Option.bind_some, lz_flatten_mul_unflatten, h₁]
  rfl

end Apply

section Vectors

variable {N : ℕ}

private theorem vecSeq_smul_add (a : 𝕜) (x y : Fin N → 𝕜) (i : ℕ) :
    a * vecSeq x i + vecSeq y i = vecSeq (a • x + y) i := by
  unfold vecSeq
  split_ifs <;> simp

private theorem vecSeq_div (a : 𝕜) (x : Fin N → 𝕜) (i : ℕ) :
    vecSeq x i / a = vecSeq (a⁻¹ • x) i := by
  unfold vecSeq
  split_ifs <;> simp [div_eq_inv_mul]

private theorem lz_sum_range_star_mul (x y : Fin N → 𝕜) :
    ∑ i ∈ Finset.range N, star (vecSeq x i) * vecSeq y i = star x ⬝ᵥ y := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => star (vecSeq x i) * vecSeq y i) N]
  simp [vecSeq, dotProduct]

private theorem lz_sum_range_star_mul_self (x : Fin N → 𝕜) :
    ∑ i ∈ Finset.range N, star (vecSeq x i) * vecSeq x i = ((‖WithLp.toLp 2 x‖ ^ 2 : ℝ) : 𝕜) := by
  rw [lz_sum_range_star_mul, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq]

omit [DecidableEq P] in
private theorem lz_exactSem_sqrt (p : P) (x : Fin N → 𝕜) :
    (exactSem (𝕜 := 𝕜)).un p .sqrt ((‖WithLp.toLp 2 x‖ ^ 2 : ℝ) : 𝕜) =
      some ((‖WithLp.toLp 2 x‖ : ℝ) : 𝕜) := by
  have h0 : (0 : 𝕜) ≤ ((‖WithLp.toLp 2 x‖ ^ 2 : ℝ) : 𝕜) := RCLike.ofReal_nonneg.mpr (sq_nonneg _)
  simp only [exactSem, h0, if_true, RCLike.ofReal_re, Real.sqrt_sq (norm_nonneg _)]

private theorem lz_eq_zero_of_norm (x : Fin N → 𝕜) (h : ((‖WithLp.toLp 2 x‖ : ℝ) : 𝕜) = 0) :
    x = 0 := by
  have h' := congrArg WithLp.ofLp (norm_eq_zero.mp (RCLike.ofReal_eq_zero.mp h))
  simpa using h'

end Vectors

section Phases

/-- The first three instructions of a Lanczos step: $\mathbf{u} \leftarrow \mathbf{A}\mathbf{v}$,
then $\mathbf{w} = \mathbf{u} - \beta\mathbf{v}_{\mathrm{prev}}$ in slot `nxt`. -/
private theorem lz_exec_phase1 {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ) (o : ι)
    (p : P) (st : St P 𝕜 (OpCount P ι)) (cv pv : Fin N → 𝕜) (β : 𝕜) {W s : ℕ}
    {cur prev nxt : IExp ℕ} (hW : st.store.shape[W]? = some (p, 3 * N))
    (hs : st.store.shape[s]? = some (p, 4)) (hWs : W ≠ s) (hn3 : nxt.eval + N ≤ 3 * N)
    (hcn : cur.eval + N ≤ nxt.eval ∨ nxt.eval + N ≤ cur.eval)
    (hpn : prev.eval + N ≤ nxt.eval ∨ nxt.eval + N ≤ prev.eval)
    (hcur : ∀ i < N, st.store.read p W (cur.eval + i) = some (vecSeq cv i))
    (hprev : ∀ i < N, st.store.read p W (prev.eval + i) = some (vecSeq pv i))
    (hs1 : st.store.read p s 1 = some β) :
    ∃ st₃ : St P 𝕜 (OpCount P ι), st₃.store.shape = st.store.shape ∧
      (∀ i < N, st₃.store.read p W (nxt.eval + i) = some (vecSeq ((-β) • pv + A *ᵥ cv) i)) ∧
      (∀ b' i, (b' = W → i < nxt.eval ∨ nxt.eval + N ≤ i) → (b' = s → i ≠ 0) →
        st₃.store.read p b' i = st.store.read p b' i) ∧
      ∀ R : Builder P ι ℕ ℕ Unit, exec (exactInterp (fun _ => A) ξ)
        (stmt (.apply o p W nxt W cur 1) >>= fun _ => ins (.un p .neg ⟨s, 0⟩ ⟨s, 1⟩) >>= fun _ =>
          axpy p ⟨s, 0⟩ W prev W nxt (.const N) >>= fun _ => R).run st =
        exec (exactInterp (fun _ => A) ξ) R.run st₃ := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  obtain ⟨st1, h1, u1⟩ := lz_exec_apply A ξ o p st hW hn3 (by omega) hcur
  obtain ⟨st2, h2, u2⟩ := lz_exec_un I p st1 (dst := ⟨s, 0⟩) (x := ⟨s, 1⟩) (u := .neg)
    (by rw [u1.read_ne (Ne.symm hWs)]; exact hs1) rfl (by rw [u1.1]; exact hs) (Nat.zero_lt_succ 3)
  replace u2 : BlockUpd p st1.store st2.store s 0 1 fun _ => -β := u2
  obtain ⟨st3, h3, u3⟩ := lz_exec_axpy I rfl (fun _ => rfl) p st2 (a := ⟨s, 0⟩) (x := W)
    (xo := prev) (y := W) (yo := nxt) (n := .const N) (u2.read_in (i := 0) Nat.one_pos)
    (fun i (hi : i < N) => by rw [u2.read_ne hWs, u1.read_out (by omega)]; exact hprev i hi)
    (fun i hi => by rw [u2.read_ne hWs]; exact u1.read_in hi) (Ne.symm hWs) (fun _ => hpn)
    (by rw [u2.1, u1.1]; exact hW) hn3
  replace u3 : BlockUpd p st2.store st3.store W nxt.eval N
    fun i => -β * vecSeq pv i + vecSeq (A *ᵥ cv) i := u3
  refine ⟨st3, by rw [u3.1, u2.1, u1.1], fun i hi => by rw [u3.read_in hi, vecSeq_smul_add],
    fun b' i hW' hs' => ?_, fun R => ?_⟩
  · by_cases hb : b' = W
    · rw [u3.read_out (hW' hb), u2.read_ne (hb ▸ hWs), u1.read_out (hW' hb)]
    · rw [u3.read_ne hb]
      by_cases hbs : b' = s
      · rw [u2.read_out (by have := hs' hbs; omega), u1.read_ne hb]
      · rw [u2.read_ne hbs, u1.read_ne hb]
  · rw [exec_bind_of_exec_eq_some I h1 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h2 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h3 ⟨_, fun _ => rfl⟩]

variable (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
  (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (st : St P 𝕜 (OpCount P ι))

include hI hc in
/-- Instructions 4 to 6 of a Lanczos step: $\alpha = \operatorname{Re}\mathbf{v}^{\mathsf{H}}
\mathbf{w}$ into `s[0]` and into `aC`. -/
private theorem lz_exec_phase2 {N : ℕ} (cv wv : Fin N → 𝕜) {W s La : ℕ} {cur nxt : IExp ℕ}
    {aC : Cell ℕ ℕ} (hs : st.store.shape[s]? = some (p, 4))
    (ha : st.store.shape[aC.buf]? = some (p, La)) (hai : aC.idx.eval < La) (hWs : W ≠ s)
    (has : aC.buf ≠ s)
    (hcur : ∀ i < N, st.store.read p W (cur.eval + i) = some (vecSeq cv i))
    (hnxt : ∀ i < N, st.store.read p W (nxt.eval + i) = some (vecSeq wv i)) :
    ∃ st₆ : St P 𝕜 (OpCount P ι), st₆.store.shape = st.store.shape ∧
      st₆.store.read p aC.buf aC.idx.eval = some (RCLike.re (star cv ⬝ᵥ wv) : 𝕜) ∧
      st₆.store.read p s 0 = some (RCLike.re (star cv ⬝ᵥ wv) : 𝕜) ∧
      (∀ b' i, (b' = s → i ≠ 0) → (b' = aC.buf → i ≠ aC.idx.eval) →
        st₆.store.read p b' i = st.store.read p b' i) ∧
      ∀ R : Builder P ι ℕ ℕ Unit, exec I (dot p ⟨s, 0⟩ W cur W nxt (.const N) >>= fun _ =>
        ins (.un p .re ⟨s, 0⟩ ⟨s, 0⟩) >>= fun _ => ins (.copy p aC ⟨s, 0⟩) >>= fun _ => R).run
          st = exec I R.run st₆ := by
  obtain ⟨st4, h4, u4⟩ := lz_exec_dot I hI hc p st (dst := ⟨s, 0⟩) (n := .const N) hcur hnxt
    hWs.symm hWs.symm hs (Nat.zero_lt_succ 3)
  replace u4 : BlockUpd p st.store st4.store s 0 1 fun _ => star cv ⬝ᵥ wv :=
    u4.congr fun _ _ => lz_sum_range_star_mul cv wv
  obtain ⟨st5, h5, u5⟩ := lz_exec_un I p st4 (dst := ⟨s, 0⟩) (x := ⟨s, 0⟩) (u := .re)
    (u4.read_in (i := 0) Nat.one_pos) (by rw [hI]; rfl) (by rw [u4.1]; exact hs)
    (Nat.zero_lt_succ 3)
  replace u5 : BlockUpd p st4.store st5.store s 0 1 fun _ => (RCLike.re (star cv ⬝ᵥ wv) : 𝕜) := u5
  obtain ⟨st6, h6, u6⟩ := lz_exec_copy I p st5 (dst := aC) (x := ⟨s, 0⟩)
    (u5.read_in (i := 0) Nat.one_pos) (by rw [u5.1, u4.1]; exact ha) hai
  refine ⟨st6, by rw [u6.1, u5.1, u4.1], by simpa using u6.read_in (i := 0) Nat.one_pos,
    by rw [u6.read_ne has.symm]; exact u5.read_in (i := 0) Nat.one_pos,
    fun b' i hs' ha' => ?_, fun R => ?_⟩
  · have h6' : st6.store.read p b' i = st5.store.read p b' i := by
      by_cases hb : b' = aC.buf
      · exact u6.read_out (by have := ha' hb; omega)
      · exact u6.read_ne hb
    by_cases hbs : b' = s
    · rw [h6', u5.read_out (by have := hs' hbs; omega), u4.read_out (by have := hs' hbs; omega)]
    · rw [h6', u5.read_ne hbs, u4.read_ne hbs]
  · rw [exec_bind_of_exec_eq_some I h4 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h5 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h6 ⟨_, fun _ => rfl⟩]

include hI hc in
/-- Instructions 7 to 11 of a Lanczos step: $\mathbf{z} = \mathbf{w} - a\mathbf{v}$ in slot
`nxt`, then $\|\mathbf{z}\|$ into `s[1]` and into `bC`. -/
private theorem lz_exec_phase3 {N : ℕ} (cv wv : Fin N → 𝕜) (a : 𝕜) {W s Lb : ℕ} {cur nxt : IExp ℕ}
    {bC : Cell ℕ ℕ} (hW : st.store.shape[W]? = some (p, 3 * N))
    (hs : st.store.shape[s]? = some (p, 4)) (hb : st.store.shape[bC.buf]? = some (p, Lb))
    (hbi : bC.idx.eval < Lb) (hWs : W ≠ s) (hbW : bC.buf ≠ W) (hbs : bC.buf ≠ s)
    (hn3 : nxt.eval + N ≤ 3 * N) (hcn : cur.eval + N ≤ nxt.eval ∨ nxt.eval + N ≤ cur.eval)
    (hs0 : st.store.read p s 0 = some a)
    (hcur : ∀ i < N, st.store.read p W (cur.eval + i) = some (vecSeq cv i))
    (hnxt : ∀ i < N, st.store.read p W (nxt.eval + i) = some (vecSeq wv i)) :
    ∃ st₁₁ : St P 𝕜 (OpCount P ι), st₁₁.store.shape = st.store.shape ∧
      (∀ i < N, st₁₁.store.read p W (nxt.eval + i) = some (vecSeq ((-a) • cv + wv) i)) ∧
      st₁₁.store.read p s 1 = some ((‖WithLp.toLp 2 ((-a) • cv + wv)‖ : ℝ) : 𝕜) ∧
      st₁₁.store.read p bC.buf bC.idx.eval =
        some ((‖WithLp.toLp 2 ((-a) • cv + wv)‖ : ℝ) : 𝕜) ∧
      (∀ b' i, (b' = W → i < nxt.eval ∨ nxt.eval + N ≤ i) → (b' = s → 2 < i) →
        (b' = bC.buf → i ≠ bC.idx.eval) → st₁₁.store.read p b' i = st.store.read p b' i) ∧
      ∀ R : Builder P ι ℕ ℕ Unit, exec I (ins (.un p .neg ⟨s, 0⟩ ⟨s, 0⟩) >>= fun _ =>
        axpy p ⟨s, 0⟩ W cur W nxt (.const N) >>= fun _ =>
        dot p ⟨s, 2⟩ W nxt W nxt (.const N) >>= fun _ =>
        ins (.un p .sqrt ⟨s, 1⟩ ⟨s, 2⟩) >>= fun _ => ins (.copy p bC ⟨s, 1⟩) >>= fun _ =>
          R).run st = exec I R.run st₁₁ := by
  set z := (-a) • cv + wv
  obtain ⟨st7, h7, u7⟩ := lz_exec_un I p st (dst := ⟨s, 0⟩) (x := ⟨s, 0⟩) (u := .neg) hs0
    (by rw [hI]; rfl) hs (Nat.zero_lt_succ 3)
  replace u7 : BlockUpd p st.store st7.store s 0 1 fun _ => -a := u7
  obtain ⟨st8, h8, u8⟩ := lz_exec_axpy I hI hc p st7 (a := ⟨s, 0⟩) (x := W) (xo := cur) (y := W)
    (yo := nxt) (n := .const N) (u7.read_in (i := 0) Nat.one_pos)
    (fun i hi => by rw [u7.read_ne hWs]; exact hcur i hi)
    (fun i hi => by rw [u7.read_ne hWs]; exact hnxt i hi) hWs.symm (fun _ => hcn)
    (by rw [u7.1]; exact hW) hn3
  replace u8 : BlockUpd p st7.store st8.store W nxt.eval N (vecSeq z) :=
    u8.congr fun i _ => vecSeq_smul_add _ _ _ i
  obtain ⟨st9, h9, u9⟩ := lz_exec_dot I hI hc p st8 (dst := ⟨s, 2⟩) (n := .const N)
    (fun i hi => u8.read_in hi) (fun i hi => u8.read_in hi) hWs.symm hWs.symm
    (by rw [u8.1, u7.1]; exact hs) (show 2 < 4 by norm_num)
  replace u9 : BlockUpd p st8.store st9.store s 2 1 fun _ => ((‖WithLp.toLp 2 z‖ ^ 2 : ℝ) : 𝕜) :=
    u9.congr fun _ _ => lz_sum_range_star_mul_self z
  obtain ⟨st10, h10, u10⟩ := lz_exec_un I p st9 (dst := ⟨s, 1⟩) (x := ⟨s, 2⟩) (u := .sqrt)
    (u9.read_in (i := 0) Nat.one_pos) (by rw [hI]; exact lz_exactSem_sqrt p z)
    (by rw [u9.1, u8.1, u7.1]; exact hs) (show 1 < 4 by norm_num)
  replace u10 : BlockUpd p st9.store st10.store s 1 1 fun _ => ((‖WithLp.toLp 2 z‖ : ℝ) : 𝕜) := u10
  obtain ⟨st11, h11, u11⟩ := lz_exec_copy I p st10 (dst := bC) (x := ⟨s, 1⟩)
    (u10.read_in (i := 0) Nat.one_pos) (by rw [u10.1, u9.1, u8.1, u7.1]; exact hb) hbi
  refine ⟨st11, by rw [u11.1, u10.1, u9.1, u8.1, u7.1], fun i hi => ?_,
    by rw [u11.read_ne hbs.symm]; exact u10.read_in (i := 0) Nat.one_pos,
    by simpa using u11.read_in (i := 0) Nat.one_pos, fun b' i hW' hs' hb' => ?_, fun R => ?_⟩
  · rw [u11.read_ne hbW.symm, u10.read_ne hWs, u9.read_ne hWs]
    exact u8.read_in hi
  · have h11' : st11.store.read p b' i = st10.store.read p b' i := by
      by_cases hb : b' = bC.buf
      · exact u11.read_out (by have := hb' hb; omega)
      · exact u11.read_ne hb
    rw [h11']
    by_cases hbs : b' = s
    · have := hs' hbs
      rw [u10.read_out (by omega), u9.read_out (by omega), u8.read_ne (hbs ▸ hWs.symm),
        u7.read_out (by omega)]
    · by_cases hbW : b' = W
      · rw [u10.read_ne hbs, u9.read_ne hbs, u8.read_out (hW' hbW), u7.read_ne hbs]
      · rw [u10.read_ne hbs, u9.read_ne hbs, u8.read_ne hbW, u7.read_ne hbs]
  · rw [exec_bind_of_exec_eq_some I h7 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h8 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h9 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h10 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h11 ⟨_, fun _ => rfl⟩]

include hI hc in
/-- The normalisation of a Lanczos step: slot `nxt` divided by the cell `c` unless `c` equals
the cell `d`, which holds $0$. -/
private theorem lz_exec_phase4 {N : ℕ} (z : Fin N → 𝕜) {W : ℕ} {nxt : IExp ℕ} {c d : Cell ℕ ℕ}
    (hW : st.store.shape[W]? = some (p, 3 * N)) (hcW : c.buf ≠ W) (hn3 : nxt.eval + N ≤ 3 * N)
    (hs1 : st.store.read p c.buf c.idx.eval = some ((‖WithLp.toLp 2 z‖ : ℝ) : 𝕜))
    (hs3 : st.store.read p d.buf d.idx.eval = some 0)
    (hnxt : ∀ i < N, st.store.read p W (nxt.eval + i) = some (vecSeq z i)) :
    ∃ st' : St P 𝕜 (OpCount P ι), exec I (ifThenElse p .eq c d (pure ())
        (rscl p c W nxt (.const N))).run st = some st' ∧
      st'.store.shape = st.store.shape ∧
      (∀ i < N, st'.store.read p W (nxt.eval + i) =
        some (vecSeq ((‖WithLp.toLp 2 z‖ : 𝕜)⁻¹ • z) i)) ∧
      ∀ b' i, (b' = W → i < nxt.eval ∨ nxt.eval + N ≤ i) →
        st'.store.read p b' i = st.store.read p b' i := by
  rw [show (ifThenElse (ι := ι) p .eq c d (pure ()) (rscl p c W nxt (.const N))).run =
    .seq (.ite p .eq c d .skip (rscl p c W nxt (.const N)).run) .skip from rfl,
    exec_seq_skip, lz_exec_ite_eq I hI p st _ _ hs1 hs3]
  split_ifs with h0
  · have hz := lz_eq_zero_of_norm z h0
    refine ⟨_, exec_skip I _, rfl, fun i hi => ?_, fun _ _ _ => rfl⟩
    rw [hnxt i hi, hz, smul_zero]
  · obtain ⟨st', h', u'⟩ := lz_exec_rscl I hI hc p { st with cnt := st.cnt + I.charge (.cmp p) }
      (a := c) (x := W) (xo := nxt) (n := .const N) (xs := vecSeq z) h0 hs1 hnxt hcW hW hn3
    refine ⟨st', h', u'.1, fun i hi => by rw [u'.read_in hi, vecSeq_div], fun b' i hb => ?_⟩
    by_cases hbW : b' = W
    · exact u'.read_out (hb hbW)
    · exact u'.read_ne hbW

end Phases

section Step

omit [RCLike 𝕜] [DecidableEq P] in
/-- Builders reassociate definitionally. -/
private theorem lz_bind_assoc {α β : Type} (x : Builder P ι ℕ ℕ α) (f : α → Builder P ι ℕ ℕ β)
    (g : β → Builder P ι ℕ ℕ Unit) : (x >>= f) >>= g = x >>= fun u => f u >>= g := rfl

/-- **One step of the Lanczos program computes `NLAlib.lanczosStep`** in exact arithmetic: from
slot `cur` holding $\mathbf{q}_j$, slot `prev` holding $\mathbf{q}_{j-1}$, `s[1]` $= \beta_j$
and `s[3]` $= 0$, the run writes $\alpha_j$ into `aC`, $\beta_{j+1}$ into `bC` and `s[1]`,
$\mathbf{q}_{j+1}$ into slot `nxt`, and changes no other cell outside `s`. -/
private theorem lz_exec_lanczosStep {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ)
    (o : ι) (p : P) (st : St P 𝕜 (OpCount P ι)) (S : LanczosState 𝕜 (Fin N)) {W s La Lb : ℕ}
    {cur prev nxt : IExp ℕ} {aC bC : Cell ℕ ℕ} (hW : st.store.shape[W]? = some (p, 3 * N))
    (hs : st.store.shape[s]? = some (p, 4)) (ha : st.store.shape[aC.buf]? = some (p, La))
    (hai : aC.idx.eval < La) (hb : st.store.shape[bC.buf]? = some (p, Lb))
    (hbi : bC.idx.eval < Lb) (hWs : W ≠ s) (haW : aC.buf ≠ W) (has : aC.buf ≠ s)
    (hbW : bC.buf ≠ W) (hbs : bC.buf ≠ s) (hab : aC.buf ≠ bC.buf) (hn3 : nxt.eval + N ≤ 3 * N)
    (hcn : cur.eval + N ≤ nxt.eval ∨ nxt.eval + N ≤ cur.eval)
    (hpn : prev.eval + N ≤ nxt.eval ∨ nxt.eval + N ≤ prev.eval)
    (hcur : ∀ i < N, st.store.read p W (cur.eval + i) = some (vecSeq S.cur i))
    (hprev : ∀ i < N, st.store.read p W (prev.eval + i) = some (vecSeq S.prev i))
    (hs1 : st.store.read p s 1 = some (S.beta : 𝕜)) (hs3 : st.store.read p s 3 = some 0) :
    ∃ st', exec (exactInterp (fun _ => A) ξ) (lanczosStepWith
        (fun W src dst => stmt (.apply o p W dst W src 1)) p (.const N) W cur prev nxt s aC
          bC).run st = some st' ∧
      st'.store.shape = st.store.shape ∧
      st'.store.read p aC.buf aC.idx.eval = some (lanczosAlpha A S : 𝕜) ∧
      st'.store.read p bC.buf bC.idx.eval = some ((lanczosStep A S).beta : 𝕜) ∧
      (∀ i < N, st'.store.read p W (nxt.eval + i) = some (vecSeq (lanczosStep A S).cur i)) ∧
      st'.store.read p s 1 = some ((lanczosStep A S).beta : 𝕜) ∧
      st'.store.read p s 3 = some 0 ∧
      ∀ b' i, b' ≠ s → (b' = W → i < nxt.eval ∨ nxt.eval + N ≤ i) →
        (b' = aC.buf → i ≠ aC.idx.eval) → (b' = bC.buf → i ≠ bC.idx.eval) →
        st'.store.read p b' i = st.store.read p b' i := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  obtain ⟨st3, sh3, n3, f3, h3⟩ := lz_exec_phase1 A ξ o p st S.cur S.prev (S.beta : 𝕜) hW hs
    hWs hn3 hcn hpn hcur hprev hs1
  set wv := (-(S.beta : 𝕜)) • S.prev + A *ᵥ S.cur with hwv
  have hcur3 : ∀ i < N, st3.store.read p W (cur.eval + i) = some (vecSeq S.cur i) := fun i hi => by
    rw [f3 _ _ (fun _ => by omega) (fun h => absurd h hWs)]; exact hcur i hi
  obtain ⟨st6, sh6, a6, s06, f6, h6⟩ := lz_exec_phase2 I rfl (fun _ => rfl) p st3 S.cur wv
    (by rw [sh3]; exact hs) (by rw [sh3]; exact ha) hai hWs has hcur3 n3
  have hα : (RCLike.re (star S.cur ⬝ᵥ wv) : 𝕜) = (lanczosAlpha A S : 𝕜) := by
    rw [lanczosAlpha, hwv, neg_smul, neg_add_eq_sub]
  rw [hα] at a6 s06
  have hW6 : ∀ i, st6.store.read p W i = st3.store.read p W i := fun i =>
    f6 _ _ (fun h => absurd h hWs) (fun h => absurd h.symm haW)
  obtain ⟨st11, sh11, n11, s111, b11, f11, h11⟩ := lz_exec_phase3 I rfl (fun _ => rfl) p st6
    S.cur wv (lanczosAlpha A S : 𝕜) (by rw [sh6, sh3]; exact hW) (by rw [sh6, sh3]; exact hs)
    (by rw [sh6, sh3]; exact hb) hbi hWs hbW hbs hn3 hcn s06
    (fun i hi => by rw [hW6]; exact hcur3 i hi) (fun i hi => by rw [hW6]; exact n3 i hi)
  set z := (-(lanczosAlpha A S : 𝕜)) • S.cur + wv with hz
  have hz' : z = A *ᵥ S.cur - (S.beta : 𝕜) • S.prev - (lanczosAlpha A S : 𝕜) • S.cur := by
    rw [hz, hwv, neg_smul, neg_smul]; abel
  have hs3' : st11.store.read p s 3 = some 0 := by
    rw [f11 _ _ (fun h => absurd h.symm hWs) (fun _ => by norm_num) (fun h => absurd h.symm hbs),
      f6 _ _ (fun _ => by norm_num) (fun h => absurd h.symm has),
      f3 _ _ (fun h => absurd h.symm hWs) (fun _ => by norm_num)]
    exact hs3
  obtain ⟨st12, h12, sh12, n12, f12⟩ := lz_exec_phase4 I rfl (fun _ => rfl) p st11 z
    (c := ⟨s, 1⟩) (d := ⟨s, 3⟩) (by rw [sh11, sh6, sh3]; exact hW) hWs.symm hn3 s111 hs3' n11
  have hstep : lanczosStep A S = ⟨S.cur, (‖WithLp.toLp 2 z‖ : 𝕜)⁻¹ • z, ‖WithLp.toLp 2 z‖⟩ := by
    rw [hz']; rfl
  refine ⟨st12, (h3 _).trans ((h6 _).trans ((h11 _).trans h12)), by rw [sh12, sh11, sh6, sh3],
    ?_, ?_, by rw [hstep]; exact n12, ?_, by rw [f12 _ _ (fun h => absurd h.symm hWs)]; exact hs3',
    fun b' i hbs' hW' ha' hb' => ?_⟩
  · rw [f12 _ _ (fun h => absurd h haW),
      f11 _ _ (fun h => absurd h haW) (fun h => absurd h has) (fun h => absurd h hab)]
    exact a6
  · rw [f12 _ _ (fun h => absurd h hbW), hstep]; exact b11
  · rw [f12 _ _ (fun h => absurd h.symm hWs), hstep]; exact s111
  · rw [f12 _ _ hW', f11 _ _ hW' (fun h => absurd h hbs') hb', f6 _ _ (fun h => absurd h hbs') ha',
      f3 _ _ hW' (fun h => absurd h hbs')]

/-- **The start of the Lanczos program**: from buffer `bb` holding $\mathbf{b}$, slot 0 of `W`
holds $\mathbf{q}_0 = \mathbf{b}/\|\mathbf{b}\|$, slot 2 holds $\mathbf{0}$, `s[1]` $= 0$ and
`s[3]` $= 0$; no cell outside `W` and `s` changes. -/
private theorem lz_exec_lanczosInit {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ)
    (p : P) (st : St P 𝕜 (OpCount P ι)) (b : Fin N → 𝕜) {bb W s : ℕ}
    (hW : st.store.shape[W]? = some (p, 3 * N)) (hs : st.store.shape[s]? = some (p, 4))
    (hWs : W ≠ s) (hbW : bb ≠ W) (hbs : bb ≠ s)
    (hb : ∀ i < N, st.store.read p bb (0 + i) = some (vecSeq b i)) :
    ∃ st' : St P 𝕜 (OpCount P ι), st'.store.shape = st.store.shape ∧
      (∀ i < N, st'.store.read p W (0 + i) = some (vecSeq (lanczosState A b 0).cur i)) ∧
      (∀ i < N, st'.store.read p W (2 * N + i) = some (vecSeq (lanczosState A b 0).prev i)) ∧
      st'.store.read p s 1 = some ((lanczosState A b 0).beta : 𝕜) ∧
      st'.store.read p s 3 = some 0 ∧
      (∀ b' i, b' ≠ W → b' ≠ s → st'.store.read p b' i = st.store.read p b' i) ∧
      ∀ R : Builder P ι ℕ ℕ Unit, exec (exactInterp (fun _ => A) ξ)
        (lanczosInit p (.const N) bb W s >>= fun _ => R).run st =
          exec (exactInterp (fun _ => A) ξ) R.run st' := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  obtain ⟨st1, h1, u1⟩ := lz_exec_lit I rfl p st (dst := ⟨s, 3⟩) hs (show 3 < 4 by norm_num)
  replace u1 : BlockUpd p st.store st1.store s 3 1 fun _ => 0 := u1
  obtain ⟨st2, h2, u2⟩ := lz_exec_forRange_lit I rfl p st1 (W := W) (off := 2 * N)
    (n := .const N) (o := 2 * .const N) rfl (by rw [u1.1]; exact hW) (by simp; omega)
  replace u2 : BlockUpd p st1.store st2.store W (2 * N) N fun _ => 0 := u2
  obtain ⟨st3, h3, u3⟩ := lz_exec_copyv I (fun _ => rfl) p st2 (x := bb) (xo := 0) (y := W)
    (yo := 0) (n := .const N) (fun i hi => by rw [u2.read_ne hbW, u1.read_ne hbs]; exact hb i hi)
    (fun h => absurd h hbW) (by rw [u2.1, u1.1]; exact hW) (by simp; omega)
  replace u3 : BlockUpd p st2.store st3.store W 0 N (vecSeq b) := u3
  have hb3 : ∀ i < N, st3.store.read p bb (0 + i) = some (vecSeq b i) := fun i hi => by
    rw [u3.read_ne hbW, u2.read_ne hbW, u1.read_ne hbs]; exact hb i hi
  obtain ⟨st4, h4, u4⟩ := lz_exec_dot I rfl (fun _ => rfl) p st3 (dst := ⟨s, 2⟩) (n := .const N)
    (xo := 0) (yo := 0) hb3 hb3 (Ne.symm hbs) (Ne.symm hbs) (by rw [u3.1, u2.1, u1.1]; exact hs)
    (show 2 < 4 by norm_num)
  replace u4 : BlockUpd p st3.store st4.store s 2 1 fun _ => ((‖WithLp.toLp 2 b‖ ^ 2 : ℝ) : 𝕜) :=
    u4.congr fun _ _ => lz_sum_range_star_mul_self b
  obtain ⟨st5, h5, u5⟩ := lz_exec_un I p st4 (dst := ⟨s, 2⟩) (x := ⟨s, 2⟩) (u := .sqrt)
    (u4.read_in (i := 0) Nat.one_pos) (lz_exactSem_sqrt p b)
    (by rw [u4.1, u3.1, u2.1, u1.1]; exact hs) (show 2 < 4 by norm_num)
  replace u5 : BlockUpd p st4.store st5.store s 2 1 fun _ => ((‖WithLp.toLp 2 b‖ : ℝ) : 𝕜) := u5
  have hs35 : st5.store.read p s 3 = some 0 := by
    rw [u5.read_out (by norm_num), u4.read_out (by norm_num), u3.read_ne hWs.symm,
      u2.read_ne hWs.symm]
    exact u1.read_in (i := 0) Nat.one_pos
  obtain ⟨st6, h6, sh6, n6, f6⟩ := lz_exec_phase4 I rfl (fun _ => rfl) p st5 b (nxt := 0)
    (c := ⟨s, 2⟩) (d := ⟨s, 3⟩) (by rw [u5.1, u4.1, u3.1, u2.1, u1.1]; exact hW) hWs.symm
    (by simp; omega) (u5.read_in (i := 0) Nat.one_pos) hs35
    (fun i hi => by rw [u5.read_ne hWs, u4.read_ne hWs]; exact u3.read_in hi)
  obtain ⟨st7, h7, u7⟩ := lz_exec_lit I rfl p st6 (dst := ⟨s, 1⟩)
    (by rw [sh6, u5.1, u4.1, u3.1, u2.1, u1.1]; exact hs) (show 1 < 4 by norm_num)
  replace u7 : BlockUpd p st6.store st7.store s 1 1 fun _ => 0 := u7
  refine ⟨st7, by rw [u7.1, sh6, u5.1, u4.1, u3.1, u2.1, u1.1], fun i hi => ?_,
    fun i hi => ?_, by simpa [lanczosState] using u7.read_in (i := 0) Nat.one_pos,
    by rw [u7.read_out (by norm_num), f6 _ _ (fun h => absurd h hWs.symm)]; exact hs35,
    fun b' i hW' hs' => ?_, fun R => ?_⟩
  · rw [u7.read_ne hWs]
    exact n6 i hi
  · rw [u7.read_ne hWs, f6 _ _ (fun _ => by simp; omega), u5.read_ne hWs, u4.read_ne hWs,
      u3.read_out (by omega), u2.read_in hi]
    simp [lanczosState, vecSeq]
  · rw [u7.read_ne hs', f6 _ _ (fun h => absurd h hW'), u5.read_ne hs', u4.read_ne hs',
      u3.read_ne hW', u2.read_ne hW', u1.read_ne hs']
  · simp only [lanczosInit, lz_bind_assoc]
    rw [exec_bind_of_exec_eq_some I h1 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h2 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h3 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h4 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h5 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h6 ⟨_, fun _ => rfl⟩,
        exec_bind_of_exec_eq_some I h7 ⟨_, fun _ => rfl⟩]

end Step

section Program

/-- Slot $a < 3$ of length $N$ fits in $3N$ cells. -/
private theorem lz_slot_le {N a : ℕ} (ha : a < 3) : N * a + N ≤ 3 * N := by
  interval_cases a <;> omega

/-- The loop invariant of the Lanczos program before step `j`, with the buffers of the program
(`1`, `2`, `3` the outputs, `4` the three slots, `5` the scalars). -/
private def LzInv {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (b : Fin N → 𝕜) (p : P)
    (sh : Array (P × ℕ)) (j : ℕ) (st : St P 𝕜 (OpCount P ι)) : Prop :=
  st.store.shape = sh ∧
  (∀ i < N, st.store.read p 4 (N * (j % 3) + i) = some (vecSeq (lanczosState A b j).cur i)) ∧
  (∀ i < N, st.store.read p 4 (N * ((j + 2) % 3) + i) =
    some (vecSeq (lanczosState A b j).prev i)) ∧
  st.store.read p 5 1 = some ((lanczosState A b j).beta : 𝕜) ∧ st.store.read p 5 3 = some 0 ∧
  ∀ k < j, st.store.read p 1 k = some (lanczosAlpha A (lanczosState A b k) : 𝕜) ∧
    st.store.read p 2 k = some ((lanczosState A b (k + 1)).beta : 𝕜) ∧
    ∀ i < N, st.store.read p 3 (N * k + i) = some (vecSeq (lanczosState A b k).cur i)

/-- One iteration of the loop of the Lanczos program keeps the invariant. -/
private theorem lz_inv_step {N q : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (b : Fin N → 𝕜)
    (ξ : Dist → ℕ → ℝ) (o : ι) (p : P) (sh : Array (P × ℕ)) (hal : sh[1]? = some (p, q))
    (hbe : sh[2]? = some (p, q)) (hQ : sh[3]? = some (p, N * (q + 1)))
    (hW : sh[4]? = some (p, 3 * N)) (hs : sh[5]? = some (p, 4)) {j : ℕ} (hj : j < q)
    (st : St P 𝕜 (OpCount P ι)) (h : LzInv A b p sh j st) :
    ∃ st', exec (exactInterp (fun _ => A) ξ)
      (copyv p 4 (.const N * (.var j % 3)) 3 (.const N * .var j) (.const N) >>= fun _ =>
        lanczosStepWith (fun W src dst => stmt (.apply o p W dst W src 1)) p (.const N) 4
          (.const N * (.var j % 3)) (.const N * ((.var j + 2) % 3))
          (.const N * ((.var j + 1) % 3)) 5 ⟨1, .var j⟩ ⟨2, .var j⟩).run st = some st' ∧
      LzInv (ι := ι) A b p sh (j + 1) st' := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  obtain ⟨hsh0, hcur, hprev, hs1, hs3, hold⟩ := h
  obtain ⟨st1, h1, u1⟩ := lz_exec_copyv I (fun _ => rfl) p st (x := 4)
    (xo := .const N * (.var j % 3)) (y := 3) (yo := .const N * .var j) (n := .const N)
    (xs := vecSeq (lanczosState A b j).cur) hcur (fun h => absurd h (by norm_num))
    (by rw [hsh0]; exact hQ) (by
      simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_var]
      rw [Nat.mul_succ]; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hj.le) _)
  replace u1 : BlockUpd p st.store st1.store 3 (N * j) N (vecSeq (lanczosState A b j).cur) := u1
  have hm : j % 3 < 3 ∧ (j + 1) % 3 < 3 ∧ (j + 2) % 3 < 3 := by omega
  obtain ⟨st2, h2, sh2, ha2, hb2, hn2, hs12, hs32, f2⟩ := lz_exec_lanczosStep A ξ o p st1
    (lanczosState A b j) (W := 4) (s := 5) (cur := .const N * (.var j % 3))
    (prev := .const N * ((.var j + 2) % 3)) (nxt := .const N * ((.var j + 1) % 3))
    (aC := ⟨1, .var j⟩) (bC := ⟨2, .var j⟩) (by rw [u1.1, hsh0]; exact hW)
    (by rw [u1.1, hsh0]; exact hs) (by rw [u1.1, hsh0]; exact hal) hj
    (by rw [u1.1, hsh0]; exact hbe) hj (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (lz_slot_le hm.2.1)
    (slot_disjoint N (a := j % 3) (b := (j + 1) % 3) (by omega))
    (slot_disjoint N (a := (j + 2) % 3) (b := (j + 1) % 3) (by omega))
    (fun i hi => by rw [u1.read_ne (by norm_num)]; exact hcur i hi)
    (fun i hi => by rw [u1.read_ne (by norm_num)]; exact hprev i hi)
    (by rw [u1.read_ne (by norm_num)]; exact hs1) (by rw [u1.read_ne (by norm_num)]; exact hs3)
  have f2' : ∀ b' i, b' ≠ 5 → b' ≠ 4 → b' ≠ 1 → b' ≠ 2 →
      st2.store.read p b' i = st1.store.read p b' i := fun b' i h5 h4 h1 h2 =>
    f2 b' i h5 (fun h => absurd h h4) (fun h => absurd h h1) (fun h => absurd h h2)
  refine ⟨st2, (exec_bind_of_exec_eq_some I h1 ⟨_, fun _ => rfl⟩ _).trans h2,
    ⟨by rw [sh2, u1.1, hsh0], fun i hi => hn2 i hi, fun i hi => ?_, hs12, hs32,
      fun k hk => ?_⟩⟩
  · have hd := slot_disjoint N (a := j % 3) (b := (j + 1) % 3) (by omega)
    rw [show (j + 1 + 2) % 3 = j % 3 by omega, f2 _ _ (by norm_num) (fun _ => by
      change _ < N * ((j + 1) % 3) ∨ N * ((j + 1) % 3) + N ≤ _; omega)
      (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num)), u1.read_ne (by norm_num)]
    exact hcur i hi
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · obtain ⟨ha, hb, hq⟩ := hold k hk
      refine ⟨?_, ?_, fun i hi => ?_⟩
      · rw [f2 _ _ (by norm_num) (fun h => absurd h (by norm_num)) (fun _ => Nat.ne_of_lt hk)
          (fun h => absurd h (by norm_num)), u1.read_ne (by norm_num)]
        exact ha
      · rw [f2 _ _ (by norm_num) (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
          (fun _ => Nat.ne_of_lt hk), u1.read_ne (by norm_num)]
        exact hb
      · have := Nat.add_mul_lt_mul_of_lt_of_lt hi hk
        rw [f2' _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
          u1.read_out (Or.inl (by omega))]
        exact hq i hi
    · refine ⟨ha2, hb2, fun i hi => ?_⟩
      rw [f2' _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
      exact u1.read_in hi

/-- The outputs of the Lanczos program in a store: `alpha` (buffer 1), `beta` (buffer 2) and the
basis (buffer 3, column-major). -/
private def LzOut {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (b : Fin N → 𝕜) (p : P) (q : ℕ)
    (s : Store P 𝕜) : Prop :=
  (∀ j < q, s.read p 1 j = some (lanczosAlpha A (lanczosState A b j) : 𝕜)) ∧
  (∀ j < q, s.read p 2 j = some ((lanczosState A b (j + 1)).beta : 𝕜)) ∧
  ∀ j < q + 1, ∀ i < N, s.read p 3 (N * j + i) = some (vecSeq (lanczosState A b j).cur i)

omit [RCLike 𝕜] in
/-- The run of `forRange n body >>= f`: the loop, then the run of `f`. -/
private theorem lz_exec_forRange_bind (I : Interp P ι 𝕜 (OpCount P ι)) {n : IExp ℕ}
    {body : ℕ → Builder P ι ℕ ℕ Unit} {st st₁ : St P 𝕜 (OpCount P ι)}
    (h : exec I (.loop n fun i => (body i).run) st = some st₁) {f : Unit → Builder P ι ℕ ℕ Unit} :
    exec I (forRange n body >>= f).run st = exec I (f ()).run st₁ := by
  rw [exec_run_bind I (b := forRange n body) (X := .loop n fun i => (body i).run) (fun _ => rfl),
    show (forRange n body).run =
    .seq (.loop n fun i => (body i).run) .skip from rfl, exec_seq_skip, h, Option.bind_some]

/-- The Lanczos program after its two allocations. -/
private theorem lz_exec_lanczosInner {N : ℕ} (q : ℕ) (A : Matrix (Fin N) (Fin N) 𝕜)
    (b : Fin N → 𝕜) (ξ : Dist → ℕ → ℝ) (o : ι) (p : P) (st : St P 𝕜 (OpCount P ι))
    (hal : st.store.shape[1]? = some (p, q)) (hbe : st.store.shape[2]? = some (p, q))
    (hQ : st.store.shape[3]? = some (p, N * (q + 1)))
    (hW : st.store.shape[4]? = some (p, 3 * N)) (hs : st.store.shape[5]? = some (p, 4))
    (hb : ∀ i < N, st.store.read p 0 (0 + i) = some (vecSeq b i)) :
    ∃ st', exec (exactInterp (fun _ => A) ξ) (lanczosInit p (.const N) 0 4 5 >>= fun _ =>
        (forRange (.const q) fun j =>
          copyv p 4 (.const N * (.var j % 3)) 3 (.const N * .var j) (.const N) >>= fun _ =>
          lanczosStepWith (fun W src dst => stmt (.apply o p W dst W src 1)) p (.const N) 4
            (.const N * (.var j % 3)) (.const N * ((.var j + 2) % 3))
            (.const N * ((.var j + 1) % 3)) 5 ⟨1, .var j⟩ ⟨2, .var j⟩) >>= fun _ =>
        copyv p 4 (.const N * (.const q % 3)) 3 (.const N * .const q) (.const N)).run st =
          some st' ∧ st'.store.shape = st.store.shape ∧ LzOut A b p q st'.store := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  obtain ⟨st1, sh1, c1, p1, s11, s31, -, h1⟩ := lz_exec_lanczosInit A ξ p st b (bb := 0) (W := 4)
    (s := 5) hW hs (by norm_num) (by norm_num) (by norm_num) hb
  have inv0 : LzInv (ι := ι) A b p st.store.shape 0 st1 :=
    ⟨sh1, fun i hi => by simpa using c1 i hi, fun i hi => by
      rw [show N * ((0 + 2) % 3) = 2 * N by omega]; exact p1 i hi, s11, s31,
      fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  obtain ⟨st2, h2, inv⟩ := exists_exec_loop_eq_some_of_forall I (n := .const q)
    (fun j st' => LzInv (ι := ι) A b p st.store.shape j st') inv0
    (fun j hj st' h => lz_inv_step A b ξ o p _ hal hbe hQ hW hs hj st' h)
  obtain ⟨hshq, hcurq, -, -, -, holdq⟩ := inv
  obtain ⟨st3, h3, u3⟩ := lz_exec_copyv I (fun _ => rfl) p st2 (x := 4)
    (xo := .const N * (.const q % 3)) (y := 3) (yo := .const N * .const q) (n := .const N)
    (xs := vecSeq (lanczosState A b q).cur) hcurq (fun h => absurd h (by norm_num))
    (by rw [hshq]; exact hQ) (by simp only [IExp.eval_mul, IExp.eval_const]; rw [Nat.mul_succ])
  replace u3 : BlockUpd p st2.store st3.store 3 (N * q) N (vecSeq (lanczosState A b q).cur) := u3
  refine ⟨st3, ?_, by rw [u3.1, hshq], fun j hj => ?_, fun j hj => ?_, fun j hj i hi => ?_⟩
  · rw [h1, lz_exec_forRange_bind I h2]
    exact h3
  · rw [u3.read_ne (by norm_num)]; exact (holdq j hj).1
  · rw [u3.read_ne (by norm_num)]; exact (holdq j hj).2.1
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have := Nat.add_mul_lt_mul_of_lt_of_lt hi hj
      rw [u3.read_out (Or.inl (by omega))]
      exact (holdq j hj).2.2 i hi
    · exact u3.read_in hi

private theorem lz_LzOut_pop {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} {b : Fin N → 𝕜} {p : P} {q : ℕ}
    {s : Store P 𝕜} (hs : 4 < s.size) (h : LzOut A b p q s) : LzOut A b p q s.pop := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj i hi => ?_⟩
  · rw [Store.read_pop_of_lt (by omega)]; exact h.1 j hj
  · rw [Store.read_pop_of_lt (by omega)]; exact h.2.1 j hj
  · rw [Store.read_pop_of_lt (by omega)]; exact h.2.2 j hj i hi

private theorem lz_exec_lanczosBasisProg {N : ℕ} (q : ℕ) (A : Matrix (Fin N) (Fin N) 𝕜)
    (b : Fin N → 𝕜) (ξ : Dist → ℕ → ℝ) (o : ι) (p : P) (st : St P 𝕜 (OpCount P ι))
    (hsz : st.store.size = 4) (hal : st.store.shape[1]? = some (p, q))
    (hbe : st.store.shape[2]? = some (p, q)) (hQ : st.store.shape[3]? = some (p, N * (q + 1)))
    (hb : ∀ i < N, st.store.read p 0 (0 + i) = some (vecSeq b i)) :
    ∃ st', exec (exactInterp (fun _ => A) ξ)
        (lanczosBasisProg p o (.const N) (.const q) 0 1 2 3).run st = some st' ∧
      LzOut A b p q st'.store := by
  set I := exactInterp (P := P) (ι := ι) (fun _ => A) ξ
  unfold lanczosBasisProg lanczosBasisProgWith
  rw [run_alloc_bind]
  refine exec_alloc_of I fun st₁ h₁ => ?_
  simp only [hsz, run_alloc_bind]
  refine exec_alloc_of I (Q := fun s => LzOut A b p q s.pop) fun st₂ h₂ => ?_
  have h5 : st₁.store.size = 5 := by rw [h₁, Array.size_push, hsz]
  rw [h5]
  have hsh : ∀ k < 4, st₂.store.shape[k]? = st.store.shape[k]? := fun k hk => by
    rw [h₂, Store.getElem?_shape_push_of_lt (s := st₁.store) _ (by omega), h₁,
      Store.getElem?_shape_push_of_lt (s := st.store) _ (by omega)]
  have hW : st₂.store.shape[4]? = some (p, 3 * N) := by
    rw [h₂, Store.getElem?_shape_push_of_lt (s := st₁.store) _ (by omega), h₁, ← hsz,
      Store.getElem?_shape_push_size]
    rfl
  have hs : st₂.store.shape[5]? = some (p, 4) := by
    rw [h₂, ← h5, Store.getElem?_shape_push_size]
    rfl
  have hb₂ : ∀ i < N, st₂.store.read p 0 (0 + i) = some (vecSeq b i) := fun i hi => by
    rw [h₂, Store.read_push_of_lt (s := st₁.store) (by omega), h₁,
      Store.read_push_of_lt (s := st.store) (by omega)]
    exact hb i hi
  obtain ⟨st₃, h₃, sh₃, out₃⟩ := lz_exec_lanczosInner q A b ξ o p st₂
    (by rw [hsh 1 (by norm_num)]; exact hal) (by rw [hsh 2 (by norm_num)]; exact hbe)
    (by rw [hsh 3 (by norm_num)]; exact hQ) hW hs hb₂
  have h6 : st₃.store.size = 6 := by
    rw [Store.size_eq_of_shape_eq sh₃, h₂, Array.size_push, h5]
  exact ⟨st₃, h₃, lz_LzOut_pop (by simp [h6]) (lz_LzOut_pop (by omega) out₃)⟩

end Program

/-- **The Lanczos program computes the Lanczos recurrence** in exact arithmetic, for every
square $\mathbf{A}$ and $\mathbf{b}$ (no symmetry, no breakdown hypothesis): the run succeeds,
`alpha[j]` $= \alpha_j$ and `beta[j]` $= \beta_{j+1}$ of `NLAlib.lanczosState` (0-based, as the
library indexes it), and `Q` holds `NLAlib.lanczosMatrix A b (q + 1)`. With
`Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix` this is the Krylov basis. The counts and
memory (`docs/design/Computation.md` §6) join when the statement becomes a registered
`MatrixFree` target. [Paige1976], [Saad2011, §6.6]. -/
theorem exec_lanczosBasisProg_exactInterp (p : P) (o : ι) {N : ℕ} (q : ℕ)
    (A : Matrix (Fin N) (Fin N) 𝕜) (b : Fin N → 𝕜) (ξ : Dist → ℕ → ℝ) :
    ∃ st', exec (exactInterp (fun _ => A) ξ)
        (lanczosBasisProg p o (.const N) (.const q) 0 1 2 3).run
        (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
          Array.replicate q none, Array.replicate (N * (q + 1)) none]) = some st' ∧
      (∀ j < q, st'.store.read p 1 j = some (lanczosAlpha A (lanczosState A b j) : 𝕜)) ∧
      (∀ j < q, st'.store.read p 2 j = some ((lanczosState A b (j + 1)).beta : 𝕜)) ∧
      Holds st'.store p 3 0 (lanczosMatrix A b (q + 1)) := by
  obtain ⟨st', h, ha, hb, hQ⟩ := lz_exec_lanczosBasisProg q A b ξ o p
    (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
      Array.replicate q none, Array.replicate (N * (q + 1)) none]) (by simp [inputState])
    (by simp [inputState, Store.getElem?_shape]) (by simp [inputState, Store.getElem?_shape])
    (by simp [inputState, Store.getElem?_shape])
    (fun i hi => by simp [inputState, Store.read, vecSeq, hi])
  refine ⟨st', h, ha, hb, fun i j => ?_⟩
  rw [show 0 + (i : ℕ) + N * j = N * j + i by ring, hQ j j.2 i i.2]
  simp [vecSeq, lanczosMatrix]


end NLAlib
