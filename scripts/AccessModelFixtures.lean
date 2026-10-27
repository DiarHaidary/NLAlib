import NLAlib

/-! # Access-model fixtures: the cheating programs cannot meet a model

The old check E3 examined realisations syntactically and had gaps (`docs/design/Computation.md`,
"Guarantees"): a tail whose conclusion is not `RunsWithin`, a tape law that depends on the
matrix, and a program that turns a value of a type parameter into literals. A published result
is now the proof of a registered target (`scripts/Targets.lean`, rule E3), an access model about
a first-order tree (`NLAlib.Computation.Prog`), which quantifies over the matrix, the tape and the
declared inputs after the tree. Each theorem below proves that the model form of a cheating
program, written as a tree, is false, so it cannot be built.

* `not_matrixFree_leakTree`: a matrix in the program, through a value of a type parameter read
  by a class (gap 3): the tree's literal is fixed before the matrix is quantified.
* `not_matrixFree_copyTree`: a matrix in the initial store (the old `runsWithin_cheat`): the
  store holds only declared inputs, which are quantified independently of the matrix.
* `not_matrixFree_drawTree`: a matrix on the tape (the old `runsWithin_cheatTape`): the tape is
  quantified independently of the matrix.
* `not_matrixFreeProb_drawTree`: a tape whose law depends on the matrix (gap 2): the law is
  `tapeLaw`, fixed by the definition (`matrixFreeProb_iff` shows it), and under it a draw is not
  an entry of the matrix with probability $1/2$ at least. A tail whose conclusion is not
  `RunsWithin` (gap 1) is not a registered target, and the target lint flags it.

Run with `lake env lean scripts/AccessModelFixtures.lean` after `lake build NLAlib`. -/

namespace AccessModelFixtures

open NLAlib.Computation MeasureTheory ProbabilityTheory

/-- A class that reads an entry out of a value of a type parameter. -/
class Entries (M : Type) where
  /-- The entry. -/
  entry : M → ℚ

instance : Entries (Matrix (Fin 1) (Fin 1) ℚ) := ⟨fun A => A 0 0⟩

/-- A tree that writes one literal into the one declared cell. -/
def litTree (q : ℚ) : Prog Unit Unit 0 1 := .instr (.lit () ⟨0, .const 0⟩ q)

/-- Gap 3: a tree whose literal is the entry of a value of a type parameter. -/
def leakTree {M : Type} [Entries M] (x : M) : Prog Unit Unit 0 1 := litTree (Entries.entry x)

/-- The old `runsWithin_cheat`: a tree that copies its declared input into its output. -/
def copyTree : Prog Unit Unit 0 2 := .instr (.copy () ⟨1, .const 0⟩ ⟨0, .const 0⟩)

/-- The old `runsWithin_cheatTape`: a tree that draws its output from the tape. -/
def drawTree (d : Dist) : Prog Unit Unit 0 1 := .instr (.draw () d ⟨0, .const 0⟩)

/-- The run of one literal into the one declared cell. -/
theorem read_of_exec_lit {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {ξ : Dist → ℕ → ℝ} {q : ℚ}
    {n : Fin 0 → ℕ} {st : St Unit ℝ (OpCount Unit Unit)}
    (h : (litTree q).exec (exactInterp (fun _ => A) ξ) N n
      (inputState () [Array.replicate 1 none]) = some st) :
    st.store.read () 0 0 = some (q : ℝ) := by
  simp [litTree, Prog.exec, FStmt.exec, Instr.subst, Cell.subst, IExp.subst, IExp.eval,
    Instr.run, exactInterp, exactSem, inputState, Store.write] at h
  rw [← h]
  simp [Store.read]

/-- The run of one copy from the declared input cell into the declared output cell. -/
theorem read_of_exec_copy {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {ξ : Dist → ℕ → ℝ} {x : ℝ}
    {n : Fin 0 → ℕ} {st : St Unit ℝ (OpCount Unit Unit)}
    (h : copyTree.exec (exactInterp (fun _ => A) ξ) N n
      (inputState () [#[some x], Array.replicate 1 none]) = some st) :
    st.store.read () 1 0 = some x := by
  simp [copyTree, Prog.exec, FStmt.exec, Instr.subst, Cell.subst, IExp.subst, IExp.eval,
    Instr.run, inputState, Store.write, Store.read] at h
  rw [← h]
  simp [Store.read]

/-- The run of one draw into the one declared cell. -/
theorem read_of_exec_draw {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {ξ : Dist → ℕ → ℝ} {d : Dist}
    {n : Fin 0 → ℕ} {st : St Unit ℝ (OpCount Unit Unit)}
    (h : (drawTree d).exec (exactInterp (fun _ => A) ξ) N n
      (inputState () [Array.replicate 1 none]) = some st) :
    st.store.read () 0 0 = some (ξ d 0) := by
  simp [drawTree, Prog.exec, FStmt.exec, Instr.subst, Cell.subst, IExp.subst, IExp.eval,
    Instr.run, exactInterp, inputState, Store.write] at h
  rw [← h]
  simp [Store.read]

/-- **A matrix in the program** (gap 3): whatever the rational matrix $\mathbf{A}_0$, the tree
that writes its entry as a literal does not compute the trace of every matrix, so the
matrix-free model is false. -/
theorem not_matrixFree_leakTree (A₀ : Matrix (Fin 1) (Fin 1) ℚ) :
    ¬ MatrixFree (𝕜 := ℝ) () (leakTree A₀) (fun _ _ => True) (fun _ _ => Unit)
      (fun _ _ _ => ![Array.replicate 1 none]) (fun _ _ => Finsupp.single (.lit ()) 1)
      (fun _ _ _ => 1) (fun _ _ _ A _ st => st.store.read () 0 0 = some A.trace) := by
  intro h
  obtain ⟨st, hrun, -, -, hpost⟩ :=
    h 1 (fun _ => 0) trivial () (Matrix.of fun _ _ => (A₀ 0 0 : ℝ) + 1) (fun _ _ => 0)
  have := read_of_exec_lit hrun
  rw [this, Matrix.trace_fin_one] at hpost
  simp [Entries.entry] at hpost

/-- **A matrix in the initial store**: the initial store holds only the declared inputs, which
the model quantifies independently of the matrix, so a tree that copies its input does not
compute the trace of every matrix. -/
theorem not_matrixFree_copyTree :
    ¬ MatrixFree (𝕜 := ℝ) () copyTree (fun _ _ => True) (fun _ _ => ℝ)
      (fun _ _ x => ![#[some x], Array.replicate 1 none])
      (fun _ _ => Finsupp.single (.copy ()) 1) (fun _ _ _ => 2)
      (fun _ _ _ A _ st => st.store.read () 1 0 = some A.trace) := by
  intro h
  obtain ⟨st, hrun, -, -, hpost⟩ :=
    h 1 (fun _ => 0) trivial (0 : ℝ) (Matrix.of fun _ _ => 1) (fun _ _ => 0)
  rw [read_of_exec_copy hrun, Matrix.trace_fin_one] at hpost
  simp at hpost

/-- **A matrix on the tape**: the model quantifies over every tape independently of the matrix,
so a tree that draws its output does not compute the trace of every matrix. -/
theorem not_matrixFree_drawTree :
    ¬ MatrixFree (𝕜 := ℝ) () (drawTree .gaussian) (fun _ _ => True) (fun _ _ => Unit)
      (fun _ _ _ => ![Array.replicate 1 none])
      (fun _ _ => Finsupp.single (.draw () .gaussian) 1) (fun _ _ _ => 1)
      (fun _ _ _ A _ st => st.store.read () 0 0 = some A.trace) := by
  intro h
  obtain ⟨st, hrun, -, -, hpost⟩ :=
    h 1 (fun _ => 0) trivial () (Matrix.of fun _ _ => 1) (fun _ _ => 0)
  rw [read_of_exec_draw hrun, Matrix.trace_fin_one] at hpost
  simp at hpost

/-- The law of the tape is part of `MatrixFreeProb`: no hypothesis of a target can replace
it. -/
theorem matrixFreeProb_iff {r b : ℕ} (p : Unit) (prog : Prog Unit Unit r b)
    (valid : ℕ → (Fin r → ℕ) → Prop) (X : ℕ → (Fin r → ℕ) → Type)
    (inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option ℝ))
    (cost : ℕ → (Fin r → ℕ) → OpCount Unit Unit) (mem : ℕ → (Fin r → ℕ) → Unit → ℕ)
    (good : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) ℝ →
      St Unit ℝ (OpCount Unit Unit) → Prop)
    (bound : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) ℝ → ℝ) :
    MatrixFreeProb p prog valid X inputs cost mem good bound ↔
      ∀ N n, valid N n → ∀ (x : X N n) (A : Matrix (Fin N) (Fin N) ℝ) (Ω : Type)
        (_ : MeasurableSpace Ω) (μ : Measure Ω) (ξ : Ω → Dist → ℕ → ℝ), HasLaw ξ tapeLaw μ →
        μ.real {ω | ¬ prog.RunsWithin (exactInterp (fun _ => A) (ξ ω)) N n
          (inputState p (List.ofFn (inputs N n x))) (cost N n) (mem N n) (good N n x A)} ≤
          bound N n x A :=
  Iff.rfl

/-- Under the law of the tape, the first Rademacher draw is $1$ with probability $1/2$. -/
theorem measureReal_rademacher_eq_one :
    tapeLaw.real {ω : Dist → ℕ → ℝ | ω .rademacher 0 = 1} = 1 / 2 := by
  have hm : Measurable fun ω : Dist → ℕ → ℝ => ω .rademacher 0 :=
    (measurable_pi_apply 0).comp (measurable_pi_apply Dist.rademacher)
  have hmap : tapeLaw.map (fun ω : Dist → ℕ → ℝ => ω .rademacher 0) = NLAlib.rademacherMeasure := by
    have h1 := (measurePreserving_eval_infinitePi (fun d : Dist => NLAlib.iidSequence d.law)
      Dist.rademacher).map_eq
    have h2 := (measurePreserving_eval_infinitePi (fun _ : ℕ => Dist.rademacher.law) 0).map_eq
    rw [show (fun ω : Dist → ℕ → ℝ => ω .rademacher 0) =
        ((Function.eval 0 ∘ Function.eval Dist.rademacher : (Dist → ℕ → ℝ) → ℝ)) from rfl,
      ← Measure.map_map (measurable_pi_apply 0) (measurable_pi_apply Dist.rademacher), tapeLaw, h1]
    exact h2
  have : {ω : Dist → ℕ → ℝ | ω .rademacher 0 = 1} =
      (fun ω : Dist → ℕ → ℝ => ω .rademacher 0) ⁻¹' {1} := rfl
  rw [this, measureReal_def, ← Measure.map_apply hm (measurableSet_singleton 1), hmap]
  simp [NLAlib.rademacherMeasure, Measure.dirac_apply', Set.indicator]
  norm_num

/-- **A tape whose law depends on the matrix** (gap 2): under the law of the tape, which the
definition fixes, a tree that draws its output computes the trace of the zero $1 \times 1$
matrix with probability at most $1/2$, so the instance with failure probability $0$ is false. With
a hypothesis making the tape equal to an entry of the matrix the old form held. -/
theorem not_matrixFreeProb_drawTree :
    ¬ MatrixFreeProb (𝕜 := ℝ) () (drawTree .rademacher) (fun _ _ => True)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none])
      (fun _ _ => Finsupp.single (.draw () .rademacher) 1) (fun _ _ _ => 1)
      (fun _ _ _ A st => st.store.read () 0 0 = some A.trace) (fun _ _ _ _ => 0) := by
  intro h
  have h0 := h 1 (fun _ => 0) trivial () 0 (Dist → ℕ → ℝ) _ tapeLaw id
    ⟨aemeasurable_id, Measure.map_id⟩
  have key : tapeLaw.real {ω : Dist → ℕ → ℝ | ω .rademacher 0 = 1} ≤ 0 := by
    refine le_trans (measureReal_mono ?_) h0
    rintro ω hω ⟨st, hrun, -, -, hpost⟩
    change ω .rademacher 0 = 1 at hω
    rw [read_of_exec_draw hrun, Matrix.trace_fin_one] at hpost
    simp [hω] at hpost
  rw [measureReal_rademacher_eq_one] at key
  norm_num at key

end AccessModelFixtures
