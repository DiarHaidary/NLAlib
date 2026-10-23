import NLAlib

/-! # Access-model fixtures: the cheating realisations cannot be instances

The old check E3 examined realisations syntactically and had gaps (`docs/design/Computation.md`,
"Guarantees"): a tail whose conclusion is not `RunsWithin`, a tape law that depends on the
matrix, and a program that turns a value of a type parameter into literals. Results are now
instances of the access models, which quantify over the matrix, the tape and the declared inputs
after the program. Each theorem below proves that the instance form of a cheating realisation is
false, so it cannot be built; the non-instance forms are flagged by the lint (E3,
`scripts/Programs.lean`).

* `not_matrixFree_leakProg`: a matrix in the program, through a value of a type parameter read by
  a class (gap 3).
* `not_matrixFree_copyProg`: a matrix in the initial store (the old `runsWithin_cheat`): the
  store holds only declared inputs, which are quantified independently of the matrix.
* `not_matrixFree_drawProg`: a matrix on the tape (the old `runsWithin_cheatTape`): the tape is
  quantified independently of the matrix.
* `not_matrixFreeProb_drawProg`: a tape whose law depends on the matrix (gap 2): the law is
  `tapeLaw`, fixed by the definition (`matrixFreeProb_iff` shows it), and under it a draw is not
  an entry of the matrix with probability $1/2$ at least. A tail whose conclusion is not
  `RunsWithin` (gap 1) is a `MatrixFreeProb` instance or is flagged.

Run with `lake env lean scripts/AccessModelFixtures.lean` after `lake build NLAlib`. -/

namespace AccessModelFixtures

open NLAlib.Computation MeasureTheory ProbabilityTheory

/-- A class that reads an entry out of a value of a type parameter. -/
class Entries (M : Type) where
  /-- The entry. -/
  entry : M → ℚ

instance : Entries (Matrix (Fin 1) (Fin 1) ℚ) := ⟨fun A => A 0 0⟩

/-- Gap 3: a program that takes a value of a type parameter and writes its entry as a literal. -/
def leakProg {VB VI M : Type} [Entries M] (x : M) (out : Cell VB VI) :
    Builder Unit Unit VB VI Unit :=
  Builder.ins (.lit () out (Entries.entry x))

/-- The run of one literal into the one declared cell. -/
theorem read_of_exec_lit {A : Matrix (Fin 1) (Fin 1) ℝ} {ξ : Dist → ℕ → ℝ} {q : ℚ}
    {st : St Unit ℝ (OpCount Unit Unit)}
    (h : exec (exactInterp (fun _ => A) ξ) (.seq (.instr (.lit () ⟨0, .const 0⟩ q)) .skip)
      (inputState () [Array.replicate 1 none]) = some st) :
    st.store.read () 0 0 = some (q : ℝ) := by
  simp [exec, Instr.run, exactInterp, exactSem, inputState, Store.write] at h
  rw [← h]
  simp [Store.read]

/-- The run of one copy from the declared input cell into the declared output cell. -/
theorem read_of_exec_copy {A : Matrix (Fin 1) (Fin 1) ℝ} {ξ : Dist → ℕ → ℝ} {x : ℝ}
    {st : St Unit ℝ (OpCount Unit Unit)}
    (h : exec (exactInterp (fun _ => A) ξ)
      (.seq (.instr (.copy () ⟨1, .const 0⟩ ⟨0, .const 0⟩)) .skip)
      (inputState () [#[some x], Array.replicate 1 none]) = some st) :
    st.store.read () 1 0 = some x := by
  simp [exec, Instr.run, inputState, Store.write, Store.read] at h
  rw [← h]
  simp [Store.read]

/-- The run of one draw into the one declared cell. -/
theorem read_of_exec_draw {A : Matrix (Fin 1) (Fin 1) ℝ} {ξ : Dist → ℕ → ℝ} {d : Dist}
    {st : St Unit ℝ (OpCount Unit Unit)}
    (h : exec (exactInterp (fun _ => A) ξ) (.seq (.instr (.draw () d ⟨0, .const 0⟩)) .skip)
      (inputState () [Array.replicate 1 none]) = some st) :
    st.store.read () 0 0 = some (ξ d 0) := by
  simp [exec, Instr.run, exactInterp, inputState, Store.write] at h
  rw [← h]
  simp [Store.read]

/-- **A matrix in the program** (gap 3): whatever the rational matrix $\mathbf{A}_0$, the program
family that writes its entry as a literal does not compute the trace of every matrix, so the
matrix-free instance is false. -/
theorem not_matrixFree_leakProg (A₀ : Matrix (Fin 1) (Fin 1) ℚ) :
    ¬ MatrixFree (𝕜 := ℝ) (ι := Unit) (r := 0) (b := 1) ()
      (fun _ _ _ _ h => (leakProg A₀ ⟨h 0, 0⟩).run) (fun _ _ => True) (fun _ _ => Unit)
      (fun _ _ _ => ![Array.replicate 1 none]) (fun _ _ => Finsupp.single (.lit ()) 1)
      (fun _ _ _ => 1) (fun _ _ _ A _ st => st.store.read () 0 0 = some A.trace) := by
  intro h
  obtain ⟨st, hrun, -, -, hpost⟩ :=
    h 1 (fun _ => 0) trivial () (Matrix.of fun _ _ => (A₀ 0 0 : ℝ) + 1) (fun _ _ => 0)
  have := read_of_exec_lit hrun
  rw [this, Matrix.trace_fin_one] at hpost
  simp [Entries.entry] at hpost

/-- The old `runsWithin_cheat`: a program that copies its declared input into its output. -/
def copyProg {VB VI : Type} (src dst : Cell VB VI) : Builder Unit Unit VB VI Unit :=
  Builder.ins (.copy () dst src)

/-- **A matrix in the initial store**: the initial store holds only the declared inputs, which
the model quantifies independently of the matrix, so a program that copies its input does not
compute the trace of every matrix. -/
theorem not_matrixFree_copyProg :
    ¬ MatrixFree (𝕜 := ℝ) (ι := Unit) (r := 0) (b := 2) ()
      (fun _ _ _ _ h => (copyProg ⟨h 0, 0⟩ ⟨h 1, 0⟩).run) (fun _ _ => True) (fun _ _ => ℝ)
      (fun _ _ x => ![#[some x], Array.replicate 1 none])
      (fun _ _ => Finsupp.single (.copy ()) 1) (fun _ _ _ => 2)
      (fun _ _ _ A _ st => st.store.read () 1 0 = some A.trace) := by
  intro h
  obtain ⟨st, hrun, -, -, hpost⟩ :=
    h 1 (fun _ => 0) trivial (0 : ℝ) (Matrix.of fun _ _ => 1) (fun _ _ => 0)
  rw [read_of_exec_copy hrun, Matrix.trace_fin_one] at hpost
  simp at hpost

/-- The old `runsWithin_cheatTape`: a program that draws its output from the tape. -/
def drawProg {VB VI : Type} (d : Dist) (dst : Cell VB VI) : Builder Unit Unit VB VI Unit :=
  Builder.ins (.draw () d dst)

/-- **A matrix on the tape**: the model quantifies over every tape independently of the matrix,
so a program that draws its output does not compute the trace of every matrix. -/
theorem not_matrixFree_drawProg :
    ¬ MatrixFree (𝕜 := ℝ) (ι := Unit) (r := 0) (b := 1) ()
      (fun _ _ _ _ h => (drawProg .gaussian ⟨h 0, 0⟩).run) (fun _ _ => True) (fun _ _ => Unit)
      (fun _ _ _ => ![Array.replicate 1 none])
      (fun _ _ => Finsupp.single (.draw () .gaussian) 1) (fun _ _ _ => 1)
      (fun _ _ _ A _ st => st.store.read () 0 0 = some A.trace) := by
  intro h
  obtain ⟨st, hrun, -, -, hpost⟩ :=
    h 1 (fun _ => 0) trivial () (Matrix.of fun _ _ => 1) (fun _ _ => 0)
  rw [read_of_exec_draw hrun, Matrix.trace_fin_one] at hpost
  simp at hpost

/-- The law of the tape is part of `MatrixFreeProb`: no hypothesis of an instance can replace
it. -/
theorem matrixFreeProb_iff {r b : ℕ} (p : Unit) (prog : ProgFamily Unit Unit r b)
    (valid : ℕ → (Fin r → ℕ) → Prop) (X : ℕ → (Fin r → ℕ) → Type)
    (inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option ℝ))
    (cost : ℕ → (Fin r → ℕ) → OpCount Unit Unit) (mem : ℕ → (Fin r → ℕ) → Unit → ℕ)
    (good : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) ℝ →
      St Unit ℝ (OpCount Unit Unit) → Prop)
    (bound : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) ℝ → ℝ) :
    MatrixFreeProb p prog valid X inputs cost mem good bound ↔
      ∀ N n, valid N n → ∀ (x : X N n) (A : Matrix (Fin N) (Fin N) ℝ) (Ω : Type)
        (_ : MeasurableSpace Ω) (μ : Measure Ω) (ξ : Ω → Dist → ℕ → ℝ), HasLaw ξ tapeLaw μ →
        μ.real {ω | ¬ RunsWithin (exactInterp (fun _ => A) (ξ ω)) (prog.inst N n)
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
definition fixes, a program that draws its output computes the trace of the zero $1 \times 1$
matrix with probability at most $1/2$, so the instance with failure probability $0$ is false. With
a hypothesis making the tape equal to an entry of the matrix the old form held. -/
theorem not_matrixFreeProb_drawProg :
    ¬ MatrixFreeProb (𝕜 := ℝ) (ι := Unit) (r := 0) (b := 1) ()
      (fun _ _ _ _ h => (drawProg .rademacher ⟨h 0, 0⟩).run) (fun _ _ => True)
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
