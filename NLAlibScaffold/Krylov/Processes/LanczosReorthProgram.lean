/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosReorthProgramRounding
public import NLAlib.Krylov.Processes.LanczosReorthRecurrence
public import NLAlib.Computation.StaticCost
public import NLAlib.Matrix.Computation.MatvecRoutine
public import NLAlibScaffold.Matrix.Computation.ClassicalGramSchmidt
public import NLAlibScaffold.Krylov.FinitePrecision.LanczosReorthSpectral
public import NLAlib.Krylov.Processes.LanczosProgramRounded
public import NLAlib.Krylov.Processes.LanczosOracleProgramRounded

/-!
# Lanczos with full reorthogonalization as a program: exact and rounded runs (scaffold)

Statements for the programs of `NLAlib/Krylov/Processes/LanczosReorthProgramTree.lean` (stage
LANCZOS-REORTH, design note `docs/design/Krylov-LanczosReorth.md` §2, ids G3–G8): the exact run
of the stored-matrix tree (the drafted target's output clause; the target itself is registered by
the maintainer), its static count, the rounded run of the generic loop for any certified product
and orthogonalization routine families, the CGS2 trees (stored and oracle), and their composition
with the backward model and interlacing. Patterned on
`NLAlib.LanczosImplementation.exec_rounded_compiled`
and `NLAlib.LanczosOracleImplementation.exec_rounded_compiled`; the run-time handles are
`work` $= 8$, `scalars` $= 9$, `coef` $= 10$, the matrix slot $7$.

## Main results

* `NLAlib.lanczosReorthProg.exec_storedInterp_compiled` (G3),
  `NLAlib.lanczosReorthProg.staticCost_count_le` (G4).
* `NLAlib.LanczosReorthImplementation.exec_rounded_loop` (G5).
* `NLAlib.LanczosReorthImplementation.exec_rounded_compiled` (G6),
  `NLAlib.LanczosReorthImplementation.exec_rounded_oracle_compiled` (G6o).
* `NLAlib.LanczosReorthImplementation.exec_rounded_compiled_backward` (G7),
  `NLAlib.LanczosReorthImplementation.exec_rounded_compiled_interlacing` (G8).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

/-- **The exact run of the stored-matrix tree** (G3): under `NLAlib.Computation.storedInterp` (exact
arithmetic, the matrix as ROM, column-major), from the declared inputs, the compiled tree
succeeds and its buffers hold $\mathbf{b}$, the basis `NLAlib.lanczosReorthMatrix`, the
coefficients $\alpha_j$, $\beta_j$, the input norm, the last previous vector and the norms
$\nu_{j+1}$ of `NLAlib.lanczosReorthState`, for every real matrix (no symmetry or breakdown
premise). The output clause of the drafted target `StoredEntriesLanczosReorth`
(design note §2.3); counts are G4. No printed source.
Proof: `NLAlib.lanczosReorthProg.toStmt_compiled`; then the proof of main's stored-entries
Lanczos target (in `NLAlib/Krylov/Processes/LanczosProgram.lean`) step for step, with the loop
invariant
extended by the basis columns $0..j$ and `nu`, and one more phase per step: the extra `nrm2` and
`NLAlib.Computation.exec_cgs2_exactSem` at $j + 1$ columns, matching `NLAlib.cgsProject` twice
(sums over `Finset.range (j + 1)` against `Matrix.mulVec` of the stored columns); zero branch and
zero continuation as in the plain proof (after breakdown every later vector, coefficient and
correction is $0$). L, about 700 lines; intermediate lemmas: the loop invariant, one step, the
initialization (reuse `NLAlib/Krylov/Processes/LanczosProgramInitialization.lean`). -/
theorem lanczosReorthProg.exec_storedInterp_compiled {P ι : Type} [DecidableEq P] (tag : P)
    (N q : ℕ) (b : Fin N → ℝ) (vals : ℕ → ℝ) (ξ : Dist → ℕ → ℝ) :
    ∃ out : St P ℝ (OpCount P ι),
      (lanczosReorthProg.compiled (ι := ι) tag).exec (storedInterp (N ^ 2) vals ξ tag) N ![q]
          (inputState tag (List.ofFn ![(Array.ofFn b).map some,
            Array.replicate (N * (q + 1)) none, Array.replicate q none,
            Array.replicate (q + 1) none, Array.replicate 1 none, Array.replicate N none,
            Array.replicate q none])) = some out ∧
      Holds out.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
      Holds out.store tag 1 0
        (lanczosReorthMatrix (fun i j : Fin N => vals (i + N * j)) b (q + 1)) ∧
      Holds out.store tag 2 0 (fun (j : Fin q) (_ : Fin 1) =>
        lanczosAlpha (fun i j : Fin N => vals (i + N * j))
          (lanczosReorthState (fun i j : Fin N => vals (i + N * j)) b j).toLanczosState) ∧
      Holds out.store tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) =>
        (lanczosReorthState (fun i j : Fin N => vals (i + N * j)) b j).beta) ∧
      out.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
      Holds out.store tag 5 0 (fun i (_ : Fin 1) =>
        (lanczosReorthState (fun i j : Fin N => vals (i + N * j)) b q).prev i) ∧
      Holds out.store tag 6 0 (fun (j : Fin q) (_ : Fin 1) =>
        (lanczosReorthState (fun i j : Fin N => vals (i + N * j)) b ((j : ℕ) + 1)).nu) := by
  sorry

private lemma sum_map_range_eq_finsetSum (f : ℕ → ℕ) (q : ℕ) :
    (List.map f (List.range q)).sum = ∑ x ∈ Finset.range q, f x := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private lemma two_mul_sum_range_id_add (q : ℕ) : 2 * ∑ x ∈ Finset.range q, x + q = q * q := by
  induction q with
  | zero => simp
  | succ q ih => rw [Finset.sum_range_succ]; nlinarith

/-- **The static count of the stored-matrix tree** (G4): every component of the static operation
count of `NLAlib.lanczosReorthProg.compiled` is at most `NLAlib.lanczosReorthCount`.
Proof: as main's static count of the plain tree
(`NLAlib/Krylov/Processes/LanczosProgramStaticCost.lean`): unfold the static cost of the compiled
tree
(`FStmt.staticCost`, `StaticCost.seq`, `StaticCost.branch`, `StaticCost.alloc`), evaluate the
nested loops (the inner loop bounds $j + 1$ give $\sum_{j<q}(j+1) = q(q+1)/2$), and compare
componentwise (`Finsupp.single_apply`, `omega`/`nlinarith` per kind). If a component of the
drafted formula is too small, enlarge it in the design note (it is a draft) and record the change.
M, about 80 lines. -/
theorem lanczosReorthProg.staticCost_count_le {P ι : Type} [DecidableEq P] (tag : P)
    (width : P → ℕ) (N q : ℕ) :
    ((lanczosReorthProg.compiled (ι := ι) tag).staticCost (fun k => Finsupp.single k 1)
      width N ![q]).count ≤ lanczosReorthCount tag N q := by
  classical
  intro k
  change (FStmt.staticCost (fun k => Finsupp.single k 1) width
    (lanczosReorthProg.compiled (ι := ι) tag) (Fin.cons N ![q])).count k ≤ _
  change (StaticCost.seq _ _).count k ≤ _
  simp only [FStmt.staticCost, StaticCost.seq, StaticCost.branch, StaticCost.alloc,
    StaticCost.step, StaticCost.zero, StaticCost.sequence_count_apply, Instr.kind, Instr.subst,
    IExp.evalIn, Finsupp.add_apply, Finsupp.sup_apply, List.map_const', List.sum_replicate,
    List.length_range, Finsupp.zero_apply]
  simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.cons_zero, add_zero, zero_add,
    smul_eq_mul, Matrix.Fin.cons_vecCons, Nat.succ_eq_add_one,
    Fin.snoc_apply_zero, Matrix.cons_val_zero, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty, List.map_const', List.length_range, List.sum_replicate,
    Fin.val_eq_zero, Fin.mk_one, Fin.cons_one, Matrix.cons_val_fin_one]
  cases k <;> simp only [lanczosReorthCount, Finsupp.add_apply, Finsupp.single_apply,
    OpKind.bin.injEq, OpKind.un.injEq, OpKind.lit.injEq, OpKind.cmp.injEq,
    OpKind.copy.injEq, OpKind.rom.injEq, reduceCtorEq, add_zero, zero_add, mul_zero,
    ite_false, sum_map_range_eq_finsetSum]
  -- the loop bodies depend on the step through the CGS2 width `j + 1`: Gauss's sum
  case bin p b =>
    have hS := two_mul_sum_range_id_add q
    cases b <;> by_cases hp : tag = p <;>
      simp [hp, Finset.sum_add_distrib, add_mul, ← Finset.sum_mul] <;> nlinarith
  case un p u =>
    have hS := two_mul_sum_range_id_add q
    cases u <;> by_cases hp : tag = p <;>
      simp [hp, Finset.sum_add_distrib, add_mul, ← Finset.sum_mul] <;> nlinarith
  case lit p =>
    have hS := two_mul_sum_range_id_add q
    by_cases hp : tag = p
    · simp [hp, Finset.sum_add_distrib]; nlinarith
    · simp [hp]
  all_goals (try split_ifs) <;> norm_num <;> ring_nf <;> omega

namespace LanczosReorthImplementation

variable {P ι K : Type} [DecidableEq P]

private theorem reorth_foldlM_transfer {α σ σ' : Type} (R : σ → σ' → Prop)
    {f : σ → α → Option σ} {g : σ' → α → Option σ'}
    (hfg : ∀ x a a' b, R a a' → f a x = some b → ∃ b', g a' x = some b' ∧ R b b') :
    ∀ (l : List α) {a : σ} {a' : σ'} {b : σ}, R a a' → l.foldlM f a = some b →
      ∃ b', l.foldlM g a' = some b' ∧ R b b'
  | [], _, a', _, hR, h => by cases h; exact ⟨a', rfl, hR⟩
  | x :: l, _, _, _, hR, h => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨c, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c', h1', hR'⟩ := hfg x _ _ _ hR h1
    rw [h1']
    exact reorth_foldlM_transfer R hfg l hR' h2

/-- Runs under two interpretations that differ only in their charges: the store, tape
positions and memory ledgers evolve identically (the counts are never read). -/
private theorem reorth_exec_transfer {C : Type} [AddMonoid C] (I J : Interp P ι K C)
    (hsem : I.sem = J.sem) (htape : I.tape = J.tape) (horacle : I.oracle = J.oracle)
    (hheight : I.height = J.height) (hrom : I.rom = J.rom) (hwidth : I.width = J.width) :
    ∀ (s : Stmt P ι ℕ ℕ) {a a' b : St P K C}, a.store = a'.store → a.pos = a'.pos →
      a.cur = a'.cur → a.peak = a'.peak → a.curW = a'.curW → a.peakW = a'.peakW →
      exec I s a = some b → ∃ b', exec J s a' = some b' ∧ b.store = b'.store ∧
        b.pos = b'.pos ∧ b.cur = b'.cur ∧ b.peak = b'.peak ∧ b.curW = b'.curW ∧
        b.peakW = b'.peakW
  | .skip, _, a', _, h1, h2, h3, h4, h5, h6, h => by
    rw [exec_skip] at h
    cases h
    exact ⟨a', exec_skip J a', h1, h2, h3, h4, h5, h6⟩
  | .seq s t, _, _, _, h1, h2, h3, h4, h5, h6, h => by
    rw [exec_seq] at h
    obtain ⟨c, hc1, hc2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c', hc1', k1, k2, k3, k4, k5, k6⟩ :=
      reorth_exec_transfer I J hsem htape horacle hheight hrom hwidth s h1 h2 h3 h4 h5 h6 hc1
    obtain ⟨b', hb', l1, l2, l3, l4, l5, l6⟩ :=
      reorth_exec_transfer I J hsem htape horacle hheight hrom hwidth t k1 k2 k3 k4 k5 k6 hc2
    refine ⟨b', ?_, l1, l2, l3, l4, l5, l6⟩
    rw [exec_seq, hc1', Option.bind_some]
    exact hb'
  | .instr i, a, a', _, h1, h2, h3, h4, h5, h6, h => by
    rw [exec_instr] at h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨{ a' with store := r.1, pos := r.2, cnt := a'.cnt + J.charge i.kind }, ?_, rfl, rfl,
      h3, h4, h5, h6⟩
    rw [exec_instr, ← hsem, ← htape, ← h1, ← h2, hr]
    rfl
  | .apply o p dst dOff src sOff cols, a, a', _, h1, h2, h3, h4, h5, h6, h => by
    rw [exec] at h ⊢
    rw [← hheight, ← horacle, ← h1]
    split_ifs at h ⊢ with hif
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨X, hX, Y, hY, s, hs, rfl⟩ := h
    refine ⟨{ a' with store := s, cnt := a'.cnt + (J.charge (.load p o) +
      cols.eval • J.charge (.matvec p o)) }, ?_, rfl, h2, h3, h4, h5, h6⟩
    rw [hX, Option.bind_some, hY, Option.bind_some, hs]
    rfl
  | .rom p dst i, a, a', _, h1, h2, h3, h4, h5, h6, h => by
    rw [exec] at h ⊢
    rw [← hrom, ← h1]
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, s, hs, rfl⟩ := h
    refine ⟨{ a' with store := s, cnt := a'.cnt + J.charge (.rom p) }, ?_, rfl, h2, h3, h4,
      h5, h6⟩
    rw [hv, Option.bind_some, hs]
    rfl
  | .alloc p len body, a, a', _, h1, h2, h3, h4, h5, h6, h => by
    rw [exec_alloc] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨c', hc', k1, k2, k3, k4, k5, k6⟩ :=
      reorth_exec_transfer I J hsem htape horacle hheight hrom hwidth (body a.store.size)
        (a := { a with
          store := a.store.push (p, Array.replicate len.eval none),
          cur := Function.update a.cur p (a.cur p + len.eval),
          peak := Function.update a.peak p (max (a.peak p) (a.cur p + len.eval)),
          curW := a.curW + len.eval * I.width p,
          peakW := max a.peakW (a.curW + len.eval * I.width p) })
        (a' := { a' with
          store := a'.store.push (p, Array.replicate len.eval none),
          cur := Function.update a'.cur p (a'.cur p + len.eval),
          peak := Function.update a'.peak p (max (a'.peak p) (a'.cur p + len.eval)),
          curW := a'.curW + len.eval * J.width p,
          peakW := max a'.peakW (a'.curW + len.eval * J.width p) })
        (by simp [h1]) h2 (by simp [h3]) (by simp [h3, h4]) (by simp [h5, hwidth])
        (by simp [h5, h6, hwidth]) hc
    refine ⟨{ c' with
      store := Array.pop c'.store
      cur := Function.update c'.cur p (c'.cur p - len.eval)
      curW := c'.curW - len.eval * J.width p }, ?_, by simp [k1], k2, by simp [k3],
        k4, by simp [k5, hwidth], k6⟩
    rw [exec_alloc, show a'.store.size = a.store.size by rw [h1], hc', Option.map_some]
  | .loop n body, a, a', _, h1, h2, h3, h4, h5, h6, h => by
    rw [exec_loop] at h ⊢
    obtain ⟨b', hb', l1, l2, l3, l4, l5, l6⟩ := reorth_foldlM_transfer
      (fun (x : St P K C) (y : St P K C) => x.store = y.store ∧ x.pos = y.pos ∧
        x.cur = y.cur ∧ x.peak = y.peak ∧ x.curW = y.curW ∧ x.peakW = y.peakW)
      (fun i x y z hR hz => reorth_exec_transfer I J hsem htape horacle hheight hrom hwidth
        (body i) hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1 hR.2.2.2.2.1 hR.2.2.2.2.2 hz)
      (List.range n.eval) ⟨h1, h2, h3, h4, h5, h6⟩ h
    exact ⟨b', hb', l1, l2, l3, l4, l5, l6⟩
  | .whileFuel fuel p c x y body, a, a', _, h1, h2, h3, h4, h5, h6, h => by
    rw [exec] at h ⊢
    obtain ⟨r, hr, hfin⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r', hr', l1, l2, l3, l4, l5, l6, l7⟩ := reorth_foldlM_transfer
      (f := fun (s : St P K C × Bool) (_ : ℕ) => if s.2 = true then
          (cmpStep I p c x y s.1).bind fun r =>
            if r.1 = true then Option.map (fun st' => (st', true)) (exec I body r.2)
            else some (r.2, false)
        else some s)
      (g := fun (s : St P K C × Bool) (_ : ℕ) => if s.2 = true then
          (cmpStep J p c x y s.1).bind fun r =>
            if r.1 = true then Option.map (fun st' => (st', true)) (exec J body r.2)
            else some (r.2, false)
        else some s)
      (fun (x : St P K C × Bool) (y : St P K C × Bool) => x.1.store = y.1.store ∧
        x.1.pos = y.1.pos ∧ x.1.cur = y.1.cur ∧ x.1.peak = y.1.peak ∧ x.1.curW = y.1.curW ∧
        x.1.peakW = y.1.peakW ∧ x.2 = y.2)
      (fun _ x y z hR hz => by
        obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hR
        rcases x with ⟨xs, xb⟩
        rcases y with ⟨ys, yb⟩
        dsimp only at k1 k2 k3 k4 k5 k6 k7 hz ⊢
        subst k7
        cases xb with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hz ⊢
          subst hz
          exact ⟨_, rfl, k1, k2, k3, k4, k5, k6, rfl⟩
        | true =>
          simp only [↓reduceIte] at hz ⊢
          obtain ⟨q, hq, hz2⟩ := Option.bind_eq_some_iff.mp hz
          simp only [cmpStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
          obtain ⟨va, hva, vb, hvb, rr, hrr, rfl⟩ := hq
          have hq' : cmpStep J p c x y ys =
              some (rr, { ys with cnt := ys.cnt + J.charge (.cmp p) }) := by
            simp only [cmpStep, ← k1, hva, hvb, Option.bind_some, ← hsem, hrr, Option.map_some]
          rw [hq', Option.bind_some]
          dsimp only at hz2 ⊢
          cases rr with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hz2 ⊢
            subst hz2
            exact ⟨_, rfl, k1, k2, k3, k4, k5, k6, rfl⟩
          | true =>
            simp only [↓reduceIte, Option.map_eq_some_iff] at hz2 ⊢
            obtain ⟨st', hst', rfl⟩ := hz2
            obtain ⟨st'', hst'', m1, m2, m3, m4, m5, m6⟩ :=
              reorth_exec_transfer I J hsem htape horacle hheight hrom hwidth body
                (a := { xs with cnt := xs.cnt + I.charge (.cmp p) })
                (a' := { ys with cnt := ys.cnt + J.charge (.cmp p) }) k1 k2 k3 k4 k5 k6 hst'
            exact ⟨(st'', true), ⟨st'', hst'', rfl⟩, m1, m2, m3, m4, m5, m6, rfl⟩)
      (List.range fuel.eval) (a := (a, true)) (a' := (a', true)) ⟨h1, h2, h3, h4, h5, h6, rfl⟩ hr
    rw [hr', Option.bind_some]
    rcases r with ⟨rs, rb⟩
    rcases r' with ⟨rs', rb'⟩
    dsimp only at l7 hfin ⊢
    subst l7
    cases rb with
    | true => simp at hfin
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hfin ⊢
      subst hfin
      exact ⟨rs', rfl, l1, l2, l3, l4, l5, l6⟩
  | .ite p c x y t e, a, a', _, h1, h2, h3, h4, h5, h6, h => by
    rw [exec_ite] at h ⊢
    obtain ⟨q, hq, hz2⟩ := Option.bind_eq_some_iff.mp h
    simp only [cmpStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨va, hva, vb, hvb, rr, hrr, rfl⟩ := hq
    have hq' : cmpStep J p c x y a' =
        some (rr, { a' with cnt := a'.cnt + J.charge (.cmp p) }) := by
      simp only [cmpStep, ← h1, hva, hvb, Option.bind_some, ← hsem, hrr, Option.map_some]
    rw [hq', Option.bind_some]
    dsimp only at hz2 ⊢
    cases rr with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hz2 ⊢
      exact reorth_exec_transfer I J hsem htape horacle hheight hrom hwidth e
        (a := { a with cnt := a.cnt + I.charge (.cmp p) })
        (a' := { a' with cnt := a'.cnt + J.charge (.cmp p) }) h1 h2 h3 h4 h5 h6 hz2
    | true =>
      simp only [↓reduceIte] at hz2 ⊢
      exact reorth_exec_transfer I J hsem htape horacle hheight hrom hwidth t
        (a := { a with cnt := a.cnt + I.charge (.cmp p) })
        (a' := { a' with cnt := a'.cnt + J.charge (.cmp p) }) h1 h2 h3 h4 h5 h6 hz2
  | .named _ _ body, _, _, _, h1, h2, h3, h4, h5, h6, h => by
    rw [exec_named] at h ⊢
    exact reorth_exec_transfer I J hsem htape horacle hheight hrom hwidth body h1 h2 h3 h4 h5 h6 h

private theorem reorth_roundingFactor_succ_le (N : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (hsmall : lanczosImplementationRoundoffBound N u ≤ 1 / 100) :
    roundingFactor (N + 1) u ≤ lanczosImplementationRoundoffBound N u := by
  have hγ := roundingFactor_le_two_mul_of_lanczosImplementationRoundoffBound_le
    (N := N) (m := N + 1) (by omega) hu hsmall
  rw [lanczosImplementationRoundoffBound_def] at hsmall ⊢
  push_cast at hγ
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [mul_nonneg (mul_nonneg hN hN) hu, mul_nonneg hN hu]

/-- The work phase of one reorthogonalized step: product, both Paige updates, the stored
coefficient and the stored norm before orthogonalization. -/
private theorem reorth_exec_work (I : Interp P ι K (OpCount P ι)) {u : P → ℝ} {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q t slot : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (pre : Store P K → Prop) (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A) pre 1 8
      (IExp.const N * IExp.var t) 0 (mv 8 (IExp.var t)))
    (st : St P K (OpCount P ι))
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot), (tag, N), (tag, 2), (tag, q + 1)])
    (hpre : pre st.store) (ht : t < q) (vc vp : Fin N → ℝ) (bt : ℝ)
    (hvc : ∀ i : Fin N, ∃ w, st.store.read tag 1 (N * t + i) = some w ∧ dec tag w = vc i)
    (hvp : ∀ i : Fin N, ∃ w, st.store.read tag 5 i = some w ∧ dec tag w = vp i)
    (hbt : ∃ w, st.store.read tag 3 t = some w ∧ dec tag w = bt)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (uv wv zv : Fin N → ℝ) (an nn : ℝ),
      exec I (do
        mv 8 (IExp.var t)
        ins (.un tag .neg ⟨9, 1⟩ ⟨3, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 5 0 8 0 (IExp.const N)
        dot tag ⟨2, IExp.var t⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
        ins (.un tag .neg ⟨9, 1⟩ ⟨2, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
        nrm2 tag ⟨6, IExp.var t⟩ 8 0 (IExp.const N) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ p k i, k ≠ 8 → (k = 9 → i ≠ 1) → (k = 2 → i ≠ t) → (k = 6 → i ≠ t) →
        out.store.read p k i = st.store.read p k i) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 8 i = some w ∧ dec tag w = zv i) ∧
      (∃ w, out.store.read tag 2 t = some w ∧ dec tag w = an) ∧
      (∃ w, out.store.read tag 6 t = some w ∧ dec tag w = nn) ∧
      ‖WithLp.toLp 2 (A *ᵥ vc - uv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) * specNorm A * ‖WithLp.toLp 2 vc‖ ∧
      ‖WithLp.toLp 2 (uv - bt • vp - wv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 uv‖ + |bt| * ‖WithLp.toLp 2 vp‖) ∧
      |vc ⬝ᵥ wv - an| ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 vc‖ * ‖WithLp.toLp 2 wv‖ ∧
      ‖WithLp.toLp 2 (wv - an • vc - zv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 wv‖ + |an| * ‖WithLp.toLp 2 vc‖) ∧
      0 ≤ nn ∧ |nn - ‖WithLp.toLp 2 zv‖| ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 zv‖ := by
  have hu := h.nonneg (p := tag) trivial
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N hu hsmall
  have hn : (N : ℝ) * u tag < 1 := by
    have hsucc := hwin.1
    push_cast at hsucc
    nlinarith
  have hγ := reorth_roundingFactor_succ_le N hu hsmall
  -- product
  obtain ⟨st₁, W₁, hr₁, hw₁, he₁⟩ := hmv.run st vc hpre
    (by simpa only [IExp.eval_mul, IExp.eval_const, IExp.eval_var] using hvc)
    (fun i hi => ⟨N, by simp [hshape], by simpa using hi⟩)
  have sh₁ := Store.shape_of_writeBlock_eq_some hw₁
  have f₁ : ∀ p k i, k ≠ 8 → st₁.store.read p k i = st.store.read p k i :=
    fun p k i hk => Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hk)
  have r₁ (i : Fin N) : st₁.store.read tag 8 i = some (W₁ i) := by
    simpa using Store.read_of_writeBlock_eq_some_of_lt hw₁ (j := (i : ℕ)) (by simp)
  let uv : Fin N → ℝ := fun i => dec tag (W₁ i)
  -- previous update
  let xp : ℕ → ℝ := fun i => if hi : i < N then vp ⟨i, hi⟩ else 0
  let yu : ℕ → ℝ := fun i => if hi : i < N then uv ⟨i, hi⟩ else 0
  obtain ⟨st₂, W₂, hr₂, sh₂, rd₂, f₂, he₂⟩ := h.exec_neg_axpy_norm_sub_le I tag st₁
    ⟨3, IExp.var t⟩ ⟨9, 1⟩ 5 0 8 0 (IExp.const N) bt xp yu hwin.2.1
    (by change ∃ w, st₁.store.read tag 3 t = some w ∧ _; rw [f₁ tag 3 t (by omega)]; exact hbt)
    (by intro i hi; change i < N at hi; rw [IExp.eval_zero, zero_add, f₁ tag 5 i (by omega)]
        simpa [xp, hi] using hvp ⟨i, hi⟩)
    (by intro i hi; change i < N at hi; refine ⟨W₁ ⟨i, hi⟩, ?_, ?_⟩
        · simpa using r₁ ⟨i, hi⟩
        · simp [yu, hi, uv])
    ⟨2, by rw [sh₁, hshape]; rfl, by simp⟩ (by simp) (by simp) (by omega)
  let wv : Fin N → ℝ := fun i => dec tag (W₂ i)
  have r₂ (i : Fin N) : st₂.store.read tag 8 i = some (W₂ i) := by simpa using rd₂ i
  -- dot
  let xc : ℕ → ℝ := fun i => if hi : i < N then vc ⟨i, hi⟩ else 0
  let yw : ℕ → ℝ := fun i => if hi : i < N then wv ⟨i, hi⟩ else 0
  have hxc (i : ℕ) (hi : i < N) (s : St P K (OpCount P ι))
      (hs : s.store.read tag 1 (N * t + i) = st.store.read tag 1 (N * t + i)) :
      ∃ w, s.store.read tag 1 ((IExp.const N * IExp.var t).eval + i) = some w ∧
        dec tag w = xc i := by
    simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_var]
    rw [hs]
    simpa [xc, hi] using hvc ⟨i, hi⟩
  obtain ⟨w0, -, -⟩ := hbt
  have hdst₃ : ∃ w store, st₂.store.write tag 2 t w = some store :=
    ⟨w0, Store.exists_write_eq_some_of_getElem?_shape w0
      (by rw [sh₂, sh₁, hshape]; rfl) ht⟩
  obtain ⟨st₃, an, hr₃, hw₃, he₃⟩ := h.exec_dot_abs_dotProduct_sub_le I tag st₂ hz
    ⟨2, IExp.var t⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N) xc yw hn
    (fun i hi => hxc i hi st₂ (by
      rw [f₂ tag 1 _ (Or.inl (by omega)) (by simp), f₁ tag 1 _ (by omega)]))
    (by intro i hi; change i < N at hi; refine ⟨W₂ i, ?_, ?_⟩
        · simpa using r₂ ⟨i, hi⟩
        · simp [yw, hi, wv])
    (by simp) (by simp) hdst₃
  have sh₃ := Store.shape_of_write_eq_some hw₃
  have f₃ : ∀ p k i, (k ≠ 2 ∨ i ≠ t) → st₃.store.read p k i = st₂.store.read p k i :=
    fun p k i hk => Store.read_of_write_eq_some_of_ne hw₃ hk
  have ra₃ : st₃.store.read tag 2 t = some an := Store.read_of_write_eq_some hw₃
  -- projection update
  obtain ⟨st₄, W₄, hr₄, sh₄, rd₄, f₄, he₄⟩ := h.exec_neg_axpy_norm_sub_le I tag st₃
    ⟨2, IExp.var t⟩ ⟨9, 1⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N) (dec tag an)
    xc yw hwin.2.1 ⟨an, ra₃, rfl⟩
    (fun i hi => hxc i hi st₃ (by
      rw [f₃ tag 1 _ (Or.inl (by omega)), f₂ tag 1 _ (Or.inl (by omega)) (by simp),
        f₁ tag 1 _ (by omega)]))
    (by intro i hi; change i < N at hi; refine ⟨W₂ i, ?_, ?_⟩
        · rw [f₃ tag 8 _ (Or.inl (by omega))]; simpa using r₂ ⟨i, hi⟩
        · simp [yw, hi, wv])
    ⟨2, by rw [sh₃, sh₂, sh₁, hshape]; rfl, by simp⟩ (by simp) (by simp) (by omega)
  let zv : Fin N → ℝ := fun i => dec tag (W₄ i)
  have r₄ (i : Fin N) : st₄.store.read tag 8 i = some (W₄ i) := by simpa using rd₄ i
  -- the stored norm before orthogonalization
  let xz : ℕ → ℝ := fun i => if hi : i < N then zv ⟨i, hi⟩ else 0
  have hdst₅ : ∃ w store, st₄.store.write tag 6 t w = some store :=
    ⟨w0, Store.exists_write_eq_some_of_getElem?_shape w0
      (by rw [sh₄, sh₃, sh₂, sh₁, hshape]; rfl) ht⟩
  obtain ⟨out, wn, hr₅, hw₅, hpos, herr, -⟩ := h.exec_nrm2_abs_norm_sub_le_zero_iff I tag hz st₄
    ⟨6, IExp.var t⟩ 8 0 (IExp.const N) xz hwin.1 hwin.2.2.1
    (by intro i hi; change i < N at hi; refine ⟨W₄ i, ?_, ?_⟩
        · simpa using r₄ ⟨i, hi⟩
        · simp [xz, hi, zv])
    (by simp) hdst₅
  have sh₅ := Store.shape_of_write_eq_some hw₅
  have f₅ : ∀ p k i, (k ≠ 6 ∨ i ≠ t) → out.store.read p k i = st₄.store.read p k i :=
    fun p k i hk => Store.read_of_write_eq_some_of_ne hw₅ hk
  refine ⟨out, uv, wv, zv, dec tag an, dec tag wn, ?_, ?_, ?_, ?_, ?_, ?_, he₁, ?_, ?_, ?_,
    hpos, ?_⟩
  · have cu : ExecutionComposable I (do
        ins (.un tag .neg ⟨9, 1⟩ ⟨3, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 5 0 8 0 (IExp.const N) : Builder P ι ℕ ℕ Unit) :=
      (executionComposable_single I (fun _ => rfl)).bind
        (executionComposable_single I (fun _ => rfl))
    have cz : ExecutionComposable I (do
        ins (.un tag .neg ⟨9, 1⟩ ⟨2, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N) :
          Builder P ι ℕ ℕ Unit) :=
      (executionComposable_single I (fun _ => rfl)).bind
        (executionComposable_single I (fun _ => rfl))
    change exec I (do
      mv 8 (IExp.var t)
      (do
        ins (.un tag .neg ⟨9, 1⟩ ⟨3, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 5 0 8 0 (IExp.const N))
      dot tag ⟨2, IExp.var t⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
      (do
        ins (.un tag .neg ⟨9, 1⟩ ⟨2, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N))
      nrm2 tag ⟨6, IExp.var t⟩ 8 0 (IExp.const N) : Builder P ι ℕ ℕ Unit).run st = some out
    rw [hmv.composable, hr₁, Option.bind_some, cu, hr₂, Option.bind_some,
      exec_run_bind I (b := dot tag ⟨2, IExp.var t⟩ 1 (IExp.const N * IExp.var t)
        8 0 (IExp.const N)) (fun _ => rfl), hr₃, Option.bind_some, cz, hr₄, Option.bind_some]
    exact hr₅
  · rw [sh₅, sh₄, sh₃, sh₂, sh₁]
  · intro p k i h8 h9 h2 h6
    rw [f₅ p k i (by by_cases hk : k = 6; exacts [Or.inr (h6 hk), Or.inl hk]),
      f₄ p k i (Or.inl h8) (fun hk => h9 hk),
      f₃ p k i (by by_cases hk : k = 2; exacts [Or.inr (h2 hk), Or.inl hk]),
      f₂ p k i (Or.inl h8) (fun hk => h9 hk), f₁ p k i h8]
  · intro i
    refine ⟨W₄ i, ?_, rfl⟩
    rw [f₅ tag 8 i (Or.inl (by omega))]
    exact r₄ i
  · refine ⟨an, ?_, rfl⟩
    rw [f₅ tag 2 t (Or.inl (by omega)), f₄ tag 2 t (Or.inl (by omega)) (by simp)]
    exact ra₃
  · exact ⟨wn, Store.read_of_write_eq_some hw₅, rfl⟩
  · have he := he₂.trans (mul_le_mul_of_nonneg_right hwin.2.2.2.1 (by positivity))
    have hxs : (fun i : Fin N => xp i) = vp := by funext i; simp [xp]
    have hys : (fun i : Fin N => yu i) = uv := by funext i; simp [yu]
    have heq : (fun i : Fin N => yu i - bt * xp i - dec tag (W₂ i)) = uv - bt • vp - wv := by
      ext i
      simp [xp, yu, wv]
    change ‖WithLp.toLp 2 (fun i : Fin N => yu i - bt * xp i - dec tag (W₂ i))‖ ≤
      _ * (‖WithLp.toLp 2 (fun i : Fin N => yu i)‖ +
        |bt| * ‖WithLp.toLp 2 (fun i : Fin N => xp i)‖) at he
    rw [heq, hxs, hys] at he
    exact he
  · have hxs : (fun i : Fin N => xc i) = vc := by funext i; simp [xc]
    have hys : (fun i : Fin N => yw i) = wv := by funext i; simp [yw]
    change |(fun i : Fin N => xc i) ⬝ᵥ (fun i : Fin N => yw i) - dec tag an| ≤
      _ * ‖WithLp.toLp 2 (fun i : Fin N => xc i)‖ *
        ‖WithLp.toLp 2 (fun i : Fin N => yw i)‖ at he₃
    rw [hxs, hys] at he₃
    exact he₃.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (roundingFactor_le_lanczosImplementationRoundoffBound N hu hsmall) (norm_nonneg _))
      (norm_nonneg _))
  · have he := he₄.trans (mul_le_mul_of_nonneg_right hwin.2.2.2.1 (by positivity))
    have hxs : (fun i : Fin N => xc i) = vc := by funext i; simp [xc]
    have hys : (fun i : Fin N => yw i) = wv := by funext i; simp [yw]
    have heq : (fun i : Fin N => yw i - dec tag an * xc i - dec tag (W₄ i)) =
        wv - dec tag an • vc - zv := by
      ext i
      simp [xc, yw, zv]
    change ‖WithLp.toLp 2 (fun i : Fin N => yw i - dec tag an * xc i - dec tag (W₄ i))‖ ≤
      _ * (‖WithLp.toLp 2 (fun i : Fin N => yw i)‖ +
        |dec tag an| * ‖WithLp.toLp 2 (fun i : Fin N => xc i)‖) at he
    rw [heq, hxs, hys] at he
    exact he
  · have hxs : (fun i : Fin N => xz i) = zv := by funext i; simp [xz]
    change |‖WithLp.toLp 2 (fun i : Fin N => xz i)‖ - dec tag wn| ≤
      _ * ‖WithLp.toLp 2 (fun i : Fin N => xz i)‖ at herr
    rw [hxs] at herr
    rw [abs_sub_comm]
    exact herr.trans (mul_le_mul_of_nonneg_right hγ (norm_nonneg _))

/-- The orthogonalization call and the norm after it. -/
private theorem reorth_exec_orth (I : Interp P ι K (OpCount P ι)) {u : P → ℝ} {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q t slot : ℕ} (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    {η₀ ε₁ ε₂ ε₃ : ℝ}
    (horth : IsOrthRoutine I dec tag N (t + 1) η₀ ε₁ ε₂ ε₃ (fun _ => True) 1 8 10 0 0
      (orth 8 10 (IExp.var t)))
    (st : St P K (OpCount P ι))
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot), (tag, N), (tag, 2), (tag, q + 1)])
    (ht : t < q) (w0 : K) (V : Matrix (Fin N) (Fin (t + 1)) ℝ)
    (hV : HoldsDecoded st.store dec tag 1 0 V) (zv : Fin N → ℝ)
    (hzv : ∀ i : Fin N, ∃ w, st.store.read tag 8 i = some w ∧ dec tag w = zv i)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (mid out : St P K (OpCount P ι)) (z' : Fin N → ℝ) (hv : Fin (t + 1) → ℝ) (bn : ℝ),
      exec I (orth 8 10 (IExp.var t)).run st = some mid ∧
      exec I (nrm2 tag ⟨3, IExp.var t + 1⟩ 8 0 (IExp.const N)).run mid = some out ∧
      mid.store.shape = st.store.shape ∧ out.store.shape = st.store.shape ∧
      (∀ p k i, k ≠ 8 → k ≠ 10 → mid.store.read p k i = st.store.read p k i) ∧
      (∀ p k i, (k ≠ 3 ∨ i ≠ t + 1) → out.store.read p k i = mid.store.read p k i) ∧
      (∀ i : Fin N, ∃ w, mid.store.read tag 8 i = some w ∧ dec tag w = z' i) ∧
      (∃ w, out.store.read tag 3 (t + 1) = some w ∧ dec tag w = bn) ∧
      IsOrthErr η₀ ε₁ ε₂ ε₃ V zv hv z' ∧
      0 ≤ bn ∧ (bn = 0 ↔ z' = 0) ∧
      |bn - ‖WithLp.toLp 2 z'‖| ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 z'‖ := by
  have hu := h.nonneg (p := tag) trivial
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N hu hsmall
  have hγ := reorth_roundingFactor_succ_le N hu hsmall
  obtain ⟨mid, W, Hw, mid₀, hr, hw₁, hw₂, herr⟩ := horth.run st V zv trivial hV
    (by simpa using hzv)
    (fun i hi => ⟨N, by simp [hshape], by simpa using hi⟩)
    (fun i hi => ⟨q + 1, by simp [hshape], by simp; omega⟩)
    (by omega) (by omega) (by omega)
  have shm : mid.store.shape = st.store.shape :=
    (Store.shape_of_writeBlock_eq_some hw₂).trans (Store.shape_of_writeBlock_eq_some hw₁)
  have fm : ∀ p k i, k ≠ 8 → k ≠ 10 → mid.store.read p k i = st.store.read p k i :=
    fun p k i h8 h10 => (Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl h10)).trans
      (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl h8))
  have rm (i : Fin N) : mid.store.read tag 8 i = some (W i) := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl (by omega))]
    simpa using Store.read_of_writeBlock_eq_some_of_lt hw₁ (j := (i : ℕ)) (by simp)
  let z' : Fin N → ℝ := fun i => dec tag (W i)
  let xz : ℕ → ℝ := fun i => if hi : i < N then z' ⟨i, hi⟩ else 0
  have hdst : ∃ w store, mid.store.write tag 3 (t + 1) w = some store :=
    ⟨w0, Store.exists_write_eq_some_of_getElem?_shape w0
      (by rw [shm, hshape]; rfl) (by omega)⟩
  obtain ⟨out, wn, hr₂, hwn, hpos, hnerr, hzero⟩ := h.exec_nrm2_abs_norm_sub_le_zero_iff I tag hz
    mid ⟨3, IExp.var t + 1⟩ 8 0 (IExp.const N) xz hwin.1 hwin.2.2.1
    (by intro i hi; change i < N at hi; refine ⟨W ⟨i, hi⟩, ?_, ?_⟩
        · simpa using rm ⟨i, hi⟩
        · simp [xz, hi, z'])
    (by simp) hdst
  have hxs : (fun i : Fin N => xz i) = z' := by funext i; simp [xz]
  refine ⟨mid, out, z', fun i => dec tag (Hw i), dec tag wn, hr, hr₂, shm,
    (Store.shape_of_write_eq_some hwn).trans shm, fm,
    fun p k i hk => Store.read_of_write_eq_some_of_ne hwn hk,
    fun i => ⟨W i, rm i, rfl⟩, ⟨wn, Store.read_of_write_eq_some hwn, rfl⟩, herr, hpos, ?_, ?_⟩
  · change dec tag wn = 0 ↔ (fun i : Fin N => xz i) = 0 at hzero
    rwa [hxs] at hzero
  · change |‖WithLp.toLp 2 (fun i : Fin N => xz i)‖ - dec tag wn| ≤
      _ * ‖WithLp.toLp 2 (fun i : Fin N => xz i)‖ at hnerr
    rw [hxs] at hnerr
    rw [abs_sub_comm]
    exact hnerr.trans (mul_le_mul_of_nonneg_right hγ (norm_nonneg _))

/-- Copy the current column into the previous vector, then the guarded normalization of the
reduced vector into the next column. -/
private theorem reorth_exec_commit (I : Interp P ι K (OpCount P ι)) {u : P → ℝ}
    {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P) {N q t slot : ℕ}
    (predot normed : St P K (OpCount P ι))
    (hshape : normed.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot), (tag, N), (tag, 2), (tag, q + 1)])
    (hpshape : predot.store.shape = normed.store.shape)
    (ht : t < q) (vc : Fin N → ℝ)
    (hvc : ∀ i : Fin N, ∃ w, normed.store.read tag 1 (N * t + i) = some w ∧ dec tag w = vc i)
    (zv : Fin N → ℝ)
    (hzp : ∀ i : Fin N, ∃ w, predot.store.read tag 8 i = some w ∧ dec tag w = zv i)
    (hzn : ∀ i : Fin N, ∃ w, normed.store.read tag 8 i = some w ∧ dec tag w = zv i)
    (hzero : ∃ w, normed.store.read tag 9 0 = some w ∧ dec tag w = 0)
    (hnorm : exec I (nrm2 tag ⟨3, IExp.var t + 1⟩ 8 0 (IExp.const N)).run predot =
      some normed)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (vn : Fin N → ℝ) (bn : ℝ),
      exec I (do
        copyv tag 1 (IExp.const N * IExp.var t) 5 0 (IExp.const N)
        ifThenElse tag .eq ⟨3, IExp.var t + 1⟩ ⟨9, 0⟩
          (forRange (IExp.const N) fun i =>
            ins (.lit tag ⟨1, IExp.const N * (IExp.var t + 1) + IExp.var i⟩ 0)) (do
            copyv tag 8 0 1 (IExp.const N * (IExp.var t + 1)) (IExp.const N)
            rscl tag ⟨3, IExp.var t + 1⟩ 1
              (IExp.const N * (IExp.var t + 1)) (IExp.const N)) :
            Builder P ι ℕ ℕ Unit).run normed = some out ∧
      out.store.shape = normed.store.shape ∧
      (∀ p k i, k ≠ 5 → (k = 1 → i < N * (t + 1) ∨ N * (t + 2) ≤ i) →
        out.store.read p k i = normed.store.read p k i) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 5 i = some w ∧ dec tag w = vc i) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 1 (N * (t + 1) + i) = some w ∧ dec tag w = vn i) ∧
      (∃ w, normed.store.read tag 3 (t + 1) = some w ∧ dec tag w = bn) ∧
      (bn = 0 → vn = 0) ∧
      (bn ≠ 0 → |‖WithLp.toLp 2 vn‖ ^ 2 - 1| ≤ lanczosImplementationRoundoffBound N (u tag)) ∧
      ‖WithLp.toLp 2 (zv - bn • vn)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 zv‖ := by
  classical
  let xs : ℕ → ℝ := fun i => if hi : i < N then zv ⟨i, hi⟩ else 0
  have hxs : (fun i : Fin N => xs i) = zv := by funext i; simp [xs]
  have hu := h.nonneg (p := tag) trivial
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N hu hsmall
  -- previous copy
  choose words hread hdec using hvc
  obtain ⟨fallback, _, _⟩ := hzero
  let Wc : ℕ → K := fun i => if hi : i < N then words ⟨i, hi⟩ else fallback
  have hWc (i : ℕ) (hi : i < N) :
      normed.store.read tag 1 ((IExp.const N * IExp.var t).eval + i) = some (Wc i) := by
    simpa only [Wc, dif_pos hi, IExp.eval_mul, IExp.eval_const, IExp.eval_var] using
      hread ⟨i, hi⟩
  obtain ⟨ready, hcopy, shcopy, hprev, fcopy, _⟩ := exec_copyv_frame I hc tag normed
    (IExp.const N) 1 5 (IExp.const N * IExp.var t) 0 Wc hWc (by omega)
    (by intro i hi; exact ⟨N, by rw [hshape]; rfl, by simpa using hi⟩)
  have hdst : ∃ w store, predot.store.write tag 3 (t + 1) w = some store :=
    ⟨fallback, Store.exists_write_eq_some_of_getElem?_shape fallback
      (by rw [hpshape, hshape]; rfl) (by omega)⟩
  have hy (i : ℕ) (hi : i < N) : ∃ len,
      ready.store.shape[1]? = some (tag, len) ∧ N * (t + 1) + i < len := by
    refine ⟨N * (q + 1), ?_, ?_⟩
    · rw [shcopy, hshape]
      rfl
    · calc
        N * (t + 1) + i < N * (t + 1) + N := Nat.add_lt_add_left hi _
        _ = N * (t + 2) := by ring
        _ ≤ N * (q + 1) := Nat.mul_le_mul_left N (by omega)
  obtain ⟨out, w, W, hg, shg, hrready, -, _, _, _, hvout, fg,
      hvzero, hvunit, hres, _⟩ := h.exec_guarded_copyv_rscl_of_nrm2_execution I tag hz hc
    predot normed ready ⟨3, IExp.var t + 1⟩ ⟨9, 0⟩ 8 1 0
    (IExp.const N * (IExp.var t + 1)) (IExp.const N) xs hwin.1 hwin.2.2.1
    (by intro i hi; change i < N at hi; simpa [xs, hi] using hzp ⟨i, hi⟩)
    (by
      intro i hi
      change i < N at hi
      rw [show ready.store.read tag 8 (IExp.eval 0 + i) = normed.store.read tag 8 i by
        simpa using fcopy tag 8 i (by omega)]
      simpa only [xs, dif_pos hi] using hzn ⟨i, hi⟩)
    (by simp) (by omega) (by simp) hdst (by simpa using hy) hnorm
    (by simpa using fcopy tag 3 (t + 1) (by omega))
    (by
      change ∃ w, ready.store.read tag 9 0 = some w ∧ dec tag w = 0
      rw [fcopy tag 9 0 (by omega)]
      exact ⟨fallback, by assumption, by assumption⟩)
  have hff (p : P) (k i : ℕ) (hk : k ≠ 5)
      (hi : k = 1 → i < N * (t + 1) ∨ N * (t + 2) ≤ i) :
      out.store.read p k i = normed.store.read p k i := by
    refine (fg p k i ?_).trans (fcopy p k i (Or.inl hk))
    by_cases he : k = 1
    · rcases hi he with hlt | hge
      · exact Or.inr (Or.inl (by simpa using hlt))
      · right; right
        simpa only [IExp.eval_mul, IExp.eval_const, IExp.eval_add, IExp.eval_var,
          IExp.eval_one, Nat.mul_add, Nat.mul_one, Nat.mul_succ, Nat.add_assoc] using hge
    · exact Or.inl he
  refine ⟨out, (fun i => dec tag (W i)), dec tag w, ?_, shg.trans shcopy, hff, ?_, ?_,
    ⟨w, (fcopy tag 3 (t + 1) (by omega)).symm.trans (by simpa using hrready), rfl⟩,
    hvzero, ?_, ?_⟩
  · rw [exec_run_bind I (b := copyv tag 1 (IExp.const N * IExp.var t) 5 0
      (IExp.const N)) (fun _ => rfl), hcopy, Option.bind_some]
    exact hg
  · intro i
    refine ⟨Wc i, ?_, ?_⟩
    · rw [fg tag 5 i (Or.inl (by omega))]
      simpa using hprev i i.isLt
    · simpa only [Wc, dif_pos i.isLt] using hdec i
  · intro i
    exact ⟨W i, by simpa using hvout i, rfl⟩
  · intro hne
    exact (hvunit hne).trans
      (normalizationRoundingFactor_le_lanczosImplementationRoundoffBound N hu hsmall)
  · have heq : (fun i : Fin N => xs i - dec tag w * dec tag (W i)) =
        zv - dec tag w • (fun i : Fin N => dec tag (W i)) := by
      ext i
      simp [xs]
    change ‖WithLp.toLp 2 (fun i : Fin N => xs i - dec tag w * dec tag (W i))‖ ≤
      _ * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at hres
    rw [heq, hxs] at hres
    exact hres.trans (mul_le_mul_of_nonneg_right hwin.2.2.2.2 (norm_nonneg _))

/-- The computed first column is close to the normalized input. -/
private theorem reorth_input_direction {N : ℕ} (b v1 : Fin N → ℝ) {s uu γ ε : ℝ}
    (hb : b ≠ 0) (hres : ‖WithLp.toLp 2 (b - s • v1)‖ ≤ uu * ‖WithLp.toLp 2 b‖)
    (herr : |‖WithLp.toLp 2 b‖ - s| ≤ γ * ‖WithLp.toLp 2 b‖)
    (hunit : |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤ ε) (hu : uu ≤ ε) (hγ : γ ≤ ε)
    (hε : ε ≤ 1 / 100) :
    ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - v1)‖ ≤ 3 * ε := by
  have hnb : 0 < ‖WithLp.toLp 2 b‖ := by
    rw [norm_pos_iff]
    intro h0
    exact hb (by simpa using congrArg WithLp.ofLp h0)
  set nb := ‖WithLp.toLp 2 b‖ with hnbdef
  have hv : ‖WithLp.toLp 2 v1‖ ≤ 2 := by
    have h1 : ‖WithLp.toLp 2 v1‖ ^ 2 ≤ 4 := by
      have := (abs_le.mp hunit).2
      linarith
    nlinarith [norm_nonneg (WithLp.toLp 2 v1)]
  have heq : WithLp.toLp 2 (nb⁻¹ • b - v1) = nb⁻¹ • WithLp.toLp 2 (b - s • v1) +
      (nb⁻¹ * (s - nb)) • WithLp.toLp 2 v1 := by
    ext i
    simp only [WithLp.toLp_sub, WithLp.toLp_smul, PiLp.add_apply, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul, Pi.sub_apply, Pi.smul_apply]
    field_simp
    ring
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hnb,
    abs_mul, abs_inv, abs_of_pos hnb]
  have h1 : nb⁻¹ * ‖WithLp.toLp 2 (b - s • v1)‖ ≤ uu := by
    rw [inv_mul_le_iff₀ hnb]; linarith
  have h2 : nb⁻¹ * |s - nb| ≤ γ := by
    rw [inv_mul_le_iff₀ hnb, abs_sub_comm]; linarith
  have h20 : 0 ≤ nb⁻¹ * |s - nb| := by positivity
  nlinarith [norm_nonneg (WithLp.toLp 2 v1)]

/-- The initialization of the reorthogonalized loop in the eleven-buffer store: the two zero
literals, the zero previous vector, the input norm and the guarded first column. -/
private theorem reorth_exec_initialize (I : Interp P ι K (OpCount P ι)) {u : P → ℝ}
    {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P) {N q slot : ℕ} (b : Fin N → ℝ)
    (st : St P K (OpCount P ι))
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot), (tag, N), (tag, 2), (tag, q + 1)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (v1 : Fin N → ℝ),
      exec I (do
        ins (.lit tag ⟨9, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (IExp.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
        nrm2 tag ⟨4, 0⟩ 0 0 (IExp.const N)
        ifThenElse tag .eq ⟨4, 0⟩ ⟨9, 0⟩
          (forRange (IExp.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0))
          (do copyv tag 0 0 1 0 (IExp.const N); rscl tag ⟨4, 0⟩ 1 0 (IExp.const N)) :
            Builder P ι ℕ ℕ Unit).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ p k i, k ≠ 1 → k ≠ 3 → k ≠ 4 → k ≠ 5 → k ≠ 9 →
        out.store.read p k i = st.store.read p k i) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 1 i = some w ∧ dec tag w = v1 i) ∧
      (∃ w, out.store.read tag 3 0 = some w ∧ dec tag w = 0) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 5 i = some w ∧ dec tag w = 0) ∧
      (∃ w, out.store.read tag 9 0 = some w ∧ dec tag w = 0) ∧
      (b ≠ 0 → |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤ lanczosImplementationRoundoffBound N (u tag)) ∧
      (b ≠ 0 → ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - v1)‖ ≤
        3 * lanczosImplementationRoundoffBound N (u tag)) := by
  have hu := hsem.nonneg (p := tag) trivial
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N hu hsmall
  -- zeros
  obtain ⟨zero, hzl, hd⟩ := (hsem.isArithErrSem (fun _ => trivial)).lit_zero tag
  obtain ⟨s0, _, e0, sh0, r0, f0⟩ := exec_scalar_lit I tag st ⟨9, 0⟩ 0 zero hzl
    ⟨2, by rw [hshape]; rfl, by norm_num⟩
  let st1 := { st with store := s0, cnt := st.cnt + I.charge (.lit tag) }
  obtain ⟨s1, _, e1, sh1, r1, f1⟩ := exec_scalar_lit I tag st1 ⟨3, 0⟩ 0 zero hzl
    ⟨q + 1, by change s0.shape[3]? = _; rw [sh0, hshape]; rfl,
      by simp only [IExp.eval_ofNat]; omega⟩
  let st2 := { st1 with store := s1, cnt := st1.cnt + I.charge (.lit tag) }
  obtain ⟨s2, e2, sh2, r2, f2⟩ := exec_forRange_literal_zero_var I tag zero hzl st2
    (.const N) 5 (fun i hi => ⟨N, by change s1.shape[5]? = _; rw [sh1, sh0, hshape]; rfl, hi⟩)
  let predot : St P K (OpCount P ι) :=
    { st2 with store := s2, cnt := st2.cnt + N • I.charge (.lit tag) }
  have shp : predot.store.shape = st.store.shape := sh2.trans (sh1.trans sh0)
  have fp : ∀ p k i, k ≠ 3 → k ≠ 5 → k ≠ 9 → predot.store.read p k i = st.store.read p k i := by
    intro p k i h3 h5 h9
    change s2.read p k i = _
    rw [f2 p k i (Or.inr (Or.inl h5)), f1 p k i (Or.inr (Or.inl h3)), f0 p k i (Or.inr (Or.inl h9))]
  have rz : predot.store.read tag 9 0 = some zero := by
    change s2.read tag 9 0 = _
    rw [f2 tag 9 0 (Or.inr (Or.inl (by norm_num))), f1 tag 9 0 (Or.inr (Or.inl (by norm_num)))]
    exact r0
  have rb3 : predot.store.read tag 3 0 = some zero := by
    change s2.read tag 3 0 = _
    rw [f2 tag 3 0 (Or.inr (Or.inl (by norm_num)))]
    exact r1
  have rp5 (i : Fin N) : predot.store.read tag 5 i = some zero := r2 i i.isLt
  have e012 : exec I (do
      ins (.lit tag ⟨9, 0⟩ 0)
      ins (.lit tag ⟨3, 0⟩ 0)
      forRange (IExp.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0) :
        Builder P ι ℕ ℕ Unit).run st = some predot := by
    rw [exec_run_bind I (b := ins (.lit tag ⟨9, 0⟩ 0)) (fun _ => rfl), e0, Option.bind_some,
      exec_run_bind I (b := ins (.lit tag ⟨3, 0⟩ 0)) (fun _ => rfl), e1, Option.bind_some]
    exact e2
  -- the input norm
  let xs : ℕ → ℝ := fun i => if hi : i < N then b ⟨i, hi⟩ else 0
  have hx (i : ℕ) (hi : i < N) :
      ∃ w, predot.store.read tag 0 (0 + i) = some w ∧ dec tag w = xs i := by
    rw [zero_add, fp tag 0 i (by omega) (by omega) (by omega)]
    simpa only [xs, dif_pos hi] using hb ⟨i, hi⟩
  obtain ⟨scratch, hs⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) zero
    (show predot.store.shape[4]? = some (tag, 1) by rw [shp, hshape]; rfl) (by norm_num)
  obtain ⟨normed, w, en, hw, _, _, _⟩ :=
    hsem.exec_nrm2_abs_norm_sub_le_zero_iff I tag hz predot ⟨4, 0⟩ 0 0 (.const N) xs
      hwin.1 hwin.2.2.1 hx (by norm_num) ⟨zero, scratch, hs⟩
  have shn : normed.store.shape = predot.store.shape := Store.shape_of_write_eq_some hw
  have fn : ∀ p k i, (k ≠ 4 ∨ i ≠ 0) → normed.store.read p k i = predot.store.read p k i :=
    fun p k i hk => Store.read_of_write_eq_some_of_ne hw hk
  have hxN (i : ℕ) (hi : i < N) :
      ∃ w, normed.store.read tag 0 (0 + i) = some w ∧ dec tag w = xs i := by
    rw [fn tag 0 (0 + i) (Or.inl (by norm_num))]
    exact hx i hi
  have hzN : ∃ w, normed.store.read tag 9 0 = some w ∧ dec tag w = 0 :=
    ⟨zero, (fn tag 9 0 (Or.inl (by norm_num))).trans rz, hd⟩
  have hNN : N ≤ N * (q + 1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left N (Nat.succ_le_succ (Nat.zero_le q))
  have hcap (i : ℕ) (hi : i < N) : ∃ len,
      normed.store.shape[1]? = some (tag, len) ∧ (0 : IExp ℕ).eval + i < len :=
    ⟨N * (q + 1), by rw [shn, shp, hshape]; rfl,
      by simpa only [IExp.eval_zero, zero_add] using hi.trans_le hNN⟩
  obtain ⟨out, w', W, eg, shape, _, rnorm, hnonneg, herr, hiff, hW, frame, hzv, hunit,
      hres, -⟩ := hsem.exec_guarded_copyv_rscl_of_nrm2_execution I tag hz hc
    predot normed normed ⟨4, 0⟩ ⟨9, 0⟩ 0 1 0 0 (.const N) xs hwin.1 hwin.2.2.1 hx hxN
      (by norm_num) (by norm_num) (by norm_num) ⟨zero, scratch, hs⟩ hcap en rfl hzN
  have hxs : (fun i : Fin N => xs i) = b := by funext i; simp only [xs, dif_pos i.isLt]
  change |‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ - dec tag w'| ≤
    roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at herr
  change dec tag w' = 0 ↔ (fun i : Fin N => xs i) = 0 at hiff
  change ‖WithLp.toLp 2 ((fun i : Fin N => xs i) - dec tag w' •
    (fun i : Fin N => dec tag (W i)))‖ ≤
      u tag * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at hres
  rw [hxs] at herr hiff hres
  have fo : ∀ p k i, k ≠ 1 → out.store.read p k i = normed.store.read p k i :=
    fun p k i hk => frame p k i (Or.inl hk)
  have hunit' : b ≠ 0 → |‖WithLp.toLp 2 (fun i : Fin N => dec tag (W i))‖ ^ 2 - 1| ≤
      lanczosImplementationRoundoffBound N (u tag) := fun hbne =>
    (hunit (fun he => hbne (hiff.mp he))).trans
      (normalizationRoundingFactor_le_lanczosImplementationRoundoffBound N hu hsmall)
  refine ⟨out, fun i => dec tag (W i), ?_, shape.trans (shn.trans shp), ?_, ?_, ?_, ?_, ?_,
    hunit', ?_⟩
  · have hcomp : ExecutionComposable I (do
        ins (.lit tag ⟨9, 0⟩ 0); ins (.lit tag ⟨3, 0⟩ 0)
        forRange (IExp.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0) : Builder P ι ℕ ℕ Unit) :=
      (executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          (executionComposable_single I (fun _ => rfl)))
    change exec I ((do
        ins (.lit tag ⟨9, 0⟩ 0); ins (.lit tag ⟨3, 0⟩ 0)
        forRange (IExp.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0) :
          Builder P ι ℕ ℕ Unit) >>= fun _ => _).run st = _
    rw [hcomp, e012, Option.bind_some, exec_run_bind I
      (b := nrm2 tag ⟨4, 0⟩ 0 0 (.const N)) (fun _ => rfl), en, Option.bind_some]
    exact (exec_normalize_branch_var_eq I tag normed (.const N) 0 1 0 ⟨4, 0⟩ ⟨9, 0⟩).trans eg
  · intro p k i h1 h3 h4 h5 h9
    rw [fo p k i h1, fn p k i (Or.inl h4), fp p k i h3 h5 h9]
  · intro i
    exact ⟨W i, by simpa only [IExp.eval_zero, zero_add] using hW i, rfl⟩
  · exact ⟨zero, by rw [fo tag 3 0 (by norm_num), fn tag 3 0 (Or.inl (by norm_num))]; exact rb3,
      hd⟩
  · intro i
    exact ⟨zero, by rw [fo tag 5 i (by norm_num), fn tag 5 i (Or.inl (by norm_num))]; exact rp5 i,
      hd⟩
  · exact ⟨zero, by rw [fo tag 9 0 (by norm_num), fn tag 9 0 (Or.inl (by norm_num))]; exact rz,
      hd⟩
  · intro hbne
    exact reorth_input_direction b _ hbne hres herr (hunit' hbne) hwin.2.2.2.2
      (reorth_roundingFactor_succ_le N hu hsmall) hsmall

/-- **One rounded step of the reorthogonalized loop** in the eleven-buffer store: execution,
the store layout after the step, and the local guarantees of the step. -/
private theorem reorth_exec_step (I : Interp P ι K (OpCount P ι)) {u : P → ℝ}
    {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q t slot : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (b : Fin N → ℝ) (pre : Store P K → Prop)
    (hpreFrame : ∀ s s' : Store P K, pre s → (∀ k < 8, s'.shape[k]? = s.shape[k]?) →
      (∀ i, s'.read tag 7 i = s.read tag 7 i) → pre s')
    (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A) pre 1 8
      (IExp.const N * IExp.var t) 0 (mv 8 (IExp.var t)))
    (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit) {η₀ ε₁ ε₂ ε₃ : ℝ}
    (horth : IsOrthRoutine I dec tag N (t + 1) η₀ ε₁ ε₂ ε₃ (fun _ => True) 1 8 10 0 0
      (orth 8 10 (IExp.var t)))
    (st : St P K (OpCount P ι)) (v : ℕ → Fin N → ℝ) (α β ν : ℕ → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot), (tag, N), (tag, 2), (tag, q + 1)])
    (hpre : pre st.store)
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hV : ∀ c ≤ t, ∀ i : Fin N,
      ∃ w, st.store.read tag 1 (N * c + i) = some w ∧ dec tag w = v (c + 1) i)
    (hα : ∀ c < t, ∃ w, st.store.read tag 2 c = some w ∧ dec tag w = α (c + 1))
    (hβ : ∀ c ≤ t, ∃ w, st.store.read tag 3 c = some w ∧ dec tag w = β c)
    (hp : ∀ i : Fin N, ∃ w, st.store.read tag 5 i = some w ∧ dec tag w = v t i)
    (hν : ∀ c < t, ∃ w, st.store.read tag 6 c = some w ∧ dec tag w = ν (c + 1))
    (hzero : ∃ w, st.store.read tag 9 0 = some w ∧ dec tag w = 0)
    (ht : t < q) (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (uv wv zv z' : Fin N → ℝ) (hv : Fin (t + 1) → ℝ)
      (an bn nn : ℝ) (vn : Fin N → ℝ),
      exec I (do
        mv 8 (IExp.var t)
        ins (.un tag .neg ⟨9, 1⟩ ⟨3, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 5 0 8 0 (IExp.const N)
        dot tag ⟨2, IExp.var t⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
        ins (.un tag .neg ⟨9, 1⟩ ⟨2, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
        nrm2 tag ⟨6, IExp.var t⟩ 8 0 (IExp.const N)
        orth 8 10 (IExp.var t)
        nrm2 tag ⟨3, IExp.var t + 1⟩ 8 0 (IExp.const N)
        copyv tag 1 (IExp.const N * IExp.var t) 5 0 (IExp.const N)
        ifThenElse tag .eq ⟨3, IExp.var t + 1⟩ ⟨9, 0⟩
          (forRange (IExp.const N) fun i =>
            ins (.lit tag ⟨1, IExp.const N * (IExp.var t + 1) + IExp.var i⟩ 0)) (do
            copyv tag 8 0 1 (IExp.const N * (IExp.var t + 1)) (IExp.const N)
            rscl tag ⟨3, IExp.var t + 1⟩ 1
              (IExp.const N * (IExp.var t + 1)) (IExp.const N)) :
            Builder P ι ℕ ℕ Unit).run st = some out ∧
      out.store.shape = st.store.shape ∧ pre out.store ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 0 i = some w ∧ dec tag w = b i) ∧
      (∀ c ≤ t + 1, ∀ i : Fin N, ∃ w, out.store.read tag 1 (N * c + i) = some w ∧
        dec tag w = Function.update v (t + 2) vn (c + 1) i) ∧
      (∀ c < t + 1, ∃ w, out.store.read tag 2 c = some w ∧
        dec tag w = Function.update α (t + 1) an (c + 1)) ∧
      (∀ c ≤ t + 1, ∃ w, out.store.read tag 3 c = some w ∧
        dec tag w = Function.update β (t + 1) bn c) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 5 i = some w ∧ dec tag w = v (t + 1) i) ∧
      (∀ c < t + 1, ∃ w, out.store.read tag 6 c = some w ∧
        dec tag w = Function.update ν (t + 1) nn (c + 1)) ∧
      (∃ w, out.store.read tag 9 0 = some w ∧ dec tag w = 0) ∧
      ‖WithLp.toLp 2 (A *ᵥ v (t + 1) - uv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) * specNorm A *
          ‖WithLp.toLp 2 (v (t + 1))‖ ∧
      ‖WithLp.toLp 2 (uv - β t • v t - wv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 uv‖ + |β t| * ‖WithLp.toLp 2 (v t)‖) ∧
      |v (t + 1) ⬝ᵥ wv - an| ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 (v (t + 1))‖ *
          ‖WithLp.toLp 2 wv‖ ∧
      ‖WithLp.toLp 2 (wv - an • v (t + 1) - zv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 wv‖ + |an| * ‖WithLp.toLp 2 (v (t + 1))‖) ∧
      0 ≤ nn ∧ |nn - ‖WithLp.toLp 2 zv‖| ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 zv‖ ∧
      IsOrthErr η₀ ε₁ ε₂ ε₃ (LanczosReorthRun.basisOf v (t + 1)) zv hv z' ∧
      |bn - ‖WithLp.toLp 2 z'‖| ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 z'‖ ∧
      ‖WithLp.toLp 2 (z' - bn • vn)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 z'‖ ∧
      (bn ≠ 0 → |‖WithLp.toLp 2 vn‖ ^ 2 - 1| ≤
        lanczosImplementationRoundoffBound N (u tag)) := by
  obtain ⟨w0, hw0, hd0⟩ := hzero
  obtain ⟨s₁, uv, wv, zv, an, nn, hr₁, sh₁, f₁, hz₁, ha₁, hn₁, e₁, e₂, e₃, e₄, hnn, e₅⟩ :=
    reorth_exec_work I h hz tag pre mv hmv st hshape hpre ht (v (t + 1)) (v t) (β t)
      (hV t le_rfl) hp (hβ t le_rfl) hsmall
  have hVs₁ : HoldsDecoded s₁.store dec tag 1 0 (LanczosReorthRun.basisOf v (t + 1)) := by
    intro i c
    rw [show 0 + (i : ℕ) + N * c = N * c + i by ring, f₁ tag 1 _ (by omega) (by omega)
      (by omega) (by omega)]
    exact hV c (by omega) i
  obtain ⟨mid, normed, z', hv, bn, hr₂, hr₃, shm, shn, fm, fn, hzm, hbn, eorth, -, -, e₆⟩ :=
    reorth_exec_orth I h hz tag orth horth s₁ (sh₁.trans hshape) ht w0 _ hVs₁ zv hz₁ hsmall
  have fpre : ∀ p k i, k ≠ 8 → k ≠ 10 → (k = 9 → i ≠ 1) → (k = 2 → i ≠ t) →
      (k = 6 → i ≠ t) → (k = 3 → i ≠ t + 1) →
      normed.store.read p k i = st.store.read p k i := by
    intro p k i h8 h10 h9 h2 h6 h3
    rw [fn p k i (by by_cases hk : k = 3; exacts [Or.inr (h3 hk), Or.inl hk]), fm p k i h8 h10, f₁ p k i h8 h9 h2 h6]
  let I' : Interp P ι K (OpCount P ι) := { I with charge := fun k => Finsupp.single k 1 }
  obtain ⟨normed', hr₃', n1, n2, n3, n4, n5, n6⟩ := reorth_exec_transfer I I' rfl rfl rfl rfl rfl
    rfl (nrm2 tag ⟨3, IExp.var t + 1⟩ 8 0 (IExp.const N)).run (a' := mid) rfl rfl rfl rfl rfl rfl
    hr₃
  obtain ⟨out', vn, bn', hr₄', sh₄, f₄, hp₄, hv₄, hbn', hvzero, hunit, e₇⟩ :=
    reorth_exec_commit I' h hz (fun _ => rfl) tag mid normed'
      (by rw [← n1]; exact shn.trans (sh₁.trans hshape))
      (by rw [← n1]; exact shm.trans shn.symm) ht (v (t + 1))
      (fun i => by
        rw [← n1, fpre tag 1 _ (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)]
        exact hV t le_rfl i)
      z' hzm (fun i => by rw [← n1, fn tag 8 i (Or.inl (by omega))]; exact hzm i)
      ⟨w0, by rw [← n1, fpre tag 9 0 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]; exact hw0, hd0⟩ hr₃' hsmall
  obtain ⟨out, hr₄, o1, -, -, -, -, -⟩ := reorth_exec_transfer I' I rfl rfl rfl rfl rfl rfl
    (do
      copyv tag 1 (IExp.const N * IExp.var t) 5 0 (IExp.const N)
      ifThenElse tag .eq ⟨3, IExp.var t + 1⟩ ⟨9, 0⟩
        (forRange (IExp.const N) fun i =>
          ins (.lit tag ⟨1, IExp.const N * (IExp.var t + 1) + IExp.var i⟩ 0)) (do
          copyv tag 8 0 1 (IExp.const N * (IExp.var t + 1)) (IExp.const N)
          rscl tag ⟨3, IExp.var t + 1⟩ 1
            (IExp.const N * (IExp.var t + 1)) (IExp.const N)) :
          Builder P ι ℕ ℕ Unit).run (a' := normed) n1.symm n2.symm n3.symm n4.symm n5.symm
    n6.symm hr₄'
  rw [← n1] at sh₄ f₄ hbn'
  rw [o1] at sh₄ f₄ hp₄ hv₄
  have hbb : bn' = bn := by
    obtain ⟨x, hx, hdx⟩ := hbn
    obtain ⟨y, hy, hdy⟩ := hbn'
    rw [hx] at hy
    cases hy
    rw [← hdx, ← hdy]
  subst hbb
  have shout : out.store.shape = st.store.shape := sh₄.trans (shn.trans sh₁)
  have fall : ∀ p k i, k ≠ 5 → k ≠ 8 → k ≠ 10 → (k = 9 → i ≠ 1) → (k = 2 → i ≠ t) →
      (k = 6 → i ≠ t) → (k = 3 → i ≠ t + 1) →
      (k = 1 → i < N * (t + 1) ∨ N * (t + 2) ≤ i) →
      out.store.read p k i = st.store.read p k i := by
    intro p k i h5 h8 h10 h9 h2 h6 h3 h1
    rw [f₄ p k i h5 h1, fpre p k i h8 h10 h9 h2 h6 h3]
  -- the new cells, read through the later phases
  have fafter : ∀ p k i, k ≠ 5 → k ≠ 1 → k ≠ 8 → k ≠ 10 → k ≠ 3 →
      out.store.read p k i = s₁.store.read p k i := by
    intro p k i h5 h1 h8 h10 h3
    rw [f₄ p k i h5 (fun h => absurd h h1), fn p k i (Or.inl h3), fm p k i h8 h10]
  refine ⟨out, uv, wv, zv, z', hv, an, bn', nn, vn, ?_, shout, ?_, ?_, ?_, ?_, ?_, hp₄, ?_, ?_,
    e₁, e₂, e₃, e₄, hnn, e₅, eorth, e₆, e₇, hunit⟩
  · change exec I (do
      (do
        mv 8 (IExp.var t)
        ins (.un tag .neg ⟨9, 1⟩ ⟨3, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 5 0 8 0 (IExp.const N)
        dot tag ⟨2, IExp.var t⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
        ins (.un tag .neg ⟨9, 1⟩ ⟨2, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
        nrm2 tag ⟨6, IExp.var t⟩ 8 0 (IExp.const N) : Builder P ι ℕ ℕ Unit)
      orth 8 10 (IExp.var t)
      nrm2 tag ⟨3, IExp.var t + 1⟩ 8 0 (IExp.const N)
      (do
        copyv tag 1 (IExp.const N * IExp.var t) 5 0 (IExp.const N)
        ifThenElse tag .eq ⟨3, IExp.var t + 1⟩ ⟨9, 0⟩
          (forRange (IExp.const N) fun i =>
            ins (.lit tag ⟨1, IExp.const N * (IExp.var t + 1) + IExp.var i⟩ 0)) (do
            copyv tag 8 0 1 (IExp.const N * (IExp.var t + 1)) (IExp.const N)
            rscl tag ⟨3, IExp.var t + 1⟩ 1
              (IExp.const N * (IExp.var t + 1)) (IExp.const N)) :
            Builder P ι ℕ ℕ Unit)).run st = some out
    have cw : ExecutionComposable I (do
        mv 8 (IExp.var t)
        ins (.un tag .neg ⟨9, 1⟩ ⟨3, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 5 0 8 0 (IExp.const N)
        dot tag ⟨2, IExp.var t⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
        ins (.un tag .neg ⟨9, 1⟩ ⟨2, IExp.var t⟩)
        axpy tag ⟨9, 1⟩ 1 (IExp.const N * IExp.var t) 8 0 (IExp.const N)
        nrm2 tag ⟨6, IExp.var t⟩ 8 0 (IExp.const N) : Builder P ι ℕ ℕ Unit) :=
      hmv.composable.bind ((executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          ((executionComposable_single I (fun _ => rfl)).bind
            ((executionComposable_single I (fun _ => rfl)).bind
              ((executionComposable_single I (fun _ => rfl)).bind
                (executionComposable_single I (fun _ => rfl)))))))
    rw [cw, hr₁, Option.bind_some, horth.composable, hr₂, Option.bind_some,
      exec_run_bind I (b := nrm2 tag ⟨3, IExp.var t + 1⟩ 8 0 (IExp.const N)) (fun _ => rfl),
      hr₃, Option.bind_some]
    exact hr₄
  · exact hpreFrame st.store out.store hpre (fun k _ => by rw [shout])
      (fun i => fall tag 7 i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
  · intro i
    rw [fall tag 0 i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
    exact hb i
  · intro c hc i
    by_cases he : c = t + 1
    · subst c
      simpa using hv₄ i
    · have hi : N * c + i < N * (t + 1) := by
        calc
          N * c + i < N * c + N := Nat.add_lt_add_left i.isLt _
          _ = N * (c + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ N * (t + 1) := Nat.mul_le_mul_left N (by omega)
      rw [fall tag 1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (fun _ => Or.inl hi)]
      simpa only [Function.update_of_ne (by omega : c + 1 ≠ t + 2)] using hV c (by omega) i
  · intro c hc
    by_cases he : c = t
    · subst c
      simpa [fafter tag 2 t (by omega) (by omega) (by omega) (by omega) (by omega)] using ha₁
    · rw [fall tag 2 c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]
      simpa only [Function.update_of_ne (by omega : c + 1 ≠ t + 1)] using hα c (by omega)
  · intro c hc
    by_cases he : c = t + 1
    · subst c
      obtain ⟨w, hw, hdw⟩ := hbn'
      exact ⟨w, by rw [f₄ tag 3 (t + 1) (by omega) (by omega)]; exact hw, by simpa using hdw⟩
    · rw [fall tag 3 c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]
      simpa only [Function.update_of_ne he] using hβ c (by omega)
  · intro c hc
    by_cases he : c = t
    · subst c
      simpa [fafter tag 6 t (by omega) (by omega) (by omega) (by omega) (by omega)] using hn₁
    · rw [fall tag 6 c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]
      simpa only [Function.update_of_ne (by omega : c + 1 ≠ t + 1)] using hν c (by omega)
  · exact ⟨w0, by rw [fall tag 9 0 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)]; exact hw0, hd0⟩

/-- **The rounded loop of the reorthogonalized program**: from the initialized eleven-buffer
store, every requested step executes; the final store holds the basis, the coefficients and the
stored norms, and every step meets its local guarantees. -/
private theorem reorth_exec_loop (I : Interp P ι K (OpCount P ι)) {u : P → ℝ}
    {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q slot : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (b : Fin N → ℝ) (pre : Store P K → Prop)
    (hpreFrame : ∀ s s' : Store P K, pre s → (∀ k < 8, s'.shape[k]? = s.shape[k]?) →
      (∀ i, s'.read tag 7 i = s.read tag 7 i) → pre s')
    (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A) pre 1 8
      (IExp.const N * IExp.var t) 0 (mv 8 (IExp.var t)))
    (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit) {η₀ ε₁ ε₂ ε₃ : ℝ}
    (horth : ∀ t < q, IsOrthRoutine I dec tag N (t + 1) η₀ ε₁ ε₂ ε₃ (fun _ => True) 1 8 10 0 0
      (orth 8 10 (IExp.var t)))
    (st : St P K (OpCount P ι)) (v1 : Fin N → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot), (tag, N), (tag, 2), (tag, q + 1)])
    (hpre : pre st.store)
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hv1 : ∀ i : Fin N, ∃ w, st.store.read tag 1 i = some w ∧ dec tag w = v1 i)
    (hβ0 : ∃ w, st.store.read tag 3 0 = some w ∧ dec tag w = 0)
    (hp : ∀ i : Fin N, ∃ w, st.store.read tag 5 i = some w ∧ dec tag w = 0)
    (hzero : ∃ w, st.store.read tag 9 0 = some w ∧ dec tag w = 0)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (v : ℕ → Fin N → ℝ) (α β ν : ℕ → ℝ),
      exec I (forRange (IExp.const q) fun j => do
        mv 8 (IExp.var j)
        ins (.un tag .neg ⟨9, 1⟩ ⟨3, IExp.var j⟩)
        axpy tag ⟨9, 1⟩ 5 0 8 0 (IExp.const N)
        dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j) 8 0 (IExp.const N)
        ins (.un tag .neg ⟨9, 1⟩ ⟨2, IExp.var j⟩)
        axpy tag ⟨9, 1⟩ 1 (IExp.const N * IExp.var j) 8 0 (IExp.const N)
        nrm2 tag ⟨6, IExp.var j⟩ 8 0 (IExp.const N)
        orth 8 10 (IExp.var j)
        nrm2 tag ⟨3, IExp.var j + 1⟩ 8 0 (IExp.const N)
        copyv tag 1 (IExp.const N * IExp.var j) 5 0 (IExp.const N)
        ifThenElse tag .eq ⟨3, IExp.var j + 1⟩ ⟨9, 0⟩
          (forRange (IExp.const N) fun i =>
            ins (.lit tag ⟨1, IExp.const N * (IExp.var j + 1) + IExp.var i⟩ 0)) (do
            copyv tag 8 0 1 (IExp.const N * (IExp.var j + 1)) (IExp.const N)
            rscl tag ⟨3, IExp.var j + 1⟩ 1
              (IExp.const N * (IExp.var j + 1)) (IExp.const N)) :
            Builder P ι ℕ ℕ Unit).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 0 i = some w ∧ dec tag w = b i) ∧
      (∀ c ≤ q, ∀ i : Fin N, ∃ w, out.store.read tag 1 (N * c + i) = some w ∧
        dec tag w = v (c + 1) i) ∧
      (∀ c < q, ∃ w, out.store.read tag 2 c = some w ∧ dec tag w = α (c + 1)) ∧
      (∀ c ≤ q, ∃ w, out.store.read tag 3 c = some w ∧ dec tag w = β c) ∧
      (∀ c < q, ∃ w, out.store.read tag 6 c = some w ∧ dec tag w = ν (c + 1)) ∧
      v 0 = 0 ∧ β 0 = 0 ∧ v 1 = v1 ∧
      ∀ j, ∃ (uv wv zv z' : Fin N → ℝ) (hv : ℕ → ℝ), j < q →
        ‖WithLp.toLp 2 (A *ᵥ v (j + 1) - uv)‖ ≤
          lanczosImplementationRoundoffBound N (u tag) * specNorm A *
            ‖WithLp.toLp 2 (v (j + 1))‖ ∧
        ‖WithLp.toLp 2 (uv - β j • v j - wv)‖ ≤
          lanczosImplementationRoundoffBound N (u tag) *
            (‖WithLp.toLp 2 uv‖ + |β j| * ‖WithLp.toLp 2 (v j)‖) ∧
        |v (j + 1) ⬝ᵥ wv - α (j + 1)| ≤
          lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 (v (j + 1))‖ *
            ‖WithLp.toLp 2 wv‖ ∧
        ‖WithLp.toLp 2 (wv - α (j + 1) • v (j + 1) - zv)‖ ≤
          lanczosImplementationRoundoffBound N (u tag) *
            (‖WithLp.toLp 2 wv‖ + |α (j + 1)| * ‖WithLp.toLp 2 (v (j + 1))‖) ∧
        0 ≤ ν (j + 1) ∧ |ν (j + 1) - ‖WithLp.toLp 2 zv‖| ≤
          lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 zv‖ ∧
        IsOrthErr η₀ ε₁ ε₂ ε₃ (LanczosReorthRun.basisOf v (j + 1)) zv
          (fun i : Fin (j + 1) => hv i) z' ∧
        |β (j + 1) - ‖WithLp.toLp 2 z'‖| ≤
          lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 z'‖ ∧
        ‖WithLp.toLp 2 (z' - β (j + 1) • v (j + 2))‖ ≤
          lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 z'‖ ∧
        (β (j + 1) ≠ 0 → |‖WithLp.toLp 2 (v (j + 2))‖ ^ 2 - 1| ≤
          lanczosImplementationRoundoffBound N (u tag)) := by
  obtain ⟨out, hr, ⟨v, α, β, ν, hsh, hpr, hbo, hV, hα, hβ, -, hν, -, hv0, hb0, hv1o, hpf⟩⟩ :=
    exists_exec_loop_eq_some_of_forall I (n := IExp.const q)
    (body := fun j => (do
        mv 8 (IExp.var j)
        ins (.un tag .neg ⟨9, 1⟩ ⟨3, IExp.var j⟩)
        axpy tag ⟨9, 1⟩ 5 0 8 0 (IExp.const N)
        dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j) 8 0 (IExp.const N)
        ins (.un tag .neg ⟨9, 1⟩ ⟨2, IExp.var j⟩)
        axpy tag ⟨9, 1⟩ 1 (IExp.const N * IExp.var j) 8 0 (IExp.const N)
        nrm2 tag ⟨6, IExp.var j⟩ 8 0 (IExp.const N)
        orth 8 10 (IExp.var j)
        nrm2 tag ⟨3, IExp.var j + 1⟩ 8 0 (IExp.const N)
        copyv tag 1 (IExp.const N * IExp.var j) 5 0 (IExp.const N)
        ifThenElse tag .eq ⟨3, IExp.var j + 1⟩ ⟨9, 0⟩
          (forRange (IExp.const N) fun i =>
            ins (.lit tag ⟨1, IExp.const N * (IExp.var j + 1) + IExp.var i⟩ 0)) (do
            copyv tag 8 0 1 (IExp.const N * (IExp.var j + 1)) (IExp.const N)
            rscl tag ⟨3, IExp.var j + 1⟩ 1
              (IExp.const N * (IExp.var j + 1)) (IExp.const N)) :
            Builder P ι ℕ ℕ Unit).run)
    (fun t s => ∃ (v : ℕ → Fin N → ℝ) (α β ν : ℕ → ℝ),
      s.store.shape = st.store.shape ∧ pre s.store ∧
      (∀ i : Fin N, ∃ w, s.store.read tag 0 i = some w ∧ dec tag w = b i) ∧
      (∀ c ≤ t, ∀ i : Fin N, ∃ w, s.store.read tag 1 (N * c + i) = some w ∧
        dec tag w = v (c + 1) i) ∧
      (∀ c < t, ∃ w, s.store.read tag 2 c = some w ∧ dec tag w = α (c + 1)) ∧
      (∀ c ≤ t, ∃ w, s.store.read tag 3 c = some w ∧ dec tag w = β c) ∧
      (∀ i : Fin N, ∃ w, s.store.read tag 5 i = some w ∧ dec tag w = v t i) ∧
      (∀ c < t, ∃ w, s.store.read tag 6 c = some w ∧ dec tag w = ν (c + 1)) ∧
      (∃ w, s.store.read tag 9 0 = some w ∧ dec tag w = 0) ∧
      v 0 = 0 ∧ β 0 = 0 ∧ v 1 = v1 ∧
      ∀ j, ∃ (uv wv zv z' : Fin N → ℝ) (hv : ℕ → ℝ), j < t →
        ‖WithLp.toLp 2 (A *ᵥ v (j + 1) - uv)‖ ≤
          lanczosImplementationRoundoffBound N (u tag) * specNorm A *
            ‖WithLp.toLp 2 (v (j + 1))‖ ∧
        ‖WithLp.toLp 2 (uv - β j • v j - wv)‖ ≤
          lanczosImplementationRoundoffBound N (u tag) *
            (‖WithLp.toLp 2 uv‖ + |β j| * ‖WithLp.toLp 2 (v j)‖) ∧
        |v (j + 1) ⬝ᵥ wv - α (j + 1)| ≤
          lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 (v (j + 1))‖ *
            ‖WithLp.toLp 2 wv‖ ∧
        ‖WithLp.toLp 2 (wv - α (j + 1) • v (j + 1) - zv)‖ ≤
          lanczosImplementationRoundoffBound N (u tag) *
            (‖WithLp.toLp 2 wv‖ + |α (j + 1)| * ‖WithLp.toLp 2 (v (j + 1))‖) ∧
        0 ≤ ν (j + 1) ∧ |ν (j + 1) - ‖WithLp.toLp 2 zv‖| ≤
          lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 zv‖ ∧
        IsOrthErr η₀ ε₁ ε₂ ε₃ (LanczosReorthRun.basisOf v (j + 1)) zv
          (fun i : Fin (j + 1) => hv i) z' ∧
        |β (j + 1) - ‖WithLp.toLp 2 z'‖| ≤
          lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 z'‖ ∧
        ‖WithLp.toLp 2 (z' - β (j + 1) • v (j + 2))‖ ≤
          lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 z'‖ ∧
        (β (j + 1) ≠ 0 → |‖WithLp.toLp 2 (v (j + 2))‖ ^ 2 - 1| ≤
          lanczosImplementationRoundoffBound N (u tag)))
    ⟨Function.update 0 1 v1, 0, 0, 0, rfl, hpre, hb,
      fun c hc i => by
        obtain rfl : c = 0 := by omega
        simpa using hv1 i,
      fun c hc => absurd hc (by omega),
      fun c hc => by
        obtain rfl : c = 0 := by omega
        simpa using hβ0,
      fun i => by simpa using hp i,
      fun c hc => absurd hc (by omega), hzero,
      by simp, rfl, by simp,
      fun j => ⟨0, 0, 0, 0, 0, fun hj => absurd hj (by omega)⟩⟩
    (by
      intro t ht s ⟨v, α, β, ν, hsh, hpr, hbs, hV, hα, hβ, hp, hν, hzs, hv0, hb0, hv1s, hpf⟩
      obtain ⟨out, uv, wv, zv, z', hv, an, bn, nn, vn, hr, sho, hpro, hbo, hVo, hαo, hβo, hpo,
          hνo, hzo, e₁, e₂, e₃, e₄, hnn, e₅, eorth, e₆, e₇, hunit⟩ :=
        reorth_exec_step I h hz tag b pre hpreFrame mv (hmv t) orth (horth t (by simpa using ht)) s v α β ν
          (hsh.trans hshape) hpr hbs hV hα hβ hp hν hzs (by simpa using ht) hsmall
      have ev : ∀ k, k < t + 2 → Function.update v (t + 2) vn k = v k :=
        fun k hk => Function.update_of_ne (by omega) _ _
      have ea : ∀ k, k < t + 1 → Function.update α (t + 1) an k = α k :=
        fun k hk => Function.update_of_ne (by omega) _ _
      have eb : ∀ k, k < t + 1 → Function.update β (t + 1) bn k = β k :=
        fun k hk => Function.update_of_ne (by omega) _ _
      have en : ∀ k, k < t + 1 → Function.update ν (t + 1) nn k = ν k :=
        fun k hk => Function.update_of_ne (by omega) _ _
      have hbasis : ∀ k, k ≤ t + 1 → LanczosReorthRun.basisOf (Function.update v (t + 2) vn) k =
          LanczosReorthRun.basisOf v k := by
        intro k hk
        ext i c
        simp only [LanczosReorthRun.basisOf, Matrix.of_apply]
        rw [ev _ (by omega)]
      refine ⟨out, hr, Function.update v (t + 2) vn, Function.update α (t + 1) an,
        Function.update β (t + 1) bn, Function.update ν (t + 1) nn, sho.trans hsh, hpro, hbo,
        hVo, hαo, hβo, ?_, hνo, hzo, by rw [ev 0 (by omega), hv0], by rw [eb 0 (by omega), hb0],
        by rw [ev 1 (by omega), hv1s], ?_⟩
      · intro i
        simpa only [ev (t + 1) (by omega)] using hpo i
      · intro j
        by_cases hjt : j < t
        · obtain ⟨uv', wv', zv', z'', hv', hf⟩ := hpf j
          refine ⟨uv', wv', zv', z'', hv', fun _ => ?_⟩
          rw [ev j (by omega), ev (j + 1) (by omega), ev (j + 2) (by omega), ea (j + 1) (by omega),
            eb j (by omega), eb (j + 1) (by omega), en (j + 1) (by omega),
            hbasis (j + 1) (by omega)]
          exact hf hjt
        · by_cases hjt' : j = t
          · subst j
            refine ⟨uv, wv, zv, z', fun i => if hi : i < t + 1 then hv ⟨i, hi⟩ else 0,
              fun _ => ?_⟩
            have hhv : (fun i : Fin (t + 1) =>
                (fun i => if hi : i < t + 1 then hv ⟨i, hi⟩ else 0) (i : ℕ)) = hv := by
              funext i
              exact dif_pos i.isLt
            rw [ev t (by omega), ev (t + 1) (by omega), eb t (by omega), hbasis (t + 1) le_rfl,
              hhv]
            simp only [Function.update_self]
            exact ⟨e₁, e₂, e₃, e₄, hnn, e₅, eorth, e₆, e₇, hunit⟩
          · exact ⟨0, 0, 0, 0, 0, fun hj => absurd hj (by omega)⟩)
  refine ⟨out, v, α, β, ν, ?_, hsh, hbo, hV, hα, hβ, hν, hv0, hb0, hv1o, hpf⟩
  change exec I (.seq (.loop (IExp.const q) _) .skip) st = _
  rw [exec_seq_skip]
  exact hr

/-- G5 with the orthogonalization certificate needed only at the executed steps. -/
private theorem reorth_exec_rounded_loop_aux {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K (OpCount P ι))
    (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (st : St P K (OpCount P ι)) (N q : ℕ) (slot : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (pre : Store P K → Prop) (hpre : pre st.store)
    (hpreFrame : ∀ s s' : Store P K, pre s → (∀ k < 8, s'.shape[k]? = s.shape[k]?) →
      (∀ i, s'.read tag 7 i = s.read tag 7 i) → pre s')
    (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A) pre 1 8
      (IExp.const N * IExp.var t) 0 (mv 8 (IExp.var t)))
    (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit) {η₀ ε₁ ε₂ ε₃ : ℝ}
    (hε : 0 ≤ ε₁ ∧ 0 ≤ ε₂ ∧ 0 ≤ ε₃)
    (horth : ∀ t < q, IsOrthRoutine I dec tag N (t + 1) η₀ ε₁ ε₂ ε₃ (fun _ => True) 1 8 10 0 0
      (orth 8 10 (IExp.var t)))
    (hA : Aᵀ = A) (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ out : St P K (OpCount P ι),
      exec I (lanczosReorthLoop tag (IExp.const N) (IExp.const q) 0 1 2 3 4 5 6 mv orth).run
        st = some out ∧
      out.store.shape = st.store.shape ∧
      (b ≠ 0 → LanczosReorthOutputs out.store dec tag N q A b
        (lanczosImplementationRoundoffBound N (u tag)) τ η₀ ε₁ ε₂ ε₃) := by
  classical
  have hu := hsem.nonneg (p := tag) trivial
  have hε0 := lanczosImplementationRoundoffBound_nonneg N hu
  have hsize : st.store.size = 8 := by
    simpa [Store.shape] using congrArg Array.size hshape
  -- the three scoped allocations
  let st₃ : St P K (OpCount P ι) :=
    ((st.allocate tag (IExp.const N).eval (I.width tag)).allocate tag (2 : IExp ℕ).eval
      (I.width tag)).allocate tag (IExp.const q + 1).eval (I.width tag)
  have sh₃ : st₃.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot), (tag, N), (tag, 2), (tag, q + 1)] := by
    simp only [st₃, St.shape_allocate, hshape, IExp.eval_const, IExp.eval_ofNat, IExp.eval_add]
    rfl
  have rd₃ : ∀ p k i, k < 8 → st₃.store.read p k i = st.store.read p k i := by
    intro p k i hk
    simp only [st₃]
    rw [St.read_allocate_of_lt _ _ _ _ _ _ _ (by simp [St.allocate, hsize]; omega),
      St.read_allocate_of_lt _ _ _ _ _ _ _ (by simp [St.allocate, hsize]; omega),
      St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega)]
  have hpre₃ : pre st₃.store := hpreFrame st.store st₃.store hpre
    (fun k hk => by
      rw [sh₃, hshape]
      interval_cases k <;> rfl)
    (fun i => rd₃ tag 7 i (by omega))
  have hb₃ : ∀ i : Fin N, ∃ w, st₃.store.read tag 0 i = some w ∧ dec tag w = b i := by
    intro i
    rw [rd₃ tag 0 i (by omega)]
    exact hb i
  -- initialization
  let I' : Interp P ι K (OpCount P ι) := { I with charge := fun k => Finsupp.single k 1 }
  obtain ⟨init', v1, hri', shi, fi, hv1, hβ0, hp0, hz0, hunit1, hdir⟩ :=
    reorth_exec_initialize I' hsem hz (fun _ => rfl) tag b st₃ sh₃ hb₃ hsmall
  obtain ⟨init, hri, i1, -, -, -, -, -⟩ := reorth_exec_transfer I' I rfl rfl rfl rfl rfl rfl
    (do
      ins (.lit tag ⟨9, 0⟩ 0)
      ins (.lit tag ⟨3, 0⟩ 0)
      forRange (IExp.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
      nrm2 tag ⟨4, 0⟩ 0 0 (IExp.const N)
      ifThenElse tag .eq ⟨4, 0⟩ ⟨9, 0⟩
        (forRange (IExp.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0))
        (do copyv tag 0 0 1 0 (IExp.const N); rscl tag ⟨4, 0⟩ 1 0 (IExp.const N)) :
          Builder P ι ℕ ℕ Unit).run (a' := st₃) rfl rfl rfl rfl rfl rfl hri'
  rw [i1] at shi fi hv1 hβ0 hp0 hz0
  have hprei : pre init.store := hpreFrame st₃.store init.store hpre₃
    (fun k _ => by rw [shi]) (fun i => fi tag 7 i (by omega) (by omega) (by omega) (by omega)
      (by omega))
  obtain ⟨out₃, v, α, β, ν, hrl, shl, hbl, hVl, hαl, hβl, hνl, hv0, hb0, hv1l, hpf⟩ :=
    reorth_exec_loop I hsem hz tag b pre hpreFrame mv hmv orth horth init v1
      (shi.trans sh₃) hprei
      (fun i => by
        rw [fi tag 0 i (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hb₃ i)
      hv1 hβ0 hp0 hz0 hsmall
  have shl' : out₃.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot), (tag, N), (tag, 2), (tag, q + 1)] :=
    shl.trans (shi.trans sh₃)
  have hsize₃ : out₃.store.size = 11 := by
    simpa [Store.shape] using congrArg Array.size shl'
  let out : St P K (OpCount P ι) :=
    ((out₃.release tag (IExp.const q + 1).eval (I.width tag)).release tag (2 : IExp ℕ).eval
      (I.width tag)).release tag (IExp.const N).eval (I.width tag)
  have rdo : ∀ p k i, k < 8 → out.store.read p k i = out₃.store.read p k i := by
    intro p k i hk
    change Store.read out₃.store.pop.pop.pop p k i = _
    rw [Store.read_pop_of_lt (by simp only [Array.size_pop, hsize₃]; omega),
      Store.read_pop_of_lt (by simp only [Array.size_pop, hsize₃]; omega),
      Store.read_pop_of_lt (by rw [hsize₃]; omega)]
  refine ⟨out, ?_, ?_, ?_⟩
  · -- the scoped program
    have hinit : ExecutionComposable I (do
        ins (.lit tag ⟨9, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (IExp.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
        nrm2 tag ⟨4, 0⟩ 0 0 (IExp.const N)
        ifThenElse tag .eq ⟨4, 0⟩ ⟨9, 0⟩
          (forRange (IExp.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0))
          (do copyv tag 0 0 1 0 (IExp.const N); rscl tag ⟨4, 0⟩ 1 0 (IExp.const N)) :
            Builder P ι ℕ ℕ Unit) :=
      (executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          ((executionComposable_single I (fun _ => rfl)).bind
            ((executionComposable_single I (fun _ => rfl)).bind
              (executionComposable_single I (fun _ => rfl)))))
    have hbody := hinit (fun _ => forRange (IExp.const q) fun j => do
        mv 8 (IExp.var j)
        ins (.un tag .neg ⟨9, 1⟩ ⟨3, IExp.var j⟩)
        axpy tag ⟨9, 1⟩ 5 0 8 0 (IExp.const N)
        dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j) 8 0 (IExp.const N)
        ins (.un tag .neg ⟨9, 1⟩ ⟨2, IExp.var j⟩)
        axpy tag ⟨9, 1⟩ 1 (IExp.const N * IExp.var j) 8 0 (IExp.const N)
        nrm2 tag ⟨6, IExp.var j⟩ 8 0 (IExp.const N)
        orth 8 10 (IExp.var j)
        nrm2 tag ⟨3, IExp.var j + 1⟩ 8 0 (IExp.const N)
        copyv tag 1 (IExp.const N * IExp.var j) 5 0 (IExp.const N)
        ifThenElse tag .eq ⟨3, IExp.var j + 1⟩ ⟨9, 0⟩
          (forRange (IExp.const N) fun i =>
            ins (.lit tag ⟨1, IExp.const N * (IExp.var j + 1) + IExp.var i⟩ 0)) (do
            copyv tag 8 0 1 (IExp.const N * (IExp.var j + 1)) (IExp.const N)
            rscl tag ⟨3, IExp.var j + 1⟩ 1
              (IExp.const N * (IExp.var j + 1)) (IExp.const N))) st₃
    rw [hri, Option.bind_some, hrl] at hbody
    show exec I (.seq (.alloc tag (IExp.const N) _) .skip) st = _
    rw [exec_seq_skip]
    apply exec_alloc_of_exec_eq_some
    apply exec_alloc_of_exec_eq_some
    apply exec_alloc_of_exec_eq_some
    have hs₁ : (st.allocate tag (IExp.const N).eval (I.width tag)).store.size = 9 := by
      simp [St.allocate, hsize]
    have hs₂ : ((st.allocate tag (IExp.const N).eval (I.width tag)).allocate tag
        (2 : IExp ℕ).eval (I.width tag)).store.size = 10 := by
      simp [St.allocate, hsize]
    rw [hsize, hs₁, hs₂]
    exact hbody
  · change Store.shape out₃.store.pop.pop.pop = _
    rw [Store.shape_pop, Store.shape_pop, Store.shape_pop, shl', hshape]
    rfl
  · intro hbne
    choose U W Z Z' Hh hpf' using hpf
    refine ⟨v, α, β, ν, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      rw [rdo tag 0 _ (by omega), show 0 + (i : ℕ) + N * j = i by
        rw [Fin.val_eq_zero j]; ring]
      exact hbl i
    · intro i j
      rw [rdo tag 1 _ (by omega), show 0 + (i : ℕ) + N * j = N * j + i by ring]
      exact hVl j (by omega) i
    · intro j c
      rw [rdo tag 2 _ (by omega), show 0 + (j : ℕ) + q * c = j by
        rw [Fin.val_eq_zero c]; ring]
      exact hαl j j.isLt
    · intro j c
      rw [rdo tag 3 _ (by omega), show 0 + (j : ℕ) + (q + 1) * c = j by
        rw [Fin.val_eq_zero c]; ring]
      exact hβl j (by omega)
    · intro j c
      rw [rdo tag 6 _ (by omega), show 0 + (j : ℕ) + q * c = j by
        rw [Fin.val_eq_zero c]; ring]
      exact hνl j j.isLt
    · rw [hv1l]
      exact hdir hbne
    · intro m hm0 hmq hadm
      have nsr : ∀ x y : Fin N → ℝ, ‖WithLp.toLp 2 (x - y)‖ = ‖WithLp.toLp 2 (y - x)‖ :=
        fun x y => by rw [WithLp.toLp_sub, WithLp.toLp_sub, norm_sub_rev]
      refine ⟨{
        H := A
        v := v
        u := fun n => U (n - 1)
        w := fun n => W (n - 1)
        z := fun n => Z (n - 1)
        z' := fun n => Z' (n - 1)
        α := α
        β := β
        ν := ν
        h := fun n => Hh (n - 1)
        eu := fun n => U (n - 1) - A *ᵥ v n
        ew := fun n => W (n - 1) - (U (n - 1) - β (n - 1) • v (n - 1))
        ez := fun n => Z (n - 1) - (W (n - 1) - α n • v n)
        eα := fun n => α n - v n ⬝ᵥ W (n - 1)
        δ := fun n => β n • v (n + 1) - Z' (n - 1)
        ε := lanczosImplementationRoundoffBound N (u tag)
        τ := τ
        η₀ := η₀
        ε₁ := ε₁
        ε₂ := ε₂
        ε₃ := ε₃
        transpose_H := hA
        ε_nonneg := hε0
        ε_le := hsmall
        ε₁_nonneg := hε.1
        ε₂_nonneg := hε.2.1
        ε₃_nonneg := hε.2.2
        k_pos := hm0
        v_zero := hv0
        β_zero := hb0
        u_eq := fun j _ => by
          show U j = A *ᵥ v (j + 1) + (U j - A *ᵥ v (j + 1))
          abel
        norm_eu_le := fun j hj => by
          show ‖WithLp.toLp 2 (U j - A *ᵥ v (j + 1))‖ ≤ _
          rw [nsr]
          exact (hpf' j (by omega)).1
        w_eq := fun j _ => by
          show W j = U j - β j • v j + (W j - (U j - β j • v j))
          abel
        norm_ew_le := fun j hj => by
          show ‖WithLp.toLp 2 (W j - (U j - β j • v j))‖ ≤ _
          rw [nsr]
          exact (hpf' j (by omega)).2.1
        α_eq := fun j _ => by
          show α (j + 1) = v (j + 1) ⬝ᵥ W j + (α (j + 1) - v (j + 1) ⬝ᵥ W j)
          ring
        abs_eα_le := fun j hj => by
          show |α (j + 1) - v (j + 1) ⬝ᵥ W j| ≤ _
          rw [abs_sub_comm]
          exact (hpf' j (by omega)).2.2.1
        z_eq := fun j _ => by
          show Z j = W j - α (j + 1) • v (j + 1) + (Z j - (W j - α (j + 1) • v (j + 1)))
          abel
        norm_ez_le := fun j hj => by
          show ‖WithLp.toLp 2 (Z j - (W j - α (j + 1) • v (j + 1)))‖ ≤ _
          rw [nsr]
          exact (hpf' j (by omega)).2.2.2.1
        abs_ν_sub_le := fun j hj => (hpf' j (by omega)).2.2.2.2.2.1
        orth_eq := fun j hj => (hpf' j (by omega)).2.2.2.2.2.2.1
        abs_β_sub_le := fun j hj => (hpf' j (by omega)).2.2.2.2.2.2.2.1
        smul_v_eq := fun j _ => by
          show β (j + 1) • v (j + 2) = Z' j + (β (j + 1) • v (j + 1 + 1) - Z' j)
          abel
        norm_δ_le := fun j hj => by
          show ‖WithLp.toLp 2 (β (j + 1) • v (j + 2) - Z' j)‖ ≤ _
          rw [nsr]
          exact (hpf' j (by omega)).2.2.2.2.2.2.2.2.1
        abs_norm_v_sq_sub_one_le := fun j hj1 hj2 => by
          rcases Nat.lt_or_ge j 2 with hj | hj
          · obtain rfl : j = 1 := by omega
            rw [hv1l]
            exact hunit1 hbne
          · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
            have hi : i < m := by omega
            have hf := hpf' i (by omega)
            refine hf.2.2.2.2.2.2.2.2.2 (ne_of_gt ?_)
            exact lt_of_le_of_lt (mul_nonneg hτ.le hf.2.2.2.2.1) (hadm i hi)
        admissible := hadm
        τ_pos := hτ }, rfl, fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl,
        rfl⟩

/-- **Rounded run of the generic loop** (G5): for any product routine family certified by
`NLAlib.Computation.IsMatvecRoutine` (coefficient $\varepsilon\|\mathbf{A}\|_2$,
$\varepsilon$ = `NLAlib.lanczosImplementationRoundoffBound`,
that is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u$) and any
orthogonalization routine family certified by `NLAlib.Computation.IsOrthRoutine` at $(\eta_0,
\varepsilon_1, \varepsilon_2,
\varepsilon_3)$, the loop `NLAlib.lanczosReorthLoop` succeeds from a state with the seven
declared buffers and the matrix slot $7$, keeps the shape, and its outputs satisfy
`NLAlib.LanczosReorthOutputs` for every $\tau > 0$. The scheme enters only through its
certificate. No printed source; `docs/design/Krylov-LanczosReorth.md` §1.4.
Proof: follow `NLAlib.LanczosImplementation.exec_rounded_compiled` (files
`NLAlib/Krylov/Processes/LanczosProgramRounded*.lean` on main: initialization, step, prefix, run,
commit) with a
step that has two more phases: after the second `axpy`, the `nrm2` of $\nu$
(`NLAlib.Computation.IsRelErrSem.exec_nrm2_abs_norm_sub_le`
type bound $|\nu - \|\mathbf{z}\|| \le \varepsilon\|\mathbf{z}\|$), then `horth t`
(`IsOrthRoutine.run`
with the basis columns $0..t$ as $\mathbf{V}$, `work` as $\mathbf{w}$, `coef` as $\mathbf{h}$; its
frame keeps the basis and the coefficients), then main's `nrm2`/zero test/`rscl` normalization
lemmas applied to $\mathbf{z}'$. The run of an admissible prefix is assembled field by field
(`orth_eq` from the certificate, the rest as in main's `NLAlib.LanczosRun` construction,
`abs_norm_v_sq_sub_one_le` for $j \le m + 1$ from $\beta_j > 0$). Composability of
`mv`/`orth` from the certificates' `composable` fields; `hpre` transports to every intermediate
store, including the 11-buffer ones after `work`, `scalars`, `coef` are allocated (allocation only
appends buffers, so the first 8 shape entries are unchanged), because only
buffers $1..6, 8..10$ are written. H, about 1200 lines; intermediate lemmas: the store invariant
(a `NLAlib.LanczosImplementation.StoreContext` with the basis prefix and `nu`), one step, the
prefix induction, the
initialization (reused), and the assembly of `NLAlib.LanczosReorthRun`. -/
theorem exec_rounded_loop {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K (OpCount P ι))
    (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (st : St P K (OpCount P ι)) (N q : ℕ) (slot : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (pre : Store P K → Prop) (hpre : pre st.store)
    (hpreFrame : ∀ s s' : Store P K, pre s → (∀ k < 8, s'.shape[k]? = s.shape[k]?) →
      (∀ i, s'.read tag 7 i = s.read tag 7 i) → pre s')
    (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A) pre 1 8
      (IExp.const N * IExp.var t) 0 (mv 8 (IExp.var t)))
    (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit) {η₀ ε₁ ε₂ ε₃ : ℝ}
    (hε : 0 ≤ ε₁ ∧ 0 ≤ ε₂ ∧ 0 ≤ ε₃)
    (horth : ∀ t : ℕ, IsOrthRoutine I dec tag N (t + 1) η₀ ε₁ ε₂ ε₃ (fun _ => True) 1 8 10 0 0
      (orth 8 10 (IExp.var t)))
    (hA : Aᵀ = A) (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ out : St P K (OpCount P ι),
      exec I (lanczosReorthLoop tag (IExp.const N) (IExp.const q) 0 1 2 3 4 5 6 mv orth).run
        st = some out ∧
      out.store.shape = st.store.shape ∧
      (b ≠ 0 → LanczosReorthOutputs out.store dec tag N q A b
        (lanczosImplementationRoundoffBound N (u tag)) τ η₀ ε₁ ε₂ ε₃) := by
  exact reorth_exec_rounded_loop_aux I tag hsem hz st N q slot A b hshape hb pre hpre hpreFrame
    mv hmv orth hε (fun t _ => horth t) hA hsmall hτ

private theorem reorth_cgsPassBound_mono (N : ℕ) {j k : ℕ} (hjk : j ≤ k) {u η₀ : ℝ}
    (hu : 0 ≤ u) (hη₀ : 0 ≤ η₀) : cgsPassBound N j u η₀ ≤ cgsPassBound N k u η₀ := by
  rw [cgsPassBound_def, cgsPassBound_def]
  have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hs : Real.sqrt ((j : ℝ) + 1) ≤ Real.sqrt ((k : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hn : ((N + j + 2 : ℕ) : ℝ) ≤ ((N + k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have h1 : 0 ≤ 2 * (1 + η₀) := by linarith
  have h2 : 0 ≤ Real.sqrt ((j : ℝ) + 1) := Real.sqrt_nonneg _
  have h3 : (0 : ℝ) ≤ ((N + j + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul (mul_le_mul_of_nonneg_left hs h1) hn h3
    (mul_nonneg h1 (Real.sqrt_nonneg _))
  exact mul_le_mul_of_nonneg_right this hu

/-- The CGS2 call at step $t < q$ ($t + 1$ columns), certified at the parameters of $q$
columns. -/
private theorem reorth_isOrthRoutine_cgs2 {C : Type} [AddMonoid C] {u : P → ℝ}
    {dec : P → K → ℝ} (I : Interp P ι K C)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q t : ℕ} (ht : t < q) {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100)
    (hu : ((N + q + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100)
    (hc₁ : cgsPassBound N q (u tag) η₀ ≤ 1 / 100) :
    IsOrthRoutine I dec tag N (t + 1) η₀ (2 * cgsPassBound N q (u tag) η₀)
      (3 * cgsPassBound N q (u tag) η₀) (2 * (η₀ + cgsPassBound N q (u tag) η₀) ^ 2)
      (fun _ => True) 1 8 10 0 0 (cgs2 tag (IExp.const N) (IExp.var t + 1) 1 8 0 10 0) := by
  have hu0 := hsem.nonneg (p := tag) trivial
  have hmono := reorth_cgsPassBound_mono N (show t + 1 ≤ q by omega) hu0 hη₀
  have hc0 : 0 ≤ cgsPassBound N (t + 1) (u tag) η₀ := by
    rw [cgsPassBound_def]; positivity
  have hO := hsem.isOrthRoutine_cgs2 I hz tag (N := N) (j := t + 1) (IExp.const N)
    (IExp.var t + 1) rfl rfl 1 8 10 0 0 hη₀ hη
    ((mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) hu0).trans hu)
    (hmono.trans hc₁)
  refine ⟨hO.composable, fun st V w hp hV hw hwc hhc h1 h2 h3 => ?_⟩
  obtain ⟨out, W, Hw, mid, hr, hw1, hw2, he⟩ := hO.run st V w hp hV hw hwc hhc h1 h2 h3
  have h₃ : 2 * (η₀ + cgsPassBound N (t + 1) (u tag) η₀) ^ 2 ≤
      2 * (η₀ + cgsPassBound N q (u tag) η₀) ^ 2 := by
    have : η₀ + cgsPassBound N (t + 1) (u tag) η₀ ≤ η₀ + cgsPassBound N q (u tag) η₀ := by
      linarith
    have h0 : 0 ≤ η₀ + cgsPassBound N (t + 1) (u tag) η₀ := by linarith
    nlinarith
  refine ⟨out, W, Hw, mid, hr, hw1, hw2, fun hV => (he.residual hV).trans
    (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)), fun hV => (he.orth hV).trans
    (add_le_add (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right h₃ (norm_nonneg _)))⟩

/-- **Rounded run of the stored-matrix CGS2 tree** (G6): under the standard model, for symmetric
decoded $\mathbf{A}$ (ROM words) and $\mathbf{b} \ne \mathbf{0}$, the compiled tree succeeds,
keeps the shape and its outputs satisfy `NLAlib.LanczosReorthOutputs` with the CGS2 parameters at
$q$ columns, $c_1$ = `NLAlib.cgsPassBound` $N\,q\,u\,\eta_0$
= <!-- value cgsPassBound N q u \eta_0 -->$2(1+\eta_0)\sqrt{q+1}\,(N+q+2)\,u$:
$(\eta_0, 2c_1, 3c_1, 2(\eta_0 + c_1)^2)$. No printed source.
Proof: `NLAlib.lanczosReorthProg.toStmt_compiled`; the ROM load into slot $7$ as in main's
`NLAlib/Krylov/Processes/LanczosProgramRoundedInitialization.lean` (decoded matrix `HoldsDecoded …
7 0 A`, the `pre` of G5; it depends only on reads of buffer $7$, so it meets
`hpreFrame`); then
`NLAlib.LanczosReorthImplementation.exec_rounded_loop` with `mv` the `gemv` call, certified by
`NLAlib.Computation.IsRelErrSem.isMatvecRoutine_gemv` (its coefficient $\gamma_N\sqrt
N\|\mathbf{A}\|
\le \varepsilon\|\mathbf{A}\|$, `IsMatvecRoutine.mono`), and `orth` the `NLAlib.cgs2` call at
$t + 1$ columns, certified by `NLAlib.Computation.IsRelErrSem.isOrthRoutine_cgs2` and made uniform
in
$t$ by monotonicity of `NLAlib.cgsPassBound` in $j$ (`IsOrthRoutine` parameters enlarged with
`NLAlib.IsOrthErr.mono` inside the certificate). L, about 200 lines. -/
theorem exec_rounded_compiled {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K (OpCount P ι))
    (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (hc : ∀ k, I.charge k = Finsupp.single k 1)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (values : ℕ → K)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hrom : ∀ i < N * N, I.rom i = some (values i))
    (hdecode : ∀ i j : Fin N, dec tag (values (N * j + i)) = A i j) (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) (hbnz : b ≠ 0)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100) (hu : ((N + q + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100)
    (hc₁ : cgsPassBound N q (u tag) η₀ ≤ 1 / 100) {τ : ℝ} (hτ : 0 < τ) :
    ∃ out : St P K (OpCount P ι),
      (lanczosReorthProg.compiled tag).exec I N ![q] st = some out ∧
      out.store.shape = st.store.shape ∧
      LanczosReorthOutputs out.store dec tag N q A b
        (lanczosImplementationRoundoffBound N (u tag)) τ η₀ (2 * cgsPassBound N q (u tag) η₀)
        (3 * cgsPassBound N q (u tag) η₀) (2 * (η₀ + cgsPassBound N q (u tag) η₀) ^ 2) := by
  classical
  have hu0 := hsem.nonneg (p := tag) trivial
  have hsize : st.store.size = 7 := by
    simpa [Store.shape] using congrArg Array.size hshape
  let st₁ := st.allocate tag (IExp.const N * IExp.const N).eval (I.width tag)
  have sh₁ : st₁.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, N * N)] := by
    simp only [st₁, St.shape_allocate, hshape, IExp.eval_mul, IExp.eval_const]
    rfl
  obtain ⟨loaded, erom, shrom, reads, frame⟩ :=
    exec_forRange_rom I tag st₁ (IExp.const N * IExp.const N) 7 values
      (by rw [sh₁]; rfl) (by simpa only [IExp.eval_mul, IExp.eval_const] using hrom)
  let mid : St P K (OpCount P ι) :=
    { st₁ with store := loaded, cnt := st₁.cnt + (N * N) • I.charge (.rom tag) }
  have shm : mid.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, N * N)] := shrom.trans sh₁
  have hbm (i : Fin N) : ∃ w, mid.store.read tag 0 i = some w ∧ dec tag w = b i := by
    change ∃ w, loaded.read tag 0 i = some w ∧ dec tag w = b i
    rw [frame tag 0 i (by omega), St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega)]
    exact hb i
  have hmA : HoldsDecoded mid.store dec tag 7 0 A := by
    intro i j
    refine ⟨values (N * j + i), ?_, hdecode i j⟩
    simpa only [zero_add, Nat.add_comm] using reads (N * j + i) (by
      change N * (j : ℕ) + (i : ℕ) < N * N
      calc
        N * (j : ℕ) + (i : ℕ) < N * (j : ℕ) + N := Nat.add_lt_add_left i.isLt _
        _ = N * ((j : ℕ) + 1) := by ring
        _ ≤ N * N := Nat.mul_le_mul_left N j.isLt)
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N hu0 hsmall
  have hn : (N : ℝ) * u tag < 1 := by
    have hs := hwin.1
    push_cast at hs
    nlinarith
  have hc0 : 0 ≤ cgsPassBound N q (u tag) η₀ := by
    rw [cgsPassBound_def]; positivity
  obtain ⟨out₁, hrun, shout, hout⟩ := reorth_exec_rounded_loop_aux I tag hsem hz mid N q (N * N)
    A b shm hbm (fun s => HoldsDecoded s dec tag 7 0 A) hmA
    (fun s s' hs _ h7 i j => by rw [h7]; exact hs i j)
    (fun work j => gemv tag (IExp.const N) (IExp.const N) 7 0 1 (IExp.const N * j) work 0)
    (fun t => (hsem.isMatvecRoutine_gemv I tag hz N A 7 1 8 0 (IExp.const N * IExp.var t) 0
      hn (by omega) (by omega)).mono (mul_le_mul_of_nonneg_right
        (roundingFactor_mul_sqrt_le_lanczosImplementationRoundoffBound N hu0 hsmall)
        (specNorm_nonneg A)))
    (fun work coef j => cgs2 tag (IExp.const N) (j + 1) 1 work 0 coef 0)
    ⟨by linarith, by linarith, by positivity⟩
    (fun t ht => reorth_isOrthRoutine_cgs2 I hsem hz tag ht hη₀ hη hu hc₁) hA hsmall hτ
  have hsize₁ : out₁.store.size = 8 := by
    simpa [Store.shape] using congrArg Array.size (shout.trans shm)
  let out := out₁.release tag (IExp.const N * IExp.const N).eval (I.width tag)
  have rdo : ∀ p k i, k < 7 → out.store.read p k i = out₁.store.read p k i := by
    intro p k i hk
    change Store.read out₁.store.pop p k i = _
    rw [Store.read_pop_of_lt (by rw [hsize₁]; omega)]
  refine ⟨out, ?_, ?_, ?_⟩
  · rw [Prog.exec_eq_exec_toStmt, lanczosReorthProg.toStmt_compiled]
    show exec I (.seq (.alloc tag (IExp.const N * IExp.const N) _) .skip) st = _
    rw [exec_seq_skip]
    apply exec_alloc_of_exec_eq_some
    rw [hsize]
    have erom' : exec I (forRange (IExp.const N * IExp.const N) fun i =>
        stmt (.rom tag ⟨7, .var i⟩ (.var i)) : Builder P ι ℕ ℕ Unit).run st₁ = some mid := by
      change exec I (.seq (.loop (IExp.const N * IExp.const N)
        (fun i => .seq (.rom tag ⟨7, .var i⟩ (.var i)) .skip)) .skip) st₁ = _
      rw [exec_seq_skip]
      simpa only [IExp.eval_mul, IExp.eval_const] using erom
    change exec I (do
      forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨7, .var i⟩ (.var i))
      lanczosReorthLoop tag (IExp.const N) (IExp.const q) 0 1 2 3 4 5 6
        (fun work j => gemv tag (IExp.const N) (IExp.const N) 7 0 1 (IExp.const N * j) work 0)
        (fun work coef j => cgs2 tag (IExp.const N) (j + 1) 1 work 0 coef 0) :
          Builder P ι ℕ ℕ Unit).run st₁ = some out₁
    rw [exec_run_bind I (b := forRange (IExp.const N * IExp.const N) fun i =>
      stmt (.rom tag ⟨7, .var i⟩ (.var i))) (fun _ => rfl), erom', Option.bind_some]
    exact hrun
  · change Store.shape out₁.store.pop = _
    rw [Store.shape_pop, shout, shm, hshape]
    rfl
  · obtain ⟨v, α, β, ν, h0, h1, h2, h3, h6, hδ, hm⟩ := hout hbnz
    refine ⟨v, α, β, ν, fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_,
      fun i j => ?_, hδ, hm⟩
    · rw [rdo tag 0 _ (by omega)]; exact h0 i j
    · rw [rdo tag 1 _ (by omega)]; exact h1 i j
    · rw [rdo tag 2 _ (by omega)]; exact h2 i j
    · rw [rdo tag 3 _ (by omega)]; exact h3 i j
    · rw [rdo tag 6 _ (by omega)]; exact h6 i j

/-- **Rounded run of the matrix-free CGS2 tree** (G6o): as
`NLAlib.LanczosReorthImplementation.exec_rounded_compiled` with an oracle of accuracy
$\eta\|\mathbf{A}\|_2$, $\eta \le \varepsilon$ (`NLAlib.Computation.IsMatvecErr`), and no ROM.
Pattern: `NLAlib.LanczosOracleImplementation.exec_rounded_compiled`.
Proof: `NLAlib.lanczosReorthOracleProg.toStmt_compiled`; the empty slot $7$ (`pre = True`); then
`NLAlib.LanczosReorthImplementation.exec_rounded_loop` with `mv` the `apply` call certified by
`NLAlib.Computation.IsMatvecErr.isMatvecRoutine` (mono to $\varepsilon\|\mathbf{A}\|$) and `orth`
as in
G6. M, about 100 lines. -/
theorem exec_rounded_oracle_compiled {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P) (o : ι)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (st : St P K (OpCount P ι)) (N q : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    {η : ℝ} (hmv : IsMatvecErr I o dec tag A (η * specNorm A))
    (hηmv : η ≤ lanczosImplementationRoundoffBound N (u tag)) (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) (hbnz : b ≠ 0)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100) (hu : ((N + q + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100)
    (hc₁ : cgsPassBound N q (u tag) η₀ ≤ 1 / 100) {τ : ℝ} (hτ : 0 < τ) :
    ∃ out : St P K (OpCount P ι),
      (lanczosReorthOracleProg.compiled tag o).exec I N ![q] st = some out ∧
      out.store.shape = st.store.shape ∧
      LanczosReorthOutputs out.store dec tag N q A b
        (lanczosImplementationRoundoffBound N (u tag)) τ η₀ (2 * cgsPassBound N q (u tag) η₀)
        (3 * cgsPassBound N q (u tag) η₀) (2 * (η₀ + cgsPassBound N q (u tag) η₀) ^ 2) := by
  classical
  have hu0 := hsem.nonneg (p := tag) trivial
  have hsize : st.store.size = 7 := by
    simpa [Store.shape] using congrArg Array.size hshape
  let st₁ := st.allocate tag (0 : IExp ℕ).eval (I.width tag)
  have sh₁ : st₁.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, 0)] := by
    simp only [st₁, St.shape_allocate, hshape, IExp.eval_ofNat]
    rfl
  have hb₁ (i : Fin N) : ∃ w, st₁.store.read tag 0 i = some w ∧ dec tag w = b i := by
    rw [St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega)]
    exact hb i
  have hc0 : 0 ≤ cgsPassBound N q (u tag) η₀ := by
    rw [cgsPassBound_def]; positivity
  obtain ⟨out₁, hrun, shout, hout⟩ := reorth_exec_rounded_loop_aux I tag hsem hz st₁ N q 0
    A b sh₁ hb₁ (fun _ => True) trivial (fun _ _ _ _ _ => trivial)
    (fun work j => stmt (.apply o tag work 0 1 (IExp.const N * j) 1))
    (fun t => (hmv.isMatvecRoutine 1 8 (IExp.const N * IExp.var t) 0 (by omega)).mono
      (mul_le_mul_of_nonneg_right hηmv (specNorm_nonneg A)))
    (fun work coef j => cgs2 tag (IExp.const N) (j + 1) 1 work 0 coef 0)
    ⟨by linarith, by linarith, by positivity⟩
    (fun t ht => reorth_isOrthRoutine_cgs2 I hsem hz tag ht hη₀ hη hu hc₁) hA hsmall hτ
  have hsize₁ : out₁.store.size = 8 := by
    simpa [Store.shape] using congrArg Array.size (shout.trans sh₁)
  let out := out₁.release tag (0 : IExp ℕ).eval (I.width tag)
  have rdo : ∀ p k i, k < 7 → out.store.read p k i = out₁.store.read p k i := by
    intro p k i hk
    change Store.read out₁.store.pop p k i = _
    rw [Store.read_pop_of_lt (by rw [hsize₁]; omega)]
  refine ⟨out, ?_, ?_, ?_⟩
  · rw [Prog.exec_eq_exec_toStmt, lanczosReorthOracleProg.toStmt_compiled]
    show exec I (.seq (.alloc tag (0 : IExp ℕ) _) .skip) st = _
    rw [exec_seq_skip]
    apply exec_alloc_of_exec_eq_some
    exact hrun
  · change Store.shape out₁.store.pop = _
    rw [Store.shape_pop, shout, sh₁, hshape]
    rfl
  · obtain ⟨v, α, β, ν, h0, h1, h2, h3, h6, hδ, hm⟩ := hout hbnz
    refine ⟨v, α, β, ν, fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_,
      fun i j => ?_, hδ, hm⟩
    · rw [rdo tag 0 _ (by omega)]; exact h0 i j
    · rw [rdo tag 1 _ (by omega)]; exact h1 i j
    · rw [rdo tag 2 _ (by omega)]; exact h2 i j
    · rw [rdo tag 3 _ (by omega)]; exact h3 i j
    · rw [rdo tag 6 _ (by omega)]; exact h6 i j

/-- **The program-level backward model** (G7): in the setting of
`NLAlib.LanczosReorthImplementation.exec_rounded_compiled`, every admissible prefix of $m$ steps
whose run satisfies the fixed-point condition has computed tridiagonal equal to the exact Lanczos
tridiagonal of $(\mathbf{H}', \mathbf{b})$ for a symmetric $\mathbf{H}'$ within
backwardRadius $+ 3\|\mathbf{A}\|_2(3\varepsilon + 2\sqrt{3(m+1)}\,\mu)$ of $\mathbf{A}$ in
Frobenius norm. No printed source; [Paige1970] in substance.
Proof: `NLAlib.LanczosReorthImplementation.exec_rounded_compiled`, unfold
`NLAlib.LanczosReorthOutputs` at $m$, then `NLAlib.LanczosReorthRun.exists_pure_backward` with
$\delta_b = 3\varepsilon$. S, about 30 lines. -/
theorem exec_rounded_compiled_backward {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (hc : ∀ k, I.charge k = Finsupp.single k 1)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (values : ℕ → K)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hrom : ∀ i < N * N, I.rom i = some (values i))
    (hdecode : ∀ i j : Fin N, dec tag (values (N * j + i)) = A i j) (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) (hbnz : b ≠ 0)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100) (hu : ((N + q + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100)
    (hc₁ : cgsPassBound N q (u tag) η₀ ≤ 1 / 100) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ out : St P K (OpCount P ι),
      (lanczosReorthProg.compiled tag).exec I N ![q] st = some out ∧
      ∃ (α β ν : ℕ → ℝ),
        HoldsDecoded out.store dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => α ((j : ℕ) + 1)) ∧
        HoldsDecoded out.store dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => β j) ∧
        HoldsDecoded out.store dec tag 6 0 (fun (j : Fin q) (_ : Fin 1) => ν ((j : ℕ) + 1)) ∧
        ∀ m, 0 < m → m ≤ q → (∀ j < m, τ * ν (j + 1) < β (j + 1)) →
          ∃ L : LanczosReorthRun N m, L.H = A ∧ (∀ j ≤ m, L.α j = α j ∧ L.β j = β j) ∧
            (L.recLevel ≤ 1 / 100 →
              Real.sqrt (3 * ((m : ℝ) + 1)) * L.orthLevel ≤ L.η₀ →
              ∃ H' : Matrix (Fin N) (Fin N) ℝ, H'ᵀ = H' ∧
                frobNorm (H' - A) ≤ L.backwardRadius + 3 * specNorm A *
                  (3 * lanczosImplementationRoundoffBound N (u tag) +
                    2 * Real.sqrt (3 * ((m : ℝ) + 1)) * L.orthLevel) ∧
                lanczosTridiagonal H' b m = L.toLanczosData.tridiagonal) := by
  obtain ⟨out, hexec, -, hout⟩ := exec_rounded_compiled I tag hsem hz hc st N q A b values hshape
    hb hrom hdecode hA hsmall hbnz hη₀ hη hu hc₁ hτ
  obtain ⟨v, α, β, ν, -, -, h2, h3, h6, hδ, hm⟩ := hout
  refine ⟨out, hexec, α, β, ν, h2, h3, h6, fun m hm0 hmq hadm => ?_⟩
  obtain ⟨L, hH, hv, hcoef, -, hLτ, hLη, -⟩ := hm m hm0 hmq hadm
  refine ⟨L, hH, fun j hj => ⟨(hcoef j hj).1, (hcoef j hj).2.1⟩, fun hrec hsm => ?_⟩
  have hδL : ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - L.v 1)‖ ≤ 3 *
      lanczosImplementationRoundoffBound N (u tag) := by
    rw [hv 1 le_rfl (by omega)]
    exact hδ
  obtain ⟨H', h1, h2', h3'⟩ := L.exists_pure_backward (hLη ▸ hη) hsm hrec
    (hLτ ▸ hτ1) hbnz hδL
  refine ⟨H', h1, ?_, h3'⟩
  rw [hH] at h2'
  exact h2'

/-- **The program-level interlacing headline** (G8): in the setting of
`NLAlib.LanczosReorthImplementation.exec_rounded_compiled_backward`, on every admissible prefix
with the fixed-point condition the computed Ritz values interlace the eigenvalues of
$\mathbf{A}$ up to backwardRadius:
$\lambda_{i+N-m}(\mathbf{A}) - e \le \theta_i \le \lambda_i(\mathbf{A}) + e$. No printed source.
Proof: `NLAlib.LanczosReorthImplementation.exec_rounded_compiled`, unfold the outputs at $m$, then
`NLAlib.LanczosReorthRun.eigenvalue_tridiagonal_le_add` and
`NLAlib.LanczosReorthRun.eigenvalue_sub_le_eigenvalue_tridiagonal` (the run's parameters satisfy
$\eta_0 \le 1/100$ and $\tau \le 1$ by the hypotheses). S, about 30 lines. -/
theorem exec_rounded_compiled_interlacing {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (hc : ∀ k, I.charge k = Finsupp.single k 1)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (values : ℕ → K)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hrom : ∀ i < N * N, I.rom i = some (values i))
    (hdecode : ∀ i j : Fin N, dec tag (values (N * j + i)) = A i j) (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) (hbnz : b ≠ 0)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100) (hu : ((N + q + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100)
    (hc₁ : cgsPassBound N q (u tag) η₀ ≤ 1 / 100) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ out : St P K (OpCount P ι),
      (lanczosReorthProg.compiled tag).exec I N ![q] st = some out ∧
      ∃ (α β ν : ℕ → ℝ),
        HoldsDecoded out.store dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => α ((j : ℕ) + 1)) ∧
        HoldsDecoded out.store dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => β j) ∧
        HoldsDecoded out.store dec tag 6 0 (fun (j : Fin q) (_ : Fin 1) => ν ((j : ℕ) + 1)) ∧
        ∀ m, 0 < m → m ≤ q → (∀ j < m, τ * ν (j + 1) < β (j + 1)) →
          ∃ L : LanczosReorthRun N m, L.H = A ∧ (∀ j ≤ m, L.α j = α j ∧ L.β j = β j) ∧
            (L.recLevel ≤ 1 / 100 →
              Real.sqrt (3 * ((m : ℝ) + 1)) * L.orthLevel ≤ L.η₀ →
              ∀ i < m, eigenvalue A (i + (N - m)) - L.backwardRadius ≤
                  eigenvalue L.toLanczosData.tridiagonal i ∧
                eigenvalue L.toLanczosData.tridiagonal i ≤ eigenvalue A i + L.backwardRadius) := by
  obtain ⟨out, hexec, -, hout⟩ := exec_rounded_compiled I tag hsem hz hc st N q A b values hshape
    hb hrom hdecode hA hsmall hbnz hη₀ hη hu hc₁ hτ
  obtain ⟨v, α, β, ν, -, -, h2, h3, h6, -, hm⟩ := hout
  refine ⟨out, hexec, α, β, ν, h2, h3, h6, fun m hm0 hmq hadm => ?_⟩
  obtain ⟨L, hH, -, hcoef, -, hLτ, hLη, -⟩ := hm m hm0 hmq hadm
  refine ⟨L, hH, fun j hj => ⟨(hcoef j hj).1, (hcoef j hj).2.1⟩, fun hrec hsm i hi => ?_⟩
  have hlo := L.eigenvalue_sub_le_eigenvalue_tridiagonal (hLη ▸ hη) hsm hrec (hLτ ▸ hτ1) hi
  have hhi := L.eigenvalue_tridiagonal_le_add (hLη ▸ hη) hsm hrec (hLτ ▸ hτ1) hi
  rw [hH] at hlo hhi
  exact ⟨hlo, hhi⟩

end LanczosReorthImplementation

end NLAlib
