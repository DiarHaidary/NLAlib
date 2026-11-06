/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Contract

/-!
# Exact integer literals and tape roundings (scaffold)

Statements for `NLAlib/Computation/Contract.lean` (stage COMPDYN S1b and M2, design note
`docs/design/Computation-DynamicPrograms.md`, §4.1, §4.5 and "S1 implementation status"): exact
arithmetic has exact integer literals at every bound, the clause is monotone in the bound, a size
written by `litIdx` reads back exactly, and the exact rounding of the tape meets the tape-rounding
contract.

## Main results

* `NLAlib.Computation.isExactIntLit_exactSem`: exact arithmetic.
* `NLAlib.Computation.IsExactIntLit.mono`: a smaller bound.
* `NLAlib.Computation.IsExactIntLit.exists_exec_litIdx`: a size written as a literal decodes to
  itself.
* `NLAlib.Computation.isTapeRounding_id`: the exact rounding of the tape.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P K : Type}

/-- **Exact arithmetic has exact integer literals**: `NLAlib.Computation.exactSem` over
$\mathbb{R}$, with the identity decoding, meets `NLAlib.Computation.IsExactIntLit` at every bound
$B$. No printed source.
Proof: `intro p k _; exact ⟨(k : ℝ), by simp [exactSem], rfl⟩` (the literal is `((k : ℚ) : ℝ)`,
`Rat.cast_natCast`). S, about 2 lines. -/
theorem isExactIntLit_exactSem (B : ℕ) :
    IsExactIntLit (P := P) (fun _ x => x) (exactSem (𝕜 := ℝ)) B := by
  intro p k _
  exact ⟨(k : ℝ), by simp [exactSem], rfl⟩

/-- **A smaller bound**: exact integer literals up to $B$ are exact up to every $B' \le B$.
No printed source.
Proof: `fun p k hk => h p k (hk.trans hB)`. S, 1 line. -/
theorem IsExactIntLit.mono {dec : P → K → ℝ} {sem : ScalarSem P K} {B B' : ℕ}
    (h : IsExactIntLit dec sem B) (hB : B' ≤ B) : IsExactIntLit dec sem B' :=
  fun p k hk => h p k (hk.trans hB)

variable [DecidableEq P]

/-- **A size written as a literal decodes to itself**: under exact integer literals up to $B$,
if the cell $(b, i)$ can be written at tag `p` and the index expression $e$ has value at most $B$,
the instruction `litIdx p (b, i) e` succeeds, and the cell then reads a word that decodes to the
value of $e$. No printed source.
Proof: `obtain ⟨z, hz, hdz⟩ := h p e.eval he`; `obtain ⟨s', hs'⟩` from
`Store.exists_write_eq_some_of_shape_eq` (or directly the hypothesis `hw` at `z`); the run is
`simp only [Instr.run, hz, Option.bind_some, hs', Option.map_some]`, and the read is
`Store.read_of_write_eq_some hs'`. S, about 8 lines. -/
theorem IsExactIntLit.exists_exec_litIdx {dec : P → K → ℝ} {sem : ScalarSem P K} {B : ℕ}
    (h : IsExactIntLit dec sem B) (tape : Dist → ℕ → K) (s : Store P K) (pos : Dist → ℕ)
    (p : P) (b i : ℕ) (e : IExp ℕ) (he : e.eval ≤ B)
    (hw : ∀ v : K, ∃ s', s.write p b i v = some s') :
    ∃ r z, (Instr.litIdx p ⟨b, .const i⟩ e).run sem tape s pos = some r ∧
      r.1.read p b i = some z ∧ dec p z = e.eval ∧ r.2 = pos := by
  obtain ⟨z, hz, hdz⟩ := h p e.eval he
  obtain ⟨s', hs'⟩ := hw z
  refine ⟨(s', pos), z, ?_, Store.read_of_write_eq_some hs', hdz, rfl⟩
  simp only [Instr.run, hz, Option.bind_some, hs', Option.map_some, IExp.eval]

omit [DecidableEq P] in
/-- **The exact rounding of the tape**: storing each ideal draw as itself in $\mathbb{R}$ meets
`NLAlib.Computation.IsTapeRounding` with the identity decoding, for every unit roundoff $u$,
floor $\tau$, range $\Omega$ and constants $c$ with $c(d)\,u \ge 0$. No printed source.
Proof: `refine ⟨fun d i x _ => ?_, fun i x hx => hx⟩`; `simp only [sub_self, abs_zero]` and
`mul_nonneg (hc d) (le_max_of_le_left (abs_nonneg x))`. S, about 3 lines. -/
theorem isTapeRounding_id (p : P) (u τ Ω : ℝ) (c : Dist → ℝ) (hc : ∀ d, 0 ≤ c d * u) :
    IsTapeRounding (fun _ x => x) p u τ Ω c (fun _ _ x => x) := by
  refine ⟨fun d i x _ => ?_, fun i x hx => hx⟩
  simp only [sub_self, abs_zero]
  exact mul_nonneg (hc d) (le_max_of_le_left (abs_nonneg x))

end NLAlib.Computation
