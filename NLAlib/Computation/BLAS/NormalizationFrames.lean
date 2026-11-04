/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.Frames

/-!
# Actual copied-vector normalization and storage frames

A computed norm may be followed by a comparison or a framed update before the source is
copied and divided into a different vector window. The primitive executions, norm-word
provenance and storage frames retain this operation order. No combined replacement program
or arithmetic model is defined.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_copyv_rscl`: actual copied-vector normalization.
* `NLAlib.Computation.IsRelErrSem.exec_copyv_rscl_of_nrm2_execution`: norm-word provenance.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

private theorem normalized_output_bounds {n : ℕ} {u q : ℝ} {x y : Fin n → ℝ}
    (hu : 0 ≤ u) (hn : (n + 1 : ℕ) * u < 1) (hg : roundingFactor (n + 1) u < 1)
    (hq : 0 < q)
    (hscale : |‖WithLp.toLp 2 x‖ - q| ≤ roundingFactor (n + 1) u * ‖WithLp.toLp 2 x‖)
    (hrel : ∀ i, RelErr u (x i) (q * y i)) :
    ‖WithLp.toLp 2 (x - q • y)‖ ≤ u * ‖WithLp.toLp 2 x‖ ∧
    |‖WithLp.toLp 2 y‖ ^ 2 - 1| ≤ normalizationRoundingFactor n u ∧
    ‖WithLp.toLp 2 (x - q • (‖WithLp.toLp 2 y‖⁻¹ • y))‖ ≤
      (2 * u + roundingFactor (n + 1) u) * ‖WithLp.toLp 2 x‖ := by
  have hpos : 0 < ‖WithLp.toLp 2 x‖ := by
    by_contra h
    have hx : ‖WithLp.toLp 2 x‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hx, zero_sub, abs_neg, abs_of_pos hq, mul_zero] at hscale
    linarith
  exact ⟨RelErr.norm_sub_le hu hrel,
    RelErr.abs_norm_sq_sub_one_le hu hn hg hpos hscale hrel,
    RelErr.norm_sub_smul_inv_norm_le hu hq.le hscale hrel⟩

variable {P ι K : Type} [DecidableEq P] {u : P → ℝ} {dec : P → K → ℝ}

/-- Copy the actual initialized source words and execute componentwise division by a
positive stored norm. The norm error premise is numerical algebra for the supplied scale;
the provenance theorem below derives it from an actual preceding nrm2 execution. The
returned words, complete destination-window frame and normalization errors are conclusions. -/
theorem IsRelErrSem.exec_copyv_rscl (I : Interp P ι K (OpCount P ι)) (p : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (st : St P K (OpCount P ι))
    (a : Cell ℕ ℕ) (x y : ℕ) (xo yo n : IExp ℕ) (av : ℝ) (xs : ℕ → ℝ)
    (hn : (n.eval + 1 : ℕ) * u p < 1) (hg : roundingFactor (n.eval + 1) (u p) < 1)
    (hav : 0 < av)
    (hscale : |‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ - av| ≤
      roundingFactor (n.eval + 1) (u p) * ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖)
    (ha : ∃ w, st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hxy : x ≠ y) (hay : a.buf ≠ y)
    (hy : ∀ i < n.eval, ∃ len, st.store.shape[y]? = some (p, len) ∧ yo.eval + i < len) :
    ∃ (copied out : St P K (OpCount P ι)) (W : ℕ → K),
      exec I (copyv p x xo y yo n).run st = some copied ∧
      exec I (rscl p a y yo n).run copied = some out ∧
      exec I (do copyv p x xo y yo n; rscl p a y yo n).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin n.eval, out.store.read p y (yo.eval + i) = some (W i)) ∧
      (∀ q buf idx, (buf ≠ y ∨ idx < yo.eval ∨ yo.eval + n.eval ≤ idx) →
        out.store.read q buf idx = st.store.read q buf idx) ∧
      ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i - av * dec p (W i))‖ ≤
        u p * ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ ∧
      |‖WithLp.toLp 2 (fun i : Fin n.eval => dec p (W i))‖ ^ 2 - 1| ≤
        normalizationRoundingFactor n.eval (u p) ∧
      ‖WithLp.toLp 2 ((fun i : Fin n.eval => xs i) -
        av • (‖WithLp.toLp 2 (fun i : Fin n.eval => dec p (W i))‖⁻¹ •
          (fun i : Fin n.eval => dec p (W i))))‖ ≤
        (2 * u p + roundingFactor (n.eval + 1) (u p)) *
          ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ := by
  classical
  obtain ⟨wa, hwa, hda⟩ := ha
  choose words hread hdec using fun i : Fin n.eval => hx i i.isLt
  let X (i : ℕ) : K := if hi : i < n.eval then words ⟨i, hi⟩ else wa
  have hX (i : ℕ) (hi : i < n.eval) : st.store.read p x (xo.eval + i) = some (X i) := by
    simpa only [X, dif_pos hi] using hread ⟨i, hi⟩
  have hdX (i : ℕ) (hi : i < n.eval) : dec p (X i) = xs i := by
    simpa only [X, dif_pos hi] using hdec ⟨i, hi⟩
  obtain ⟨copied, ec, shc, rc, fc, _⟩ := exec_copyv_frame I hc p st n x y xo yo X hX hxy hy
  have hascale : ∃ w, copied.store.read p a.buf a.idx.eval = some w ∧ dec p w = av :=
    ⟨wa, (fc p a.buf a.idx.eval (Or.inl hay)).trans hwa, hda⟩
  have hxc (i : ℕ) (hi : i < n.eval) :
      ∃ w, copied.store.read p y (yo.eval + i) = some w ∧ dec p w = xs i :=
    ⟨X i, rc i hi, hdX i hi⟩
  obtain ⟨out, W, er, hw, hW⟩ := h.exec_rscl I p copied a y yo n av xs hav.ne'
    hascale hxc (fun he => (hay he).elim)
  have hrel (i : Fin n.eval) : RelErr (u p) (xs i) (av * dec p (W i)) := by
    obtain ⟨δ, hδ, hd⟩ := hW i i.isLt
    refine ⟨δ, hδ, ?_⟩
    rw [hd]
    field_simp [hav.ne']
  obtain ⟨hres, hunit, hdir⟩ := normalized_output_bounds (h.nonneg trivial) hn hg hav hscale hrel
  refine ⟨copied, out, W, ec, er, ?_, (Store.shape_of_writeBlock_eq_some hw).trans shc,
    ?_, ?_, hres, hunit, hdir⟩
  · rw [exec_run_bind I (b := copyv p x xo y yo n) (fun _ => rfl), ec, Option.bind_some]
    exact er
  · intro i
    simpa only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_range i.isLt,
      Option.map_some] using Store.read_of_writeBlock_eq_some_of_lt (j := (i : ℕ)) hw
        (by simpa only [Array.size_map, List.size_toArray, List.length_range] using i.isLt)
  · intro q buf idx hout
    exact (Store.read_of_writeBlock_eq_some_of_ne hw
      (by simpa only [Array.size_map, List.size_toArray, List.length_range] using hout)).trans
        (fc q buf idx hout)

/-- Derive copied-vector normalization from an actual preceding norm execution and the
preserved norm word. Comparisons and framed updates may intervene between the norm and
copy/division. The nonzero coefficient premise is the actual normalization-guard fact;
no desired norm error, near-unit bound or normalization residual is assumed. -/
theorem IsRelErrSem.exec_copyv_rscl_of_nrm2_execution
    (I : Interp P ι K (OpCount P ι)) (p : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1)
    (predot normed ready : St P K (OpCount P ι))
    (a : Cell ℕ ℕ) (x y : ℕ) (xo yo n : IExp ℕ) (xs : ℕ → ℝ)
    (hn : (n.eval + 1 : ℕ) * u p < 1) (hg : roundingFactor (n.eval + 1) (u p) < 1)
    (hprex : ∀ i < n.eval,
      ∃ w, predot.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hx : ∀ i < n.eval, ∃ w, ready.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hdx : a.buf ≠ x) (hxy : x ≠ y) (hay : a.buf ≠ y)
    (hdst : ∃ v s, predot.store.write p a.buf a.idx.eval v = some s)
    (hy : ∀ i < n.eval, ∃ len, ready.store.shape[y]? = some (p, len) ∧ yo.eval + i < len)
    (hnorm : exec I (nrm2 p a x xo n).run predot = some normed)
    (horigin : ready.store.read p a.buf a.idx.eval = normed.store.read p a.buf a.idx.eval)
    (hbranch : ∃ w, ready.store.read p a.buf a.idx.eval = some w ∧ dec p w ≠ 0) :
    ∃ (copied out : St P K (OpCount P ι)) (w : K) (W : ℕ → K),
      exec I (copyv p x xo y yo n).run ready = some copied ∧
      exec I (rscl p a y yo n).run copied = some out ∧
      exec I (do copyv p x xo y yo n; rscl p a y yo n).run ready = some out ∧
      out.store.shape = ready.store.shape ∧
      ready.store.read p a.buf a.idx.eval = some w ∧
      out.store.read p a.buf a.idx.eval = some w ∧ 0 < dec p w ∧
      |‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ - dec p w| ≤
        roundingFactor (n.eval + 1) (u p) * ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ ∧
      (∀ i : Fin n.eval, out.store.read p y (yo.eval + i) = some (W i)) ∧
      (∀ q buf idx, (buf ≠ y ∨ idx < yo.eval ∨ yo.eval + n.eval ≤ idx) →
        out.store.read q buf idx = ready.store.read q buf idx) ∧
      ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i - dec p w * dec p (W i))‖ ≤
        u p * ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ ∧
      |‖WithLp.toLp 2 (fun i : Fin n.eval => dec p (W i))‖ ^ 2 - 1| ≤
        normalizationRoundingFactor n.eval (u p) ∧
      ‖WithLp.toLp 2 ((fun i : Fin n.eval => xs i) -
        dec p w • (‖WithLp.toLp 2 (fun i : Fin n.eval => dec p (W i))‖⁻¹ •
          (fun i : Fin n.eval => dec p (W i))))‖ ≤
        (2 * u p + roundingFactor (n.eval + 1) (u p)) *
          ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ := by
  obtain ⟨stN, w, he, hw, hn0, herr⟩ := h.exec_nrm2_abs_norm_sub_le I p predot hz
    a x xo n xs hn hg hprex (fun he => (hdx he).elim) hdst
  have hst : stN = normed := Option.some.inj (he.symm.trans hnorm)
  have hr : ready.store.read p a.buf a.idx.eval = some w := by
    rw [horigin, ← hst]
    exact Store.read_of_write_eq_some hw
  obtain ⟨old, hold, hne⟩ := hbranch
  have hword : old = w := Option.some.inj (hold.symm.trans hr)
  have hpos : 0 < dec p w := lt_of_le_of_ne hn0 (Ne.symm (hword ▸ hne))
  obtain ⟨copied, out, W, ec, er, ecr, hshape, hW, frame, hres, hunit, hdir⟩ :=
    h.exec_copyv_rscl I p hc ready a x y xo yo n (dec p w) xs hn hg hpos herr
      ⟨w, hr, rfl⟩ hx hxy hay hy
  exact ⟨copied, out, w, W, ec, er, ecr, hshape, hr,
    (frame p a.buf a.idx.eval (Or.inl hay)).trans hr, hpos, herr, hW, frame, hres, hunit, hdir⟩

end NLAlib.Computation
