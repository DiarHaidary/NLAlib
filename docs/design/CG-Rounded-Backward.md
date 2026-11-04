# The backward model of actual stored CG execution

Date: 2026-11-04. This corollary reuses the registered stored-entry tree unchanged.
It adds no target, Result id, arithmetic semantics or run interface.

The existing full compiled-program theorem derives a CGRun from actual primitive operations
under an unbounded relative-error contract. This corollary selects its positive-prefix case
when q>0 and decoded b is nonzero. It retains the actual execution, resource bound, stored
word/decoder ties and status. The canonical CGRun backward matrix and dilated RHS then give
the model spectrum, Frobenius perturbation radius, exact model coefficient/residual matching,
and direct physical-energy error comparison. The initial model-distance term remains
2||b||²δ/a², and the existing local150m² rounding remainder remains separate.
No residual-to-energy conversion or assumed local error/trajectory appears in the inputs.

Reuse: CGRun.frobNorm_backwardH_sub_dilatedH_le, spectrum_backwardH_subset_Icc,
cgAlpha_backwardH, norm_cgState_backwardH_r, norm_dilatedRhs and the canonical
CGEnergyEstimator.abs_quadForm_sub_x_sub_quadForm_backwardH_sub_cgIterate_le.
The model is positive definite, so its solution equation in the final universal comparison
is nonvacuous. Zero dimension, zero input and zero budget remain explicit branches of the
common compiled-program theorem; they do not create a CGRun of length zero.

The checked implementation is
`NLAlib/Krylov/LinearSystems/CGProgramRoundedBackward.lean`, declaring
`NLAlib.CGImplementation.exec_rounded_compiled_backward`. It imports the canonical
`CGProgramRounded` compiled-program theorem, with no proposal imports. The program, target
and count definitions remain unchanged. The full source declaration is the canonical signature;
the model facts are derived from actual execution rather than accepted as premises.
