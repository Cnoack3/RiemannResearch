import RiemannResearch.Analysis.ZetaFactorBudgetGap
import RiemannResearch.Analysis.PrimitiveRegularizationCertificates
import RiemannResearch.RH.ProjectedPairSpectralObstruction

/-! Axiom audit for the spectral-correction continuation. -/

/-- info: 'RiemannResearch.Analysis.ZetaFactorObstruction.no_accumulating_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.ZetaFactorObstruction.no_accumulating_zeros

/-- info: 'RiemannResearch.Analysis.PrimitiveRegularization.trust_region_minimizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.PrimitiveRegularization.trust_region_minimizes

/-- info: 'RiemannResearch.Analysis.PrimitiveRegularization.approximate_source_centered_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.PrimitiveRegularization.approximate_source_centered_identity

/-- info: 'RiemannResearch.Analysis.PrimitiveRegularization.approximate_source_residual_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.PrimitiveRegularization.approximate_source_residual_bound

/-- info: 'RiemannResearch.Analysis.PrimitiveRegularization.exact_source_residual_le_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.PrimitiveRegularization.exact_source_residual_le_quarter

/-- info: 'RiemannResearch.Analysis.PrimitiveRegularization.exists_approximate_source_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.PrimitiveRegularization.exists_approximate_source_budget

/-- info: 'RiemannResearch.RH.ProjectedPairSpectralObstruction.finite_cube_block_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.ProjectedPairSpectralObstruction.finite_cube_block_pos

/-- info: 'RiemannResearch.Analysis.ZetaFactorObstruction.diagonal_budget_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.ZetaFactorObstruction.diagonal_budget_gap
