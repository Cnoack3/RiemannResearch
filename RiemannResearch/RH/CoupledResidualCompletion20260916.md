# Coupled Pareto residual corrections: Lean coverage

Date: 2026-09-16.

Scope: five recovered Lean modules and eighteen new Lean modules.

This continuation recovers the five modules from the previously unpublished commit
`d1dec0626614e643b8b801cc1cec008fcf0752e7`, closes several of its formalization gaps,
and states the unresolved estimates explicitly. “Defined” below does not mean
“proved”. There is no unconditional proof of the logarithmic upper bound or RH.

The mathematical source is preserved as
`RH/CoupledResidualCorrectionsSource20260916.md`. Its prose claims should be read
with the formalization statuses below.

## Recovered proofs

| Module | Verified content |
| --- | --- |
| `Analysis/CorrelationNormalizedCorrection` | Signed Gram normal equations, screened normalized witnesses, exact constrained optimum, and zero-gain infeasibility. |
| `RH/CoupledResidualCorrections` | Actual finite Pareto budgets, residuals and positive distances; legal dilations, exact transported energy, coupled correction bound, binary signed-source identity, interscale bound, and exact reconstruction optimum. |
| `Analysis/HeadTailResidualLift` | Weighted raw-tail minimum from the compressed normal equation. The actual solvability hypothesis is now discharged by the new head modules. |
| `Analysis/FiniteResidueCharge` | Vandermonde charge forcing and interpolation identities. The actual conductor-cardinality and coefficient-representation hypotheses are now discharged. |
| `Analysis/LogarithmicResidualBarrier` | Finite logarithmic gain telescoping and a bound conditional on a stated distance envelope. |

## New proved results

| Modules | Result and exact scope |
| --- | --- |
| `Analysis/HeadTailCompression`, `RH/PhysicalHeadResidualLift` | Actual head projection is surjective on the old budget; the compressed head equation has a unique solution. Every physical tail screening target is attainable. The exact raw-tail minimum and its extra weighted head cost are proved without a domain-specific solvability provider. |
| `RH/FreshCoprimeDecomposition` | The doubled budget is the algebraic direct sum of the transported space and the two fresh generators at each new index coprime to six. Proves exact counts, dimensions, a bounded count error, and the two dyadic congruence-class increments. |
| `RH/FreshCoprimeSchur` | The screened fresh family is independent. Its actual Gram map is invertible, and its inverse coefficients give the fresh optimum. Proves the full gain split, signed covariance/source formulas, and a normalized fresh correction when its gain is positive. |
| `Analysis/FiniteResidueConductorSupport` | Exact conductor count $3M-\lfloor M/2\rfloor-2\lfloor M/3\rfloor+\lfloor M/6\rfloor\le2M+1$. |
| `RH/ParetoFiniteResidueCharge` | Constructs zero-total residue coefficients for every actual legal vector and for the old optimum. The actual optimum has a nonzero constant charge or a nonzero even moment with corresponding odd index at most $4M-1$. This is a moment statement, not yet the derivative-order theorem. |
| `Analysis/PeriodicResidueGenerating`, `Analysis/PeriodicResidueLaplace`, `Analysis/PeriodicResidueLaplaceAtZero` | Finite geometric/residue identities, the exact positive-parameter exponential formula, the removable value at zero and continuity there. The periodic convention at zero is retained. |
| `RH/ActualResidualLaplace` | Supplies the actual optimum's coefficients and common-period divisibility, then proves its exact finite exponential formula, value at zero, and continuity. No analytic identification provider is assumed. |
| `Analysis/InterscaleResidualConstraints`, `RH/DyadicResidualConstraints` | Finite telescoping source budgets and absolute/weighted-square summability for the actual binary signed correlations, including the zero-energy case. |
| `Analysis/SharpLogarithmicResidualBarrier` | Arbitrarily late scaled relative gains below every constant greater than one; necessity of reconstruction-cost constant at least $1/\log2$. Both results explicitly assume the distance lower envelope. |
| `RH/BurnolDyadicComparison` | The explicit actual Burnol envelope implies the dyadic envelope and the sharp restriction on every eventual legal-witness logarithmic cost constant. The external envelope itself remains an unproved formalization target. |
| `RH/ParetoHaarComparison` | No conductor-independent comparison of full quotient energies. The exact optimal squared-norm factor is $L\nu_L(1)$, between $L/2$ and $L/2+1/2$. |
| `RH/TwoThreeSquareRelations` | The kernel of the full finite two-seed synthesis is exactly the span of the commuting squares. The squares are independent and the relation space has dimension $\lfloor M/3\rfloor$. This proves the finite functional-relation content of the chat's formal-variable argument. |
| `RH/LogarithmicCorrectionTarget` | Exact equivalence of normalized legal cost and actual gain bounds; equivalence of their eventual logarithmic forms; conditional implication to mathlib's `RiemannHypothesis`. |

Key actual-space declarations include:

- `CoupledResidual.full_gain_eq_transport_add_fresh`;
- `CoupledResidual.transportedSpace_disjoint_freshSpace`;
- `CoupledResidual.actual_residual_raw_tail_minimum`;
- `CoupledResidual.fit_finite_charge_forcing`;
- `CoupledResidual.actual_residual_laplace_data`;
- `FiniteTwoSeedCompletion.fullSeedSynthesis_ker_eq_squareRelationSpan`;
- `CoupledResidual.logarithmicCostBound_iff_gainBound`;
- `CoupledResidual.riemannHypothesis_of_logarithmicCostBound`.

The coupled-space declarations are under `RiemannResearch.RH.Pareto`;
the standalone scalar barrier is under `RiemannResearch.Analysis`.

## Unproved mathematics: recorded as propositions

`RH/LogarithmicCorrectionTarget` defines:

- `LogarithmicCostBound`: eventual legal screened witnesses with correlation
  $D_M$ and energy at most $C\log(2M)D_M$, for some $C>0$;
- `LogarithmicGainBound`: the equivalent bound
  $D_M\le C\log(2M)(D_M-D_{2M})$.

There is no inhabitant of either proposition supplied by this work.
The implication to RH is a theorem with the relevant proposition as an explicit
hypothesis. Defining an open target adds neither an axiom nor a proof.

## Remaining formalization obligations

`RH/CoupledResidualAnalyticTargets` defines precise actual-residual propositions
for the parts of the source whose analytic proof has not been formalized here:

- `LaplaceFiniteOrder`: a nonzero derivative of the actual finite Laplace ratio
  at order at most $4M-1$. The remaining bridge is the Bernoulli/Taylor coefficient
  identification and nonvanishing, not the finite moment forcing.
- `FarPeriodIntegralIdentity`: integrability and the exact far-period correlation
  integral for the actual residual and legal generator.
- `FarPeriodGainLowerBound`: residual-dependent far-period detection at the
  stated power, with no uniform amplitude or threshold in the old budget.
- `BurnolDistanceLowerEnvelope`: the classical analytic lower bound transferred
  to the actual Pareto distances.
- `DyadicDistanceLowerEnvelope`: the lower envelope consumed by the scalar barrier.

The last envelope is proved conditional on `BurnolDistanceLowerEnvelope` in
`RH/BurnolDyadicComparison`; it is not an additional independent assumption.

These are definitions of propositions, not theorem providers. The inverse-head
spectral-eigenbasis reformulation, the fresh-block crude trace/norm estimate, and
an extended-real `limsup` packaging of the cost barrier are also not separate
proved declarations in this continuation. Their main exact projection/Gram
identities and the sharp scalar obstruction are proved as listed above.

## Generalized CRT scope

The two-seed finite relation theorem and the Pareto/Haar obstruction are now
formalized. The larger CRT claims have the following precise scope at the pinned
mathlib revision `51e6992efd06126df61a496bebf8f49482a4e129`:

| Claim | Existing formal coverage | Remaining gap |
| --- | --- | --- |
| Two arbitrary integer moduli | `Nat.chineseRemainder'`, `Nat.chineseRemainder'_lt_lcm`, `Nat.mod_lcm`; project `Pareto.residueCRTEquiv`. | The pair theorem used in the program is covered. |
| Finite family with pairwise gcd compatibility | `Nat.chineseRemainderOfFinset` covers pairwise coprime moduli. | The arbitrary finite gcd-compatibility statement is not supplied here. |
| Profinite integers as the product of the p-adic integers | `PadicInt.toZModPow`, `PadicInt.lift`, and the general profinite completion have inverse-limit infrastructure. | No theorem assembling the full product equivalence with its ring and topology is supplied here. |
| Derived Amitsur descent | `comonadicExtendScalars` covers ordinary faithfully flat module extension. | The descendable-algebra totalization statement in stable symmetric monoidal infinity categories remains unformalized. |

These broader claims are not axioms used by the coupled correction proofs.
Algebraic reconstruction does not supply the unresolved Pareto norm estimate.
The checked square-relation theorem concerns the actual real function spaces;
the abstract complex polynomial-ring Koszul complex is not separately packaged.

## Verification

The five recovered modules passed a full project build in the current isolated
workspace. The head/support group and the fresh/CRT/barrier/target group then
passed serialized Lean source verification using focused imports.

The final actual-Laplace and Burnol/dyadic bridges passed in
`job_OTAxWTP9ub8jEKQz4E4a5ikJBWXX6KPz`, with no diagnostics.

The fresh/CRT/barrier/target verification job
`job_gu9qyyRtIoGrmJ2iOZZU6CmVrvLXvXnS` checked representative theorem axioms:
only `propext`, `Classical.choice`, and `Quot.sound` were reported, including
for the conditional RH implication. No project-local axiom, proof placeholder,
or unsafe declaration is introduced.

All modules are exported through `RiemannResearch.lean`; final integrated
validation and publication are performed by the publication checkpoint.
