# Projected inverse-column concentration audit — 28 September 2026

Subsequent investigation: `ProjectedDualMassObstructionAudit20260928.md`
records checked relative Schur asymptotics and finite dual approximation
bounds, plus a critical-zero obstruction to this strict-margin provider
on paper. The complete obstruction is not yet formalized in Lean.
The sufficient implications below remain valid; RH remains Open.

Continuation of Cnoack3/RiemannResearch commit
396b7c015e48d46aca4648d4587799ebffe4ec63.

## Conclusion

No unconditional sub-stretched bound on the actual inverse-Gram column mass
has been obtained. The available diagonal/Bessel control, exact Schur updates,
and inspected conductor results do not discharge that provider.

This continuation isolates a concrete l2 concentration budget, proves its
connection to the existing coefficient-mass criterion, and weakens the
endpoint requirement to cofinal smallness at the arithmetic exponent itself.
The quantitative concentration provider and RH remain **Open**.

## Notation

Stage n spans g_2,...,g_(n+1). Put h_d = coefficientRiesz d, P_n = the finite
orthogonal projection, and, for k:Fin n,

    c_(n,d,k) = coefficientCLM(k+2)(P_n h_d),
    B_(n,d) = sum_k |c_(n,d,k)|,
    L_(n,d) = sum_k c_(n,d,k)^2.

For d=i+2 present at stage n, the signed coefficients are exactly
(G_n^-1)_(k,i). In particular L is the squared l2 norm of the inverse column,
not its full Pareto Hilbert energy.

The checked arithmetic provider gives some a>0 and C>=0 with

    ||tailError n||^2 <= 8+C n exp(-a Phi(n)) eventually,
    Phi(n) = ((6+log n) log(6+log n))^(1/11).

## What diagonal and Bessel control actually give

The new unconditional inequalities are

    B_(n,d)^2 <= n L_(n,d),

    L_(n,d) <= ||P_n h_d||^2 sum_k (G_n^-1)_(k,k)
             <= ||h_d||^2 sum_k ||coefficientDual k||^2.

These retain the complete growing trace. A bounded fixed inverse diagonal
does not give a bounded l2 inverse column: the coefficients are inner
products with a nonorthogonal dual family. Ordinary Bessel applies to the
orthonormal modes, not directly to those raw coefficients.

Declarations: projectedDualCoefficientMass_sq_le_card_energy,
projectedDualColumnEnergy_le_diagonal_trace,
projectedDualColumnEnergy_le_dual_trace.

## A complete approximate-support estimate

Choose any subset I of the n column indices, with m=|I|, and define

    Q_(n,d)(I) = m sum_(k in I) c_k^2
                 + (n-m) sum_(k outside I) c_k^2.

Finite Cauchy--Schwarz on both sets and (x+y)^2<=2(x^2+y^2) give

    B_(n,d)^2 <= 2 Q_(n,d)(I),
    projectedDualTailEnergy n d <= 2 Q_(n,d)(I)/(n+1).

Nothing outside I is discarded. If the column is exactly supported on I,
the sharper bound B^2<=m L holds without the factor two, with exact
sparsity explicitly hypothesized.

More flexibly, suppose

    sum_(k outside I) c_k^2 <= rho L,  rho>=0.

Then

    Q(I) <= [m+(n-m)rho] L,
    B^2 <= 2 [m+(n-m)rho] L.

The effective-support cost is kappa=m+(n-m)rho. It is built from a selected
set and a quantitative l2 leakage bound; it is not defined tautologically
as B^2/L. The estimate is valid for the empty set, the full set, zero column
energy, and arbitrary positive stages.

Declarations: projectedDualCoefficientMass_sq_le_split_energy,
projectedDualTailEnergy_le_split_energy,
projectedDualCoefficientMass_sq_le_support_energy,
projectedDualSplitEnergy_le_effective_support.

The generic Analysis/FiniteCoefficientConcentration.lean also proves

    B^2 <= (sum_k w_k)(sum_k c_k^2/w_k),  w_k>0,

which allows other weighting choices. The application is
projectedDualCoefficientMass_sq_le_weighted_energy.

## Sufficient quantitative providers, all explicitly Open

For any b<a it suffices that, separately for every fixed d>1, there is K_d
such that at arbitrarily large n one can choose I and rho>=0 satisfying

    sum_(k outside I) c_k^2 <= rho L,
    exp(-b Phi(n)) [|I|+(n-|I|)rho] L <= K_d.

This is limitResidual_eq_zero_of_cofinal_stretched_l2_concentration.
It first bounds Q, then applies
limitResidual_eq_zero_of_cofinal_stretched_split_energy, which calls the
existing limitResidual_eq_zero_of_cofinal_stretched_coefficient_mass.

The two displayed estimates must hold at the same cofinal indices.
Distinct infinite sets of good indices cannot be intersected without
additional justification. No common subsequence across different d is
required.

For example, on those same indices, bounds L<=A_d exp(u Phi(n)) and
kappa<=D_d exp(v Phi(n)) are sufficient when u+v<a: take b=u+v.
Neither factor estimate has been supplied here.

A weaker endpoint requirement dispenses with b<a: for every d>1 and
epsilon>0, cofinally one can choose I with

    exp(-a Phi(n)) Q_(n,d)(I) < epsilon.

This is limitResidual_eq_zero_of_cofinally_small_split_energy. Its
coefficient-mass version is
limitResidual_eq_zero_of_cofinally_small_coefficient_mass.
These require only liminf zero of the nonnegative quantities, rather
than convergence along all stages.

exists_stretched_l2_concentration_rh_criterion obtains a>0 from the
checked arithmetic provider and, **assuming the displayed concentration
budget**, concludes both limitResidual=0 and RiemannHypothesis.
There is no RH premise or imported RH-to-density converse. The unresolved
budget is strong enough to imply RH and is not claimed equivalent to it.

Conversely, if a fixed correction limit is nonzero, then for every b<a,

    exp(-b Phi(n)) B_(n,d)^2 -> infinity.

This conditional necessary-growth statement is
coefficient_mass_stretched_barrier_of_nonzero_correction.

## Schur accumulation and its remaining dimension cost

Let m_(d,j)=modeCoefficient d j, s_j=residueModeScale j>0, z_j=eliminated j,
and

    A_j = sum_(k<=j) |modeCoefficient(k+2,j)|
        = (1+||z_j||_1)/s_j,
    s_j^2 = schurSigma j.

The new exact mode representation gives the rank-one update for the old
and new entries. Taking absolute values yields

    B_(n+1,d) <= B_(n,d)+|m_(d,n)| A_n,
    B_(n,d) <= sum_(j<n) |m_(d,j)| A_j.

Declarations: projectedDualColumn_eq_mode_sum,
projectedDualColumn_succ_old, projectedDualColumn_succ_new,
residueModeCoefficientMass_eq_schur,
projectedDualCoefficientMass_le_accumulated_schur.

Applying Cauchy--Schwarz and the existing summability of m_(d,j)^2 gives

    B_(n,d)^2 <= (sum_(j>=0) m_(d,j)^2) sum_(j<n) A_j^2.

The fixed-d factor is finite. The remaining amplification energy satisfies
the new unconditional lower bound sum_(j<n) A_j^2>=n, because every
normalized mode has coefficient mass A_j>=1. Thus this absolute-value
Bessel majorant retains at least a linear dimension cost. This statement
concerns the majorant, not a lower bound on the actual column mass.

Declarations: projectedDualCoefficientMass_sq_le_bessel_schur,
residueModeCoefficientMass_one_le, schur_amplification_energy_ge_stage.
No accumulated sub-stretched Schur envelope is proved.

## Other inspected dependencies and scope

- ParetoCRTGramTransfer.lean retains the complete signed nonuniformity
  correction and coefficient-dependent envelopes; it supplies no inverse
  spectrum or column-concentration provider.
- Analysis/FiniteResidueConductorSupport.lean counts conductors in a
  two-seed charge construction. It does not identify the support of this
  projected inverse column.
- NymanInverseCoefficientBound.lean bounds nymanConductorInverse, a
  different constructive conductor inverse. Its weighted coefficient
  bound is not a bound on G_n^-1.
- ResidueModeGramInverse.lean identifies G_n^-1 with M_n^T M_n. It does
  not bound the accumulated l1 column of that product.
- The previous cumulative signed-gain bridge remains available once the
  residual is zero; no signed-gain provider is discharged here.

The modules use finite sums, the complete infinite Pareto Hilbert space,
and the repository's checked stretched arithmetic provider. No new
arithmetic hypothesis is hidden in a definition, and no project-local
axiom, sorry, admit, or unsafe declaration is introduced.
