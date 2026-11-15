# Density coupling as operator variance

Date: 2026-11-15. Source: Christian Noack's variance observation.
Modules: Analysis/CompressionVariance.lean and RH/QDensityCouplingVariance.lean.

## Exact setting

H = L2(Q), V = closure span {g_k : k >= 2}, W = V-perp-Q.
B is the existing QDensityMetric.B, multiplication by
b(n) = (n+1)/(zeta(2)n) on positive physical sites.
D divides physical coordinates by n, so B = (I+D)/zeta(2).
Let P be Q-orthogonal projection onto V, A = P B restricted to V,
and C = (I-P) B restricted to V. The actual Lean C is
QDensityCouplingSurjectivity.coupling.

Define Phi(T) = P T restricted to V. Then

Var_Phi(B) = Phi(B^2) - Phi(B)^2 = C* C.

This is operator compression variance. No identification of V with
L2 of a sub-sigma-algebra is assumed.

## Exact identities

For v,u in V and every real center mu:

< C* C v,u > = < C v,C u >.

||Bv-u||^2 = ||Cv||^2 + ||Av-u||^2.

||(B-mu I)v||^2 = <C*Cv,v> + ||(A-mu I)v||^2.

The first identity gives positivity and self-adjointness. The second gives
the exact minimum approximation error. The third is a law of total
centered variance. For unit v and mu=<Bv,v>, define
nu_v(n)=Q(n)|v(n)|^2 in physical coordinates. Then the left side is the
ordinary scalar variance of b under nu_v. This probabilistic interpretation
is explanatory; the Lean theorem checks the underlying Hilbert-space identity.

Affine transformation gives
Var_Phi(aT+bI)=a^2 Var_Phi(T) at the quadratic-form level.
In particular <C*Cv,v> = zeta(2)^(-2) <Var_Phi(D)v,v>.

## Declaration map

General declarations are in namespace Submodule.

| Declaration | Exact content |
|---|---|
| operatorCompression, operatorLeakage, compressionVariance | Actual subspace-valued continuous linear operators |
| compressionVariance_eq_square_defect | Phi(T^2)-Phi(T)^2 for symmetric T |
| compressionVariance_inner, compressionVariance_quadratic | Polarized and quadratic Gram identities |
| compressionVariance_nonneg, compressionVariance_self_adjoint | Positivity and self-adjointness |
| compressionVariance_apply_eq_zero_iff | Kernel = vectors v with Tv in V |
| compressionVariance_zero_iff_invariant | Zero variance iff T preserves V |
| operatorCompression_best_approximation | Complete least-squares identity |
| compressionVariance_total | Exact total centered variance |
| compressionVariance_le_centered_energy | Bound by any scalar-centered energy |
| operatorLeakage_affine, compressionVariance_affine_quadratic | Affine variance law |

Application declarations are in RiemannResearch.RH.QDensityCouplingVariance.

| Declaration | Status and content |
|---|---|
| coupling_gram_eq_second_moment | Unconditional exact identity for actual C and B |
| coupling_total_variance | Unconditional centered decomposition |
| coupling_reciprocal_variance | Exact reciprocal normalization |
| coupling_gram_zero_iff_fullClosure | Unconditional equivalence: C*C=0 iff V=H |
| riemannHypothesis_of_coupling_gram_zero | Conditional research reduction; actual C*C=0 is Open |
| reverse_gram_quadratic | <CC*w,w>=||C*w||^2 |
| reverse_gram_strictly_positive | Strict positivity on each nonzero w, from injectivity of C* |
| reverse_gram_gap_iff_finiteDimensional | Uniform positive reverse-variance gap iff W is finite-dimensional |

## Remaining obligations and boundary

Open: show C*C=0, equivalently B(V) is contained in V, equivalently V=H.
The existing density-to-RH theorem then gives RH. This file does not claim
the converse RH-to-totality implication.

Alternative structural goal, also Open: establish a uniform constant delta>0
with <CC*w,w> >= delta^2 ||w||^2 for every w in W. This is equivalent
to finite-dimensionality of W (and, by the existing coupling theorem,
surjectivity of C). Finite dimension is not identified with W=0 here.

Positivity, compactness, injectivity of C*, or small tail upper bounds do not
supply either missing condition. A finite numerical table cannot certify
the every-vector statements.

## Provenance

R. V. Kadison, "A generalized Schwarz inequality and algebraic invariants
for operator algebras", Ann. of Math. 56 (1952), 494-503, Theorem 1,
supports the positive-map perspective.

R. Sharma and A. Thakur, "More inequalities for positive linear maps",
J. Math. Inequal. 7 (2013), 1-9, equation (1.1), doi:10.7153/jmi-07-01,
supports the operator-variance terminology.

The implementation uses orthogonal projections and adjoints directly,
retains every squared remainder, and adds no domain-specific axiom.
