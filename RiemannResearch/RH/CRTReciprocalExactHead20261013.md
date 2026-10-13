# Finite reciprocal-square CRT certificates and Nyman–Beurling

Source: user-provided conversation, 13 October 2026. Terminology and the
discrete criterion: B. Bagchi, https://arxiv.org/abs/math/0607733, Theorem 1,
Remark 8. No mathematical novelty claim is made.

## Definitions and exact target

For positive integers n, let P(n)=1/[n(n+1)], Q(n)=1/[zeta(2)n^2], and
r_d(n)=(n mod d)/d. At stage j take a positive period L_j, a finite set
s_j of divisors d>=2 of L_j, real coefficients c_{j,d}, and
F_j(n)=sum_{d in s_j} c_{j,d} r_d(n). Squarefree L_j ensures squarefree
support, but the forward theorem needs no squarefreeness assumption.

M_j is the endpoint of the exact initial interval, not the indicator index m.
Require M_j -> infinity and F_j(n)=1 for 1<=n<=M_j. The finite certificate is

B_L(R)=sum_{a=1}^L R(a)^2/a^2, with R=1-F.

The open arithmetic assumption is one constant C with B_{L_j}(1-F_j)<=C
for every stage. Neither this bound nor the requisite bounded-energy family
is constructed by the formalization.

## Formal results

* ParetoCRTReciprocalEnergy.lean proves the complete periodic Pareto energy
  is at most 2 B_L(R), using the exact existing progression regrouping.
  crtReciprocalEnergy_eq_tail removes the initial zero residual coordinates
  exactly, without discarding any repeated periods.
* CRTReciprocalExactHeadRH.lean proves closure membership from cofinal exact
  heads and the uniform certificate bound, then concludes Mathlib's actual
  RiemannHypothesis using the already proved Mellin obstruction. The literal
  finite divisor-sum theorem constructs its Hilbert vectors and proves their
  membership, boundedness, and periodicity internally.
* NormalizedResidueExactHeadCharges.lean proves that exact matching forces
  c_m=-mu(m) for 2<=m<=M (absent coefficients interpreted as zero), and
  sum c_d/d=1. No squarefree or balance hypothesis is needed for extraction.
* CRTReciprocalCertificate.lean verifies the exact period-six example
  F=r_2+(913/769)r_3+(481/769)r_6, with F(1)=F(2)=1 and
  B_6(1-F)=1669/27684<1/16.

These are conditional research reductions where the uniform arithmetic
bound appears explicitly. The Lean implication is not an assumption named
RH, and no project-local axiom is introduced. Candidate axiom checks returned
only propext, Classical.choice, and Quot.sound.

## Relation to the Q formulation

The same finite certificate B_L occurs in the conversation's Q formulation.
Its elementary sharp comparison is B_L/zeta(2)<=||R||_Q^2<=B_L.
The new formal proof instead uses ||R||_P^2<=2 B_L and the existing Pareto
Nyman–Beurling machinery, so it reaches the same sufficient condition.
The sharp Q-weight comparison, the fixed-m isometric transport, and the full
RH converse with squarefree exact-head correction are paper arguments here,
not newly formalized declarations in these modules.

Allowing L to grow freely is essential to the proposed research formulation.
No specified primorial schedule is asserted sufficient. Finite certificates,
including the period-six example, do not prove a uniform bound.

## Next research obligation

Construct legal exact-head coefficients with a cofinal sequence M_j and
a proved uniform bound on B_{L_j}(1-F_j). The fixed small coefficients and
the remaining single charge constraint identify the finite quadratic
optimization problem, but do not control its minima uniformly.
