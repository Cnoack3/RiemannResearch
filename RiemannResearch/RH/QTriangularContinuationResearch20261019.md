# Triangular direction synthesis and research continuation

Date: 19 October 2026.

The uploaded Balazard refinement's concrete overlap, strong Pareto and Q
dual convergence, and three-remainder inverse-Gram identity are already
present in the starting repository. This continuation adds an exact legal
scalar synthesis rather than duplicating those results.

For a finite distinct dictionary d_i>1 let
G=(<g_i,g_j>_Q), b_i=<1,g_i>_Q, v_i=1-1/d_i,
U=sum_i (G^{-1}v)_i g_i, A=v^T G^{-1}v, and B=v^T G^{-1}b.
For A nonzero define F=(B/A)U. The new Lean module
RH/QTriangularRayleigh.lean proves

    ||1-F||_Q^2 = 1-B^2/A,
    ||1-aU||_Q^2 = ||1-F||_Q^2 + A(a-B/A)^2,
    ||1-F||_Q^2 = ||1-P_V 1||_Q^2 + ||P_V 1-F||_Q^2.

The subsequent target-mean/escape update extends the first equality to A=0
as well, under Lean's total division convention.
All norms are complete actual Q norms. The finite dictionary assumptions
are explicit; no RH, target density, or arithmetic cancellation provider
is assumed. The candidate lies in the original legal finite span because
it is a scalar multiple of the displayed synthesis U.

The subsequent `QPrimorialChargeDirection.lean` update settles this
investigation for the natural primorial divisor dictionaries:
B^2/A tends to zero, and the squared target error of F tends to one.
Norm escape and eventual retention of fixed atom pairings prove this
unconditionally, without assuming anything about target closure.
See `QTriangularDirectionEscapeResearch20261019.md` for the proof and
updated agenda. The scalar ray is insufficient; the entire legal span
is not ruled out.

The bounded complete-energy exact-head problem remains Open.

Integration note: newer main independently supplied norm escape and the
primorial application while these five iterations were running. The
integrated update reuses and extends those owners, adds the squarefree
prefix application, and adds the exact coefficient probes and dual
density modules. Both research records are retained.


## Five completed research iterations

These five iterations follow the initial scalar-synthesis commit. They
develop the same triangular-dual problem and stop at the requested limit.

### 1. Exact capacity growth obstruction

RH/QTriangularTargetDirection.lean proves the actual atom pairings
<U_D,g_d>_Q=1-1/d and the complete-Q lower estimate

    (1-1/d)^2 <= A_D ||g_d||_Q^2.

The general theorem norm_tendsto_atTop_of_vanishing_test_pairing in
Analysis/EscapingRieszDirections.lean proves norm escape. The specialized
directionFit_norm_tendsto_atTop discharges the residue hypotheses.
This uses the already established strong limit g_d -> 0 in Q, not RH.
The independent norm-escape proof from this run is integrated through
these concurrently published owners; directionCapacity_atom_bound adds
the complete finite lower estimate without a duplicate capacity module.

### 2. Weak escape after normalization

Analysis/EscapingRieszDirections.lean proves a general Hilbert
theorem. Its normalized_riesz_weak_zero is generalized here from
eventually constant generator pairings to convergent generator pairings. Suppose u_n belongs to a fixed atom closure, ||u_n|| -> infinity,
and <u_n,v_i> has a finite limit for each fixed atom v_i. Then for every
fixed ambient target x,

    <u_n / ||u_n||, x> -> 0.

The target need not belong to the atom closure. The proof first
approximates its orthogonal projection by finite spans and then uses
orthogonality of the target residual. No density assumption is hidden.

### 3. Application to the actual squarefree inverse-Gram dictionaries

Let D_s be all squarefree integers from 2 through s+1. Let s_j >= 2
be squarefree and tend to infinity. For the actual Q-Gram matrices of
these dictionaries, set

    A_j = v^T G_j^{-1} v,
    B_j = v^T G_j^{-1} b_j.

RH/QSquarefreeTriangularEscape.lean proves, with these structural
cutoff hypotheses and without any RH assumption,

    ||U_{D_{s_j}}|| -> infinity,
    B_j^2 / A_j -> 0,
    ||1 - (B_j/A_j) U_{D_{s_j}}||_Q^2 -> 1.

The last declaration is
squarefreeDirection_rayleighFit_error_tendsto_one. This prefix-dictionary
application reuses the concurrently published escape mechanism, preserving
the separate primorial application in QPrimorialChargeDirection.lean. In particular, the
earlier suggestion that B_j^2/A_j might tend to one cannot work along
these cofinal squarefree cutoffs. The finite inverse-Gram
Cauchy--Schwarz inequality remains correct; the proposed asymptotic
lower estimate is ruled out for this direction.

The hypotheses say which dictionaries are used. They are not unresolved
analytic estimates. The theorem is stated for arbitrary cofinal
squarefree cutoff sequences; it does not additionally formalize a
particular prime-enumeration provider.

### 4. Exact coefficient recovery from neighboring cutoffs

Write R_N for the repository's actual Q Riesz vector, so
<R_N,h>_Q=Lambda_N(h). For d=n+1 the new probe is

    Z_d = d [2d R_d - (d-1) R_{d-1} - (d+1) R_{d+1}].

RH/QTriangularCoefficientProbe.lean proves for every ambient Q vector h

    <Z_d,h>_Q = qCoefficientCLM d h = -w(d;h).

This follows from the full exact finite identity

    (n+2) T_{n+2} - 2(n+1) T_{n+1} + n T_n
      = (1/(n+1)) mobiusRieszHilbert(n+1)

in the Pareto space, where T_N is triangularChargeRiesz N.
There is no endpoint omission, de-averaging hypothesis, or asymptotic
estimate. For d,e >= 2, <Z_d,g_e>_Q is exactly the Kronecker delta.
The indexing in Lean is coefficientProbe n = Z_{n+1}.

### 5. Completeness of the entire triangular dual dictionary

RH/QTriangularDualDensity.lean proves

    closure(span{R_N : N >= 0}) = QHilbert.

It also proves that the actual finite-span projections of any Q vector
onto this dual dictionary converge in complete Q norm to that vector.
The proof uses the exact coefficient probes from iteration 4 and the
existing separation theorem for all Mobius coordinates.

This is a dual completeness result. The vectors R_N are not asserted
to be legal residue combinations. In particular, this theorem and
R_N -> 0 strongly are compatible and do not establish the legal
squarefree closure required for RH.

## Numerical diagnostic, separate from kernel verification

A host floating-point calculation used complete periodic Q-Gram entries
computed from trigamma residue sums. It gave the following diagnostic;
these are not formal rational certificates.

| Largest allowed conductor | Squarefree atoms | A | B^2/A | b^T G^{-1} b |
|---:|---:|---:|---:|---:|
| 5 | 3 | 5.3672 | 0.62089 | 0.97276 |
| 10 | 6 | 13.4054 | 0.27620 | 0.98275 |
| 20 | 12 | 27.3233 | 0.15165 | 0.98848 |
| 40 | 25 | 60.2297 | 0.06508 | 0.99130 |
| 80 | 49 | 125.0269 | 0.03266 | 0.99270 |

Wolfram independently simplified the finite scalar completion-of-square
identity to zero. The general mathematical conclusions above rely on Lean,
not on the numerical pattern.

## Remaining RH obligation and recommended direction

The single v direction should not be pursued as a target approximation
scheme. The full triangular family retains all coefficient information
through exact neighboring second differences, so a synthesis argument
would need several cutoffs with controlled complete energy. Its dual
completeness alone supplies no legal synthesis estimate.

The most concrete remaining sufficient arithmetic target is still:

    H_j -> infinity,
    F_j is a finite squarefree legal combination,
    F_j(k)=1 for 1 <= k <= H_j,
    sup_j ||F_j||_Q < infinity.

The repository's signed head-step cost-minus-gain budget is a direct
way to formulate this target. Its known sublinear energy estimate does
not imply the required uniform bound. No such provider has been proved
in these iterations. RH remains Open.

The initial scalar synthesis and all five research developments are
exported by RiemannResearch.lean. Publication must follow the server
checkpoint gate; successful snippets alone do not certify integration.
