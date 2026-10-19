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

The third equality also covers A=0 under Lean's total division convention.
All norms are complete actual Q norms. The finite dictionary assumptions
are explicit; no RH, target density, or arithmetic cancellation provider
is assumed. The candidate lies in the original legal finite span because
it is a scalar multiple of the displayed synthesis U.

This gives a concrete way to test a proposed correlation estimate.
It does not establish B^2/A -> 1. The next research investigation is
whether this particular direction can retain a nonzero normalized target
correlation as dictionaries grow. The atoms themselves tend to zero as
their conductors escape, while v_i tends to one; this warrants checking
capacity growth before pursuing an asymptotic lower bound.

The bounded complete-energy exact-head problem remains Open.
