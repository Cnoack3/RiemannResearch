# Q residue Gram formalization and research agenda

Source: the user's Q-measure inverse-Gram research program and its symbolic
write-up of 13 October 2026. Wolfram numerical calculations are excluded.
The verification ledger below must be read together with the theorem types.

## Exact objects

The probability law is Q(N=n)=1/(zeta(2)n^2) on positive integers. The residue
atom is g_d(n)=(n mod d)/d, encoded in the existing `ZetaTwoHilbert.QHilbert`.
All means, inner products, errors and closures below use this actual law.
Finite prime identities use the existing proved independence of prime
valuations under Q; they do not replace Q by a uniform CRT model.

## Finite covariance and genuine inverses

Let b_i=E_Q[g_{d_i}], G_ij=E_Q[g_{d_i}g_{d_j}] and V=G-b b^T.
For a centered solution Vu=b put T=b^T u. Then T is nonnegative and independent
of the choice of u. With c=u/(1+T), Gc=b and the full Q error is

    ||1-sum_i c_i g_{d_i}||_Q^2 = 1/(1+T).

Distinct conductors d_i>1 give linearly independent residue vectors and
centered residue vectors. Consequently both G and V are positive definite.
Here genuine matrix inverses are legitimate and

    G^(-1)b = V^(-1)b/(1+b^T V^(-1)b),
    det G = det V (1+b^T V^(-1)b),
    optimal error = det V / det G.

The full matrix identity is also retained:

    G^(-1)=V^(-1)-(V^(-1)b)(V^(-1)b)^T/(1+T).

The general finite linear-algebra module also retains the exact mean-one
variance remainder and the full Schur-update solve and information identity.

## Squarefree Q capacity and the analytic boundary

The existing squarefree optimizer stages include zero coordinates for
nonsquarefree integers. They therefore use normal equations, without a false
nonsingularity assumption. If e_n is their actual optimal squared error,
define capacity_n=(1-e_n)/e_n. The centered solve exists at every stage and
every solution has information capacity_n. Exact identities give

    capacity_n -> infinity
      iff e_n -> 0
      iff 1 belongs to the closed squarefree residue span
      iff the existing squarefree exact-head bounded-tail property.

The capacity is monotone, with exact increment

    capacity_(n+1)-capacity_n
      = ||optimizer_(n+1)-optimizer_n||_Q^2/(e_n e_(n+1)).

The established Mellin-obstruction consumer gives capacity divergence =>
Mathlib's `RiemannHypothesis`.

**Conditional research reduction.** The displayed RH iff theorem explicitly
takes `hforward : RiemannHypothesis -> squarefree Q closure` as an argument.
It does not prove or postulate this argument. Its remaining formalization
obligation is **Open**: supply the analytic RH-to-squarefree-density provider.
The earlier mathematical write-up derives this direction from classical
analytic results on damped Mobius sums; those analytic results and their
application have not been assembled here in Lean. Ordinary Mathlib logical
foundations do not discharge that obligation. No claim that RH itself has
been proved is made.

Uniform boundedness of b^T G^(-1)b alone is automatic: it is at most one.
The required assertion is convergence to one, equivalently capacity tending
to infinity or the full squared error tending to zero.

## Exact moment and arithmetic-coordinate formulas

The residue means and lcm-period Gram entries are finite trigamma sums,
obtained from the existing periodic inverse-square expectation theorem.
Dilation obeys the actual Q identity

    E_Q[f(N) 1_{k|N}] = k^(-2) E_Q[f(kN)]   (k>0).

For bounded f, finite signed combinations may be interchanged with the
expectation. In particular, putting

    h_r = sum_{k|r} mu(r/k) k^2 1_{k|N},
    T_d(k)=E_Q[g_d(kN)],

the exact residue coordinate is

    E_Q[g_d h_r] = sum_{k|r} mu(r/k) T_d(k).

This is a direct connection between inclusion-exclusion coordinates and the
legal residue atoms, preserving every signed term.

Finite squarefree prime wavelets W_A=product_{p in A}(p^2 1_{p|N}-1) have
diagonal Gram matrix with squared norm product_{p in A}(p^2-1). These alone
only retain the radical of N. Prime exponents require the local wavelets

    H_(p,0)=1,
    H_(p,a+1)=p^(2a+2)1_{v_p>=a+1}-p^(2a)1_{v_p>=a}.

Their finite tensor Gram matrix is diagonal, with local squared weight
p^(2a)(p^2-1) for exponent a+1. Scaled valuation tails are finite telescoping
sums of these wavelets. The full divisibility dictionary, including composite
intersections, is dense in the actual QHilbert via the existing Noor totality
theorem and an exact shift/normalization map.

The finite wavelets are assembled into a complete, unconditional arithmetic
Hilbert basis. Triangular inversion proves that the Mobius wavelets and all
divisibility indicators have the same algebraic span. Prime factorization
proves their actual Q Gram diagonal. Thus, for every residue pair,

    G_de = sum_(r>=1) a_d(r) a_e(r)/J_2(r),

and the full error is exactly

    ||1-sum_d c_d g_d||_Q^2
      = sum_(r>=1) (1_(r=1)-sum_d c_d a_d(r))^2/J_2(r).

`QArithmeticCapacity.lean` specializes this infinite arithmetic energy to
chosen actual squarefree normal-equation coefficients. It equals e_n exactly;
its convergence to zero is equivalent to capacity divergence and actual
squarefree closure. The RH iff still retains the analytic forward provider.
No tail has been discarded and no rate estimate follows merely from Parseval.

## Inclusion-exclusion: an exact obstruction and a refinement

For a squarefree conductor L, the unweighted residue sieve satisfies

    F_L=-sum_{d|L} mu(d)g_d = C_L-n alpha_L,
    alpha_L=sum_{d|L}mu(d)/d=product_{p|L}(1-1/p),

where C_L counts integers up to n that are coprime to L. If L covers every
prime up to M, then for 1<=n<=M, F_L(n)=1-alpha_L*n. Thus its head error is
exactly M*alpha_L^2/zeta(2).

For the concrete product of 2 and all odd primes <=2m+1, an elementary
Wallis-product comparison proves

    full Q error of F_L >= 1/(4*zeta(2)).

Consequently this naive primorial Möbius family does not converge to 1 in
L^2(Q). This excludes one particular construction, not squarefree density.

For positive d,p the exact atom refinement is

    g_(dp)(n)=g_d(floor(n/p))+g_p(n)/d.

An explicitly paired finite weighted extension consequently obeys

    F_new(n)=F(n)-u F(floor(n/p))+u alpha g_p(n),
    alpha_new=alpha(1-u/p).

The finite paired construction does not silently assume that old and new
divisor indices are disjoint; any specialization to an Euler-product sieve
must justify its arithmetic indexing.

## Next research steps

1. **Open: analytic forward provider.** Formalize RH-to-squarefree-Q-density
   using a precise damped Möbius approximation theorem and the existing
   equivalent Q/Pareto norms. Keep the required uniform tail estimates visible.
   Exact critical-line Plancherel is already available in
   `ParetoFiniteMellinHalfPlane.finiteResidueError_boundary_zeta_energy`.
   The missing analytic provider needs RH-conditioned convergence and uniform
   bounds for ordered initial Mobius sums on Re(s)>1/2, followed by L2 control
   as damping tends to zero. Use `Tendsto` of finite initial sums: the existing
   `dampedMobiusWeight_LSeriesHasSum` uses unordered `HasSum` and requires
   Re(s+epsilon)>1. Its absolute-convergence hypothesis cannot simply be
   weakened to 1/2. Existing moving-band results reach damping 1/2, not zero.
2. **Open: useful residue-coordinate bounds.** Exploit periodic dilation and
   prime-power cancellations in T_d(k) to estimate the actual covariance
   capacities or their exact Schur increments.
3. **Open: weighted prime refinements.** Study damped/optimized u_p in the exact
   refinement recurrence. Control both the density term on the growing head
   and the full tail; finite-head interpolation alone is insufficient.
4. **Open: determinant growth.** Use det(V_N)/det(G_N)=e_N as an alternative
   form of the same approximation problem, with explicitly independent
   squarefree conductor lists. Finite invertibility alone gives no limiting
   estimate.

## Verification status

All eighteen modules passed the combined-source Lean check
`job_odrFWDBr6cOqe6pYDSRhfpP-16VrjAFW` (exit code 0, verified, 328.072 seconds).
The audited full inverse, full Parseval, sieve-obstruction and conditional RH
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The printed RH iff type explicitly retains the analytic `hforward` argument.

The first project checkpoint, `job_fvNV5iNUFmi6aJ9F7mcyoIDj8B6UiWlO`,
terminated with a 3600-second Lake build timeout. Its last reported build
count was 6799 of 6807 tasks. That checkpoint did not certify or publish the
project; it did not report a Lean proof error. The source and retained build
were recovered in the same workspace for a publication retry. This build
failure does not discharge or refute the analytic obligations above.

The recovery checkpoint, `job_1_WjVQnSGAx1_whxuCMpixzqTe91-c24`, completed
its aggregate and changed-module build and retained the result in local commit
`3a523e84fb2e28686c86d5b576dfde824ad32945`. Publication then failed while
cherry-picking onto newer main: the root import list and theorem catalog
conflicted. The same Lean sources were carried into a fresh current-main
workspace; both sets of imports and catalog entries are preserved. That
integrated source must pass the publication checkpoint before it is pushed.

Publication additionally requires the Lean-server checkpoint to validate
the actual changed modules and aggregate project through their own imports.
The final publication report supplies that terminal job and commit. The open
analytic formalization obligations above remain independent of compilation.
