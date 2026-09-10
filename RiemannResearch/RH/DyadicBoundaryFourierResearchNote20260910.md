Update, September 10, 2026: `DyadicBoundaryTents.lean` now proves the exact
integer affine tent pieces at every dyadic depth. `DyadicResidueStepApproximation.lean`
and `DyadicResidueTerminalOctave.lean` prove the signed finite residue/step bridge
with complete boundary error at most (a-1)^2/(K+1), and 1/(2N+1) for the binary
terminal octave. `Analysis/AbelCancellationMultiplier.lean` proves the elementary
multiplier bound, sharpened to 2/(1+q), and the finite mean-cancellation algebra.
The full real/Fourier identities and interchanges below remain unverified.

Status: **Not Lean verified.** This ordinary research review is retained for independent review. Its proposed Fourier multiplier identity is an open candidate, and no assertion in this note is used as a provider by the new Lean modules.

# Analytic review of the signed mean-energy frontier

This is an independent ordinary-mathematics review, not a Lean verification.
No verification job, source mutation, or remote publication was made by this
reviewer. The root coordinator owns all formal verification.

## Conclusion

There is no fixed-boundary-coordinate counterexample from the comparison
family `C_epsilon`. Its fixed boundary coefficients tend to zero. This does
not establish convergence of their full square sum. The potentially useful
next analytic direction is to identify the actual remainder as a zeta-shift
multiplier acting on the exact log-periodic boundary tents. Its expected
triadic multiplier has a uniform elementary bound; the full arithmetic
boundary-energy estimate remains unproved.

## An ordinary exact description of a fixed boundary

Write `a_l(f) = 4 <Q b_l,f>`, for positive integer `l`, and `V_m = Q T_m 1`.
Let

    tau_l(x) = max(0, 1 - abs(x-(2*l+1))),
    phi_l(x) = sum_{d in Z} tau_l(2^(-d)*x),  x>0.

The supports of the terms have disjoint interiors. Thus `phi_l` is continuous,
bounded by one, and `phi_l(2*x)=phi_l(x)`. The exact odd/even recurrence already
proved for `a_l(V_m)` gives

    a_l(V_m) = phi_l(m)       (m positive integer).

This can be proved by strong induction on `m`: the even recurrence is dyadic
invariance; the odd recurrence is linear interpolation on the tent grid plus
the new root tent. In particular `phi_l(1)=0`. This real-tent identification
is ordinary mathematics supplied here; it is not currently claimed as a new
checked Lean declaration.

The kernel-lift refinement also gives the physical coordinate description

    (Q b_l)(k) = (1/2) sum_{d>=0} b_l(floor(k/2^d)).

The nonzero terms have disjoint integer supports, so

    abs((Q b_l)(k)) <= (l+1)/2.

Because `T_m R_3` is nonnegative and has exact mean `log 3`, this implies

    abs(a_l(T_m R_3)) <= 2*(l+1)*log 3

uniformly in the positive conductor `m`. This is only a fixed-coordinate
bound; its constant grows with `l`, so it cannot bound the full square sum.
It does justify fixed-coordinate arithmetic pairings through weighted L1
at each positive damping.

## Why the comparison's fixed coefficients vanish

Define the logarithmic mean

    c_l0 = (1/log 2) integral_{A}^{2A} phi_l(x) dx/x,

which is independent of `A>0`. Then

    a_l(Q R_2) = (log 2)*c_l0.

Here is an exact finite-telescope justification that retains the endpoint.
The jumps of `R_2` are `1 - 2*1_{2|k}`. Truncating those jumps at `K` gives a
step combination that agrees with `R_2` on `k<=K` and is constant afterward.
Since `R_2` is bounded, these step combinations converge to `R_2` in the
physical weighted Hilbert norm. Their boundary coefficient is exactly

    sum_{K/2 < k <= K} phi_l(k)/k.

Taking a dyadic sequence `K=2^D A`, with positive integer `A`, converts this
to the logarithmic Riemann integral above. The terminal octave supplies a
nonzero quantity; canceling two divergent full sums would incorrectly erase
it.

Meanwhile, for `q=3^(-epsilon)`,

    a_l(stepAbel(epsilon))
      = (1-q) sum_{j>=0} q^j phi_l(3^(j+1)).

The log-periodic continuous function is sampled by an irrational rotation,
since `log 3/log 2` is irrational. Its Abel averages tend to `c_l0`. One can
prove this directly: for every nonconstant Fourier monomial the geometric
average tends to zero, then approximate the continuous periodic function by
trigonometric polynomials. Consequently

    a_l(C_epsilon) -> 0      for each fixed l.

For example, at `l=1`,

    a_1(Q R_2) = -2 log(3/2) + 4 log(4/3),

and the step-Abel coefficient tends to this number divided by `log 2`.
These two terms cancel in `C_epsilon`; neither may be discarded separately.

## Candidate exact Fourier multiplier identity: not yet a checked provider

Let `tau_h=2*pi*h/log 2`, `z_h=exp(i*tau_h*log 3)`, and let `c_lh` be the
Fourier coefficients in

    phi_l(x) = sum_h c_lh*x^(i*tau_h).

For fixed `l`, the coefficients are `O_l((1+abs(h))^(-2))`. The proposed
residue identification is

    a_l(T_m R_3)
      = c_l0*log 3
        + sum_{h!=0} c_lh*m^(i*tau_h)*(1-z_h)*zeta(1-i*tau_h).

The mean term comes from the removable limit
`(1-3^(-s))*zeta(1+s) -> log 3` at `s=0`; omitting it is an error.

If this identity and all indicated interchanges are established, the exact
arithmetic definition gives the particularly useful remainder formula

    a_l(E_epsilon)
      = sum_{h!=0} c_lh
          * (N_epsilon*zeta(1-i*tau_h)/zeta(1+epsilon-i*tau_h)-1)
          * (1-z_h)/(1-q*z_h).

This formula has not been formally verified here and should be recorded as
the next identity to prove, not as an established project theorem. A concrete
proof route is to regularize the jump Dirichlet series by an additional
positive real exponent, use its absolutely convergent identity, retain the
mean-pole limit, and then justify the Fourier limit. Uniform bounds in the
Fourier frequency are needed before removing that auxiliary exponent. At
fixed positive `epsilon`, the arithmetic conductor and Abel interchanges can
then use absolute convergence. No vanishing-damping interchange is automatic.

## A rigorous useful algebraic bound and the remaining obstruction

For `abs(z)=1` and `0<q<1`, the exact identity

    abs(1-q*z)^2 = (1-q)^2 + q*abs(1-z)^2

implies

    abs((1-z)/(1-q*z)) <= q^(-1/2).

Thus the proposed *remainder* multiplier retains cancellation of the apparent
triadic small divisors. It is uniformly bounded for `0<epsilon<=1/2`.
Applying an estimate to `(1-q*z)^(-1)` alone would discard this cancellation.

Even after the proposed multiplier identity, a fixed-`l` Fourier estimate is
not a bound on

    B(E_epsilon) = (1/4) sum_{l>=1} abs(a_l(E_epsilon))^2.

The constants, Fourier/boundary interactions, and growing-scale tail must
all be controlled together. Neither `O(1)` nor the stronger `O(epsilon)`
bound is proved by this review. Nor is either bound refuted. Full legal
recovery and complementary raw-lift energy remain separate from this
projected-family question.
