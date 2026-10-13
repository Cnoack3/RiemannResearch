# Backward RH audit: conditional A and B

Source: the user's request to verify the preceding backwards-RH argument with Lean before attempting either missing arithmetic estimate. The deductions below are independently formalized; no mathematical novelty is asserted.

## Scope

The intended verification concerns exact conditional statements in the actual full Pareto Hilbert spaces and the actual compact spectral system. Neither arithmetic lower bound A nor contrast bound B is supplied. A successful implication theorem does not discharge a hypothesis appearing in its type.

Project stage `n` uses conductors through `n+1`; tripling the cutoff is therefore `3*n+2`. The project dilation is scaled by `m`; the floor dilation used in this argument is its multiple `1/m`.

## A: innovations and the quantifier correction

Write `d_N` for the squared full projection error at conductor cutoff N, and `I_(m,N)=<r_N,D_m F_N>` for m=2,3. Define

`A_N = 2 I_(2,N)^2 + 3 I_(3,N)^2`.

The exact signed identity pairs each innovation with `F_(3N)-F_N`. Cauchy--Schwarz gives

`A_N <= 2 (d_N-d_(3N)) (1-d_N)`.

For any fixed eta>0, the lower bound `A_N >= eta d_N^2` on a cofinal set implies d_N tends to zero and hence RH. The same conclusion follows from the weaker cofinal quartic lower bound `A_N >= eta d_N^4`.

An additional exact orthogonality identity removes the previous-scale column `D_m F_(N/3)`. For N divisible by three,

`A_N <= 2 (d_(N/3)-d_N) (d_N-d_(3N))`.

Consequently `A_N >= eta d_N^2` at a middle stage already forces

`d_N <= (2/(2+eta)) d_(N/3)`.

Imposing this at every geometric stage yields geometric decay in the scale index. The earlier quadratic-recurrence upper bound is a valid but weaker consequence. It must not be used to suggest the every-scale quadratic-source hypothesis is compatible with a logarithmic lower barrier.

The quartic exponent is a suggested future research target: for a model `d_N ~ C/log N`, both adjacent gains have size `d_N^2`, so their product has size `d_N^4`. This is an upper-bound scale calculation, not evidence of a positive lower bound for the actual innovations.

## B: Jensen and the critical moving margin

For all actual nonnegative weights and eigenvalues, write

`T = sum w lambda/(1+lambda)`,
`S = sum w lambda/(1+lambda)^2`,
`J = sum [w lambda/(1+lambda)] log(1+log(1+lambda))`.

For T>0, S>0 and finite weighted Jensen gives

`J >= T log(1+log(T/S))`.

The convex function is `f(x)=log(1-log x)` on `0<x<=1`. Its second derivative is `-log x / [x^2 (1-log x)^2] >= 0`.

Given a positive tail envelope sigma, put `ell=1+log(1/sigma)` and `D=log ell`. Along a cofinal sequence, the budget

`J/D <= (1-1/ell) T + E`, with `ell E -> 0`,

forces the limiting correction to zero. The finite expression is used only once D>0, which is automatic eventually. Equivalently the actual complete contrast must satisfy

`C >= [h(L)-D+D/ell] T - D E`.

All weights, eigenvalues, and signed contrast terms are retained. The remaining contrast inequality is an open domain-specific obligation.

## Endpoint implication

The actual first-site-subtracted Gram inequality is `(x-a/2)^2 <= (y/2)(x-a^2/2)`, where x is the doubled-cutoff energy, y the lower-cutoff energy, and a the upper residual at the first site. The bound `a <= (2-sqrt(2)) y` yields `x <= y-[(4 sqrt(2)-5)/7] y^2`. The corresponding cofinal bound with an additive error tending to zero implies RH. The first-coordinate upper bound remains an open arithmetic hypothesis.

## External rate comparison

Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function* (2001), Theorems 1.2--1.3, https://arxiv.org/pdf/math/0103058, supplies the classical Nyman--Beurling logarithmic lower barrier.

For the full residue space, the continuous lift of `F_N(n)=sum a_d {n/d}` is `sum a_d {x/d} - (sum a_d/d){x}`. It equals F_N(floor x) for x>=1 and vanishes for 0<x<1. Under t=1/x its error integral is the full Pareto error, and every dilation parameter is at least 1/N. This is the analytic comparison to Burnol; it is distinguished from the Lean-checked finite adjacent-gain implication. The present checkpoint does not formalize Burnol's theorem.

## Verification record

The weighted Jensen development passed server job `job_2PqCYLwfPx6ZHDHVbzC-_Eov09fGYaoF` (exit 0), with only `propext`, `Classical.choice`, and `Quot.sound`. The actual A and endpoint declarations produced the same foundational axiom list in the development audit. Publication is gated on the final checkpoint validating all persisted modules and their integration. No open arithmetic provider has been attacked or claimed.
