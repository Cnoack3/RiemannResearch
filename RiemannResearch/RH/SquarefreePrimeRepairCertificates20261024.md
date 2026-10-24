# Squarefree prime repairs: exact family, obstruction, and rational certificates

This note separates ordinary mathematical proofs from executable rational
certificates. The new bad-prime obstruction below has not itself been
formalized in Lean in this note. It makes no claim of an unconditional RH proof.

## An explicit family and its exact head

For an integer `N >= 1`, put

\[
A_N=\sum_{d=1}^{N}\frac{\mu(d)}d,\qquad
G_{N,q}=-\sum_{d=2}^{N}\mu(d)g_d+qA_Ng_q,
\qquad q>N\text{ prime}.
\]

All nonzero coefficients have squarefree conductors. The coefficient slope is
one, and for every positive integer `n`,

\[
G_{N,q}(n)-1
=n-1+\sum_{d=2}^{N}\mu(d)\lfloor n/d\rfloor
 -qA_N\lfloor n/q\rfloor. \tag{1}
\]

For `1 <= n <= N`, the last term vanishes and the classical finite Mobius
identity `sum_(d<=n) mu(d) floor(n/d)=1` proves `G_(N,q)(n)=1`.
The formula therefore supplies finite rational syntheses and exact physical
heads without a uniform-energy assumption.

For any finite coefficient family `c_d`, define

\[
L=-1+\sum_{c_d<0}c_d\frac{d-1}{d},\qquad
U=-1+\sum_{c_d>0}c_d\frac{d-1}{d},\qquad
B=\max(|L|,|U|).
\]

Because `0 <= g_d(n) <= (d-1)/d`, this gives the complete amplitude bound
`|G(n)-1| <= B`. Its ceiling is an executable nonnegative integer amplitude
certificate suitable for the online selector.

## A rigorous obstruction to unrestricted repair-prime choice

First, `A_N` never vanishes. For `N=1` it is one. For `N>=2`, Bertrand's
postulate gives a prime `p` with `N/2 < p <= N`. The only positive integer
`d<=N` divisible by `p` is `p`. Thus

\[
A_N=B_N-1/p,
\]

where the rational number `B_N` has a denominator coprime to `p`. Equality
to zero would require a rational with denominator coprime to `p` to equal
`1/p`, which is impossible after cross multiplication.

Let `V_N=-sum_(2<=d<=N) mu(d)g_d`. Since `P` is a probability measure and
`0<=g_d<=1`,

\[
\|V_N-1\|_P\le N.
\]

The first `q-1` coordinates give

\[
\|qg_q\|_P^2
\ge\sum_{n=1}^{q-1}\frac{n}{n+1}
\ge\frac{q-1}{2}.
\]

Consequently the reverse triangle inequality gives

\[
\|G_{N,q}-1\|_P
\ge |A_N|\sqrt{\frac{q-1}{2}}-N. \tag{2}
\]

Choose a prime `q_N>N` satisfying `q_N-1 >= 8 N^2/A_N^2`. The least such
prime is executable, and prime infinitude proves that its search terminates.
Equation (2) proves

\[
\boxed{\|G_{N,q_N}-1\|_P^2\ge N^2.}
\]

This is an entirely squarefree legal exact-head family whose complete
residual energies diverge. It does not disprove a bound for a better choice,
such as `q_N=nextprime(N)`. It does show that making a repair conductor very
large is not, by itself, a valid energy-control mechanism.

## Reproducible complete-norm certificates

The companion Python script `exact_head_rational_certificates.py` uses
integer and rational arithmetic throughout its certificates. Displayed
decimal numbers are approximations to exact rational interval endpoints.
It uses `q_N=nextprime(N)` and retains the signed expression (1) before
squaring. If `D=lcm(1,...,N)`, the numerator
`b_n=D*(G_(N,q)(n)-1)` is an integer, so no floating-point evaluation of the
residual occurs.

For a fixed grid size `S=2^bits`, each signed rational summand `x_n` is
enclosed by

\[
\frac{\lfloor Sx_n\rfloor}{S}\le x_n
\le\frac{\lfloor Sx_n\rfloor+1}{S}.
\]

Summing through cutoff `K` therefore has total rounding uncertainty at
most `K/S`. For squared residuals, the complete remaining tails satisfy

\[
0\le\sum_{n>K}\frac{r(n)^2}{n(n+1)}\le\frac{B^2}{K+1},
\qquad
0\le\sum_{n>K}\frac{r(n)^2}{n^2}\le\frac{B^2}{K}.
\]

For signed pairings of two residuals, the same bounds hold with two-sided
intervals and `B_1 B_2` in place of `B^2`. The script independently encloses
`zeta(2)` by a rational finite sum and the integral remainder interval
`[1/(K+1),1/K]`; interval division then certifies complete normalized
`Q` energies and pairings.

The JSON records feasibility, exact coefficients, amplitude bounds, finite
sum intervals, complete tail intervals, and full energies separately.

### Repair costs

The script does not numerically compute projection vectors or normal repair
costs. Let `p` be the complete-Q projection of one onto this same finite dictionary, let
`delta=||1-p||_Q^2`, and let `R` be the optimal feasible normal repair cost.
The feasible correction `G-p` and orthogonality give

\[
0\le R\le\|G-1\|_Q^2-\delta\le\|G-1\|_Q^2.
\]

Thus the certified Q-energy upper endpoints also give upper certificates
for `R`, with no claim that they are its actual values.

More precisely, in the restricted dictionary consisting of squarefree
conductors at most `N` and the single prime `q>N`, the exact-head feasible
vector is unique. Indeed, zero head values force the total linear slope
and all conductor coefficients through `N` to vanish by the triangular
finite-difference/Mobius identities; the remaining `q` coefficient must
then vanish as well. Thus equality holds in the first upper inequality
for this restricted dictionary. Enlarging the dictionary can lower the
optimal complete repaired error, so its candidate energy remains a valid
upper certificate after enlargement.

## The remaining arithmetic estimate

For the specified next-prime family, the unresolved estimate is a bound
uniform in `N` for the complete sum of the square of (1), weighted by
`1/(n(n+1))`. Exact heads, rational coefficients, small energies in a
finite table, and the bad-prime obstruction establish none of that
uniform estimate.

The useful analytic target suggested by the certificates is a signed
window estimate for (1), followed by a summable bound on all remaining
windows. Bounding its Mobius sum and prime correction separately loses
the cancellation visible in the computed complete energies. Neither a
uniform bound nor subpolynomial repair growth has been established here.
