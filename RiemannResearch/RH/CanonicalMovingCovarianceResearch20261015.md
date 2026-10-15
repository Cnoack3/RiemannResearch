# Canonical moving-test covariance and the full Q-energy gap

Date: 2026-10-15.
Base: [e9118f357f93f48a5364c9f53bbe381d7783d8a0](https://github.com/Cnoack3/RiemannResearch/commit/e9118f357f93f48a5364c9f53bbe381d7783d8a0).

Source: the user's moving-test extension of the October 15 fixed-test theorem.
The additional arguments use the repository's checked complete-tail identities,
finite Cauchy--Schwarz, and existing quantitative PNT providers. No novelty
claim is made.

## 1. Measures and the actual canonical family

Use the physical sequence spaces with

\[
P(n)=\frac1{n(n+1)},\qquad Q(n)=\frac1{\zeta(2)n^2}\quad(n\ge1).
\]

For the same physical sequence \(u\), the established complete comparisons are

\[
\|u\|_P^2\le\zeta(2)\|u\|_Q^2\le2\|u\|_P^2.
\]

The October 15 fixed-test module is in the Pareto namespace. The new Q module
constructs the actual Q encoding and checks its change of weights, rather than
identifying differently weighted inner products.

Put \(g_d(n)=(n\bmod d)/d\), and define exactly

\[
m(N)=\sum_{d=1}^N\frac{\mu(d)}d,\qquad
F_N=-\sum_{d=1}^N\mu(d)g_d+(N+1)m(N)g_{N+1},\qquad r_N=1-F_N.
\]

The boundary correction is part of the family. The existing theorem gives
\(F_N(n)=1\) for \(1\le n\le N\), and

\[
|r_K(n)|\le1+2K\quad(K\ge1,\ n\ge1).
\]

The nonzero Mobius terms have squarefree conductors. The correction has a
squarefree conductor whenever \(N+1\) is squarefree; in particular \(N=p-1\)
works for every prime \(p\). An arbitrary cutoff is legal in the unrestricted
residue family, but its correction need not have squarefree conductor.

## 2. Sufficient conditions for moving tests

Write

\[
\delta_N^P=\frac{\|r_N\|_P^2}{N+1},\qquad
\delta_N^Q=\frac{\|r_N\|_Q^2}{N+1}.
\]

For any moving physically bounded tests \(|f_N(n)|\le A_N\), \(A_N\ge0\),
the checked estimates are

\[
|\langle f_N,r_N\rangle_P|^2\le A_N^2\delta_N^P,\qquad
|\langle f_N,r_N\rangle_Q|^2
 \le\frac2{\zeta(2)}A_N^2\delta_N^Q.
\]

Thus \(A_N^2\delta_N^P\to0\), respectively \(A_N^2\delta_N^Q\to0\),
implies the corresponding pairing tends to zero.
No fixed-test hypothesis is hidden in this application.

For canonical tests it suffices that \((1+2K_N)^2\delta_N^P\to0\).
The Q comparison also gives

\[
\delta_N^Q\le\frac2{\zeta(2)}\delta_N^P,\qquad
|\langle r_K,r_N\rangle_Q|^2
 \le\left(\frac2{\zeta(2)}\right)^2(1+2K)^2\delta_N^P.
\]

All physical coordinates are included.

## 3. An unconditional explicit growing cutoff

Qualitative PNT gives sublinear energy. More is available in the existing
CanonicalMobiusStretchedEnergy.lean: there are \(a>0\), \(C\ge0\), such that
eventually

\[
\|r_N\|_P^2\le8+CN\exp[-a\Phi(6+\log N)],
\qquad \Phi(s)=(s\log s)^{1/11}.
\]

The new proof uses the existing elementary inverse-square majorant for a
stretched exponential and proves \((6+\log N)^2/N\to0\).
Consequently there is \(D\ge0\) such that eventually

\[
\boxed{\delta_N^P\le\frac{D}{(6+\log N)^2}.}
\]

Let

\[
L_N=6+\log N,\qquad
\boxed{K_N=1+\left\lfloor\sqrt{L_N}\right\rfloor.}
\]

This is a concrete, positive cutoff and \(K_N\to\infty\).
Eventually \(K_N\le2\sqrt{L_N}\), so the proof bounds its block budget by

\[
K_N(1+2K_N)^2\delta_N^P
\le\frac{50D}{\sqrt{L_N}}\longrightarrow0.
\]

In particular \(\langle r_{K_N},r_N\rangle_P\to0\) and
\(\langle r_{K_N},r_N\rangle_Q\to0\).
This proves unconditional existence and supplies an explicit prescription.
The arithmetic constants and the starting index remain existential;
no numerical onset or optimal growth rate is certified.

## 4. Growing columns and signed or convex test averages

Define the complete covariance column energies

\[
B^P(K,N)=\sum_{k=1}^{K}|\langle r_k,r_N\rangle_P|^2,\qquad
B^Q(K,N)=\sum_{k=1}^{K}|\langle r_k,r_N\rangle_Q|^2.
\]

The checked bounds are

\[
B^P(K,N)\le K(1+2K)^2\delta_N^P,\qquad
B^Q(K,N)\le
\left(\frac2{\zeta(2)}\right)^2K(1+2K)^2\delta_N^P.
\]

Both vanish for the explicit \(K_N\), controlling any selected test inside
that block. The code indexes these tests by \(k+1\) for \(k\) in Finset.range K.

For \(T_N=\sum_{k=1}^{K_N}a_{N,k}r_k\), finite Cauchy--Schwarz gives

\[
|\langle T_N,r_N\rangle_Q|^2
\le\left(\sum_{k=1}^{K_N}a_{N,k}^2\right)B^Q(K_N,N).
\]

Bounded squared coefficient mass therefore gives pairing decay.
Convex weights are included because nonnegativity and sum one imply
\(\sum_k a_{N,k}^2\le1\). The same statements are checked for P.

These are complete column and pairing estimates. They do not control
\(\|T_N\|^2\) or the quadratic form of the moving square covariance matrix.

## 5. Exact full Q energy and the remaining uniformity estimate

For finite \(s\), with arbitrary signed coefficients \(a_k\), the development
retains the exact identities

\[
\begin{aligned}
C^Q_{kl}
 &=\langle r_k,r_l\rangle_Q\\
 &=\sum_{n=1}^{\infty}
   \frac{(1-F_k(n))(1-F_l(n))}{\zeta(2)n^2},\\
\left\|\sum_{k\in s}a_kr_k\right\|_Q^2
 &=\sum_{k,l\in s}a_ka_lC^Q_{kl}\\
 &=\sum_{n=1}^{\infty}\frac1{\zeta(2)n^2}
   \left(\sum_{k\in s}a_k(1-F_k(n))\right)^2.
\end{aligned}
\]

All diagonal terms, signed cross terms, and the infinite tail remain.

The exact additional sufficient estimate is: there is one real \(C\) such that
for every head length \(M\) one can choose finite \(s_M\) and \(a_{M,k}\) with

\[
\begin{gathered}
k\in s_M\ \Longrightarrow\ k\ge M,\quad k+1\text{ squarefree},\\
\sum_{k\in s_M}a_{M,k}=1,\qquad
\boxed{\sum_{k,l\in s_M}a_{M,k}a_{M,l}C^Q_{kl}\le C.}
\end{gathered}
\]

Then \(A_M=\sum_{k\in s_M}a_{M,k}F_k\) is a finite squarefree legal combination,
equals one on \(1,\ldots,M\), and has uniformly bounded complete energy.
The checked conditional consumers give Q squarefree closure membership and RH.
For convex averages add \(a_{M,k}\ge0\); the same sufficient estimate applies.

**Open:** an arithmetic provider of this uniform signed or convex energy budget.
Neither the new column estimates nor the PNT ceilings supply it.
The ceiling \(\|r_N\|_P^2\le(N+1)D/L_N^2\) still allows unbounded energies.
Decay of entries separately cannot discard diagonal energies or justify an
interchange with an increasing double sum.

This uniformity goal has RH strength for this route. The existing Mellin
obstruction is compatible with PNT sublinear energy bounds, while excluding
bounded exact-head legal averages if an off-line zero exists.

## 6. A diagnostic showing why the available abstract bounds are insufficient

This is an analytic example, not a new Lean theorem and not a model of the
legal arithmetic span.

In the actual Q-weighted space let \(h(n)=n^{1/4}\) and, for \(N\ge1\), set

\[
S_N=\frac1{\zeta(2)}\sum_{n=N+1}^{2N}n^{-3/2},\qquad
u_N(n)=\frac{n^{1/4}{\bf1}_{N<n\le2N}}{S_N}.
\]

Exactly,

\[
\langle h,u_N\rangle_Q=1,\qquad
\|u_N\|_Q^2=S_N^{-1},\qquad u_N(n)=0\quad(n\le N).
\]

Counting the \(N\) terms gives

\[
\frac1{2^{3/2}\zeta(2)\sqrt N}\le S_N
 \le\frac1{\zeta(2)\sqrt N},
\qquad
\zeta(2)\sqrt N\le\|u_N\|_Q^2
 \le2^{3/2}\zeta(2)\sqrt N.
\]

Each physical sequence is bounded, with amplitude at most
\(2^{7/4}\zeta(2)N^{3/4}\), hence at most \(1+2N\) for all sufficiently large N.
The normalized energy tends to zero at this stronger rate, and the same
support-based bounded-test estimates apply.

Nevertheless any signed average \(v_M=\sum a_Nu_N\), with all \(N\ge M\) and
\(\sum a_N=1\), satisfies

\[
1=\langle h,v_M\rangle_Q^2
\le\left(\frac1{\zeta(2)}\sum_{n>M}n^{-3/2}\right)\|v_M\|_Q^2.
\]

The tail factor tends to zero, so these energies cannot be uniformly bounded.
Support, bounded physical tests, and sublinear energy rates alone therefore
do not imply the missing budget. Further joint arithmetic structure of the
actual legal residuals must enter. This example does not rule out a proof
using additional exact arithmetic identities.

## 7. Declarations and status

All names have prefix RiemannResearch.RH.

| File | Main declarations | Status |
| --- | --- | --- |
| CanonicalMobiusMovingCovariance.lean | Pareto.MovingCovariance.moving_test_tendsto, moving_canonical_tendsto, blockEnergy_le, blockAverage_tendsto | Unconditional |
| CanonicalMobiusMovingCutoff.lean | Pareto.MovingCovariance.energyRate_eventual_log_square, exists_growing_canonical_tests, explicitCutoff_blockEnergy_tendsto, signed and convex block limits | Unconditional, using checked quantitative PNT |
| QCanonicalMovingCovariance.lean | QCanonicalMovingCovariance.moving_test_tendsto, explicitCutoff_covariance_tendsto, explicitCutoff_blockEnergy_tendsto, signed and convex block limits | Unconditional Q results |
| QCanonicalAverageEnergy.lean | QCanonicalMovingCovariance.residualAverage_energy, residual_covariance_weighted, residualAverage_weighted | Exact complete Q identities |
| QCanonicalAverageEnergy.lean | QCanonicalMovingCovariance.squarefree_closure_of_bounded_residual_gram, riemannHypothesis_of_bounded_residual_gram | Conditional research reductions; full Gram budget Open |

The final publication gate validates the saved delta and its aggregate import
before pushing. Isolated snippet checks alone do not certify the entire project.
No unconditional squarefree closure or RH is asserted.
