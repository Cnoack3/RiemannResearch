# Full-conductor fixed-modulus oscillation

Prepared 9 November 2026.

## Result and remaining obligation

The actual full-conductor displacement is still not proved bounded. No proof of RH is claimed.
The Lean declarations give an exact matched Q/P dual identity for the signed carry expression and
reduce a sufficient estimate to complete finite Gram matrices on an expanding physical head.
The modulus L and bound C must stay fixed; the head H_j may tend to infinity arbitrarily slowly.

The relevant existing modules were unchanged between commit
400f31ac10335de7029ff4ae317e6105dcdb8014 and the inspected base
82a186b4567a89c6d22319f26b73c718de358b25. The latter adds squarefree research;
the application here uses the full displacement and all divisor conductors.

## Setup and the exact identity

Put P(n)=1/[n(n+1)], Q(n)=1/[zeta(2)n^2], and g_q(n)=(n mod q)/q for n>=1,
with physical value zero at n=0. Let S be a closed physical subspace in Q and T the same
subspace in P. Set f_Q=Pi_S^Q 1, f_P=Pi_T^P 1, d=f_Q-f_P, and r_P=1-f_P.
Write D h(n)=h(n)/n in Pareto coordinates.

Let e_n represent physical evaluation in Q, and define
\[
 K_{n,m}=\Pi_S^Q(e_n-e_m),\qquad
 W_{n,m}=(I-\Pi_T^P)D K_{n,m}.
\]
The transports between Hilbert coordinate models are explicit in Lean.

The matched normal equations give the signed identity
\[
 \boxed{\zeta(2)[d(n)-d(m)]=\langle r_P,W_{n,m}\rangle_P.}
\]
Indeed, Q-orthogonality gives <d,K>_Q=<r_P,K>_Q.
The metric identity zeta(2)<u,v>_Q=<u,v>_P+<u,Dv>_P and P-orthogonality
remove <r_P,K>_P. P-orthogonality also removes the projection of DK.
These are identities for the actual residual; no assumed decay or invariance is used.

The exact energy is
\[
 \|W_{n,m}\|_P^2
 =\|D K_{n,m}\|_P^2-\|\Pi_T^P D K_{n,m}\|_P^2.
\]
Only after retaining that subtraction do we use
\[
 \zeta(2)|d(n)-d(m)|\le\|r_P\|_P\,\|W_{n,m}\|_P.
\]
The inequality can lose cancellation between r_P and W; the signed identity remains primary.

For the actual full closure, set n=kL+t and m=t. The existing exact carry formula yields
\[
 \boxed{\zeta(2)\left[d(kL)+
 \sum_{\substack{1\le q\le kL+t\\q\nmid L}}
 b_q(d)\,\mathbf1_{(kL\bmod q)+(t\bmod q)\ge q}\right]
 =\langle r_P,W_{kL+t,t}\rangle_P.}
\]
Here b_q(f)=sum_{a|q} mu(q/a)[f(a)-f(a-1)].
No endpoint, prime power, or signed summand has been omitted.

## A weaker finite-stage sufficient estimate

Use the existing full divisor spaces S_j=span{g_q:q|R_j}, with nested,
divisor-exhausting positive periods R_j, and their matched P spaces T_j.
The existing convergence identifies d_j with the actual full d in the limit.

It suffices to find a fixed L>=1, finite C, and H_j tending to infinity such that
\[
 \|r_{P,j}\|_P\,\|W_{j;n,m}\|_P\le\zeta(2)C
 \quad(1\le n,m\le H_j,\ n\equiv m\pmod L).
\]
For each fixed pair, the head eventually contains both sites, so the bound passes to the
pointwise limit. The existing fixed-modulus implication then gives RH.

This hypothesis is Open. Finite observations, Hilbert convergence, compactness of D,
and finite-stage periodicity do not prove it. A uniform operator estimate for every target
would be stronger than needed. The exact signed pairings for target 1 may be much smaller.

## Complete finite matrix certificate (paper deduction)

Choose a basis g of the finite dictionary and let
\[
 G_Q=(\langle g_a,g_b\rangle_Q),\quad G_P=(\langle g_a,g_b\rangle_P),\quad
 J=(\langle g_a,Dg_b\rangle_P),\quad
 J_2=(\langle Dg_a,Dg_b\rangle_P).
\]
Let beta=g(n)-g(m), kappa=G_Q^{-1} beta, and E_P=||r_P||_P^2. Then
\[
 \|W_{n,m}\|_P^2
 =\kappa^T[J_2-JG_P^{-1}J]\kappa.
\]
The missing sufficient estimate is therefore
\[
 E_{P,j}\,\beta^T G_{Q,j}^{-1}
   [J_{2,j}-J_jG_{P,j}^{-1}J_j]G_{Q,j}^{-1}\beta
 \le\zeta(2)^2C^2
\]
on the expanding heads, at one fixed modulus. This is a finite, computable statement for
each stage. Its uniform validity is not established. This matrix translation is a
paper deduction tested numerically. The Lean theorem uses the Hilbert-space kernel norm.

For the constant target, c_P=G_P^{-1}b_P and c_Q=G_Q^{-1}b_Q. In addition,
\[
 \zeta(2)(c_Q-c_P)
 =G_Q^{-1}[\zeta(2)b_Q-b_P-Jc_P].
\]
This equality preserves the cancellation of the forcing and its fitted component.

## Numerical method and limitations

The script uses all conductors q|R, q>=2, including R and every prime power.
It sums each complete infinite residue class analytically. For a=1,...,R:
\[
 P_R(a)=[\psi((a+1)/R)-\psi(a/R)]/R,\quad
 Q_R(a)=\psi_1(a/R)/[\zeta(2)R^2].
\]
The D and D^2 folded weights are zeta(2)Q_R-P_R and
zeta(3,a/R)/R^3-zeta(2)Q_R+P_R.
Thus no physical tail has been truncated. SciPy evaluations and matrix solves are
floating point, not interval certificates. Negative eigenvalues from roundoff would be
clipped only for square roots; the raw minimum eigenvalue is recorded. In this run all
recorded minimum eigenvalues were positive. Maximum normal-equation defects are below
8e-16; maximum signed coefficient-identity defect is below 6e-13.
These diagnostics do not replace rigorous error enclosures.

For fixed modulus 2, the complete-period oscillation is computed over residue classes
mod gcd(R,2); this covers every pair of positive physical integers, including the
positive site R representing residue zero. The head is 1,...,M for R=lcm(1,...,M).

| R | M | complete oscillation | complete screened Cauchy bound | head oscillation | head screened Cauchy bound |
|---:|---:|---:|---:|---:|---:|
| 6 | 3 | 0.015436 | 0.076829 | 0.005769 | 0.068943 |
| 12 | 4 | 0.024297 | 0.080466 | 0.022240 | 0.076864 |
| 60 | 5 | 0.048647 | 0.121125 | 0.024877 | 0.064051 |
| 420 | 7 | 0.122413 | 0.238272 | 0.024588 | 0.051503 |
| 840 | 8 | 0.140514 | 0.304148 | 0.025895 | 0.053242 |
| 2520 | 9 | 0.164655 | 0.427829 | 0.022763 | 0.053349 |

The tests give evidence against assuming that complete oscillation decreases with
Hilbert error, or that the screened kernel diameter is bounded by 1. They do not
refute existence of some uniform finite bound. The much smaller head bounds motivate
the head criterion; six small nontrivial stages cannot establish its uniform estimate.

## Endpoint, prime-power, and binary-limit tests

For f=g_8, L=60, k=1, t=4, the escaping conductor 8 contributes b_8(f)=-1:
\[
 f(64)-f(4)=-1/2=f(60)-1=1/2-1.
\]
For t=1 the carry sum is zero while f(61)-f(1)=f(60)=1/2.
These explicitly rule out deleting the endpoint or restricting escaping conductors to
primes not dividing L. The Lean examples verify the first arithmetic witness
and its endpoint/carry cancellation. The script also performs 54 exact rational
carry-identity checks, independently of the floating-point Gram calculations.

The actual matched displacement at R=2520 also retains this cancellation. With
L=60,t=4,k=1, its endpoint is approximately -0.0125687533. Its nonzero carry
contributions in this identity are:

| q | signed contribution |
|---:|---:|
| 7 | -0.0279977070 |
| 8 | -0.0012044489 |
| 9 | +0.0082896267 |
| 21 | +0.0327784170 |
| 63 | -0.0160828192 |

Their signed sum is -0.0042169314, giving d(64)-d(4)=-0.0167856847 after
the endpoint is added. The powers 8 and 9 escape although their prime bases divide 60.

For F_J=sum_{k=1}^J g_{2^k}, the known limit is the binary digit sum s_2.
At fixed modulus 2, s_2(2^J-1)-s_2(1)=J-1; at J=32 this is 31 even though
the established paper tail estimate for F-F_32 is about 5.21e-5 in P norm.
For L=2,t=1,k=7, the carry sum for s_2 is zero but its endpoint s_2(14)=3
accounts for the entire difference. This directly exposes an endpoint-only obstruction.

The binary approximants are not the matched target-one projections: their normal
equations against g_2 have nonzero defects (recorded in the JSON). Thus this example
tests the invalid general periodic-limit inference; it is not a counterexample to a
new bound using both actual normal equations. The infinite digit-sum counterexample
remains paper-level here; it is not represented as newly kernel-checked.

## Lean modules and experiment

- Analysis/ResidueOscillation.lean: add bound_of_expanding_head_limit.
- RH/QMatchedOscillationKernel.lean: generic matched test identity, physical pair
  kernel, exact screened energy, and Cauchy bound, for explicitly matched Q/P spaces.
- RH/QFullOscillationDual.lean: exact full carry pairing, conditional head-kernel
  criterion, and concrete endpoint/prime-power examples.
- RiemannResearch.lean: export the two new modules.
- [Finite experiment](FullOscillationFiniteExperiment20261109.md): complete-period
  calculations, the reproducer, and numerical diagnostics.

The existing LCM projection construction is reused without changes. No continuity of
a profinite limit, reciprocal invariance of the legal closure, or RH is assumed.

## Verification evidence

The [verification record](FullOscillationVerification20261109.md) gives the
Bazel file-check result, source hash, and executable axiom audit. The file
check covers the application and its transitive imports. The audit checks
axiom dependencies of 21 selected declarations.

The expanding-head theorem is a **conditional research reduction**.
Its uniform kernel-product premise remains **Open**.

## Source

The existing closure-to-RH route agrees with Bagchi, Theorem 1,
On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis:
https://arxiv.org/html/math/0607733v1 . This source supports the weighted legal-closure
criterion; it does not supply the missing oscillation or screened-kernel estimate.
