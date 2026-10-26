# Squarefree CRT cross moments and intrinsic reciprocal energy

Date: 2026-10-26.

## Status and scope

RH has not been proved. This continuation formalizes the handoff's signed
cancellation and cumulative-moment agenda and proves an unconditional
intrinsic dual-energy bound for the actual squarefree correction. The remaining
arithmetic provider is explicitly Open.

Source: the user's handoff
RH_Squarefree_Infinite_CRT_Weighted_Energy_Research_Handoff_2026-10-26.md,
based on checkpoint 30f5e3d178f915978faa01326f288a555af2d988.
These results use the actual masked squarefree stage, not an unrestricted
periodic approximation or the all-conductor legal space.

## Objects

Q(n)=1/(zeta(2)n^2) for positive integers. Let V_N be the span of g_d for
squarefree 2 <= d <= N+1, P_N its Q-orthogonal projection,
r_N=1-P_N1, Bf(n)=f(n)/(n+1), and b_N=P_N B r_N.

Let a_k(n)=n/(k+6+log n)^k and E_k(H,f)=sum_{1<=n<=H} a_k(n)Q(n)f(n)^2.
For a positive common modulus L, put u=C_L B r_N and e=u-b_N.
The complete conditional fibers and Q measure are retained.
The existing source bound is E_2(H,u)<=D, where
D=sum_{n>=1}1/[n(6+log n)^2]<infinity.

## Exact signed criteria

QSquarefreeCRTCrossCriterion.lean retains
s=x+t+2K, with x=E_2(H,b_N), s=E_2(H,u), t=E_2(H,e),
K=sum_{n<=H}a_2(n)Q(n)b_N(n)e(n), and R=t+2K=s-x.

For arbitrary positive moduli (divisibility is unnecessary for these identities):

* R>=-A implies x<=D+A.
* K>=-A implies x<=D+2A.
* -2K<=theta*x+t+A, theta<1, implies x<=(D+A)/(1-theta).
  No nonnegativity assumption on theta is needed.
* Existence of a cofinal constant bound on x is equivalent to existence of a
  cofinal constant lower bound on R, and also on K, after changing constants.
* If the actual limiting residual is nonzero, R and K tend to minus infinity
  along every divergent physical head and every positive-modulus schedule.

Each of the three bound hypotheses has a theorem concluding Mathlib's
RiemannHypothesis. These are conditional research reductions. The bounds are
not proved unconditionally for the actual corrections.

## Cumulative moments: exact Abel analysis

Define M(H)=sum_{n<=H}Q(n)b_N(n)e(n). Ordinary orthogonality gives the exact
identity
M(H)=||T_H b_N||_Q^2-<T_H b_N,T_H u>_Q
    =||T_H b_N-(1/2)T_H u||_Q^2-(1/4)||T_H u||_Q^2.

The scalar finite Abel identity is proved over every commutative ring in
Analysis/FiniteAbelSummation.lean. QHeadCrossMoments.lean specializes it:
K_k(H)=a_k(H)M(H)-sum_{t=0}^{H-1}(a_k(t+1)-a_k(t))M(t).

Define the nonnegative positive cumulative variation
Phi_k(H)=sum_{t=0}^{H-1}(a_k(t+1)-a_k(t))*max(M(t),0).
The physical coordinate zero contributes zero.

The established source tail bound yields
a_k(H)||T_H u||_Q^2/4 <= 1/2.
This constant is deliberately obtained from the existing checked tail bound;
the sharper paper constant 1/4 is not asserted by this declaration.

Consequently the actual correction satisfies, unconditionally at each common
modulus,
K_k(H)>=-1/2-Phi_k(H),
E_2(H,b_N)<=D+1+2 Phi_2(H).

Thus one fixed finite A and a divergent head H(N), with Phi_2(H(N))<=A at
arbitrarily large stages, imply RH. If the limiting residual is nonzero,
Phi_2(H(N)) tends to infinity for every divergent head and every common-modulus
schedule.

The conductor obligation has a concrete unconditional provider:
L(N)=(N+1)!. Every active conductor divides this factorial, regardless of
squarefreeness. Hence the factorial-modulus RH theorem has only the head
divergence and cofinal positive-variation bound as substantive premises.

A concrete one-sided sufficient condition is now proved:
for some C>=0, at arbitrarily large N, M_N(t)<=C/(t+1) for 0<t<H(N).
No lower bound on M_N(t) is assumed. The discrete profile estimate
a_2(t+1)-a_2(t)<=1/(8+log(t+1))^2 gives Phi_2(H)<=C*D.
The existing logarithmic-tail theorem proves D<=1/3, so
E_2(H,b_N)<=(4+2C)/3.
The factorial-modulus theorem
riemannHypothesis_of_frequently_reciprocal_cumulative_bound
therefore concludes RH from exactly this envelope and H(N)->infinity.
The envelope for the actual corrections remains Open.

The lower bound on M is not an upper bound on its positive part. Inserting
it into the negative Abel sum with the opposite inequality direction would
be invalid. The formal identities preserve that sign.

## An unconditional reciprocal dual-energy estimate

QReciprocalVariational.lean proves for arbitrary Q vectors
<r,Br>-[2<Br,v>-<v,Bv>]=<r-v,B(r-v)>
and <Br,v>^2 <= <r,Br><v,Bv>, together with
<f,Bf><=||f||^2/2.

For every v in the actual legal stage, QSquarefreeIntrinsicEnergy.lean proves
<r_N,Br_N>-[2<b_N,v>-<v,Bv>]=<r_N-v,B(r_N-v)>,
2<b_N,v>-<v,Bv> <= <r_N,Br_N> <= ||r_N||^2/2 <= 1/2,
and <b_N,v>^2 <= <r_N,Br_N><v,Bv>.

These statements are unconditional. The norm being controlled is the dual
norm of the compressed reciprocal form. It is not the requested unbounded
logarithmic energy.

A concrete paper transfer target is v=P_N W_H b_N, where W_H is the diagonal
multiplier a_2(n)1_{n<=H}. Then <b_N,v>=E_2(H,b_N)=x. If
<v,Bv><=C*x uniformly on suitable good stages, the homogeneous inequality
gives x^2<=C*x/2, hence x<=C/2. This transfer estimate remains Open.

## Numerical diagnostics, not proofs

Wolfram evaluated complete G,J,mu,nu by polygamma residue sums and solved
G c=mu, G alpha=nu-J c. The progression tails were not cut off.
Use an independent active dictionary: squarefree 2<=d<=N+1; do not invert
the masked Gram containing zero atoms.

Representative values (35--50 digit working precision, displayed rounded):

| N | H | E_2(H,b_N) | K | R=s-x |
|---:|---:|---:|---:|---:|
| 5 | 5 | 6.06508125e-7 | 2.06162704e-7 | 5.78156445e-7 |
| 10 | 10 | 1.05196010e-6 | 6.69859539e-7 | 3.43110689e-6 |
| 15 | 15 | 1.08948377e-6 | 2.68323344e-7 | 3.66189589e-6 |
| 30 | 30 | 1.01455947e-6 | 2.05462399e-7 | 2.56762667e-6 |
| 30 | 600 | 3.90086444e-6 | -3.63744075e-6 | 4.21497121e-7 |
| 30 | 6000 | 5.23245389e-6 | -4.98730436e-6 | -9.09275993e-7 |

The last row is numerical evidence against all-head nonnegativity of the
combined remainder. It does not refute a cofinal bounded negative part.
For N=30, t*M(t) was at most approximately 2.68022255e-4 for t<=6000,
and Phi_2(6000) was approximately 5.48798854e-6. This does not certify an
infinite or all-stage bound.

## Literature and transfer limits

The external sources support context and research direction, not the missing
arithmetic provider:

* Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of
  the Riemann hypothesis, https://arxiv.org/abs/math/0607733.
* Alouges--Darses--Hillion, Polynomial approximations in a generalized
  Nyman--Beurling criterion, https://arxiv.org/html/2006.02953v2.
  Its abstract and introduction explicitly separate unconditional approximation
  from coefficient/Gram control. That distinction remains essential here.

* Ehm, On certain Gram matrices and their associated series,
  https://arxiv.org/pdf/2405.06349, Theorem 2.1 and Section 8.1.
  The paper supplies continuous Mellin Gram decompositions but explicitly
  leaves its inversion-error estimate open. Its q=2 is a critical-line
  smoothing exponent, not this discrete probability measure Q.

A paper-level exact transfer, not separately formalized here, is
G_P(d,e)=A(d,e)-A(d,1)/e-A(1,e)/d+A(1,1)/(de),
where A is Ehm's q=1 Gram. It follows by embedding
g_d(floor x)={x/d}-{x}/d. Also
G_P=zeta(2)(G_Q-J_Q), mu_P=zeta(2)(mu_Q-nu_Q), so the actual forcing is
nu_Q-J_Q G_Q^{-1}mu_Q=(G_P G_Q^{-1}mu_Q-mu_P)/zeta(2).
The formula requires an independent basis when using inverses. These
identities do not supply a uniform estimate for that inverse or forcing.

Reproducible Wolfram code is included in CRTCrossMomentWolframDiagnostics20261026.md.
Those scripts perform diagnostics only and are not part of the Lean proof.

## Next arithmetic work

1. Prove the cofinal Phi bound for one divergent head. Equivalently for the
   signed criteria, seek a cofinal lower bound on K or R. Do not replace the
   actual b_N by the bounded source.
2. Investigate a one-sided bound M_N(t)<=C/(t+1) on the used heads, retaining
   the actual signed right-hand side nu-J G^{-1}mu. More permissive integrable
   envelopes may also suffice; a two-sided absolute estimate is unnecessary.
3. Investigate the reciprocal-form comparison for P_N W_H b_N. The newly
   proved intrinsic energy is available without an RH hypothesis.
4. Use complete-Q matrices and prime-adjunction/Schur complements only after
   verifying their squarefree legality hypotheses. Uniform Haar conditioning
   and generic preservation of the legal span remain invalid shortcuts.
5. A pointwise or finite numerical pattern is not the required all-stage or
   cofinal provider. Keep all unproved arithmetic obligations marked Open.

No source-level axiom, proof placeholder, or unsafe theorem substitute is used.
The final server checkpoint is the publication gate; individual snippet jobs
alone do not certify the final project delta. Workspace-opening client time
was not measured and is not counted as kernel verification duration.

## Verification record before publication

Saved-source check job_H0fcmf8vNcpwMN1fSyAvtX5uibrHyr6B succeeded,
verified=true, exit_code=0, reported elapsed_seconds=19.740.
The four inspected principal declarations depend only on propext,
Classical.choice, and Quot.sound. Their explicit arithmetic hypotheses remain
part of their theorem types. Queue delay reported by submission/start stamps
was below 0.001 seconds; client polling time is separate. Final publication
uses the server checkpoint, which validates the unpublished project delta.
