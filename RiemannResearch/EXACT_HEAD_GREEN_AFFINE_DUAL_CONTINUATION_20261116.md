# Exact-head Green continuation: affine duality and certified moments

Date: 16 November 2026 (America/Los_Angeles).
Base: `2ac5952fb4fb0efd67d12408390c8ed7fa3fa07a`.

## Mathematical changes

Let `R` be the actual complete-weight atom residual, `q=||R||²`, `b` its
Green profile, and `h(d)=c0+c1*d/x` its squarefree-weighted affine normal fit.
Let `e=b-h`, `w(d)=mu(d)²/d`, and `t(d)=d/x`.

For every affine observer `a(d)=a0+a1*t(d)`, the exact normal equations give

    <mu,e>_w = <mu-a,e>_w.

The new finite theorem retains the full two-coordinate Gram remainder before
estimating. Consequently

    (signedSum(b)-signedSum(h))² <= sigma_x * E_aff,x,
    sigma_x = sum_{d<=x} w(d) (mu(d)-a(d))².

Choosing the observer's own affine normal fit exists for every x>=2 and gives
`0 <= sigma_x <= W_x`. More precisely, with `W,V,U,m0,m1,Delta` as in the
handoff, the exact removed energy is

    Delta * (W-sigma) = U*m0² - 2*V*m0*m1 + W*m1².

This is finite Hilbert projection algebra, not a new asymptotic theorem.
At cutoff 5 the normal observer is

    a0=229/191, a1=-590/191, sigma=160/191, W=61/30.

The old full-mass criterion remains a corollary of the new direct signed-error
criterion. For the actual affine fit the sufficient jointly cofinal hypotheses
are now

    sigma_x E_aff,x <= k² q_x² + C q_x,
    m_x <= (1-delta) q_x + B,          0 <= k < delta, C >= 0.

The observer coefficients may vary with x; no uniform coefficient bound is
assumed. Both conditions must hold at the same stages. The full legal norm
still includes the terminal term. No target-closure or bounded-q assumption
has been introduced.

## Finite cutoff-five providers

The period is 30. The signed probe is explicitly

    psi_5(r) = [111*r - 7*floor(r/2) - 125*floor(r/3)
                - 361*floor(r/5)]/191.

A six-decimal rational upper-atom correction at divisors 6,10,15 is

    (349246, -1152475, -1432725)/1000000.

Its complete centered-probe energy for alpha=1/2 lies in `[0.6288,0.63]`.
The period's 29 nonterminal residues and every infinite progression tail
are retained. This strengthens the finite proposed upper bound 2/3.

A separate certificate uses the existing trial optimizer coefficients and a
tighter normal-defect budget. It bounds the actual fitted moment in
`[0.0251,0.0282]`. Together with the existing actual energy lower bound
`q_5>=0.0379`, this proves the finite proportional target

    m_5 <= (3/4) q_5.

The trial coefficients only propose a vector. The actual-optimizer conclusion
uses the proved observation-error inequality. No numerical inverse is assumed.

## A necessary head test for R5

Every upper atom and every upper-span correction vanishes at r<=x. The
canonical target also vanishes on the positive head. Therefore, for every
alpha and every legal upper-span correction v,

    H_x := sum_{r=1}^x psi_x(r)²/[r(r+1)]
      <= ||psi_x-alpha*C_P-v||²_complete.

This test depends only on x, so it can be evaluated before constructing P.
At x=5, `0.6026 <= H_5 <= 0.6027`. At x=3, `H_3=49/72>2/3`, independently
of alpha and v. The latter excludes an all-cutoff 2/3 bound, but does not
exclude the handoff's proposed eventual/cofinal bound starting after stage 3.

Any **full-energy** centered-probe provider must control this uncorrectable
head as well as the remaining residues. Optimizing an upper correction
cannot remove head cost. The complementary-energy criterion in
`RH/ExactHeadAtomMoment.lean` and the
[tail continuation](EXACT_HEAD_GREEN_TAIL_CONTINUATION_20261116.md)
omit the head from the signed observation because the optimizer is zero
there. That weaker sufficient R5 route does not require a uniform
head-energy bound.

The companion [head-coercivity derivation](EXACT_HEAD_GREEN_HEAD_COERCIVITY_DERIVATION_20261116.md)
uses elementary squarefree asymptotics to derive, on paper,
`H_x` comparable to `x*m0(x)^2 + Mertens(x)^2/x`. This asymptotic step is
**not yet formalized in Lean**. It indicates why a global uniform R5 bound
would already force the strong bound `Mertens(x)=O(sqrt(x))`; a cofinal
bound yields control only on those stages.

## Published material checked and its role

1. Luis Baez-Duarte, *A strengthening of the Nyman-Beurling criterion for the
   Riemann hypothesis*, Rend. Lincei Mat. Appl. 14 (2003), 5-11,
   [author manuscript](https://arxiv.org/abs/math/0202141).
   This supports the natural-dilation closure criterion. Its RH-to-approximation
   proof uses RH; those approximation estimates cannot be reused as unconditional
   providers for the present implication.
2. Jean-Francois Burnol, *A lower bound in an approximation problem involving
   the zeros of the Riemann zeta function*, Adv. Math. 170 (2002), 56-70,
   [author manuscript](https://arxiv.org/abs/math/0103058).
   Its bound concerns the classical approximation distance, not this q_x.
   No transfer of its lower-bound scale to exact-head q is asserted.
3. Sandro Bettin, J. Brian Conrey and David W. Farmer, *An optimal choice of
   Dirichlet polynomials for the Nyman-Beurling criterion* (2013), Theorem 1,
   [author manuscript](https://arxiv.org/abs/1211.5191).
   The matching optimal approximation result assumes RH and a reciprocal
   zeta-derivative moment condition. It motivates signed, smoothed coefficients,
   but cannot discharge R4 or R5 without circularity.
4. Francois Alouges, Sebastien Darses and Erwan Hillion, *Polynomial
   approximations in a generalized Nyman-Beurling criterion*, JTNB 34 (2022),
   767-785, [published article](https://doi.org/10.5802/jtnb.1227).
   Its separation of approximation from coefficient control supports treating
   the remaining quantitative Gram bound as a separate obligation.
5. Werner Ehm, *On certain Gram matrices and their associated series*,
   [primary preprint, 2024](https://arxiv.org/abs/2405.06349), Sections 8.1-8.3.
   The centered mixed-moment decompositions motivate retaining signed cross
   terms. His discussion explicitly leaves key product estimates unresolved;
   it does not provide the uniform estimate sought here. This is a preprint,
   distinguished from the published articles above.

The new finite projection identities are independently assembled from the
repository's weighted Gram and affine-completion identities. They are not
claimed to be theorems quoted from these papers, nor claimed to be novel.

## Revised research agenda

| Priority | Next task | Acceptance criterion |
|---|---|---|
| R4 | Estimate the direct signed affine residual pairing, with the projected Mobius factor as a fallback | Jointly cofinal `(signedSum(b)-m)² <= k²q²+Cq`, `k<delta`; no bounded-q premise |
| R5-head | Formalize the head coercivity derivation in the companion note; distinguish global from cofinal bounds | A checked comparison of H_x with x*m0(x)^2+M(x)^2/x |
| R5-tail | Construct upper-span corrections after accounting for the head lower bound | Complete centered energy <=M, including all remaining residues and infinite tails |
| R1 | Replay proportional signed-moment and dispersion certificates at x=7, then 11 and 13 | Kernel-checked actual optimizer conclusions, not only rational external computations |
| R2/R3 | Use exact divisor/carry identities and keep simultaneous jumps | Equality with signed mixed and boundary terms before any norm estimate |
| R6 | Test sigma/W and H_x before expensive primorial construction | Exact rational finite tables; floating diagnostics labeled separately |

External exact rational observer data at 13 cutoffs through 251 are retained
in `ResearchData/ExactHeadGreen20261116/affine_observer_exact_data.json`.
The sigma/W ratio is about 0.412 at 5 but already about 0.99993 at 251.
This is finite evidence that the projected factor alone may give little
large-stage relative improvement; it is not a proof of a limiting ratio.

Uniform/cofinal R4 and R5 remain **Open**. RH is not proved.

## Declarations, verification and recovery

| Module | Principal declarations |
|---|---|
| Analysis/FiniteAffineResidualDuality.lean | affine_residual_gram_identity; affine_residual_pairing_sq_le; affine_normal_removed_energy |
| RH/MobiusAffineDuality.lean | profile_error_sq_le_affine_mobius_loss; exists_normal_mobius_budget; mobius_five_normal_loss |
| RH/ExactHeadGreenAffineCriterion.lean | riemannHypothesis_of_atom_signed_profile_deficit; riemannHypothesis_of_atom_affine_residual_deficit |
| RH/ExactHeadAtomStageFiveMoment.lean | centered_probe_energy_interval; fitted_moment_five_deficit |
| RH/ExactHeadAtomStageFive.lean | fitted_moment_five_interval; primorial_five_signed_moment_deficit |
| RH/ExactHeadMomentHeadObstruction.lean | probe_head_energy_le_centered; probe_head_three_energy; centered_probe_three_gt_two_thirds |

The integrated focused check of `//RiemannResearch/RH:ExactHeadGreenAxiomAudit`
passed with Bazel/BuildBuddy in 189.960 seconds, job
`job_zQ1hIKC9ZEehCaM6xZA8j0LR9B3pSlKg`.
[Focused build](https://app.buildbuddy.io/invocation/81503fea-8e59-4410-b7e7-da7a3da2e724).
All 26 guarded transitive axiom checks matched exactly
`[propext, Classical.choice, Quot.sound]`.
The explicit equality `probe_head_three_energy` was extracted afterward
from the already checked inequality proof; it is included in the final
full-project publication checkpoint. The checkpoint result is the authority
for the published commit and complete build status.

Managed workspace: `ws_JTdg7P_Moic1v8sjQ4aJwspRq66UefTw`.
Reopen this token to continue the retained source tree; do not create a
second active verification job in the same workspace.
