# Weighted prime refinements: exact energy and a greedy obstruction

Date: 2026-10-13.
Starting point: commit 916ac4e34fc39271aea3084e284f6b18399e93b3.
Source: the user's weighted-prime research request and the published
QResidueRefinement, QPrimeSieve, and ZetaTwoHilbertSpace modules.
The line-search algebra is standard Hilbert geometry. The arithmetic finding
here is a failure mechanism for the specified greedy refinement construction;
no priority claim is made.

## Exact arithmetic direction and full error

Write g_d(n) = (n mod d)/d, F(n) = -sum_{d in S} w(d) g_d(n), and
alpha = sum_{d in S} w(d)/d. The published paired extension gives

    F_new = F + u A_p,
    A_p(n) = -F(floor(n/p)) + alpha g_p(n).

Every function here is a bounded finite residue combination, so its full
Q norm and cross products are summable. Put R = 1-F, H_p(n)=F(floor(n/p)),
beta = <R,A_p>_Q, and gamma = ||A_p||_Q^2. Exactly,

    E(u) = ||R||_Q^2 - 2u beta + u^2 gamma,
    beta = -<R,H_p>_Q + alpha <R,g_p>_Q,
    gamma = ||H_p||_Q^2 - 2alpha <H_p,g_p>_Q
            + alpha^2 ||g_p||_Q^2.

These are the actual pairings sum_{n>=1} x(n)y(n)/(zeta(2)n^2).
In particular, neither the signed cross term nor any tail is discarded.
For every cutoff M the same equation is the sum of the head and tail
quadratics, each retaining its own signed beta contribution. A finite
truncation of beta or gamma is not substituted for the full quantity.

The new module connects finite coefficients to the existing QHilbert vectors
with sequence_weighted, sequence_refinement_direction, and sequence_paired.
hilbert_fullError identifies the Hilbert norm with QPrimeSieve.fullError;
paired_fullError_quadratic specializes the energy equation to the actual
pairedResidueExtension. energy_quadratic_tsum exposes the complete infinite
weighted sums.

## Exact finite optimizer and iteration

If gamma > 0,

    E(u) = E(0) - beta^2/gamma + gamma (u-beta/gamma)^2.

Thus u*=beta/gamma is the unique minimizer and the exact drop is beta^2/gamma.
If gamma=0, A_p=0 in QHilbert, beta=0, and every weight gives the same error.
The Lean results energy_complete_square, optimal_minimizes,
zero_direction_energy, and optimal_energy_total cover the finite cases.

For successive optimized residuals R_j and directions A_j,

    E_m = E_0 - sum_{j<m} beta_j^2/gamma_j,

with a zero summand when gamma_j=0. This is optimized_telescoping.
The directions need not be mutually orthogonal. This is a line-search
decrement, not automatically the Schur complement for the fully reoptimized
enlarged residue span. If old coefficients are refitted, the relevant Schur
denominator is the squared norm of the component of A orthogonal to the old
span, rather than necessarily ||A||^2.

As an analytic consequence of the exact telescope, the nonnegative increments
have bounded partial sums and

    E_infinity = E_0 - sum_{j>=0} beta_j^2/gamma_j.

Consequently convergence to 1 requires and is equivalent to exhaustion of
the initial error by these drops. The infinite-limit statement is explained
here; the new Lean module formalizes the finite telescope. No unconditional
exhaustion theorem or RH conclusion follows from the telescope alone.

## Arithmetic obstruction to the canonical greedy construction

Specify the construction precisely: start with S={1}, w(1)=1, so F=0 and
alpha=1; introduce prime 2; then introduce larger primes once each using the
published paired extension. Old weights are not retroactively refitted.

The first direction is g_2. Since g_2 is one half of the odd-number indicator,

    <1,g_2>_Q = 2 ||g_2||_Q^2,     ||g_2||_Q^2 > 0.

Hence the UNIQUE first energy-minimizing weight is u_2=2. The resulting state is

    F_1=2g_2,       w(1)=1, w(2)=-2,       alpha_1=1-2/2=0.

Lean: two_inner, two_norm_sq_pos, first_step_complete_square,
first_step_unique_minimum, and greedy_seed.

The already published Euler-factor identity yields

    alpha_new = alpha (1-u/p).

Thus alpha=0 is absorbing, regardless of every later real weight. Furthermore,
for n<p and F(0)=0 the published refinement identity gives

    F_new(n)=F(n)+u alpha n/p.

With alpha=0 this freezes the entire head below the next prime. In particular,
F_1(2)=0, and every subsequent prime p>2 leaves F(2)=0. Greedy optimization of
the later weights cannot change that coordinate.

The module defines frozenRefinements for the resulting recurrence

    f_0(n)=2g_2(n),
    f_{j+1}(n)=f_j(n)-u_j f_j(floor(n/p_j)).

For ANY real weights u_j and ANY integer multipliers p_j>2, it proves
f_j(0)=f_j(2)=0, boundedness at every finite stage, summability of the actual
squared error, and

    fullError(f_j) >= Q(N=2) = 1/(4 zeta(2)) > 0.

Lean: frozen_zero, frozen_two, frozen_bounded, frozen_fullError_lower,
frozen_not_tendsto_zero. zero_reciprocal_freezes_head and
zero_reciprocal_preserved connect this recurrence to the published paired
coefficient update.

The inequality is used only after the exact coordinate identity and full
energy have been retained, to certify a rigorous obstruction. It is not a
lossy asymptotic argument. This bound rules out the canonical greedy scheme
even with arbitrarily optimized later weights. It is a different mechanism
from the growing-head obstruction for the unweighted primorial sieve.

## What remains viable and open

This result does not rule out the whole legal residue span or RH.
Changing the initial seed, revisiting old coefficients, or jointly optimizing
an enlarged finite span changes the construction. Such a repair must be
explicit: once the greedy prime-two step has made alpha zero, merely choosing
better weights at larger fresh primes cannot repair the missing coordinate.

For a repaired family, exact finite minimization still leaves the full
infinite-tail/exhaustion condition open. Independent prime valuations under Q
do not by themselves factor floor-dilation/residue cross terms. A useful next
target is a simultaneous head-correcting update with old coefficients allowed
to move, followed by a signed full-tail identity. No convergence claim is made.

## Verification scope

The new source is RH/QWeightedRefinementEnergy.lean, exported by the root
module, with a focused theorem-catalog entry. Server-side snippet checks and
the final checkpoint are the verification path; hosted CI is not used.
Publication is permitted only when the checkpoint validates the final source,
including any integration changes. The final response reports the actual
terminal verification and publication status.

Successful isolated server check: job_r3_ilo4JGFDP1R9032n5EXWEscw_Lxti (exit 0).
Axiom inspection of the main obstruction, first-step uniqueness, arithmetic
energy, and telescope returned only propext, Classical.choice, and Quot.sound.
The first publication attempt stopped on a concurrent theorem-catalog edit;
no unverified integration was pushed. The same source was transferred to
current main at 5f2ce46b6d7bd5e87ebe7833f01b2a0272fc7ad5 for a fresh checkpoint.
