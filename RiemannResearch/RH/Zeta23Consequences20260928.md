# Consequences of the completed Zeta23 import — 28 September 2026

Continuation of commit 59a1fded801352540eca5a61270a72db5de77128.
This development uses the imported critical-zero provider and existing actual
Pareto/Mellin definitions. It neither assumes nor proves RH.

## Mathematical results

Write h_d for coefficientRiesz d, P_n for projection onto the finite legal
space, B_(n,d) for projectedDualCoefficientMass n d, and
Q_(n,d)=||h_d-P_n h_d||. The arithmetic profile is
Phi(n)=((6+log n) log(6+log n))^(1/11).

### Each small column has a critical witness

`SmallDualCriticalZeros.lean` proves that the critical-line Mellin zeros of
each individual h_2 and h_3 form at most one conjugate pair. The proof uses
x=2^(-s), y=3^(-s), |x|^2=1/2, and |y|^2=1/3:

- M_s(h_2)=0 forces Re(x)=27/40.
- M_s(h_3)=0 forces 24 Re(x)^2+16 Re(x)-21=0 and Re(x)>0.

In each case the real part of x is unique, and its imaginary part is determined
up to sign. The Mellin numerator then determines y. Equality of both powers
2^(-s),3^(-s) determines s, by the already proved integer-log relation for
conductors 2 and 3. Thus there is at most one exceptional positive ordinate
for each dual.

The imported theorem supplies simple critical zeta zeros above any height.
Consequently each column has nonvanishing witnesses above any height, and one
arbitrarily high simple critical zero simultaneously detects both columns.
No numerical zero location is assumed.

### A finite-cutoff stability bound

For each d in {2,3}, some fixed L>0 satisfies, for every n,

    L^2/8 <= Q_(n,d)^2 log(4(12+B_(n,d)+L)/L).

This uses only the proved critical Mellin cutoff with
R=2 log(4(12+B+L)/L). The resulting tail is at most L/2. It uses no canonical
arithmetic-energy estimate. This is an error/mass tradeoff for the actual
projected dual; it is not a claim that Burnol's full distance asymptotic has
been formalized.

### Quantitative endpoint obstruction for both columns

There exist a>0 and kappa>0 such that, eventually, simultaneously for d=2 and d=3,

    kappa <= Phi(n)^2 exp(-a Phi(n)) B_(n,d)^2.

The arithmetic theorem supplies a. A conditional interface preserves any
positive exponent a for which its displayed canonical-energy estimate holds.
The endpoint result follows from the fourth-power projection-error estimate
and the critical cutoff, choosing R=(a+1)Phi(n). If the normalized mass were
small, the tail would be small and the head would contradict the nonzero
Mellin value.

Consequences:

- For BOTH columns separately, exp(-b Phi(n)) B_(n,d)^2 tends to infinity
  for every b<a, with the same positive a.
- Phi(n)^2 exp(-a Phi(n)) B_(n,d)^2 cannot tend to zero along ANY cofinal
  subsequence, separately for either column.
- In particular the endpoint envelope B_(n,d)^2=o(exp(a Phi(n))/Phi(n)^2)
  is impossible. This retains the exact quadratic profile loss.

A bounded endpoint mass exp(-a Phi(n))B^2 is not ruled out. Nor is cofinal
smallness without the quadratic factor ruled out: a sequence comparable to
1/Phi(n)^2 is consistent with the new lower bound.

`critical_cutoff_quadratic_loss_sharp_model` verifies the scalar model
phi=t, B=exp(2t)/t, Q=2/sqrt(t), a=4, C=16, D=0, L=1, for t>=1.
The error envelope holds with equality, the cutoff holds for EVERY R>0,
and t^2 exp(-4t)B^2=1 exactly. Taking t=n+1 gives a diverging profile.
Thus the scalar hypotheses cannot force this normalized quantity to diverge;
finer arithmetic information would be needed. No identification of this
model with the actual projected duals is claimed.

### Uniform subcritical-shape coercivity

Let E_alpha(n,c) be the complete shapeLegalTailEnergy and A(n,c) the actual
complexReciprocalSource. One constant C>0, independent of alpha,n,c, satisfies

    alpha(1-alpha)|A(n,c)|^2 <= C E_alpha(n,c),  0<alpha<1.

Hence every finite shape capacity is at most C/[alpha(1-alpha)]. At every fixed
subcritical shape, all trials normalized by A=1 have a positive energy gap.
For any fixed a0>0 there is delta>0 such that normalized trials with
alpha>=a0 and alpha<1 satisfy

    delta(1-alpha) <= E_alpha(n,c).

Thus vanishing complete energy at shapes bounded away from zero forces
alpha to tend to one. Even for moving shapes, E_alpha/(1-alpha) cannot tend
to zero. This removes the old external critical-zero premise from the
below-one capacity obstruction; it does not establish endpoint density.

## Remaining RH obligation

The direct signed physical-tail pairing criterion remains open. The repository
already proves that arbitrarily late small signed pairings for each fixed d>1
force the limiting corrections and residual to vanish, and hence imply RH.
No such cancellation estimate follows from the bounds above.

The imported positive proportion of simple critical zeros does not rule out
an exceptional off-line zero. The RH-to-natural-density direction remains an
explicit analytic formalization dependency where used in equivalences.
Certificate-energy divergence does not imply capacity divergence.

## Sources and verification

- Alpoge–Furman, https://arxiv.org/abs/2608.13637, and the pinned Zeta23 source:
  supports the imported zero-proportion and actual critical-zero provider.
- https://github.com/anthropics/formal-math/tree/fbdc36bbf17d20af3fd0447c6d1a8a02773c9844/zeta23
- Burnol, https://arxiv.org/abs/math/0103058: context for logarithmic
  critical-zero approximation obstructions; its full theorem is not used as
  an unproved premise of these additions.

The algebraic and cutoff refinements were derived from existing project
identities. Wolfram checked the finite polynomial elimination as an exploratory
calculation; all mathematical claims recorded as established require Lean proofs.
No dependency pins or upstream proof bodies are changed.

The complete coherent candidate passed Lean in verification job
`job_cc5PKzIUI68Cx_iHeX8ZtIsRpBp8Ef1E` (exit code 0). Fourteen principal
axiom audits reported only `propext`, `Classical.choice`, and `Quot.sound`,
including the premise-free both-column endpoint, strict-margin divergence,
cofinal endpoint obstruction, common witness, and shape-rate declarations.
Publication additionally validates the separated source modules and affected
dependents. The full imported baseline passed `lake build RiemannResearch`.
There are no added axioms or proof placeholders.
