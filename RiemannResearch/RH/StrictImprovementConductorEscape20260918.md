# RH attempt: strict improvement, conductor escape, and vanishing gains

Date: 2026-09-18. Starting project commit: 86212ce788ddff7327f20df6a4b9217d91221cf4.

RH has not been proved. This continuation strengthens the actual conditional-mean variational route with unconditional results, while isolating why strict descent does not settle its open energy bound.

## Exact objects

Let H_Y be the finite legal functions F with F(n)=1 for 1≤n≤Y, and put

    C_F(t) = (F(1)+...+F(t))/t,
    q_t = 2/((t+1)(t+2)),
    E(F) = sum_(t≥1) q_t C_F(t)^2,
    lambda_Y = inf_(F in H_Y) E(F).

The signed correlation is I(F,R)=sum q_t C_F(t) C_R(t).
For legal R with zero head,

    E(F+uR) = E(F) + 2u I(F,R) + u² E(R).

If E(R)>0, the exact optimal gain is I(F,R)²/E(R). All actual weights, signs, and mixed terms remain present.

## New unconditional arithmetic improvement

For every Y>0 and every F in H_Y, there is G in H_Y with E(G)<E(F).
This extends the existing mean-zero three-generator theorem to every finite legal witness.

For a periodic F with nonzero period mean m, write the exact identity

    C_F(t) = m + B_F(t)/t,    |B_F(t)|≤B.

Choose d>Y with B<|m|d. Then m C_F(t)>0 for every t≥d.
The pulse H_d=2{n/(2d)}−{n/d} has nonnegative Cesaro means, zero means for t<d,
and C_(H_d)(2d)=1/2. Thus the actual signed sum satisfies

    m I(F,H_d)>0.

Projection along this legal, head-preserving direction strictly lowers energy.
When m=0, the existing checked three-generator detection theorem supplies a
nonzero correlation. Consequently

    lambda_Y < E(F) for every finite F in H_Y.

In particular, the unrestricted infimum is never attained by a finite legal
witness. This is stronger than saying a witness exceeds the compulsory head
mass Y/(Y+2): the unrestricted infimum itself may be larger than that mass.

## Finite matrix minima and uniform improvement at a fixed conductor

Let M_(Y,D) be the project's attained minimum over residues 2,...,D, with D≥Y+1.
Its existing definition is the exact inverse-matrix value

    1ᵀ (A G⁻¹ Aᵀ)⁻¹ 1.

The new results prove:

1. lambda_Y < M_(Y,D).
2. For every finite D, some E>D satisfies M_(Y,E)<M_(Y,D).
3. There is one new finite witness G_E and delta>0 such that
   E(G_E)+delta≤E(F) for every feasible witness F using the old budget D.
4. If E(F_j)→lambda_Y, then F_j eventually leaves every fixed residue dictionary.
   Any sequence of valid conductor budgets D_j for those witnesses tends to infinity.

The second statement does not assert strict improvement when each individual
next column is added. The larger improving budget and its positive gain may
depend on both the head and the old budget.

## Why this attempt still stops short of RH

For every legal head-preserving correction R, including the zero-energy case,

    0 ≤ I(F,R)²/E(R) ≤ E(F)−lambda_Y,

where Lean uses its usual totalized division convention at E(R)=0; in that case
the signed correlation is also zero by an existing theorem.

Hence, along any minimizing sequence, every adaptively chosen scalar gain
tends to zero. More strongly, for every epsilon>0 there is an actual finite
F in H_Y for which ALL legal head-preserving scalar gains are smaller than
epsilon. A positive additive gain floor uniform over all conductors is therefore
impossible. The positive fixed-conductor bound above must deteriorate as
conductors escape.

This does not rule out a successful residual-specific estimate relative to a
target energy. It explains why repeatedly invoking the existing strict-
improvement theorem cannot prove the needed growth bound.

The decisive open target remains subpolynomial control of lambda_Y, globally
or along a cofinal sequence:

    for every epsilon>0, lambda_Y ≤ C_epsilon Y^epsilon eventually.

The project already proves that such control implies Mathlib's RiemannHypothesis.
No proof or provider of this target is added here. The classical reverse
implication is not used. Strict decreases can have a positive limiting excess,
and these finite-dimensional results do not estimate that excess as Y grows.

## Formalization and verification

New modules:

- RH/ConditionalHeadStrictImprovement.lean: nonnegative pulse means, explicit
  nonzero-mean detection, all-head strict improvement, nonattainment, the
  variational gain bound, simultaneous small gains, and adaptive gain convergence.
- RH/ConditionalConductorStrictImprovement.lean: strict finite-matrix gap,
  strict enlargement, uniform fixed-conductor improvement, and conductor escape.

There are 14 proved theorem declarations across these modules. No proof
placeholder, project-local axiom, or RH assumption is introduced.
The coherent main candidate was verified with exit_code 0 and verified=true;
principal axiom audits reported only propext, Classical.choice, and Quot.sound.
The final repository checkpoint validates the integrated modules and affected
dependents before committing and publication. Its outcome and commit are
reported by the coordinating run.

Source: the existing project declarations and the mathematical derivation in
this continuation; no claim of mathematical priority is made.
