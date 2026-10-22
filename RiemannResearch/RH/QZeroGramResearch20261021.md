# Zero ordinates, determinant errors, and finite Mellin Gram certificates

Date: 2026-10-21.

## Verified scope

The new modules use the actual complete Q Hilbert space,
Q(n)=1/(zeta(2)n^2), its sequence-preserving Pareto image, and the literal
closed squarefree residue span. They assume no RH or zero-density theorem.

Targeted server job job_7_KqBemftXQhWCvxQGqLiZ6UMYKWAnDt passed:
exit_code=0, verified=true, reported execution 14.531 seconds.
It built both new modules. Seven central axiom checks reported only
propext, Classical.choice, and Quot.sound. The containing commit's successful
checkpoint certifies final project publication.

## Single-zero and height certificates

RH/QZeroGramObstruction.lean proves, for every f in the squarefree legal
closure and every zeta zero rho with Re(rho)>1/2 and rho!=1,

  (2 Re(rho)-1)/(zetaTwo normSq(rho)) <= ||qOne-f||^2.

The declarations are zero_displacement_bound and zero_floor.
The proof combines the existing continuous Mellin separator with the
complete Q-to-Pareto norm comparison, including all physical coordinates.

Using the actual zeta functional equation, zero_horizontal_bound proves,
throughout the open critical strip,

  |Re(rho)-1/2| <= (zetaTwo/2)(1+Im(rho)^2)||qOne-f||^2.

zero_height_band and zero_free_rectangle_certificate give the uniform
height-T versions and explicit finite-error certificates.
zero_optimizer_floor, zero_optimizer_height_band, and zero_limiting_floor
specialize these results to the actual squarefree optimizers and their
limiting residual.

## Actual finite Gram calculus and full signed remainder

RH/ParetoMellinFiniteGram.lean constructs

  K_c(x) = sum_i conj(c_i) x^(-s_i), x>1,
  G_ij = 1/(s_i+conj(s_j)-1).

finiteMellinKernel_memLp, finiteMellinKernel_pairing,
finiteMellinKernel_gram_integral, and finiteMellinKernel_energy prove the
actual integrability, moment pairing, and complete complex Gram energy.
mellinCauchyGram_entry_re_im displays the ordinate differences in G_ij.

finiteMellinKernel_remainder proves exactly

  integral |weightedStep(f)-conj(K_c)|^2
    = ||f||^2 + Re(c* G c) - 2 Re(c* Mellin(f)).

The normal-equation and literal inverse-matrix lower certificates follow
from this nonnegative remainder, retaining every off-diagonal term.

For actual zeta zeros s_i, residual_mellin_eq_one_div supplies the moments
b_i=1/s_i. zeroGram_inverse_error_bound and zeroGram_inverse_floor prove

  Re(b* G^(-1) b) <= zetaTwo ||qOne-f||^2,

with the explicit hypothesis det(G)!=0. This nonsingularity hypothesis is
not silently inferred from distinctness in the formalized declaration.

## Stronger exact Q identity

Let r=qOne-f and let C_Q(r)=normCorrection(r), the existing complete positive
change-of-law series. For every finite zero list and every complex c,
zeroGram_energy_exact proves

  zetaTwo ||r||^2
    = 2 Re(c* b) - Re(c* G c)
      + integral |weightedStep(toPareto(r))-conj(K_c)|^2
      + zetaTwo C_Q(r).

zeroGram_variational_bound therefore proves

  2 Re(c* b) - Re(c* G c) + zetaTwo C_Q(r)
    <= zetaTwo ||r||^2.

These last two results require no inverse, nonsingularity, or distinctness.
They apply to redundant and singular finite dictionaries as stated.

## Remaining obligations

- Unformalized finite algebra: derive nonsingularity from distinct nodes
  in the continuity half-plane, prove the Cauchy determinant product, and
  pass to the corresponding infinite zero-product lower comparison.
- Unformalized analytic theorem: Burnol's asymptotic lower bound, including
  multiplicity derivative kernels, and its conductor-cutoff transfer to Q.
  The logarithmic convergence-rate claim in the chat is not Lean-verified here.
- Unresolved RH-strength arithmetic: squarefree capacity saturation or
  total relative projection-gain divergence. The new lower certificates do
  not prove that the determinant ratio tends to zero.

The first two items are formalization tasks for the mathematical arguments
quoted in the chat. The third remains the substantive mathematical obstacle.

## Sources

Source: the user-directed determinant-ratio and zero-ordinate argument.

J.-F. Burnol, "A note on Nyman's equivalent formulation of the Riemann
Hypothesis", https://arxiv.org/abs/math/9910055, Sections 1-2, supports the
classical kernel geometry and zero-product interpretation.

J.-F. Burnol, "A lower bound in an approximation problem involving the zeros
of the Riemann zeta function", https://arxiv.org/abs/math/0103058, Theorem 1.3,
is the source of the remaining asymptotic formalization task.
