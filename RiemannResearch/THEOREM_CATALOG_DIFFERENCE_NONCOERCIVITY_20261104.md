# Physical difference noncoercivity — 2026-11-04

Module: `RiemannResearch/RH/QDifferenceNoncoercivity.lean`.
Namespace: `RiemannResearch.RH.QDifferenceNoncoercivity`.

Established finite identities and inequalities:

- `difference_residue_norm_sq`: exact complete-Q derivative energy
  `2 * (d - 1) / d^3` for each conductor at least two.
- `residue_inverse_amplification`: primitive energy is at least
  `d / (2 * zetaTwo)` times derivative energy.
- `residue_exceeds_coercivity_constant`: an explicit conductor threshold
  defeats any proposed uniform inverse constant.
- `exists_prime_exceeding_coercivity`: the obstruction already occurs on
  prime, hence squarefree legal, atoms.
- `scaledResidue`, `scaledResidue_norm_sq`,
  `scaledResidue_difference_norm_sq`, and `scaledResidue_norm_sq_lower`:
  square-root-scaled atoms have derivative-energy formula
  `2 * (d - 1) / d^2` and a uniformly positive primitive-energy lower bound.

The general conditional closure mechanism is already in
`RH/QPrimitiveEnergyClosure.lean`. Its domain-specific obligation remains
**Open**: construct legal approximants with a uniform complete-energy bound
and derivative limit, or prove a uniform O(lambda) regularized budget.
Tensor density alone does not discharge this obligation.

Published context: Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis*, Proc. Indian Acad. Sci. (Math. Sci.)
116 (2006), 137–146, Remark 8, supports the squarefree closure criterion.
Albani, Elbau, de Hoop and Scherzer, *Optimal Convergence Rates Results for
Linear Inverse Problems in Hilbert Spaces*, Numer. Funct. Anal. Optim. 37
(2016), 521–540, doi:10.1080/01630563.2016.1144070, supports the regularization
framework; it supplies no arithmetic bound here.
