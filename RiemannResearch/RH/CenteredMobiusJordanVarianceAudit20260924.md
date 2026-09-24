# Directed RH attempt: exact centered Mobius variance

Date: 2026-09-24. No unconditional proof of RH was obtained.

The existing ParetoUniformJordanIdentification module handled legal packets.
The extension proves the following identity for actual raw Mobius coefficients:

    F_N(n) = sum_{d=1}^N (mu(d)/d)*((n mod d)-(d-1)/2)
    V_N = (1/Q)*sum_{n=0}^{Q-1} F_N(n)^2
        = (1/12)*sum_{q=2}^N J_2(q)*(sum_{d<=N, q|d} mu(d)/d)^2.

Q may be any positive common period. Q=N! gives a theorem with no hypotheses.
This is a symbolic theorem for all N, not a factorial computation.
Every divisor coordinate q>N vanishes exactly. All Mobius signs remain.

New declarations:
- gcd_square_sub_one_eq_jordan_incidence
- centeredResidue_uniform_variance_eq_jordan
- centeredMobius_uniform_variance_eq_jordan
- centeredMobius_uniform_variance_finite_cutoff
- centeredMobius_factorial_variance_eq_jordan

The coherent candidate passed Lean (exit code 0) with only
[propext, Classical.choice, Quot.sound]. The persisted module and its
affected dependents are checked at publication.

Source for the target formula: user-provided
RH_Centered_Far_Tail_and_Subpower_Obstruction_2026-09-24(1).md,
Part I, Sections 2--3. The proof extends existing local CRT covariance and
Mobius-inversion theorems. No novelty claim is made.

## Exact remaining gap

The current repository already proves a logarithmic saving for B_N/N via
rawMobiusSquareBudget_eventual_explicit_ceiling. The theorem
riemannHypothesis_of_frequently_subpower_raw_square_budget still requires:

    forall epsilon>0, exists C, frequently N atTop,
      B_N <= C*(N+1)^epsilon.

Here B_N=N*m_N^2+sum_{N<k<=N^2} U_N(k)^2/[k(k+1)].
The new uniform-variance formula does not establish this estimate.

The classical dual additive large sieve has loss L-1+N^2 on an interval of L
integers for rational frequencies with denominator at most N. Primary source
checked: E. Kowalski, Amplification Arguments for Large Sieve Inequalities,
pp. 1--2, equations (2)--(3):
https://people.math.ethz.ch/~kowalski/two-remarks-large-sieve.pdf

This source supports the external large-sieve statement only. The new Lean
proof does not assume or formalize it. Fourier identification, the large-sieve
provider, and the linear variance bound were not formalized in this task.

Even the paper bound V_N<=5N/16, combined with generic large sieve and Abel
transfer at cutoff N, leaves centered energy bounded only proportionally to N.
A better N^2 far tail therefore does not settle the middle window.
Uniform variance cannot be substituted for Pareto energy.

The next substantive target is a bound on actual signed weighted cross terms
on N<k<=N^2 improving the generic frequency-separation loss. More equivalent
RH criteria alone do not discharge this arithmetic obligation.
