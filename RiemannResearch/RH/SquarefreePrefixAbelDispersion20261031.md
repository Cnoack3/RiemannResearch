# Squarefree prefix Abel sums and exact dispersion

Date: 31 October 2026.

This continues [SquarefreeShortHeadLean20261031.md](SquarefreeShortHeadLean20261031.md)
and sections 2 and 4 of
[SquarefreePrefixResponseResearch20261030.md](SquarefreePrefixResponseResearch20261030.md).
The objects are the ordinary canonical projection onto the complete squarefree
dictionary, including composite conductors. All projections and norms use the
complete Q inner product. RH and the common arithmetic block envelope remain Open.

## Exact physical prefix and complete Abel sum

Write
`A_{N,n}(H) = sum_{m=1}^H Q(m) r_N(m) K_N(n,m)`,
where `Q(m)=1/(zeta(2)m^2)`, `r_N=1-P_N1`,
`K_N(n,.)=P_N e_n`, and `beta_m=1/(m+1)`.
The declaration `prefix_eq_physical_sum` identifies this physical expression
with the Hilbert-space definition `prefixResponse N n H`.
In particular, the normalization is part of the checked statement.

For every H, including H=0,

$
T_{N,H}(n)=(\beta_{H+1}-\beta_n)A_{N,n}(H)
+\sum_{h=1}^{H}\frac{A_{N,n}(h)}{(h+1)(h+2)}.
$

This shifted-endpoint form is equivalent to the memorandum's finite Abel formula.
For H=n-1 the endpoint is exactly zero. Subtracting any two cutoff identities
gives the complete signed interval formula with both endpoints.
No sign alternation of adjacent physical ranges is asserted.

The complete normal equation gives the checked identity

$
A_{N,n}(H)=-\langle k_{N,n},r_N-\mathbf1_{m\le H}r_N\rangle_Q.
$

Consequently A(H) tends to zero as H tends to infinity for fixed N and n.
The actual correction has the absolutely convergent representation

$
b_N(n)=\sum_{h\ge1}\frac{A_{N,n}(h)}{(h+1)(h+2)}.
$

This is `movingCorrection_hasSum_prefix`, with a `HasSum` conclusion, and
`movingCorrection_eq_tsum_prefix`. Absolute convergence is established using
the uniform-in-H bound `|A(H)| <= ||k_{N,n}|| ||r_N||` and an inverse-square
majorant. This is not a uniform-in-N-and-n polylogarithmic estimate.

## Exact prefix variance

Let `u_H=||1_{m<=H} r_N||^2`, `epsilon=||r_N||^2>0`, and

$
\ell_H=(I-P_N)\left(\mathbf1_{m\le H}r_N-\frac{u_H}{\varepsilon}r_N\right).
$

The new module checks

$
\begin{aligned}
\|P_N(\mathbf1_{m\le H}r_N)\|_Q^2
&=\frac{u_H(\varepsilon-u_H)}{\varepsilon}-\|\ell_H\|_Q^2,\\
A_{N,n}(H)^2
&\le\|k_{N,n}\|_Q^2
\left(\frac{u_H(\varepsilon-u_H)}{\varepsilon}-\|\ell_H\|_Q^2\right).
\end{aligned}
$

The first formula is an equality and the second estimates only the evaluation
pairing. The complete orthogonal loss is retained. These specialize the
existing centered-projection machinery to the actual binary head source.

## A cancellation term retained by the finite estimate

Use H interior entries, indexed here by h=1,...,H, and one endpoint entry *:

$
\begin{aligned}
x_h&=\frac{A_{N,n}(h)}{h+1},& w_h&=\frac1{h+2}\quad(1\le h\le H),\\
x_*&=\frac{A_{N,n}(H)}{H+1},&
w_*&=(H+1)(\beta_{H+1}-\beta_n).
\end{aligned}
$

The duplicate value at the last interior entry and at * is intentional:
it preserves the endpoint without a special H=0 convention.
All entries are exactly defined in `abelWeight` and `abelValue`.
For H<n all weights are nonnegative.

Set

$
W=\sum_iw_i,\qquad J=\sum_iw_ix_i^2,\qquad
D=\frac12\sum_{i,j}w_iw_j(x_i-x_j)^2.
$

Lean verifies the unconditional algebraic equality and its positive-weight bound:

$
T=\sum_iw_ix_i,\qquad \boxed{T^2+D=WJ},\qquad
D\ge0,\quad T^2\le WJ\quad(H<n).
$

The mass is exactly

$
W=\sum_{h=1}^{H}\frac1{h+2}+\frac{H+1}{H+2}-\frac{H+1}{n+1}
\le1+\sum_{h=1}^{H}\frac1{h+2}.
$

A pair of entries with positive weights and distinct normalized prefix values
certifies D>0 and therefore a strict finite improvement over `T^2 <= W J`.
This is a conditional finite certificate; no such separation with an adequate
uniform quantitative size has been proved for all required canonical blocks.

At H=n-1 the endpoint weight is zero. Thus this also records exactly the
Cauchy loss in the earlier lower-response estimate `L_N(n)^2 <= h_n J_N(n)`.
Dropping D recovers that estimate. Keeping D permits a large raw prefix energy
to be compensated by measured dispersion, with no invented cancellation.

The generic identity `FiniteWeightedVariance.pairwise_moment_exact` is valid
even for signed weights and zero total mass. Positivity is required only for
interpreting the dispersion as a nonnegative improvement.

## Exact dyadic connection to RH

Take `M=2^j`, `H_M=floor(M/(6+log M))`, and physical sites `n=M+1,...,2M`.
The complete finite block equality is

$
\sum_{n=M+1}^{2M}T_{N,H_M}(n)^2+
\sum_{n=M+1}^{2M}D_{N,H_M}(n)
=\sum_{n=M+1}^{2M}W_{H_M,n}J_{N,H_M,n}.
$

The new theorem
`QSquarefreePrefixCriterion.riemannHypothesis_of_frequently_dyadic_prefix_dispersion`
proves RH under the following explicit hypothesis: there exist one C>=0 and
one natural exponent m such that, for every dyadic block, arbitrarily large N satisfy

$
\sum_{n=M+1}^{2M}W_{H_M,n}J_{N,H_M,n}
\le CM(6+\log M)^{2m}+\sum_{n=M+1}^{2M}D_{N,H_M}(n).
$

The stage set may depend on the block. This is an EXACT REFORMULATION of the
existing short-head mean-square hypothesis, not a weaker arithmetic condition.
Its value is that it identifies the cancellation that must survive an
energy estimate. The checked theorem `block_bound_iff` makes the equivalence
explicit. The common arithmetic bound remains Open.

## What this does and does not establish

Established: the physical-coordinate bridge; complete-tail normal equation;
finite, interval, and absolutely convergent infinite Abel identities;
exact prefix source variance; exact Cauchy dispersion; nonnegativity and a
strict finite pair certificate; and the conditional dyadic RH consumer.

Not established: a uniform polylogarithmic bound for the actual response,
a quantitative dispersion lower bound large enough to establish that envelope,
or RH. In particular, positivity of D alone does not control the difference
W J - D. Bounding W J separately may still lose the cancellation needed.

The next arithmetic task is to exploit the full divisor normal equations to
control the compensated block expression W J - D. The prefix variance formula
supplies unconditional constraints, but using only
`u_H(epsilon-u_H)/epsilon <= epsilon/4` and
`||k_{N,n}||^2 <= zeta(2)n^2` retains polynomial evaluation growth.
Neither finite Abel summation nor the exact dispersion identity removes that
growth on its own.

## Source and validation map

- `RH/QSquarefreePrefixAbel.lean`: actual prefixes, complete Abel sum, and prefix variance.
- `RH/QSquarefreePrefixDispersion.lean`: positive Abel weights, exact loss, and block identity.
- `RH/QSquarefreePrefixCriterion.lean`: explicit equivalence and conditional RH implication.
- `Analysis/FiniteWeightedVariance.lean`: unconditional pairwise moment identity.

The coherent candidate's Abel, dispersion, and variance development passed
`job_su342-s72KBiEABTuAU1WYnu2_Y_WB-8` in 6.525 server seconds.
The saved-source import check and six selected axiom audits passed
`job_z4_MIX5cOI4f2YS3q5ZfMqxqdN2kKQDI` in 20.766 server seconds.
The server built all three new modules and the changed generic variance module.
Each audited declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.
This does not discharge the explicit arithmetic hypothesis in the RH theorem.

Workspace reopening took 110.584 seconds as a client request round trip.
The displayed server verification durations exclude the deliberate polling
delay; no independent kernel-only timing or queue-delay measurement is claimed.
Final checkpoint validation and the exact published commit are reported with
delivery. An import check is not a project checkpoint.
