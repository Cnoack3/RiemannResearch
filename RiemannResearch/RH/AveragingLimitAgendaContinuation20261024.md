# Exact-head averaging: complete agenda continuation

Date: 24 October 2026.

Source: the user-provided `RH_Averaging_Limit_Research_Agenda_2026-10-24(1).md`.
This continuation treats all five priorities. It supplies an explicit squarefree
arithmetic family, stronger averaging theorems, rank-free repair comparisons,
a weaker Mellin growth criterion, and reproducible complete-tail experiments.
It does **not** establish the remaining infinite-family arithmetic estimate
or prove RH unconditionally.

## 1. Agenda status and verification boundary

| Priority | Result | Remaining obligation |
|---|---|---|
| 1. Actual arithmetic family | Least-prime-balanced Möbius family; squarefree legality, exact heads, integer amplitude certificate | **Open:** uniform complete energy, or a sufficient weaker growth condition, for this specified family |
| 2. Normal repair | A feasible competitor bounds the actual target-direction budget; exact comparison under dictionary enlargement; dependent observation rows allowed | **Open:** an upper bound uniform over growing physical heads |
| 3. Weaker averaging | Automatic mixed-term control with varying diagonal energies; inverse-energy weighted averages; finite tail-search termination from reciprocal-mass divergence; actual legal closure and RH implication | **Open:** subquadratic selected diagonal energy or divergent selected reciprocal-energy mass for actual arithmetic candidates |
| 4. Subpolynomial repair | Full relative-log convergence weakened to arbitrarily small ratios occurring cofinally; actual Mellin lower bound supplies the contradiction | **Open:** the cofinal small-growth arithmetic premise |
| 5. Finite computation | Rational complete P/Q certificates through head 256; larger 59-atom dictionary at head 64; signed pairings and signed periodic tail assembly | These are finite candidate certificates, not infinite-family bounds or certified intervals for minimum repair costs |

The Lean declarations below use no `sorry`, project-local axiom, or unsafe
declaration. Their domain-specific hypotheses remain visible in their types.
The rational Python instances and the bad-anchor argument in the companion
note have a separate verification status: they are not Lean kernel certificates.
Publication is gated by the server checkpoint; the final conversation report
records its job, validation scope and commit.

## 2. Priority 1: a specified squarefree family

Put

\[
a_N=\sum_{d\le N}\frac{\mu(d)}d,\qquad
q_N=\min\{q>N:q\text{ prime}\},
\]
\[
G_N=-\sum_{d\le N}\mu(d)g_d+q_Na_Ng_{q_N}.
\]

The conductor-one term is zero. Every remaining nonzero coefficient has a
squarefree conductor. For every positive N,

\[
G_N(n)=1\quad(1\le n\le N),\qquad
|G_N(n)-1|\le N+q_N.
\]

The formula works with any prime anchor q>N. Exactness follows from
\(\sum_{d\le N}\mu(d)\lfloor n/d\rfloor=1\) on the physical head and exact
cancellation of the linear term. The integer bound uses the existing
\(|a_N|\le1\), the zero conductor-one residue, and \(|g_d|\le1\).
Set G_0=G_1 when a natural-indexed interface also requires an index-zero value;
the online selector itself begins at head 1.

New module: `RH/QPrimeBalancedExactHead.lean`.

- `primeHead_sequence`, `primeHead_exact`, `primeHead_mem_squarefreeSpan`.
- `primeHead_residual_coefficient_bound`, `primeHead_residual_abs_le`.
- `anchorPrime`, `anchorPrime_spec`, `nextPrimeHead`.
- `nextPrimeHead_exact`, `nextPrimeHead_mem_squarefreeSpan`, `nextPrimeHead_amplitude`.

The remaining arithmetic expression is exactly

\[
\sum_{n>N}\frac{\left|1+\sum_{d\le N}\mu(d)g_d(n)-q_Na_Ng_{q_N}(n)\right|^2}
 {n(n+1)}.
\]

All signed cross terms belong to this expression. The head and amplitude
theorems alone give only a bound depending on N. They do not give a uniform
constant. Nor can choosing an arbitrarily larger prime be presumed to help:
the companion note proves, in ordinary mathematics, a squarefree exact-head
family with divergent energy when anchors grow too rapidly. The repository
also already contains the Lean-verified unrestricted counterexample
`CoefficientConvergenceCounterexample.escapingFamily_error_tendsto_atTop`.

## 3. Priority 2: target-direction bounds from genuine competitors

Fix one finite dictionary with linearly independent synthesis atoms. Its head
observation rows may be dependent. Let p be the complete-norm projection of x,
let delta=||x-p||², and let R be the minimum normal repair cost. For an actual
feasible competitor G in the same dictionary, completion of squares gives

\[
\|x-G\|^2=\delta+R+\|G-(p+v)\|^2.
\]

Consequently,

\[
R\le\|x-G\|^2-\delta,
\quad
\left|\sum_i b_i t_i\right|^2
\le(\|x-G\|^2-\delta)
  \left\|\sum_i t_i u_i\right\|^2.
\]

Thus a certified feasible candidate supplies a real target-direction estimate;
it need not be the optimum. Feasible normal equations are explicit in the
theorem types. Existing finite-dimensional feasibility results supply them;
invertibility of the observation Gram is never assumed.

New module: `Analysis/FiniteRepairComparison.lean`.

- `normal_cost_le_competitor_error_sub` and `directional_bound_of_competitor`.
- `normal_energy_mono_of_constraints`: adding compatible observations cannot
  reduce minimum normal energy in a fixed system.
- `constrained_error_antitone_of_span_le`: enlarging the dictionary at fixed
  observations decreases delta+R.
- `normal_cost_variation_le_projection_gain`:
  \(R_{new}-R_{old}\le\delta_{old}-\delta_{new}\).

R alone need not decrease as the dictionary grows. For example, in R³ take
x=e3, observation h=e2, V1=span(e1), and V2=span(e1,e2+e3).
Then (delta1,R1)=(1,0) and (delta2,R2)=(1/2,1/2); the constrained error stays 1.
This example is explanatory ordinary mathematics.

Squarefree row dependence is concrete: every squarefree legal F obeys
F(4)-F(3)-F(2)+F(1)=0. The constant target satisfies this relation. Dependence
therefore does not defeat feasibility, but forbids a blanket full-row inverse.

## 4. Priority 3: varying diagonal energy with automatic mixed-term control

Use the original executable selector N_j from the handoff, computed using U
alone. For r_N=G_N-1 it now satisfies, without any uniform energy hypothesis,

\[
|\langle r_{N_i},r_{N_j}\rangle_P|
\le\|r_{N_j}\|_P\,2^{-(j+1)}\qquad(i<j).
\]

Define the finite block diagonal

\[
D_{a,m}=\sum_{i<m}\|r_{N_{a+i}}\|_P^2.
\]

After first retaining the exact signed Gram equality, the new theorem gives

\[
\boxed{
\left\|\frac1m\sum_{i<m}r_{N_{a+i}}\right\|_P^2
\le\frac{D_{a,m}+2\sqrt{D_{a,m}}\,2^{-a}}{m^2}.}
\]

Therefore, for any offset schedule a(m),

\[
D_{a(m),m}=o(m^2)\quad\Longrightarrow\quad
\frac1m\sum_{i<m}r_{N_{a(m)+i}}\longrightarrow0.
\]

No separate cross-pairing assumption remains: the physical hypotheses and
selector prove it. This is a genuine extension of the uniform-norm argument,
not an unsupported substitution C -> C_m in the earlier theorem.

New module: `RH/ParetoVariableEnergyAverages.lean`:
`online_exact_head_pairing_variable`, `online_exact_head_block_diagonal_bound`,
`selectedBlockEnergy`, `online_exact_head_block_energy_bound`, and
`online_exact_head_block_tendsto_of_subquadratic_diagonal`.

`Analysis/SignedEnergyAverages.lean` also proves the general signed-budget
version: upper bounds D_m and X_m suffice if
\((D_m+2X_m)/m^2\to0\). Negative mixed terms are retained. Separate
little-o bounds for D_m and X_m are sufficient but stronger than this combined
condition.

## 5. Priority 3: inverse-energy weights and a terminating tail rule

Let A_i >= max(1,||r_(N_i)||²) be complete-energy certificates and set

\[
S_{a,m}=\sum_{i<m}A_{a+i}^{-1},\qquad
\overline G_{a,m}=S_{a,m}^{-1}
  \sum_{i<m}A_{a+i}^{-1}G_{N_{a+i}}.
\]

For nonempty blocks these are convex finite legal combinations. The existing
selector also controls the scaled residuals r_(N_i)/A_i, so

\[
\boxed{\|\overline G_{a,m}-1\|_P^2
\le S_{a,m}^{-1}+2\,2^{-a}S_{a,m}^{-2}.}
\]

In particular, divergence of \(S_{0,m}\) implies convergence of the legal
prefix averages to the actual constant target. This has been assembled into
an actual closure theorem and an RH implication, not just an abstract norm
statement. Prefix averages need not have growing exact heads.

For growing exact heads, start at index a>=1 and choose the **least** length
m for which S_(a,m)>=a. Divergence of total reciprocal mass proves that such
a finite length exists for every a. The block then preserves head N_a and
has squared error at most 1/a+2*2^(-a)/a². The finite error bound and least-length
existence/specification are formalized; preservation follows by the normalized
coefficients summing to one. With rational A_i the search uses exact rational
comparisons. The generic Lean `Nat.find` definition over real certificates is
noncomputable; it specifies the least length rather than providing a real-number
decision procedure. No unconditional termination claim is made without the
reciprocal-mass divergence hypothesis.

New module `RH/ParetoReciprocalEnergyAverages.lean` proves automatic complete
mixed bounds, the block bound, and prefix convergence.
`Analysis/SignedEnergyAverages.lean` contains the general weighting theorem,
`exists_reciprocal_energy_tail_mass_ge`, and `reciprocalEnergyTailLength`
with its specification and minimality theorem.
`RH/ParetoReciprocalLegalClosure.lean` proves `online_reciprocal_legal_closure`
and `riemannHypothesis_of_online_reciprocal_energy` with every arithmetic
hypothesis explicit.

This extension can succeed when equal averages fail: for orthogonal vectors
with energies i+1, equal averages have limiting energy 1/2, while reciprocal
weights have energy 1/H_m -> 0. Conversely energies 2^i give an energy floor
at least 1/2 for every finite affine combination. These are explanatory
Hilbert-space examples, not claims about legal arithmetic families.

**Open arithmetic obligation:** prove divergence of reciprocal certificates
along the actual selected heads. Individual finite certificates, small finite
experiments, and the ability to increase a head do not establish it. The crude
amplitude-derived certificates can grow too quickly to be useful here.

## 6. Priority 4: cofinally small relative-log cost suffices

Keep H_j (physical head length) separate from m (number of averaged terms).
The already-established actual Mellin obstruction says that a zero with
sigma=Re(s)>1/2 forces

\[
R_j+1\ge
\frac{2\sigma-1}{\zeta(2)|s|^2}(H_j+1)^{2\sigma-1}.
\]

It therefore suffices that H_j -> infinity and, for every epsilon>0,
arbitrarily large j satisfy

\[
\frac{\log(1+R_j)}{\log(H_j+1)}<\varepsilon.
\]

The entire ratio need not converge. The proof takes logarithms of the actual
power floor and intersects its eventual lower bound with the frequent small
values. No zero-density or sampling provider is inserted as an assumption.

New modules:

- `Analysis/SubpolynomialCofinalGrowth.lean`:
  `no_positive_power_floor_of_frequently_small_relativeLog`.
- `RH/QNormalRepairCofinalSmallGrowth.lean`:
  `riemannHypothesis_of_cofinally_small_normal_cost`.

The latter still requires actual feasible normal equations, positive
conductors, independent synthesis atoms, cofinal physical heads, and the
displayed small-growth premise. These are conditional research reductions.
No arithmetic proof of the last premise has been found here.

## 7. Priority 5: reproducible complete-tail certificates

The program sources in `CertificatePrograms.md` and exact rational JSON outputs are in
`RH/experiments/exact_head_averaging_20261024/`.

`exact_head_rational_certificates.py` certifies the least-prime family with
integer/Fraction arithmetic, directed finite-sum rounding, explicit infinite
P and Q tails, a rational zeta(2) enclosure, direct exact-head checks, and
signed adjacent pairings. Small runs use heads 1,2,4,8,16,32,64 and cutoff
200000; larger runs use heads 128,256 and cutoff 1000000. The rational strings
in JSON, not their floating display fields, are the authoritative endpoints.

The larger dictionary experiment uses squarefree 2<=d<=96, hence 59 atoms
with largest conductor 95, and exact physical head 64. Numerical optimization
only proposes coefficients. Exact rational reconstruction enforces every low
Möbius coefficient and the balance equation. The independent standard-library
verifier checks the displayed coefficients and complete error certificate.

| Candidate | Complete P squared residual | Complete Q squared residual |
|---|---|---|
| Larger squarefree dictionary, head 64 | [0.0288461096, 0.0288690873] | [0.0176645567, 0.0176785256] |
| Least-prime family, head 256 | [0.0366346621, 0.0425573155] | [0.0223110483, 0.0259115935] |

The head-64 larger-dictionary candidate rigorously improves the corresponding
least-prime candidate in both metrics. Its signed periodic Abel tail is
assembled from all singleton and pair contributions before taking the
remainder bound. The P tail upper enclosure is about 55.72 times tighter than
the crude amplitude estimate.

These intervals certify the **exhibited residual**, not the constrained
minimum. Their upper endpoints also bound the constrained residual minimum
and, since delta>=0, the optimal normal repair cost in the same dictionary.
Their lower endpoints are not lower bounds for those optima. No projection
defect or normal-cost interval is claimed to have been computed in this new
experiment. The existing older dual-certificate experiments remain separate.

Extract the two Python listings using the command in `CertificatePrograms.md`, then reproduce or independently verify from that directory:

```sh
python exact_head_rational_certificates.py --help
python expanded_squarefree_primal_certificate.py --verify
```

The second command was run successfully and reports:
`Complete rational P/Q primal certificate independently recomputed.`
The small explicit-family outputs were independently regenerated and matched.
See `certificate_review.md` for the independent review and the exact tail
inequalities. These Python certificates are not newly kernel-checked instances.

## 8. The next arithmetic target

The next step is not another compactness or limit argument. It is a signed
complete-tail estimate for a specified family, such as the least-prime family
above or optimized finite head repair. Three precise sufficient targets are:

1. Subquadratic **selected block** diagonal energy D_(a(m),m)=o(m²).
2. Divergence of the **selected** reciprocal complete-energy mass.
3. Cofinal arbitrarily small relative-log growth of the actual complete-Q
   normal repair cost.

Any one needs a checked arithmetic provider. None follows from the finite
table. Rapid growth of selected physical heads prevents replacing one rate
condition by another without proof. P and Q norm convergence transfer, but
their projections, optimizers and repair costs must continue to be kept
distinct.
