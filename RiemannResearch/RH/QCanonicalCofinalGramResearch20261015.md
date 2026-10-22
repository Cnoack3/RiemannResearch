# Uniform Q/P Gram and covariance comparison — 15 October 2026

Source: the user's request to combine both Radon--Nikodym derivatives with
the unconditional canonical residual-energy improvement. The proofs use
the already checked exact heads, the canonical PNT provider, the complete
metric identity, and standard Hilbert Cauchy--Schwarz. No novelty claim is made.

## Exact identities and notation

Write \(z=\zeta(2)\), \(P(k)=1/[k(k+1)]\), and \(Q(k)=1/(zk^2)\), for \(k\ge1\).
Every norm or pairing below refers to the identical physical sequence.

\[
 \frac{dQ}{dP}(k)=\frac{1+1/k}{z},\qquad
 \frac{dP}{dQ}(k)=\frac{zk}{k+1}.
\]
For any physical Hilbert vectors \(f,g\), put
\[
 R(f,g)=\sum_{k\ge1}\frac{f(k)g(k)}{k^2(k+1)},\qquad R(f)=R(f,f).
\]
The complete equalities are
\[
 z\langle f,g\rangle_Q=\langle f,g\rangle_P+R(f,g),
 \qquad z\|f\|_Q^2=\|f\|_P^2+R(f).
\]
The inverse density gives another exact realization:
\[
 \boxed{R(f)=z\,\mathbb E_Q\!\left[\frac{|f(K)|^2}{K+1}\right]
       =\mathbb E_P\!\left[\frac{|f(K)|^2}{K}\right]}.
\]
In Lean the inverse Q realization is inverse_correction_identity, expressed
in the genuine square-root-weighted Q coordinates.

Let \(D\) multiply physical coordinate \(k\) by \(1/k\). The new
correctionVector is an actual linear Hilbert encoding of \(D^{1/2}f\)
under P:
\[
 \langle Tf,Tg\rangle=R(f,g),\qquad \|Tf\|^2=R(f).
\]
Consequently all signed mixed terms are retained in a positive Gram form.

## Sharp scalar and matrix bounds on a common head

If \(f(k)=0\) for \(1\le k\le H\), both densities give
\[
 \boxed{0\le R(f)\le
 \min\!\left\{\frac{\|f\|_P^2}{H+1},
              \frac{z\|f\|_Q^2}{H+2}\right\}}.
\]
In particular,
\[
 \|f\|_P^2\le z\|f\|_Q^2
 \le\frac{H+2}{H+1}\|f\|_P^2.
\]
The upper constant is sharp on the full common-tail subspace: equality
is attained by a vector supported at physical coordinate \(H+1\).

For any finite family of such vectors, in every dimension and allowing
singular Gram matrices,
\[
 \boxed{G_P\preceq zG_Q\preceq\frac{H+2}{H+1}G_P}.
\]
The exact difference is the Gram matrix of their correctionVectors.
When the family is linearly independent, the genuine inverse matrices obey
\[
 \boxed{z\frac{H+1}{H+2}G_P^{-1}
        \preceq G_Q^{-1}\preceq zG_P^{-1}}.
\]
The inverse inequalities hold for every source vector. The only inverse
hypothesis is finite linear independence, which constructs actual inverses.
For canonical vectors \(r_{n_i}\), the common-head condition holds whenever
all \(n_i\ge H\). The dimension may grow arbitrarily.

Formal providers in QParetoGramComparison.lean:
synthesis_head_zero, gram_energy_bounds_of_head_zero,
capacity_bounds_of_head_zero, and inverse_matrix_quadratic_bounds_of_head_zero.

## Canonical residuals: uniform control of every cofinal Gram entry

For the actual canonical Möbius residuals \(r_N\), write
\[
 R_N=R(r_N),\qquad \delta_N=\frac{\|r_N\|_P^2}{N+1}.
\]
The established arithmetic provider proves \(\delta_N\to0\), hence
\[
 0\le R_N\le\delta_N\to0,\qquad Tr_N\longrightarrow0
 \quad\hbox{strongly in its Hilbert space}.
\]
Define the exact signed Gram discrepancy
\[
 C_{MN}=z\langle r_M,r_N\rangle_Q-\langle r_M,r_N\rangle_P.
\]
Hilbert Cauchy--Schwarz gives
\[
 \boxed{|C_{MN}|^2\le R_MR_N\le\delta_M\delta_N}.
\]
Thus, for every \(\varepsilon>0\), there is one \(H\) such that
\[
 |C_{MN}|\le\varepsilon\qquad(M,N\ge H).
\]
Both indices may tend to infinity independently, at arbitrary speeds.
The correction kernel is positive semidefinite; neither original Gram
kernel is asserted to tend to zero.

Formal providers in QCanonicalCofinalGram.lean:
correctionVector_residual_tendsto_zero,
gramDiscrepancy_sq_le, gramDiscrepancy_sq_le_energyRates,
cofinal_gramDiscrepancy_tendsto_zero, uniform_tail_gramDiscrepancy,
signedBlock_correction_eq_gram, and gramDiscrepancy_quadratic_nonneg.

## Stronger covariance transfer against arbitrary Hilbert tests

For any Hilbert test \(f\), even when its physical values are unbounded,
\[
 C_N(f)=z\langle f,r_N\rangle_Q-\langle f,r_N\rangle_P
       =\langle f,Dr_N\rangle_P.
\]
Because \(r_N\) vanishes through \(N\),
\[
 \|Dr_N\|_P^2\le\frac{R_N}{N+1}.
\]
Therefore
\[
 \boxed{|C_N(f)|^2\le\frac{\|f\|_P^2R_N}{N+1}
              \le\frac{\|f\|_P^2\delta_N}{N+1}}.
\]
This is uniform over the whole unit ball of the Hilbert test space.
More generally, any moving family satisfying
\(\|f_N\|_P^2\le A(N+1)\) has \(C_N(f_N)\to0\) unconditionally.
No pointwise bound on \(f_N\) is used.

Formal providers:
QMetricCorrectionBounds.metricPairing_sq_le_test_norm and
QCanonicalCofinalGram.testDiscrepancy_sq_le,
testDiscrepancy_sq_le_energyRate, growing_testDiscrepancy_tendsto_zero.

## Signed averages of growing dimension

For arbitrary finite indices \(n_i\) and real coefficients \(a_i\), let
\(s=\sum_i a_i r_{n_i}\). The exact complete energy identity is
\[
 z\|s\|_Q^2-\|s\|_P^2
 =R(s)=\sum_{i,j}a_i a_j C_{n_i n_j}\ge0.
\]
The stronger individual and trace budgets are
\[
 \boxed{R(s)\le
 \left(\sum_i|a_i|\sqrt{R_{n_i}}\right)^2
 \le\left(\sum_i a_i^2\right)\left(\sum_iR_{n_i}\right)
 \le\left(\sum_i a_i^2\right)\left(\sum_i\delta_{n_i}\right)}.
\]
For every \(\varepsilon>0\), one common \(H\), independent of dimension,
also gives
\[
 R(s)\le\varepsilon\left(\sum_i|a_i|\right)^2
 \quad\hbox{whenever every }n_i\ge H.
\]

Consequently, for any sequence of such sums whose minimum selected index
tends to infinity and whose coefficient l1 masses are uniformly bounded,
\[
 \boxed{z\|s_j\|_Q^2-\|s_j\|_P^2\longrightarrow0}.
\]
The number of summands may grow without restriction. The original full
energies need not be bounded. If the coefficients sum to one, \(s_j\)
is the residual of the corresponding signed average of legal candidates.
Convex averages are included.

Even unbounded l1 masses are permitted whenever the explicit weighted
budget \(\sum_i|a_{j,i}|\sqrt{R_{n_{j,i}}}\to0\).
The l2/trace estimate gives simultaneous control of every l2-unit source;
its actual finite trace is \(\sum_iR_{n_i}\).

Formal providers:
QMetricCorrectionBounds.metricCorrection_sum_le_weighted,
metricCorrection_sum_le_l2, metricCorrection_sum_tendsto_zero,
and QCanonicalCofinalGram.uniform_signed_tail_budget,
cofinal_signed_correction_tendsto_zero,
cofinal_signed_energy_discrepancy_tendsto_zero,
signedBlock_correction_le_trace.

## Stronger explicit arithmetic rate

The full checked stretched Mertens provider yields constants \(b>0\),
\(A\ge0\), and an onset, such that eventually
\[
 \boxed{R_N\le
 \frac8{N+1}+A\frac{N}{N+1}
 \exp\!\left[-b\bigl((6+\log N)\log(6+\log N)\bigr)^{1/11}\right]}.
\]
The boundary term and factor \(N/(N+1)\) are retained. This specializes
the existing complete canonical-energy estimate, improving on the
previous log-square example for the metric discrepancy.
The constants and onset remain existential, as in the checked provider.

Formal provider: QCanonicalCofinalGram.correction_eventual_stretched_bound.

## Precise research status

All the displayed canonical statements are unconditional. The finite
inverse statement assumes only the indicated finite linear independence.
The signed-family and moving-test theorems explicitly state their
coefficient or test-size restrictions.

These results transfer full Gram energy budgets and provide uniform
control of the complete change-of-measure correction. They do not supply
a bound on the common leading full residual energy. In particular, the
RH-strength task of proving a uniformly bounded legal growing-head
family or an appropriate arithmetic cancellation provider remains Open.

## Verification

The two new modules and the extended QParetoGramComparison module passed
an assembled server check in job job_YyPY_IlS7WFErNBA7MXnlPSzCzI70ZNe
(18.951 seconds). Ten representative declarations were checked with
#print axioms; each reported only propext, Classical.choice, and Quot.sound.
This development adds 40 theorem declarations and six definitions.
The exact Lean source and aggregate exports then passed the full server command
lake build RiemannResearch --quiet in job
job_u9MhKv-fuVY6kAFHi7dwNTaEgI7kK5gP (68.136 seconds, terminal succeeded).

Publication was explicitly authorized by the user on 15 October 2026.
The final checkpoint audits and validates the exact unpublished delta
before committing and pushing to main. Its terminal job record supplies
the publication result and commit.
