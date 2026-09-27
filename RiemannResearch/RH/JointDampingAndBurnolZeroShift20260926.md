# Joint damping and Burnol zero-shift continuation
Date: 2026-09-26 (user-local date)
Base: b7e4d792a14f4f946ec2287d1ef62d7520270979

## Result

Unconditional RH was not proved. The saved candidates passed the Lean
kernel after the verifier service recovered. This continuation strengthens
the existing scalar damping theorem and formalizes the isolated-zero core
of Burnol's argument, with the arithmetic RH-strength premise explicit.

## Exact scalar argument

Let w_(epsilon,c)(n) be the actual dampedPhysicalWeight and assume H(0)=0,
\[
\sum_{n\ge1}\frac{2|H(n)|}{(n+1)(n+2)}<\infty,\qquad
\lim_{N\to\infty}\frac{H(N)}{N+2}=0.
\]
For epsilon >= 0 and 0 <= c <= 1, put
\[
S_{\varepsilon,c}(N)=
\sum_{n=1}^N(H(n)-H(n-1))w_{\varepsilon,c}(n),\qquad
L_{\varepsilon,c}=
\sum_{n\ge1}H(n)(w_{\varepsilon,c}(n)-w_{\varepsilon,c}(n+1)).
\]
The primitive-side series is absolutely convergent. Finite Abel summation
gives the exact remainder
\[
S_{\varepsilon,c}(N)-L_{\varepsilon,c}
=H(N)w_{\varepsilon,c}(N+1)
-\sum_{n>N}H(n)(w_{\varepsilon,c}(n)-w_{\varepsilon,c}(n+1)).
\]
The existing weighted bounds give the uniform estimate
\[
|S_{\varepsilon,c}(N)-L_{\varepsilon,c}|
\le \frac{|H(N)|}{N+2}
+2\sum_{n>N}\frac{|H(n)|}{(n+1)(n+2)}.
\]
Therefore for every N_j tending to infinity and admissible epsilon_j,c_j
tending to zero,
\[
S_{\varepsilon_j,c_j}(N_j)\longrightarrow
2\sum_{n\ge1}\frac{H(n)}{n(n+1)(n+2)}.
\]
No monotonicity or coordination of rates is required. The Lean proof uses
dominated convergence on primitive terms masked by k < N_j. The displayed
remainder provides the mathematical explanation; the new formal
declarations establish the joint convergence itself.

Declarations:
- Analysis.primitive_abel_diagonal_partialSum_tendsto
- RH.Pareto.dampedPhysicalWeight_diagonal_primitive_boundary
- RH.Pareto.dampedPhysical_joint_ordered_pairing_tendsto

The generic declaration extends Analysis/OrderedPrimitiveAbel.lean.
The arithmetic specializations extend RH/DampedMobiusOrderedPairing.lean.

The hypotheses are ordinary analytic conditions in the generic theorem.
Showing them for the actual orthogonal residual remains an open
domain-specific obligation. Neither infinite damped Hilbert membership nor
infinite legal-series interchange follows merely from this scalar limit.

## Burnol's analytic obstruction

Source for the zero-propagation strategy:
J.-F. Burnol, “On an analytic estimate in the theory of the Riemann zeta
function and a theorem of Baez-Duarte,” arXiv:math/0202166, Corollary 4.1
and Theorem 4.2, https://arxiv.org/pdf/math/0202166.

For every rho != 1, the actual zeta function is analytic at rho and not
locally identically zero. The identity theorem and zeta(2) != 0 establish
the latter fact on the connected domain C minus {1}. Isolated zeros imply
\[
\exists\delta>0\ \forall\varepsilon\in(0,\delta):
\zeta(\rho-\varepsilon)\ne0.
\]
If rho is a zero in the right half-strip, delta can also ensure
Re(rho-epsilon)>1/2; the numerator at that point is nonzero while
zeta((rho-epsilon)+epsilon)=0.

Consequently the explicit propagation premise
\[
\forall j,\rho:\quad
\tfrac12+\varepsilon_j<\Re\rho<1,\quad \zeta(\rho)=0
\ \Longrightarrow\ \zeta(\rho-\varepsilon_j)=0
\]
for a positive sequence epsilon_j tending to zero excludes all
right-half-strip zeros. The repository's verified reflection theorem
then gives Mathlib's RiemannHypothesis.

Module: RH/BurnolDampingZeroShift.lean.
Declarations:
- zeta_eventually_ne_zero_punctured
- zeta_small_left_shift_ne_zero
- right_half_zero_shift_obstruction
- riemannHypothesis_of_cofinal_zero_propagation
- riemannHypothesis_of_zero_propagation_sequence

The final two declarations are conditional research reductions. Their
hprop hypotheses are not discharged here. The full arithmetic Mellin
identity and its continuation under finite energy are separate
formalization tasks. Establishing small-damping L2 membership for the
actual arithmetic function remains open. This module does not claim the
full formalization of Burnol's L2 theorem.

## Verification and recovery

The original preliminary signature-query job
job_m6q-g9qPucC86ktalxrBFssXfghOL8_I eventually ran and terminated with
ordinary unknown-identifier errors for speculative #check names. It was
not a proof check of these candidates.

Actual combined candidate:
job_00hjeY0AzwFuQCd8Xr7n4nudVU55OB_e
Result: succeeded, exit_code=0, verified=true, elapsed 10.073 seconds.
Four principal #print axioms reports contain only propext,
Classical.choice, and Quot.sound. There are no sorry, admit, project-local
axioms, or unsafe declarations.

These axiom reports do not discharge assumptions in theorem types.
The exact declarations retain the primitive regularity or zero-propagation
premises described above.

The publication checkpoint validates the integrated changed modules and
their reverse dependents. The commit containing this note records the
published result; a successful isolated snippet alone is not a project
publication.
