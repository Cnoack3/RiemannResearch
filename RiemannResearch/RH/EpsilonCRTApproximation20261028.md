# Epsilon witnesses for delayed-head squarefree CRT approximation

Continuation of the delayed-conductor investigation and the user's request to
use a forall-epsilon/exists formulation.

## What the reformulation achieves

The target is

\[
\forall\varepsilon>0\;\exists f\in\mathcal V_{\rm sf}:
\qquad \|1-f\|_Q<\varepsilon,
\]

where \(\mathcal V_{\rm sf}\) is the finite legal squarefree CRT span.
The norm includes every positive integer coordinate. Each witness may have
its own period, head, and coefficients. No bound on the entire preassigned
canonical family is a hypothesis of this criterion.

This statement is exactly membership of \(1\) in the closure of the legal span.
The existing capacity/closure bridge then implies RH, **conditionally on the
universal witness statement**. That arithmetic statement remains Open.
Changing quantifiers has not proved it.

The existing theorem
QSquarefreeResidualLimit.epsilon_approximation_iff_mem already characterizes
closure via eventually small optimizer errors. The new direct-witness
formulation connects the exact-head certificates to that same closure problem.

## Complete signed identity and explicit budgets

Put \(h_H=\operatorname{finiteHead}(H,1)\) and
\(\tau_H=\|1-h_H\|_Q^2=\sum_{n>H}Q(n)\). For any actual exact-head vector
\(f(n)=1\) for \(1\le n\le H\), Lean proves first the signed equality

\[
\|1-f\|_Q^2
=\|f\|_Q^2-1+2\tau_H
-2\langle 1-h_H,f-h_H\rangle_Q.
\]

Both tails and their mixed inner product are complete. The subsequent bound
uses the Hilbert triangle inequality and \(2ab\le a^2+b^2\):

\[
\|1-f\|_Q^2\le 2(\|f\|_Q^2-1)+4\tau_H,
\qquad
\tau_H\le\frac1{\zeta(2)H}\le\frac{76}{125H}\quad(H>0).
\]

A convenient sufficient epsilon budget is

\[
\|f\|_Q^2\le1+\frac{\varepsilon^2}{8},
\qquad \tau_H\le\frac{\varepsilon^2}{8}.
\]

It gives squared error at most \(3\varepsilon^2/4<\varepsilon^2\).
The rational head cutoff \(H\varepsilon^2\ge608/125\) discharges the tail
budget. For example, tolerance \(1/10\) permits choosing \(H=487\), whereas
tolerance \(1/100\) permits \(H=48640\); these are head requirements, **not**
certificates of the required energies.

For the actual minimum minimumAt j H with period
primorial (j + 2) (the product of primes at most \(j+2\)), the precise open
provider formalized in Lean is

\[
\forall\varepsilon>0\;\exists j,H:\quad
0<H\le j+1,\quad
H\varepsilon^2\ge608/125,\quad
\|\operatorname{minimumAt}(j,H)\|_Q^2\le1+\varepsilon^2/8.
\]

The theorem epsilon_approximation_of_minimum_energy_witnesses proves that this
provider suffices. It is a conditional theorem, not a proof of its premise.

## Period growth and selected bounds

The complete period-gain identity implies that any successful epsilon energy
certificate persists at every later primorial period with its head fixed.
The theorem minimum_energy_witnesses_cofinal_iff proves that adding an
arbitrary lower cutoff on the period index does not strengthen the provider.

A selected witness with \(\|1-f\|_Q<\varepsilon\) automatically satisfies
\(\|f\|_Q<1+\varepsilon\). The theorem
bounded_selection_of_epsilon_approximation extracts legal witnesses \(F_n\)
with error \(<1/(n+1)\) and norm \(<2\). The common bound is then a consequence
of complete-norm approximation, not an assumption on every member of the
original canonical family.

The weaker statement
\(\forall\varepsilon>0\;\exists L:E(L,15)<1+\varepsilon\) would already follow
by reusing the existing period-510510 witness. It says nothing about
arbitrarily small error: its head remains fixed. The tolerance and head
must be coupled, or the complete error must be bounded directly.

## A finite certified epsilon

The explicit period-9699690 witness is exactly one through head 20. Its
previously kernel-checked complete energy upper bound is

\[
U=\frac{311254353881}{312500000000}.
\]

The new exact Lean consequence is

\[
\|1-f\|_Q^2
\le2(U-1)+\frac{4\cdot76}{125\cdot20}
=\frac{17754353881}{156250000000}
<\left(\frac{17}{50}\right)^2.
\]

Thus a genuine legal finite witness has complete error below \(0.34\).
This uses the negative energy excess directly and is sharper here than
the separately allocated positive epsilon budgets.

The external rational head-23/period-223092870 certificate gives
\[
2\left(\frac{17378821007}{17545600000}-1\right)
+\frac{40000}{16449\cdot23}
=\frac{52492249483}{605323200000}<\frac9{100},
\]
hence an external arithmetic error certificate below \(0.3\).
Wolfram independently confirmed both rational comparisons. The head-23
certificate and its legal-vector/complete-energy bridge have not been
formalized in Lean; the \(0.3\) statement remains external computational
evidence. The \(0.34\) statement is the new Lean theorem.

## Modules and verification

- QExactHeadEpsilonBounds.lean: exact signed identity, complete target-tail
  formula, rational tail bound, epsilon budget, and the legal error \(<17/50\).
- QSquarefreeEpsilonCriterion.lean: direct epsilon/closure equivalence,
  conditional RH consumer, actual-minimum epsilon provider, persistence at
  later periods, cofinal-period equivalence, and bounded selected witnesses.

The combined declarations passed Lean in development job
job_4T_E4U6PomgIy82epO2m_irf1LxE8IUX (exit code 0).
Publication additionally validates the saved modules and their reverse
dependencies. No previous fixed-stage minimizer or conductor-gap result
was altered.

Open: prove the universal arithmetic epsilon provider, or another direct
complete-error provider. Neither finitely many tolerances nor an unbounded
collection of finite norms proves this statement. No unconditional RH
implication or new all-stage energy theorem is asserted.
