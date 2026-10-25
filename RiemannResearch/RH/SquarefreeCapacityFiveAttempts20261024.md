# Five attempts at squarefree Ramanujan capacity saturation

Date: 24 October 2026 (America/Los_Angeles).
Source: the user's request to prove that the squarefree packet capacities increase to one, generate and pursue a new research agenda after each attempt, and stop at RH or five attempts.

**Stopping outcome:** five mathematical approaches were investigated. Neither \(\kappa_j\to1\) nor unconditional RH was proved. The squarefree monotonicity development and an obstruction to the available reciprocal certificates were proved in Lean. All substantive hypotheses in the conditional reductions remain explicit.

## Exact target and unconditional development

Let
\[
D_j=\{q:2\le q\le j+1,\ q\text{ squarefree}\},\quad
H_j=(\langle B_q,B_r\rangle_P),\quad \ell_j(q)=\Lambda(q).
\]
Here \(P(n)=1/[n(n+1)]\), and \(B_q\) are the repository's integrated Ramanujan packets. All Gram entries use the complete infinite-tail Pareto norm.

The new module RH/SquarefreePacketCapacity.lean defines this exact dictionary and proves
\[
\kappa_j=\ell_j^TH_j^{-1}\ell_j=\|p_j\|_P^2,\qquad
\|1-p_j\|_P^2=1-\kappa_j,
\]
\[
0<\kappa_j<1\quad(j>0),\qquad
\kappa_m\le\kappa_n\quad(m\le n),\qquad
\kappa_j\longrightarrow\kappa_\infty:=\sup_j\kappa_j\le1.
\]
Stage zero is empty and has capacity zero. The finite Gram matrices are positive definite. For \(m\le n\),
\[
\kappa_n-\kappa_m=\|p_n-p_m\|_P^2.
\]
Nonsquarefree cutoffs repeat; strict monotonicity at every integer index is not asserted. Any finite legal trial \(f\in V_j\) satisfies
\[
1-\kappa_\infty\le1-\kappa_j\le\|1-f\|_P^2.
\]
The module proves that squarefree saturation implies Mathlib's RiemannHypothesis, by comparison with full conductor capacities. It does not supply an unconditional reverse RH implication.

Principal declarations: kappa_eq_inverseGram, gram_posDef, error_eq, kappa_monotone, kappa_bounds, kappa_pos, kappa_tendsto, kappa_increment_exact, kappa_succ_eq_of_not_squarefree, limiting_error_floor, riemannHypothesis_of_saturation.

## Attempt 1: direct projection

**Work:** audited the exact types in RamanujanSaturationCriteria.lean; checked the principal axiom dependencies; specialized finite Gram/projection arguments to the actual squarefree dictionary.

**Result:** monotonicity and existence of a limit are unconditional. The existing full-conductor limit is \(1-\mathrm{limitEnergy}\), and the squarefree limit is its own supremum. Neither result makes the remaining defect zero. No provider discharging that step was found.

**Agenda generated after attempt 1, pursued in attempt 2:**

1. Retain the exact normalized sampling-error decomposition.
2. Test whether arbitrarily accurate sampling removes the capacity deficit.
3. Identify an additional input stronger than sampling accuracy.

## Attempt 2: accurate sampling and normalization

All three agenda items were addressed. The existing normalized_target_error_exact theorem gives
\[
\|1-F_{D,T}\|^2
=\kappa_D^{-1}-1+\|F_{D,T}-F_{D,\infty}\|^2.
\]
Setting the sampled source equal to the true source removes only the last term.

An ordinary Hilbert-space countermodel takes orthonormal \(e_*,e_1,\ldots\) and unit target
\[
y=\sqrt\delta\,e_*+\sum_{n\ge1}\sqrt{(1-\delta)2^{-n}}\,e_n,
\qquad 0<\delta<1.
\]
The dictionary \(e_1,\ldots,e_N\) has identity Gram and capacity
\((1-\delta)(1-2^{-N})\). Sampling can be exact at every height while the limit remains \(1-\delta\). This is not an arithmetic counterexample and is not a new Lean declaration.

**Result:** no saturation proof from height selection. The Lean sampled-signal rate also retains an actual horizontal-density provider, as recorded in EffectiveSamplingAnalyticAudit20261024.md. Granting it would still leave the capacity deficit.

**Agenda generated after attempt 2, pursued in attempt 3:**

1. Keep the signed weighted-average bound and its complete remainder.
2. Bound reciprocal mass quantitatively when a positive capacity deficit persists.
3. Test whether exact heads prove divergence along the correlation-controlled selected heads.

## Attempt 3: reciprocal-energy averaging

Suppose a legal weighted trial has the complete estimate
\[
\|1-F\|_P^2\le S^{-1}+cS^{-2},\qquad S>0,\quad c\ge0.
\]
Put \(\delta=1-\kappa_\infty\ge0\). The legal error floor gives
\[
\delta S^2\le S+c.
\]
If \(\delta>0\), then
\[
S\le\max\left(1,\frac{1+c}{\delta}\right).
\]
These are new Lean theorems in Analysis/ReciprocalEnergyGap.lean. The actual squarefree consumer RH/SquarefreeCapacityReciprocalCriterion.lean proves that cofinal controlled reciprocal mass forces squarefree saturation, hence RH. Legality, the full energy estimate, and cofinality are explicit hypotheses.

The third agenda item does not follow from exact heads alone. Under the actual measure \(P\), the ordinary countermodel
\[
G_N=1-(N+1)\mathbf1_{\{n>N\}}
\]
matches the head, has mean zero, and has residual energy \(N+1\). Unselected reciprocal energies have a divergent sum, but every affine average still has mean zero and squared error at least one. This is not the actual legal arithmetic family. It isolates the need to preserve reciprocal mass after controlling correlations.

**Result:** a quantitative gap bound and a conditional saturation theorem; actual selected reciprocal divergence remains **Open**.

**Agenda generated after attempt 3, pursued in attempt 4:**

1. Instantiate the available amplitude certificates for the least-prime-balanced Möbius family.
2. Determine whether those certificates have divergent reciprocal mass under the actual selector.
3. Inspect the signed arithmetic tail for an improvement.

## Attempt 4: actual prime-balanced certificates

For the least prime \(q_N>N\), define
\[
a_N=\sum_{d\le N}\frac{\mu(d)}d,\quad
G_N=-\sum_{d\le N}\mu(d)g_d+q_Na_Ng_{q_N},\quad U(N)=N+q_N.
\]
Existing results prove squarefree legality, exact heads, and residual amplitude \(U(N)\). The corresponding periodic arithmetic function has the complete P-energy certificate
\[
\|G_N-1\|_P^2\le \frac{U(N)^2}{N+1}.
\]
This uses the exact tail probability \(P(n>N)=1/(N+1)\). The existing Q-Hilbert implementation has the same coordinate values; no equality of P and Q norms is asserted.

For the actual selector \(N_j=\mathrm{exactHeadSelection}(U,j)\), set
\[
A_j=\frac{U(N_j)^2}{N_j+1}.
\]
The new generic and arithmetic-specific Lean results prove
\[
N_j\ge4^j,\qquad A_j\ge N_j,\qquad A_j^{-1}\le4^{-j},
\qquad \sum_jA_j^{-1}<\infty.
\]
Only \(U(N)\ge2N\) is needed; the arithmetic specialization follows from \(q_N>N\). No prime-gap estimate is required.

Modules:
- Analysis/GeometricHeadCertificateObstruction.lean: exactHeadSelection_ge_four_pow, selectedAmplitudeTailCertificate_ge_head, selectedAmplitudeTailCertificate_reciprocal_summable.
- RH/PrimeHeadCertificateObstruction.lean: nextPrimeHead_amplitude_reciprocal_summable.

Thus this specific available certificate choice cannot discharge reciprocal divergence. This does **not** prove summability of reciprocals of actual residual energies: upper certificates may greatly exceed the true energies.

For the third item, ordinary algebra retains the exact floor identity
\[
G_N(n)=\sum_{d\le N}\mu(d)\lfloor n/d\rfloor
-q_Na_N\lfloor n/q_N\rfloor.
\]
For \(N<n<q_N\) and \(n<2(N+1)\), this yields
\[
G_N(n)-1=M(N)-M(n).
\]
Hence the first uncovered window contributes
\[
\sum_{N<n<q_N}\frac{|M(n)-M(N)|^2}{n(n+1)}
\]
when the stated range condition holds; for \(N>1\), Bertrand's \(q_N\le2N\) ensures it. The floor/Mertens identity and this use of Bertrand are ordinary mathematics, not new Lean declarations. They do not control the rest of the complete signed tail.

**Result:** the crude certificates are rigorously ruled out as a source of divergent reciprocal mass. Sharper actual energy estimates remain **Open**.

**Agenda generated after attempt 4, pursued in attempt 5:**

1. Preserve the full Schur complement and screened source for squarefree blocks.
2. Test whether prime-supported raw sources force divergent relative gains.
3. Identify the exact missing lower bound and stop after attempt five.

## Attempt 5: signed Schur gains and prime-supported sources

For old dictionary \(D_j\), disjoint squarefree block \(E_j\), and mixed Gram matrix \(C_j\), the existing exact identity is
\[
\kappa_{D_j\cup E_j}-\kappa_{D_j}=\eta_j^TS_j^{-1}\eta_j,
\]
\[
S_j=H_{E_j}-C_jH_{D_j}^{-1}C_j^T,\qquad
\eta_j=\ell_{E_j}-C_jH_{D_j}^{-1}\ell_{D_j}.
\]
A sufficient arithmetic estimate is
\[
\eta_j^TS_j^{-1}\eta_j\ge b_j(1-\kappa_{D_j}),\qquad
0\le b_j<1,\qquad \sum_jb_j=\infty.
\]
It contracts the defect by the product of \(1-b_j\). No provider was obtained. On composite squarefree conductors, the raw source zero leaves the screened source \(-C_jH_{D_j}^{-1}\ell_{D_j}\), without a lower bound on its inverse-Schur norm.

A stronger ordinary countermodel tests this inference. Let \(e_0,e_*,e_q\) be orthonormal, with q ranging over squarefree integers at least two. Let \(y=e_0\), \(v=e_0+b e_*\), and \(b,d>0\). Put
\[
B_2=\Lambda(2)(v+d e_2),\qquad
B_q=\Lambda(q)v+e_q+e_2\quad(q>2).
\]
Every finite family is independent and \(\langle y,B_q\rangle=\Lambda(q)\). A composite screened source after adjoining \(B_2\) equals
\[
-\frac{d}{1+b^2+d^2}\ne0,
\]
so its gain is strictly positive. Nevertheless the squarefree closed span is
\(W=\operatorname{span}(v)\oplus\ell^2(\{q:q\ge2,\ q\text{ squarefree}\})\):
\(B_p/\log p\to v\) along primes, then the coordinate vectors are recovered. Consequently
\[
\kappa_j\longrightarrow\|P_Wy\|^2=\frac1{1+b^2}<1.
\]
Exact source sampling still makes its discrepancy zero. This model does not reproduce the actual arithmetic Gram entries. It shows why source sparsity, independence, sampling accuracy, and positive Schur gains alone do not prove saturation. It is ordinary mathematics, not a Lean formalization.

**Result:** the arithmetic relative-gain lower bound remains **Open**. The fifth attempt ends without unconditional RH.

## Handoff after the stopping point — not a sixth attempt

1. Prove sharper complete signed-tail energy estimates for the specified least-prime-balanced family, then test reciprocal-mass retention along a suitable selector.
2. Investigate weights and selectors using signed correlations instead of worst-case amplitudes. Prove both correlation control and mass retention.
3. Alternatively prove the displayed inverse-Schur relative-gain lower bound for actual arithmetic blocks.
4. Keep density, target-direction, and RH-converse providers explicit. Replacing one equivalent saturation criterion with another does not discharge it.

## Verification ledger

- Existing saturation API audit: job_LC2_cwos8XXdeaTSeyaYJuYbCLJhQ62f, success, exit code 0; reported verification duration 12.094 seconds.
- Combined new declarations: job_SnGfPiF2CuAD6Je28-TQEwRSqgE4tZrG, success, verified=true, exit code 0; reported verification duration 7.482 seconds.
- Principal axiom audits list only propext, Classical.choice, and Quot.sound. The new modules use no sorry, admit, project-local axiom, or unsafe declaration.
- Combined snippet verification is not final project validation. The required checkpoint validates the saved modules and publication; its job and commit are reported in the final conversation response.
- Workspace opening and status transport incurred additional delay. Their exact round-trip durations were not instrumented and are not included in verification durations.
- Countermodels and the Mertens-window identity are ordinary mathematics, not Lean-verified arithmetic counterexamples.

Classical context: Báez-Duarte's strengthened Nyman–Beurling criterion is an approximation equivalence, not an unconditional saturation estimate: https://arxiv.org/abs/math/0202141 .
The related work explains why pointwise and L1 convergence need not yield L2 convergence: https://arxiv.org/abs/math/0011254 .
These references support the conceptual distinction only and are not imported proof providers.
