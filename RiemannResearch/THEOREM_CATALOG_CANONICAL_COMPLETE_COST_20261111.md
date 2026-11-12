# Explicit legal-family complete cost: verification and RH ledger

Continuation of D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf.
Prepared 2026-11-12 UTC (November 11 in the retained research date).
Baseline: ac1bee28482212700b25cb401ff8e3263868eda1.

## Status

The RH-strength complete-cost estimate has **not** been proved. This continuation
proves unconditional complete-cost estimates for a fully explicit legal family,
including a classical Mertens saving, and an exact equivalence identifying the
remaining arithmetic obligation. All norms below include the entire infinite
weighted sum. No finite numerical truncation is used as a proof.

The five new modules contain 34 theorem declarations and two definitions.
The final repository checkpoint supplies the integrated build/publication receipt.

## Family and normalization

For physical coordinates n >= 1, put

\[
P(n)=\frac1{n(n+1)},\qquad Q(n)=\frac1{\zeta(2)n^2},
\qquad g_d(n)=\frac{n\bmod d}{d},\qquad (Df)(n)=\frac{f(n)}n.
\]

Let

\[
m_H=\sum_{d=1}^H\frac{\mu(d)}d,\qquad
v_H=-\sum_{d=1}^H\mu(d)g_d+(H+1)m_Hg_{H+1},\qquad
E_H=\|v_H\|_P^2.
\]

The already formalized QMobiusExactHead.exactHead is reused.
QCanonicalMobiusCost.exactHead_eq_toQ identifies it with the Pareto
canonicalMobiusHilbert family under toQ. The vector is a finite legal combination
and satisfies v_H(n)=1 for 1 <= n <= H. The boundary conductor H+1 is retained,
including when it is a prime power or is not squarefree. The family is not asserted
to lie in the squarefree-only span.

The complete cost is

\[
J_\alpha(v)=\|D(v-1)\|_Q^2+\alpha\|v\|_Q^2.
\]

The fixed sequence used in the criterion is
H_j=(j+1)^2, lambda_j=(j+1)^(-4)=H_j^(-2), and legalFamily(j)=v_(H_j).
The family is independent of the exponent eta.

## Sharp geometry and transfer

For any Pareto vector v equal to 1 through H, let e_H be the coordinate head of 1.
The new exact identity is

\[
H\|v-1\|_P^2+
\|(v-e_H)+H(1-e_H)\|_P^2=(H+1)\|v\|_P^2.
\]

Thus, for H >= 1,

\[
\|v-1\|_P^2\le\frac{H+1}{H}\|v\|_P^2.
\]

This retains the complete signed tail before taking the nonnegative square
remainder. The geometric constant is sharp on the unrestricted exact-head affine
space (take v=e_H-H(1-e_H)); sharpness is a mathematical observation, not a separate
new Lean declaration.

A vector whose physical head vanishes through H satisfies

\[
\|Df\|_Q^2\le\frac{\|f\|_Q^2}{(H+1)^2}.
\]

In particular, the signed reciprocal estimate retains
\(\|v\|_Q^2+1-2\langle v,1\rangle_Q\).
Combining exact-head geometry with the proved P/Q norm comparisons gives

\[
J_\alpha(v_H)\le\frac2{\zeta(2)}
  \left(\alpha+\frac1{H(H+1)}\right)E_H
\quad(H\ge1,\ \alpha\ge0).
\]

At the balanced scale alpha=H^(-2), the lower bound follows from the energy term:

\[
\boxed{\frac{E_H}{\zeta(2)H^2}
 \le J_{H^{-2}}(v_H)
 \le \frac{4E_H}{\zeta(2)H^2}.}
\]

The more precise preceding upper bound is also available; the constant 4 is
convenient for uniform comparisons.

## Unconditional rates

The existing elementary energy bound E_H < 4H gives the new complete estimate

\[
J_{H^{-2}}(v_H)\le\frac{16}{\zeta(2)H}\qquad(H\ge1).
\]

The existing unconditional PNT energy result gives H J_(H^-2)(v_H) -> 0.
For each positive c below the repository's certified classical contour endpoint,
there is C_c >= 0 such that, **for every H >= 1**,

\[
\boxed{
J_{H^{-2}}(v_H)\le
\frac{12}{\zeta(2)H^2}
+\frac{C_c}{H}\exp(-c\sqrt{\log H}).}
\]

The endpoint is Quantitative.MobiusContour.contourEndpoint, with positivity
proved in the existing Mertens development. The family is explicit; this theorem
does not claim a numerically evaluated C_c. The proof first obtains an eventual
bound and then absorbs the finite initial segment using the elementary bound.

The arithmetic input is the repository's proved
M_sqrt_log_eventually_of_lt_contourEndpoint, combined with
canonicalMobius_energy_of_uniform_mertens_log and
exponential_entropy_le_optimal_rate. An intermediate b with c < b < endpoint
absorbs the entropy loss, preserving every strictly smaller positive rate.
No RH or unproved Mertens estimate is a hypothesis.

An independently checked route through canonicalMobius_eventual_stretched_bounds
also gives, for every fixed integer k >= 0, an eventual bound

\[
J_{H^{-2}}(v_H)\le
\frac{12}{\zeta(2)H^2}+
\frac{C_k}{H(6+\log H)^k}.
\]

The square-root logarithmic exponential is asymptotically stronger than every
fixed logarithmic saving. Neither estimate gives the near-linear power required
for RH. Constants depend on k; choosing k as a function of H is not justified.

## RH implication and equivalence ledger

For the fixed family and scale above, Lean proves

\[
\begin{aligned}
&\bigl[\forall\eta>0\ \exists C_\eta\ge0\ \forall j,\
 J_{\lambda_j}(v_{H_j})\le C_\eta\lambda_j^{1-\eta}\bigr]\\
&\quad\Longleftrightarrow
 \bigl[\forall\eta>0\ \exists B_\eta\ge0\ \forall j,\
 E_{H_j}\le B_\eta\lambda_j^{-\eta}\bigr]
 \quad\Longrightarrow\quad\mathrm{RH}.
\end{aligned}
\]

The second condition is equivalently a subpower energy bound
E_(H_j)=O_epsilon(H_j^epsilon) for every epsilon>0 (rename epsilon=2 eta).
Both conditions remain open for this family. The forward/reverse equivalence
between these two quantified estimates is kernel checked. **RH implying either
condition for this particular family is not asserted.**

| Statement | Status |
|---|---|
| Finite legality and exact head of v_H | Proved; existing construction reused and linked |
| Complete cost <= 16/(zeta(2)H) | New Lean theorem |
| Complete cost = o(H^-1) | New Lean theorem from proved PNT energy |
| Global square-root logarithmic exponential saving | New Lean theorem |
| Requested power inequality for every eta >= 1/2 | New Lean theorem |
| Requested near-linear inequality for every eta > 0 | Open arithmetic condition |
| Near-linear cost iff subpower source energy for this family | New Lean theorem |
| Subpower source energy implies Mathlib RiemannHypothesis | New conditional Lean theorem |
| Paper's stronger O(lambda_j) cost for this family | Open; by the displayed comparison it is equivalent to uniformly bounded E_(H_j) |
| RH iff the stated bound for this particular family | Not established |

The paper's original linear-cost criterion and the previous continuation's
near-linear criterion remain distinct. This continuation proves neither arithmetic
hypothesis. Axiom checking a conditional implication does not prove its hypothesis.

## Lean map

All paths below are under RiemannResearch/RH/.

| Module | Principal declarations |
|---|---|
| ParetoExactHeadEnergy.lean | exact_head_square_identity; error_norm_sq_le |
| QExactHeadCost.lean | D_norm_sq_le_of_head_zero; cost_le_signed_of_exact_head |
| QCanonicalMobiusCost.lean | exactHead_eq_toQ; complete_cost_source_bound; balanced_cost_source_upper/lower; balanced_cost_explicit; balanced_cost_little_o; legalFamily_half_loss_bound |
| QCanonicalMobiusCostRates.lean | balanced_cost_eventual_sqrt_log; balanced_cost_global_sqrt_log; legalFamily_global_sqrt_log; balanced_cost_eventual_log_power |
| QCanonicalMobiusCostCriterion.lean | near_linear_cost_iff_subpower_energy; riemannHypothesis_of_subpower_energy |

The last three modules use namespace RiemannResearch.RH.QCanonicalMobiusCost.
All five modules are exported by RiemannResearch.lean.

## Published research and computation audit

1. [Báez-Duarte, A strengthening of the Nyman-Beurling criterion](https://arxiv.org/html/math/0202141v2):
   the natural-generator closure criterion is an RH equivalence. The raw Mobius
   approximants diverge in the continuous Hilbert space; damped constructions have
   conditional membership/convergence steps. These statements do not supply an
   unconditional complete-energy bound for the boundary-corrected family above.
2. [Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation](https://arxiv.org/html/math/0607733v1):
   Theorem 1 gives the discrete residue-span criterion in the exact weight
   1/(n(n+1)); comparable weights preserve the closure formulation.
3. [Bettin, Conrey and Farmer, An optimal choice of Dirichlet polynomials](https://arxiv.org/html/1211.5191v1):
   the sharp asymptotic for logarithmically weighted Mobius coefficients assumes
   RH and an additional reciprocal-zeta-derivative moment bound. It cannot be used
   as an unconditional provider here.
4. [Maier and Rassias, Explicit estimates of sums related to the Nyman-Beurling criterion](https://arxiv.org/abs/1806.05070):
   their fixed-power saving for particular Mobius/Estermann sums is a potential
   input for a future signed Gram analysis. A transfer to the complete energy
   E_H has not been established in this continuation.

Wolfram exact checks confirmed the finite exact-head formula through H=12 and
the scalar square-completion identities. These are diagnostic checks; the Lean
proofs do not assume their outputs. A floating-point exploratory calculation at
H=10,30,100,300 suggested small source energies, but is not an interval certificate,
a proof of boundedness, or asymptotic evidence sufficient for any RH claim.

## CRT scope and next arithmetic step

The earlier audit's all-modulus inverse-limit and prime-power CRT formulations
assemble compatible residue coordinates. They justify retaining full conductor
information, including the boundary conductor H+1. CRT, Haar averages, and
profinite continuity alone do not bound the physical P/Q weighted infinite tail.
No new infinite-CRT assertion is needed or claimed for the present complete-cost
proof.

The next precise objective is subpower E_(H_j). The repository's existing
CanonicalMobiusBoundaryEnergy identity expresses this energy as a complete
critical-line integral of the corrected Mobius symbol against |zeta|^2.
Preserve the boundary cross term when estimating this integral or its signed
Gram expansion. Any use of a published cancellation theorem must establish
uniformity over the entire range, not only a finite head. The proved
E_H <= 3+O(H exp(-c sqrt(log H))) still leaves an H^(1-o(1)) source-energy scale.

## Verification receipts

- Complete combined source, including the global bound: run_code job
  job_Jk_Qkb0DQiScpWfbUBXa53TSzbHxObVn, exit 0, verified true.
  Code SHA256: 38e708e787fee8d0b028d22a7f594fda5b0764e59e1372e7a4399bd3d6e100bf.
  [BuildBuddy receipt](https://app.buildbuddy.io/invocation/27166eb2-182c-4e93-b1cf-6c01e67436f1).
- Saved modules and 15 exact `#guard_msgs` axiom checks: job
  job_DJlTpinvB2jpOJyuyNVlQO7Kj3ots29A, exit 0, verified true.
  All 15 reported exactly `[propext, Classical.choice, Quot.sound]`; no
  `sorryAx`, custom research axiom, or unsafe proof was accepted.
  Code SHA256: 4ea346c77b2c987b6cc6110ae3e12a968dac0ec36f304a623fbd4bdbeacf547c.
  [BuildBuddy receipt](https://app.buildbuddy.io/invocation/59bd5576-d001-4f48-88fc-7f50e6a91a02).
  The audited declarations were:

  - `RiemannResearch.RH.ParetoExactHeadEnergy.exact_head_square_identity`
  - `RiemannResearch.RH.ParetoExactHeadEnergy.error_norm_sq_le`
  - `RiemannResearch.RH.QExactHeadCost.D_norm_sq_le_of_head_zero`
  - `RiemannResearch.RH.QExactHeadCost.cost_le_signed_of_exact_head`
  - `RiemannResearch.RH.QCanonicalMobiusCost.exactHead_eq_toQ`
  - `RiemannResearch.RH.QCanonicalMobiusCost.complete_cost_source_bound`
  - `RiemannResearch.RH.QCanonicalMobiusCost.balanced_cost_source_upper`
  - `RiemannResearch.RH.QCanonicalMobiusCost.balanced_cost_source_lower`
  - `RiemannResearch.RH.QCanonicalMobiusCost.legalFamily_legal`
  - `RiemannResearch.RH.QCanonicalMobiusCost.balanced_cost_little_o`
  - `RiemannResearch.RH.QCanonicalMobiusCost.balanced_cost_global_sqrt_log`
  - `RiemannResearch.RH.QCanonicalMobiusCost.legalFamily_global_sqrt_log`
  - `RiemannResearch.RH.QCanonicalMobiusCost.legalFamily_half_loss_bound`
  - `RiemannResearch.RH.QCanonicalMobiusCost.near_linear_cost_iff_subpower_energy`
  - `RiemannResearch.RH.QCanonicalMobiusCost.riemannHypothesis_of_subpower_energy`

- The publication checkpoint runs the full repository Bazel/BuildBuddy target,
  performs the source audit, and publishes only if validation succeeds.
