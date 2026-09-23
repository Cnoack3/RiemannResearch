# What must be proved for an unconditional RH result

Date: 2026-09-23.
Base project commit for the original audit: d911872ed0092a731316c61f869529d1e5bc6c59.
Updated after the Noor regularity completion on the same date:
the former shifted-density formalization gap is discharged. See
`NoorRegularityCompletion20260923.md`.
Scope: the current Pareto projection, inverse-Gram, CRT/Green, residual-tail,
Noor, and Mellin/Burnol routes in RiemannResearch.

## Conclusion

The direct Pareto-to-RH implication is already formalized without a missing
analytic bridge. The remaining task is to prove a provider of an arithmetic
convergence or boundedness premise. Verifying that a conditional theorem uses
only Lean's standard axioms does not prove its explicit premise.

A particularly economical sufficient target is a finite bound on the actual
normalized residual tail at arbitrarily large cutoffs. This target does not
require a prescribed convergence rate, or even convergence of that normalized
tail to zero as an input.

## 1. The exact mathematical objects

Use the complete Pareto space
\[
 \|f\|_P^2=\sum_{n=1}^{\infty}\frac{|f(n)|^2}{n(n+1)},\qquad
 g_d(n)=\frac{n\bmod d}{d}.
\]
Let
\[
 V_N=\operatorname{span}\{g_2,\ldots,g_N\},\qquad
 V=\overline{\bigcup_N V_N},\qquad
 F_N=P_{V_N}\mathbf1,
\]
\[
 r=\mathbf1-P_V\mathbf1,\qquad
 \delta=\|r\|_P^2,\qquad
 T_N=\sum_{n>N}\frac{|r(n)|^2}{n(n+1)}.
\]
The project stage is n=N-1. In namespace
RiemannResearch.RH.Pareto.CoefficientStabilization, the corresponding objects
are projection, closedSpace, limitResidual, limitEnergy, and residualTailEnergy.

The existing unconditional projection theorem gives
\[
 F_N\longrightarrow P_V\mathbf1,\qquad
 \|\mathbf1-F_N\|_P^2
   =\delta+\|P_V\mathbf1-F_N\|_P^2.
\]
Thus convergence of the projections is already established. The missing
identification is \(P_V\mathbf1=\mathbf1\), equivalently \(\delta=0\).

Likewise every fixed optimal coefficient has an unconditional limit, but the
limit is
\[
 c_{\infty,m}=-\mu(m)+
 \sum_{d\mid m}\mu(m/d)\bigl(r(d)-r(d-1)\bigr),
\]
where the anchored value is r(0)=0. The finite divisor sum has not been proved
zero. The identity defining the correction does not identify its limit.

## 2. A precise sufficient target, with no remaining PNT hypothesis

Prove
\[
 \boxed{\exists C\in\mathbb R\;\forall K\in\mathbb N\;
   \exists N\ge K:\quad N T_N\le C.}
 \tag{A}
\]
The constant is finite because it is a real number. No sign assumption on C
is needed in the theorem; any witness automatically bounds nonnegative tails.

The verified dichotomy is
\[
 r=0
 \quad\text{or}\quad
 N T_N\longrightarrow+\infty.
\]
Consequently (A) forces r=0. Conversely r=0 supplies C=0. The added declaration
in RH/ParetoResidualTailDichotomy.lean is therefore the exact equivalence

~~~lean
theorem frequently_bounded_actual_tail_iff_residual_zero :
    (∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * residualTailEnergy N ≤ C) ↔ limitResidual = 0
~~~

This is an unconditional theorem about two equivalent propositions. It does
not assert that either proposition holds.

The cofinal, explicit-quantifier acceptance gate was checked as follows:

~~~lean
import RiemannResearch.RH.ParetoResidualTailDichotomy

open Filter
open scoped Topology
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.Pareto.CoefficientStabilization

theorem audit_RH_of_cofinal_tail_budget (C : ℝ)
    (bound : ∀ K : ℕ, ∃ N : ℕ,
      K ≤ N ∧ (N : ℝ) * residualTailEnergy N ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_frequently_bounded_actual_tail C
    (Filter.frequently_atTop.mpr bound)
~~~

The remaining work is to construct C and prove bound without assuming RH,
density, residual vanishing, or an equivalent open condition.

The PNT input is already a checked provider:
mobiusReciprocalSum_tendsto_zero in RH/CanonicalMobiusPNT.lean.
It is obtained from the project's compatibility port of PNT+'s mu_pnt_alt.
The axiom inspection of both this provider and the complete tail-to-RH
reduction returned only propext, Classical.choice, and Quot.sound.

An isolated Lean audit also verified
\[
 (A)
 \iff r=0
 \iff
 \forall m\ge2,\;
 [G_N^{-1}(b_N+G_N\mu_N)]_m\longrightarrow0.
\]
No converse from RH to density was used.

## 3. A constructive alternative that avoids referring to the unknown residual

Construct a family H_N of finite legal combinations such that
\[
 H_N(k)=1\quad(1\le k\le N)
\]
and prove, for some finite C,
\[
 \forall K\;\exists N\ge K:\quad
 \sum_{k=1}^{\infty}\frac{|H_N(k)|^2}{k(k+1)}\le C.
 \tag{B}
\]
The existing theorem
riemannHypothesis_of_frequently_bounded_exact_head_energy
concludes RH from these conditions; membership in closedSpace suffices, and
literal finite legal combinations provide it.

These H_N are auxiliary interpolants, not a redefinition of the original
optimal projections F_N. The bound on the norms of F_N does not supply (B):
the theorem also requires exact equality to 1 throughout the initial segment.

For every exact-head H_N, the energy split is exactly
\[
 \|H_N\|_P^2
 =\frac{N}{N+1}
  +\sum_{k>N}\frac{|H_N(k)|^2}{k(k+1)}.
\]
Thus a uniform bound on the complete tails of legal exact-head interpolants
is enough. Head interpolation alone is already available. Its cost in the
full infinite norm is the substantive issue.

The canonical Möbius exact-head construction currently has the checked result
\[
 \frac{\|\mathrm{canonicalMobiusHilbert}(N)\|_P^2}{N}
 \longrightarrow0.
\]
This does not give bounded norms at arbitrarily large cutoffs. A sharper bound
for that family, or a better family with controlled complete energy, would
supply the missing research input. There is no claim that the particular
canonical family must admit such a bound.

## 4. What the CRT and Gram arguments must control

The exact inverse-Gram identities and all fixed inverse-Gram entry limits
are present. The note RH/InverseGramCorrectionAttempt20260923.md also gives an
informal analytic proof of fixed-source convergence
\[
 (b_N+G_N\mu_N)_d\longrightarrow0\qquad(d\text{ fixed}).
\]
That source-convergence argument is explicitly not yet formalized.

The correction tests a growing sum
\[
 \sum_{d=2}^N (G_N^{-1})_{m,d}(b_N+G_N\mu_N)_d.
\]
Entrywise limits of the factors do not justify passage through the growing
sum. A proof must control the entire signed sum, or give a valid uniform
tail/energy estimate for it.

The existing exact dual pairing is
\[
 [G_N^{-1}(b_N+G_N\mu_N)]_m
 =-\langle A_N,u_m-P_{V_N}u_m\rangle_P,
 \qquad
 A_N=\mathbf1+\sum_{d=2}^N\mu(d)g_d.
\]
Here u_m is the actual finite-support coefficient dual. A new vanishing
argument is needed for this pairing. Its algebraic identity alone is complete.

For the CRT transfer, the genuine Pareto residue weights are not uniform.
Writing
\[
 W_Q(r)=\sum_{j=0}^{\infty}
 \frac1{(r+jQ)(r+jQ+1)},\qquad D_Q(r)=W_Q(r)-1/Q
\]
for fixed positive r, Lean proves
\[
 W_Q(r)\longrightarrow\frac1{r(r+1)},\qquad
 D_Q(1)\longrightarrow\frac12.
\]
The precise declaration is uniformDefect_one_tendsto_half.
Consequently a proof that discards the signed nonuniform correction merely
because Q grows cannot work.

The newest CRT/Green module proves the complete-tail estimate
\[
 |\operatorname{Tail}_N(A_N,B_N)|
 \le \frac{E(A_N)E(B_N)}{N+1},
\]
where the packet coefficient envelope is
\[
 E(a,s)=\sum_{q\in s}|a_q|
           \sum_{d\mid q}|\mu(q/d)|\,d.
\]
It permits changing coefficients, supports, and conductors. Its convergence
theorem still assumes
\[
 \frac{E(A_N)E(B_N)}{N+1}\longrightarrow0.
\]
That assumption must be proved for the chosen family, or replaced by a
sharper estimate preserving signed cancellation. This tail estimate by itself
does not construct approximants to 1.

## 5. Formalization gaps versus open mathematical inputs

| Route | Already available | What is still needed |
|---|---|---|
| Optimal Pareto projections | Strong convergence to P_V 1; exact full error split; fixed coefficient convergence | Prove r=0, for example via (A) or (B) |
| Inverse Gram / CRT | Exact corrections, dual pairings, entry limits, weighted CRT transfer | Control the full growing signed correction sum |
| Noor tail regularity | Shifted density and the regular-annihilator theorem are proved; TailRegular r implies RH | Prove actual residual regularity |
| Mellin-window limit | ZeroModeWindowProvider plus WindowTest imply RH | Supply profile convergence and positive window mass, then prove the actual WindowTest |
| RH equivalence for Mellin windows | Conditional forward-and-reverse assembly | The RH-to-density converse is an additional formalization input to that equivalence, not needed for the direct Pareto-to-RH route |
| Burnol product | product = 1 iff RH | Prove the product is exactly 1; positivity and convergence alone do not do so |

Noor's published Theorem 9 proves density after applying I-S in the Hardy
model. Theorem 12 gives trivial intersection of the orthogonal complement
with the local Dirichlet space. These are now formalized in the project's
actual real coefficient coordinates: `Noor.shiftedResidue_density` and
`eq_zero_of_orthogonal_tailRegular`. The proof includes the exact factor
relating the normalized residues to the logarithmic generators.
Putting the actual limiting residual in that regularity class remains open.

Reference for those mathematical statements and the strategy:
S. Waleed Noor, *A Hardy space analysis of the Báez-Duarte criterion for the RH*,
Advances in Mathematics 350 (2019), 242–255, Theorems 9 and 12:
https://arxiv.org/html/1809.09577v4.

The original audit's minimal-hypothesis check reported both hdense and hreg
as load-bearing in the then-conditional proof. The completed proof supplies
hdense internally, so `riemannHypothesis_of_tailRegular` now requires only
hreg. The earlier deletion test was a check of that proof, not a claim that
shifted density was mathematically unprovable.

Finishing the known Burnol/BSY identities would remove formalization gaps in
another route. Those identities would still need a zero-defect conclusion.
The checked product_eq_one_iff_rh makes that exact endpoint explicit.

## 6. Recommended next work

Prioritize the joint construction-and-energy problem (B): legal interpolation
on a growing initial segment together with a finite cofinal bound on its
complete Pareto energy. Retain the signed CRT correction and all mixed terms.
Use the existing finite Gram/Green machinery to identify the cost of enforcing
the head conditions, then prove a bound uniform in the chosen cutoffs.

Alternatively prove the actual-residual bound (A) directly. Lean can already
assemble either provider into Mathlib's actual RiemannHypothesis.

Noor's regularity theorem has now been completed in the real Pareto model.
This removes the named shifted-density formalization gap. The actual residual
regularity hypothesis remains an independent requirement for an RH proof.

## 7. Verification record

Workspace: ws_ttr8e82ElG_i7gHkd9vUCPdKEx_SQbpx.

First isolated audit:
- Job: job_8XlPAQeIsD_49hdsDqMDBv_1dA075fC4.
- Result: succeeded, verified=true, exit code 0, elapsed 7.108 seconds.
- Checked the bounded-tail/residual equivalence, its equivalence with all
  inverse-Gram correction limits, and its implication to RH.
- Inspected coefficient and projection convergence, the PNT provider,
  the tail dichotomy, exhaustion, tail regularity, and Mellin-window types.

Second isolated audit:
- Job: job_vET_v5TPhCOY3GwzYMVsC6vE9g_-xFo-.
- Result: succeeded, verified=true, exit code 0, elapsed 5.596 seconds.
- Checked the explicit cofinal-tail-budget theorem above.
- Inspected the exact-head-energy implication, the CRT packet envelope
  hypothesis, the nonzero residue-one defect limit, and the Burnol equivalence.

Every requested axiom query returned only:
propext, Classical.choice, Quot.sound.
No sorryAx or project-specific axiom occurred in those queried dependencies.

The permanent change is the named equivalence in
RH/ParetoResidualTailDichotomy.lean, together with its theorem-catalog entry
and this audit. The audit snippets are not permanent duplicate APIs.
Publication is through the change-aware project checkpoint, which validates
the changed Lean module and its local reverse dependencies.
No open research hypothesis is marked discharged.
