# Constructive approximants: agenda audit and new verified results

Date: 24 October 2026. Source: the user-provided constructive-approximants research handoff, Sections 5–10, and the request to finish its remaining agenda.

The constructive reductions, complete-tail certificate machinery, larger finite experiments, and an actual-Landau sampling schedule have now been developed. The requested uniform arithmetic repair bound has **not** been proved. A direct subpolynomial repair criterion is proved, but its arithmetic growth premise remains **Open**. The actual zero-density provider and extraction of a numerical Landau constant also remain **Open**. Consequently this is a conditional research reduction, not a proof of RH and not a claim that every research objective is complete.

## Agenda status

| Original priority | Result | Remaining obligation |
|---|---|---|
| 1. Identify and bound physical head repair | Existing rank-free normal equations and exact cost identity reused; new actual Mellin lower bound isolates the signed normal repair cost | **Open:** a uniform bound, or the weaker subpolynomial growth bound, for a specified cofinal arithmetic family |
| 2. Connect sampling to head repair | Earlier sampled-repair contraction and exact additive decomposition retained; new obstruction concerns the actual arithmetic target, not an assumed detector | **Open:** sampling estimates alone do not supply the unsampled normal-cost bound |
| 3. Certified finite experiments | Larger squarefree dictionaries and ten heads through 32; exact primal/dual intervals isolate projection defect, minimum interpolant norm, constrained residual minimum, and repair cost; complete mixed tails and conditioning/majorant diagnostics retained | Finite certificates do not establish an infinite-family estimate; individual numbers are independently verified Python rationals, not kernel certificates |
| 4. Constructive reductions | Online Q convergence and a finite tolerance rule now follow from physical heads, amplitudes and a complete P-energy bound; exponential height recurrence and actual sampling bound formalized | **Open:** the explicitly displayed full-energy or repair-growth premise |
| 5. Effective analytic certification | Existing unconditional actual Landau theorem supplies a coarser conductor weight; published density constants audited; strict-tail-to-energy numerical reduction checked | **Open:** formal actual-density provider, numerical Landau constant, and numerical evaluation with certified complete zero counts if such samples are requested |

## Actual normal cost and the weaker arithmetic target

In the complete Q Hilbert space let p be the legal projection of 1, let delta be its squared residual, and let u_i be the projected physical-head observation vectors. The mismatch is b_i=inner(h_i,1-p). A feasible normal solution d satisfies

\[
\langle u_i,\sum_jd_ju_j\rangle=b_i,
\qquad R_M=\sum_i d_i b_i=\|\sum_i d_i u_i\|_Q^2\ge0.
\]

The already established exact identity is

\[
\|1-(p+\sum_i d_i u_i)\|_Q^2=\delta+R_M.
\]

Rows may be dependent. No inverse of the full squarefree head matrix is assumed. Constant heads satisfy its known row relations.

The new module `QNormalRepairMellinObstruction.lean` proves that an actual zero s with sigma=Re(s)>1/2 and s!=1 forces

\[
\frac{2\sigma-1}{|s|^2}(M+1)^{2\sigma-1}
+\operatorname{metricCorrection}(1-F_M)
\le\zeta(2)(\delta+R_M).
\]

The full positive Q/P correction is retained. Since delta<=1,

\[
R_M\ge\frac{2\sigma-1}{\zeta(2)|s|^2}(M+1)^{2\sigma-1}-1.
\]

`directional_budget_power_lower` applies the same lower bound directly to any nonnegative B satisfying

\[
|\sum_i c_i b_i|^2\le B\|\sum_i c_i u_i\|_Q^2
\quad\text{for all }c.
\]

Rank-free duality supplies feasibility itself. These statements are conditional on an off-line zero; they assert neither existence of such a zero nor failure of a bounded repair family.

`QNormalRepairSubpolynomial.lean` proves the direct implication

\[
M_j\longrightarrow\infty,\qquad
\frac{\log(1+R_{M_j})}{\log(M_j+1)}\longrightarrow0
\quad\Longrightarrow\quad\mathrm{RH},
\]

for actual independent positive-conductor dictionaries, with feasible normal equations. Dictionary size can vary with j. The alternate declaration `riemannHypothesis_of_subpolynomial_directional_budgets` uses nonnegative budgets B_j in the displayed directional inequality and the analogous logarithmic limit; separate normal witnesses are unnecessary. The proofs use the actual Mellin transform and the existing positive-power obstruction, not an unproved zero-detection assumption.

This is a weaker sufficient arithmetic target than uniform boundedness. Neither growth premise has been established for the proposed family. There is no claim of an RH-to-squarefree-closure converse.

## Online complete-Q convergence

`QOnlineExactHeadConvergence.lean` assembles the executable selector from the previous continuation with complete-P tail pairings and the exact metric comparison. Suppose legal F_N have exact physical heads through N, certified integer amplitude bounds U_N, and

\[
\|1-F_N\|_P^2\le C^2\quad\text{for all }N,\qquad C\ge0.
\]

For the selected block average A_m, with first selected head N_m,

\[
\|1-A_m\|_Q^2\le
\frac{1+1/(N_m+1)}{\zeta(2)}
\left(\frac{C^2}{m}+\frac{2C\,2^{-m}}{m^2}\right).
\]

No pairwise Q-inner-product hypothesis is required. `online_block_tendsto` proves strong convergence to the actual qOne, and `online_legal_blocks` packages legality and the preserved first head. For epsilon>0, the checked stopping rule

\[
m>\frac{2(C^2+2C)}{\zeta(2)\epsilon^2}
\]

gives norm error less than epsilon. The selector does not need a numerical C; certifying this particular stopping threshold does.

## Complete finite certificates

`Analysis/ConstrainedGramCertificates.lean` retains the exact constrained square completion for a symmetric lower Gram form L:

\[
\|x-\Phi a\|^2=
\bigl(\|x\|^2+2\lambda(b)-L(z,z)\bigr)
+L(a-z,a-z)+\bigl(\|\Phi a\|^2-L(a,a)\bigr),
\]

where Ca=b and L(z,v)=inner(x,Phi(v))+lambda(Cv). Positivity of L and L<=the true complete Gram give a rigorous lower certificate. The remainder containing every Gram discrepancy is not discarded from the equality.

The extension of `FiniteSignedQuadratic.lean` propagates coordinate source intervals through the full signed quadratic expansion, bounding both the linear source error and its quadratic remainder. This supports rational enclosures of log(d)/d.

`ParetoPeriodicAbelTail.lean` proves exact complete mass, the signed centered identity, period-mean invariance under shifts, and

\[
\left|\sum_{n>N}\frac{f(n)}{n(n+1)}-\frac{\mu}{N+1}\right|
\le\frac{Lb}{(N+1)(N+2)}
\]

for a nonnegative period-L function bounded by b. Signed finite assembly retains the combined mean before estimating its remainder. It avoids enumerating the enormous period of an entire dictionary.

See `ExpandedRepairCostCertificates20261024.md` for the full table and independent reproduction. For squarefree conductors up to 60, there are 36 atoms; the head of length 32 has exact rank 20. Its complete-P target repair cost is certified in

\[
0.013405670\le R_{32}^{P}\le0.013432008.
\]

The same cases now include separate certified minimum interpolant norms. For the 15-atom dictionary and head 16 the minimum norm squared is at least 1.026568824; for 25 atoms and head 24 it is at least 1.010671591. These rule out a norm-at-most-one candidate only in those specified finite dictionaries, not a larger uniform bound or a growing family. For 36 atoms and head 32 the minimum norm squared lies in [0.999688976, 0.999703127]. The crude absolute-coefficient tail bound is approximately 264.89 times the signed periodic-Abel tail bound for that residual candidate. Unverified numerical condition estimates are explicitly separated from the exact rational LDL positivity certificates.

These experiments use the P projection and P Gram. The Q cost in the Mellin theorem is a different metric-dependent optimization; the two numerical costs are not identified. Whole-function norm comparison remains valid.

## Actual sampling schedule and remaining analytic inputs

`Analysis/ExplicitSamplingHeights.lean` defines M_0=0 and

\[
M_j=M_{j-1}+16+jw_j,\qquad T_j=\exp(M_j).
\]

The integers w_j are certified upper bounds for finite inverse-Gram weight norms. The recurrence and heights are strictly increasing. The generic scalar schedule and finite tolerance are checked.

`RH/ActualSamplingHeights.lean` uses the repository's unconditional actual rational Landau bound to supply a uniform positive constant C and the conductor weight

\[
W_L(q)=2\pi\sqrt q\,(q^{5/2}+q^{3/2}+q).
\]

Let R_L and R_H be the complete absolute-entry inverse-Gram weight norms, using W_L and 4pi(sqrt(q)-1)^2. For actual zero samples, including their analytic multiplicities,

\[
\|z(T)-\ell\|_{H^{-1}}\le
R_H E(T)/T+C R_L(1+\log^2(T+3))/T.
\]

If w_j>=max(R_H,R_L) and E(T_j)/T_j<=D/M_j, then

\[
\|z(T_j)-\ell\|_{H^{-1}}\le(D+5C)/j.
\]

Thus the Landau contribution has a checked actual provider; the horizontal-energy hypothesis is still explicit. The larger conductor weight changes the handoff's weight certificate and constants; it must not be substituted into the handoff's sharper weight formula without adjustment.

`horizontalEnergy_ratio_of_simonic_tail_at_exp` checks the numerical consequence D=12,288,000 from a precisely stated strict-tail hypothesis with constants 24000 and 1/8. The source paper's theorem has not itself been formalized. The literature range, strict versus inclusive counting convention, numerical thresholds, and existential Landau constant are audited in `EffectiveSamplingAnalyticAudit20261024.md`.

No zero list was evaluated. Therefore this work does not claim a numerical completeness or multiplicity certificate for a sampled vector. The formal sums already range over all actual zeros with their actual multiplicities; a future numerical implementation must certify that its input list matches them.

## Verification evidence and interpretation

The eight new or extended mathematical modules passed isolated project-module compilation in job `job_JWM417t1UrQ657cAbKipAYn2FnWkvSrP` (21.306 seconds reported by the server). The subsequent focused-import and axiom audit, job `job_BCKYpqAkQUapeg_U6TyMAzTahd8rbn5U`, succeeded in 12.207 server seconds. The principal declarations use only `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, or `admit` was introduced. Domain hypotheses remain visible in the theorem types and are not discharged by an axiom listing.

Final publication additionally requires the repository checkpoint to audit and compile the aggregate project and changed modules. Its terminal result and commit are the publication evidence. These server durations do not include all drafting, request round trips, or polling delays; the workspace was reused without a new opening request.

The finite computation and the formal theorem library provide different evidence. Both retain the complete tails and signed mixed terms. Neither proves the remaining arithmetic growth bound.
