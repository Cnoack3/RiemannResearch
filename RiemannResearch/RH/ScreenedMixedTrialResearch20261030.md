# Screened full-squarefree mixed trials and the remaining dyadic RH obligation

Prepared 30 October 2026. Continuation of commit
98853d729685c0bfc5e786e15d532c1dc9332bd4 and the attached
RH_Full_Squarefree_Dyadic_Research_Agenda_2026-10-30(1).md.

## 1. Result and status

This continuation completes the proposed next-head screening transport and
constructs an explicit two-direction trial using the **actual unrestricted
full-squarefree optimizer**. It proves strict positivity of its exact
two-dimensional determinant, with no regularizer and no additional spectral
hypothesis. The resulting gain is always at least the previous head-refined
raw self-dilation gain at every eligible prime stage.

**RH is not proved.** No uniform signed dyadic arithmetic estimate is supplied.
The normalized signed-excess implication to RH is now formalized, and the
explicit global mixed trial family can be substituted into it.

The new formal statements are in:

- [QCRTScreenedFloorTrial.lean](QCRTScreenedFloorTrial.lean).
- [TwoDirectionTrial.lean](../Analysis/TwoDirectionTrial.lean).
- [QCRTMixedFloorTrial.lean](QCRTMixedFloorTrial.lean).
- [QCRTDyadicBudget.lean](QCRTDyadicBudget.lean), extended by the normalized criterion.

## 2. Actual spaces and optimizers

For n>=1, Q(n)=1/(zeta(2)n^2), and g_d(n)=(n mod d)/d. All norms and
inner products below are the complete infinite Q norm. The auxiliary sequence
coordinate at zero is zero.

Let L_i=primorial(2i+2), indexed by numerical cutoff, and
U_i=span{g_d:1<d divides L_i}. Every divisor, including composite squarefree
conductors, remains available. The actual optimizer is

\[
F_i=\arg\min\{\|f\|_Q^2:f\in U_i,\ f(n)=1\ (1\le n\le i+1)\},
\quad E_i=\|F_i\|_Q^2.
\]

The old-dictionary next-head minimum and its cost are

\[
\widehat F_i=\arg\min\{\|f\|_Q^2:f\in U_i,\ f(n)=1\ (1\le n\le i+2)\},
\quad C_i^{\rm old}=\|\widehat F_i\|_Q^2-E_i.
\]

The new-dictionary old-head minimum is Z_i, and the period gain is
P_i=||F_i-Z_i||_Q^2. These three minima must remain distinct.

Define T_i^+={u in U_i:u=0 on [1,i+2]}. An eligible prime stage in the
new adjusted-family application means i>0, i+2 squarefree, and p=2i+3 prime.
The global certificate below also accounts for every other stage.

## 3. Screening is now transported into the actual certificate

Write S_i^+=I-P_{T_i^+}. For arbitrary vectors x,y,

\[
\langle\widehat F_i,S_i^+x\rangle=\langle\widehat F_i,x\rangle,\qquad
\|S_i^+x\|^2=\|x\|^2-\|P_{T_i^+}x\|^2,
\]

\[
\langle S_i^+x,S_i^+y\rangle
=\langle x,y\rangle-\langle P_{T_i^+}x,P_{T_i^+}y\rangle.
\]

Screening preserves a zero next head and legality in the enlarged dictionary.
For a raw added column w_e=g_e-(L_i/e)g_{L_i}, the existing adjusted column y_e
is exactly S_i^+w_e. The proof identifies its old-tangent difference and its
orthogonality to T_i^+, rather than assuming that two differently screened
families coincide.

Consequently, for X(t)=sum_e t_e w_e,

\[
\mathcal C_i(t)=C_i^{\rm old}
 -2\langle\widehat F_i,X(t)\rangle+\|X(t)\|^2
 -\|P_{T_i^+}X(t)\|^2.
\]

This is the previously missing transport into the **same** adjusted
full-family trial certificate used by the dyadic RH consumer. The removed
projection energy is exact. The old repair is also identified:

\[
\widehat F_i=F_i+(a_i/K_i)k_i,\qquad
C_i^{\rm old}=a_i^2/K_i.
\]

Here a_i=1-F_i(i+2), k_i is the old evaluation normal, and K_i=||k_i||^2.
Positivity at eligible sites is supplied by the existing arithmetic theorem.

Principal declarations: screen_source, screen_energy, screen_gram,
screenedTrial_completion, jointFamily_eq_screen, headFirst_eq_repair,
trialCertificate_physical, jointSynthesis_eq_screen,
trialCertificate_screen_transport.

## 4. Explicit mixed direction and exact determinant

Let D_p f(n)=f(floor(n/p)) and put

\[
h_i=S_i^+D_pF_i,\qquad
q_i=S_i^+\left(g_p-\frac{L_i}{p}g_{L_i}\right).
\]

The second vector is the d=1 adjusted column and must not be omitted.
Set

\[
A=\|h_i\|^2,\ B=\langle h_i,q_i\rangle,\ C=\|q_i\|^2,\quad
u=\langle\widehat F_i,h_i\rangle,\ v=\langle\widehat F_i,q_i\rangle,
\quad \Delta=AC-B^2.
\]

Lean proves **Delta>0 for the actual optimizer** at every eligible prime stage.
Indeed, if h_i were a multiple of q_i, independence of the complete adjusted
family would force every coefficient of F_i at conductors d>1 to vanish.
Since g_1=0, this would give F_i=0, contradicting its first head value.
This is finite strict positivity, not a uniform lower bound on Delta.

Choose the two scalar coefficients explicitly:

\[
\alpha=\frac{Cu-Bv}{\Delta},\qquad
\beta=\frac{Av-Bu}{\Delta},\qquad
G_i^{(2)}=\frac{Cu^2-2Buv+Av^2}{\Delta}.
\]

For any full divisor representation F_i=sum_{d|L_i} b_d g_d, define
lambda=sum_{d|L_i} b_d/d and

\[
t_{pd}=\alpha b_d+\mathbf1_{d=1}(\beta-\alpha\lambda).
\]

This convention is valid even if b_1 is not zero. Existence of a full
representation is proved; actualCoefficients selects one, and actualTrials
uses it. There is no unproved coefficient-representation hypothesis in the
global definition. The raw synthesis is alpha D_pF_i+beta w_p, and the
adjusted synthesis is alpha h_i+beta q_i.

No inverse of the entire new-block Gram matrix is used to choose these
coefficients. This is exact optimization over the explicit two-dimensional
subspace, not a formula restating the full new optimum.

Principal declarations: exists_oldVector, floorCoefficients_raw,
mixedCoefficients_raw, mixedSynthesis, selfFloor_not_prime_multiple,
exact_determinant_pos, actualCoefficients_spec.

## 5. Exact improvement and all remainders

The checked transition is

\[
\boxed{E_{i+1}-E_i=C_i^{\rm old}-G_i^{(2)}-\mathcal L_i(t),\quad
\mathcal L_i(t)\ge0.}
\]

The Lean loss is literally the squared norm of the difference between the
full joint-family minimum vector and the chosen joint-family synthesis,
as in dense_trial_completion. It must not be dropped from an equality.

The two-direction scalar identities give

\[
G_i^{(2)}-\frac{u^2}{A}
=\frac{(Av-Bu)^2}{A\Delta},\qquad
G_i^{(2)}-\frac{v^2}{C}
=\frac{(Cu-Bv)^2}{C\Delta}.
\]

Moreover, with A_0=E_i/p-D_{p,i+1}, the existing head-tail identity and
the new screening identity combine to give

\[
A=A_0-R_{p,i+1}(F_i)-\|P_{T_i^+}D_pF_i\|^2.
\]

Both subtracted terms are nonnegative, and source preservation gives
u=<Fhat_i,D_pF_i>. Therefore

\[
\boxed{G_i^{(2)}\ge u^2/A\ge u^2/A_0.}
\]

The last comparison is specialized and checked as exact_mixedGain_ge_raw.
It is a finite gain improvement; it supplies no lower estimate for u or v.

For numerical robustness the module also permits any upper diagonal
bar A>=A. The exact identity includes the extra nonnegative loss
(bar A-A)alpha^2. Taking bar A=A_0+tau, tau>0, ensures a positive determinant
without any additional assumption and retains the tail, screening and
regularization losses. Its comparison is with u^2/(A_0+tau), not automatically
with u^2/A_0. The exact determinant theorem removes this qualification for
the unregularized two-direction trial.

Principal declarations: mixed_certificate, mixed_step_completion,
selfFloor_energy, mixed_determinant_pos, screened_determinant_pos,
exact_mixedGain_ge_raw, exact_mixed_step.

## 6. The new concrete all-stage target

The global definition actualTrials is assembled in QCRTMixedFloorTrial.
Its fullCertificate is checked to be

\[
\mathcal C_i^{(2)}=
\begin{cases}
 E_1-E_0,&i=0,\\
 C_i^{\rm old}-G_i^{(2)},&i>0,\ i+2\text{ squarefree},\ 2i+3\text{ prime},\\
 C_i^{\rm old},&i>0,\ i+2\text{ squarefree},\ 2i+3\text{ not prime},\\
 -P_i,&i>0,\ i+2\text{ not squarefree}.
\end{cases}
\]

The declaration is actualCertificate_formula. In particular, the positive
head costs at nonprime transitions have not disappeared.

For a fixed B_0>=0, define

\[
R_m^{(2)}=
\frac{\max\{\,\sum_{i=2^m}^{2^{m+1}-1}\mathcal C_i^{(2)}-B_0,\ 0\,\}}
 {1+E_{2^m}}.
\]

The positive part is taken **after** the full signed sum. Lean now verifies

\[
\boxed{R_m^{(2)}\longrightarrow0\quad\Longrightarrow\quad\mathrm{RH}.}
\]

Use riemannHypothesis_of_normalized_dyadic_excess with
t=QCRTMixedFloorTrial.actualTrials. This remains a **conditional research
reduction**. Its sole substantive arithmetic provider is the displayed
limit. The proof converts it into the existing vanishing-overhead budget,
with additive allowance B_0+1.

**Open:** prove this limit for the actual full-squarefree optimizers, or
construct a still better full-family trial with a proved limit.

## 7. Computational evidence and its limits

[ScreenedMixedDiagnostics20261030.md](ScreenedMixedDiagnostics20261030.md)
contains the complete-period floating-point source and output. Every divisor
is retained; trigamma weights include the infinite physical tail. An
independent rerun reproduced all seven stage records exactly in the present
environment. Conditioning reaches about 4.18 million; these are not interval
bounds.

| New prime | Full gain | Previous refined raw gain | Screened scalar gain | Exact two-direction gain |
|---:|---:|---:|---:|---:|
| 5 | 0.18526149 | 0.11293752 | 0.11424775 | 0.16438892 |
| 7 | 0.01113813 | 0.00243661 | 0.00579652 | 0.00859504 |
| 11 | 0.00594893 | 0.00074433 | 0.00373771 | 0.00528497 |
| 13 | 0.00296443 | 0.00028749 | 0.00223354 | 0.00278434 |
| 17 | 0.00356932 | 0.00039879 | 0.00315967 | 0.00324375 |

The prime-7 and prime-17 rows are physical screening diagnostics at
nonsquarefree observation sites. The global formal certificate uses exact
negative period gains there. Its block totals therefore differ from sums
of the physical two-direction competitor bounds:

| Block | Actual increment | Previous raw bounds summed at all stages | New physical mixed bounds summed | New global adjusted certificate |
|---|---:|---:|---:|---:|
| [1,2) | 0.06698819 | 0.13931216 | 0.08786075 | 0.08786075 |
| [2,4) | 0.00674362 | 0.01544513 | 0.00928671 | 0.00674362 |
| [4,8) | 0.04182785 | 0.05287993 | 0.04299746 | 0.04267189 |

The corresponding old global adjusted totals are 0.13931216, 0.00674362,
and 0.04970939. Use matching certificate conventions when comparing methods.

A separate
[exact-rational calculation](CertifiedSmallEnergyDiagnostics20261030.md)
certifies

\[
0.06698818<E_2-E_1<0.06698820,\qquad
G_{\rm full}(p=5)<\tfrac34 C_1^{\rm old}.
\]

It uses rational lower/upper period weights, integral-test tail bounds,
positive rational elimination pivots, and exact constrained minima.
Its rational threshold assertions were independently rerun successfully.
This certificate is **not Lean-verified**. The printed longer decimal
endpoints are displays; the two coarse decimal thresholds above are exact
rational comparisons. It rules out a blanket every-stage 3/4 cost-capture
claim. It says nothing against an eventual signed dyadic estimate.

## 8. Why geometry alone cannot close the budget (paper-level)

For comparison only, replace the arithmetic space by
V_0={f:E_Q[f]=0}. Let U_i^0 consist of its vectors constant after 2i+2.
These are nested finite-dimensional spaces exhausting V_0.

For q_H=sum_{n<=H}Q(n), the actual head-H optimizer in V_0 equals one on
the head and -q_H/(1-q_H) on the tail. Weighted Cauchy-Schwarz proves

\[
E_H^0=q_H/(1-q_H)\sim\zeta(2)H.
\]

It belongs to U_i^0 when H=i+1, and the next-head optimizer belongs to
the old dictionary as well. Every enlargement gain is zero because these
are already the global V_0 minima. Consequently normalized dyadic excess
tends to one, not zero, for every fixed additive allowance.

This is an abstract-model obstruction, not a counterexample to the squarefree
dictionary. It explains why a proof must use its arithmetic beyond generic
projection identities. This comparison has not been formalized in this
continuation.

## 9. Next research agenda

1. **Estimate the actual signed block.** Work with actualCertificate_formula,
   retaining all nonprime head costs and all negative period gains. Seek
   R_m^(2)->0 for some fixed B_0. No per-prime domination is required.
2. **Use the actual sources.** Expand u_i=<Fhat_i,D_pF_i> and the
   compensated-prime source v_i in complete divisor coordinates. Use the
   forced low coefficients and the actual moving normal equations to find
   cross-stage cancellation. A bound on a positive Gram matrix alone is
   insufficient.
3. **Capture the remaining full-family loss.** Add structured divisor-layer
   directions to h_i,q_i, using exact screening and mixed Gram terms.
   The small calculations show appreciable residual gain at prime 5 and
   much smaller gaps at primes 11 and 13; they give no asymptotic pattern.
4. **Certify larger diagnostic stages.** Extend the rational/interval
   approach to the determinant, sources and gain at primes 11 and 13.
   Use certified feasible/dual estimates to avoid relying on floating
   inverse-Gram solves.
5. **Apply the RH consumer only after its provider is proved.**
   A successful axiom audit does not discharge the normalized-excess limit.

Do not restart the now-completed screening transport, full coefficient
indexing, or exact determinant proof as open work.

## 10. Verification and continuation

Retained workspace token:
ws_TwRqvO23-6zktAShLltSEtGhXbW-qxTY.

Absolute server root:
/home/cri_2025/lean-agent-workspaces/ws_TwRqvO23-6zktAShLltSEtGhXbW-qxTY/RiemannResearch.

The complete candidate, including exact determinant, gain domination, global
formula and normalized RH criterion, passed job_DiQ3HsQPTmR_XPaGCwTE9YfIvQsca8ou
(exit 0; server verification duration 8.788 seconds).
Selected axiom audits reported only propext, Classical.choice, and Quot.sound.

Saved mixed source and its new dependencies passed
job_PZEhdEBtvwnDEZzKOFYa5d5d8H834sYQ (exit 0; 17.276 seconds).
Saved normalized dyadic source passed
job_KHvtvCpXyUFCLc9XOsXXK9avJIb5PtIg (exit 0; 5.615 seconds).

These are development checks. Final publication is gated by the single
checkpoint covering the aggregate project and changed modules; use the
terminal checkpoint result and commit reported with delivery as its record.
Do not confuse tool request/queue/polling time with the server durations above.

## 11. Literature and algebra checks

- O'Leary and Rust, *Variable Projection for Nonlinear Least Squares Problems*:
  [NIST record](https://www.nist.gov/publications/variable-projection-nonlinear-least-squares-problems),
  [author manuscript](https://www.cs.umd.edu/~oleary/software/varpro.pdf).
  Supports orthogonal elimination as a standard method, not an RH source bound.
- Balazard and de Roton, *Sur un critere de Baez-Duarte pour l'hypothese de Riemann*:
  [arXiv:0812.1689](https://arxiv.org/abs/0812.1689).
  Its improved quantitative distance estimate assumes RH. It cannot be used
  as an unconditional provider here; no continuous-to-discrete transfer was assumed.
- Wolfram independently reduced the two-direction completion and both scalar
  excess identities to zero. Lean supplies the formal verification.
