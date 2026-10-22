# Green--Pareto--Schur: explicit finite head repair
7 October 2026 (UTC). Starting published commit:
d8945bd32bc58449d5346d26865f30116dd53379.

## Scope
The spectral geometric consumers are already complete at the starting
commit. The finite repair formalization is addressed here. The
unconditional arithmetic tightness/strict-moment estimate and the
RH-to-density converse remain Open.

## Exact boundary relocation
For 1<=k<=H put L=floor(H/k), m_L=sum_{q<=L} mu(q)/q and p=k(L+1)>H.
In physical coordinates define
B_{H,k}=-sum_{q<=L} mu(q) g_{kq}+((H+1)/k)m_L g_{H+1}.
The zero atom g_1 is harmless and may be removed. The retained exact equality is

B_{H,k}=(1/k) D_k U_L-(p/k)m_L g_p+((H+1)/k)m_L g_{H+1},

where D_k f(j)=k f(floor(j/k)) and U_L is the complete canonical
Mobius vector. Every original legal conductor through H+1 is retained.
The temporary conductor p occurs only in this equality and cancels;
the resulting legal vector has no conductor beyond H+1.

The boundary corrections have identical linear heads. Consequently
B_{H,k}(j)=1 if k<=j and 0 otherwise for every 0<=j<=H.
For y_0=0, the full signed interpolation is
T_H y=sum_{k=1}^H (y_k-y_{k-1}) B_{H,k}.
It has exactly the prescribed head.

Regrouping the finite divisor sum gives the original manuscript coefficients
c_d=-sum_{k|d} mu(d/k) (y_k-y_{k-1}) for 2<=d<=H and
c_{H+1}=(H+1) sum_{k=1}^H ((y_k-y_{k-1})/k) m_floor(H/k).
This regrouped display is explanatory; the Lean construction uses the
exact finite step representation and proves its interpolation directly.

## Concrete complete norm
The existing unconditional complete canonical bound ||U_L||^2<4L,
the exact dilation norm ||D_k f||^2=k||f||^2, |m_L|<=1 and
||g_d||^2<=2/d give a bound 2 sqrt(H)/k for each of the three retained
terms. Thus ||B_{H,k}||<=6 sqrt(H)/k.
The already formalized difference-energy identity, with its site-square
remainders and terminal term, yields
sum_{k<=H} |Delta y_k|/k<=2 sqrt(H) ||Q_H y||.
Therefore
||T_H y||<=12H ||Q_H y||.
This improves the manuscript's coarser cap 12H+4 and controls the
entire infinite physical tail.

## Actual constrained energy
The dictionary at stage M is g_2,...,g_{M+1}. For H<=M let r_M be
the actual inverse-Gram projection residual and e_HM=||Q_H r_M||.
The explicit repaired competitor satisfies the full exact equality
||x-f||^2=||r_M||^2+||T_H r_M||^2.
For the complete exact-head error infimum E_HM, the comparison is
||r_M||^2+e_HM^2<=E_HM<=||r_M||^2+144H^2 e_HM^2
and E_HM<=(1+144H^2)||r_M||^2.
No finite tail truncation or sign deletion enters these statements.

## Arithmetic audit and literature
The desired strict normalized actual moment upper bound is not supplied
by these finite estimates. The scalar model with weight delta at eigenvalue
n has T_n->delta and S_n->0 while its escaped mass stays delta; with
sigma_n=S_n+1/(n+1), its normalized double-log moment tends to delta.
Thus geometric tail decay alone cannot give a coefficient theta<1.

Primary sources inspected:
- Luis Baez-Duarte, A strengthening of the Nyman--Beurling criterion for the
  Riemann hypothesis, 2, https://arxiv.org/abs/math/0205003.
  The RH-to-natural-density direction and its damped approximants are
  classical. The centered/Pareto transfer is already proved in
  BaezDuarteCenteredBridge by centeredError_eq_hilbert_norm_sq and
  centeredApproximation_iff_one_mem. The missing checked analytic provider
  is RH -> CenteredApproximation.
- Bettin--Conrey--Farmer, An optimal choice of Dirichlet polynomials for the
  Nyman--Beurling criterion, https://arxiv.org/abs/1211.5191.
  Its sharp approximation asymptotic assumes RH and a reciprocal
  zeta-derivative moment bound. It does not discharge the unconditional
  actual-source budget here.

Wolfram checked every step head for H<=20, every test interpolation head
for H<=20, and the three elementary square-budget implications, with zero
mismatches and True results. It also computed the escape model limit delta.
These computations support proof development, not an RH estimate.

## Next exact task
Prove actual complete-source tightness or the strict cofinal normalized
double-log budget already consumed by
riemannHypothesis_of_actual_compactSpectrum_cofinal_canonical_feedback.
For the converse, formalize RH -> BaezDuarte.CenteredApproximation using
published damped approximants (and raw-to-centered transfer if needed).
Reuse the existing exact centered/Pareto norm and closure equivalence. Do not infer either from
the finite repair bound or unconditional PNT cancellation.

## Verification
The explicit interpolation core passed job_kZ4x28aX9e8blrxBMecZmxJ5PoZissZK,
exit 0. The final coherent source, including both new modules and eight
decisive axiom audits, passed job_eRstL1q5iYehMc1y7SI58BQjMgtWikU4,
exit 0. Every audited declaration depends only on propext,
Classical.choice and Quot.sound. The final source has no compiler warnings.
No sorry, admit, project-local axiom, unsafe declaration or blanket
import Mathlib is added.

One final pushed repository checkpoint validates the individual modules
and their affected reverse dependents. Its terminal publication result
is reported with the delivered commit; an accepted queued job alone
is never treated as verification or publication.

## Suggested next GitHub prompt
Continue RiemannResearch from its latest published main, using Web and
Wolfram and pushing the verified work when done. The finite Mobius repair
gap is now closed with the complete norm cap 12H and the concrete
exact-head energy comparison. Do not leave that cap as an assumption.
The remaining arithmetic target is the literal actual-source tightness
provider, or the strict cofinal normalized double-log moment budget
consumed by riemannHypothesis_of_actual_compactSpectrum_cofinal_canonical_feedback.
Keep the canonical sigma_n=S_n+1/(n+1), theta<1, all conductors, the full
source measure and both correction squares. For the classical converse,
formalize RH -> BaezDuarte.CenteredApproximation; reuse the already
checked centered/Pareto norm and closure transfer. Identify substantive
analytic hypotheses and any unresolved provider explicitly. Do not
replace either obligation with another conditional consumer or claim RH
from finite norm bounds, PNT cancellation or the geometric limits.
