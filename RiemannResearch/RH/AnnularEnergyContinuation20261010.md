# Actual annular energy, Mellin continuation, and RH

**Continuation — 10 October 2026.** The original record is historical: the
current repository had already discharged its lattice-decay obligation.
This continuation removes a different obstacle, the independent local Mellin
identity premise, and proves the sufficient energy-to-RH direction.

**RH is not proved.** The actual arithmetic energy estimate remains open.

## 1. Current baseline and exact signals

The inspected repository baseline is
`0a2796ac17454689cea43361b41c4d0f55c2bc30`, later than the attached record's
publication `2ef23fbffda5f687c3945cb6acbaf99ccf1bbacf`.
The intervening lattice continuation proves, for every positive real cutoff,

\[
\delta(x)=\frac{-B_3(\{x\})+7B_3(\{x/2\})-14B_3(\{x/4\})+8B_3(\{x/8\})}{3x^2},
\qquad |\delta(x)|\le\frac{10}{27x^2}.
\]

The coefficient is optimal. It also proves the exact energy transfer and
its bounded, convergent signed correction. Those are existing repository
results, not new claims of this continuation.

Retain

\[
A(x)=\sum_{n\ge1}\Lambda(n)W(n/x)-\frac7{64}x,
\qquad U(x)=\sum_{n\ge1}(\Lambda(n)-1)W(n/x),
\qquad A=U+\delta.
\]

Every prime power, fractional cutoff, singleton term, and lattice square
is retained. In particular,

\[
E_A(X)-E_U(X)=\int_{[1,X]}
\frac{2U(x)\delta(x)+\delta(x)^2}{x^2}\,dx,
\qquad |E_A(X)-E_U(X)|\le\frac{1105}{5832}.
\]

## 2. The new analytic bridge

Put

\[
M(s)=\frac{2(1-2^{-s})(1-2^{-s-1})(1-2^{-s-2})}{s(s+1)(s+2)},
\qquad
\mathcal E(s)=-M(s)\frac{\zeta'(s)}{\zeta(s)}-\frac{7/64}{s-1}.
\]

The multiplier is analytic and nonzero on \(\Re s>0\). The actual Mellin
identity is already proved on \(\Re s>1\):

\[
F(s):=\int_1^\infty A(x)x^{-s-1}\,dx=\mathcal E(s).
\]

For \(0\le a<1\), suppose the **actual infinite vector** belongs to
\(H_a=L^2((1,\infty),x^{-2a-1}dx)\). The existing weighted Mellin theorem
makes \(F\) analytic on \(\Re s>a\).

The domain \(D_a=\{s:\Re s>a,\ s\ne1\}\) is preconnected. A direct
proof uses four overlapping convex regions: its upper and lower parts,
\(\Re s>1\), and \(a<\Re s<1\). Both \(F\) and \(\mathcal E\) are
meromorphic on \(D_a\). Their equality on the initial half-plane propagates
as equality of meromorphic germs throughout \(D_a\).

This is the missing local bridge; it is proved by the meromorphic identity
principle, not supplied as a new arithmetic hypothesis. At a zeta zero
\(\rho\in D_a\), the expression has order exactly \(-1\), whereas the
analytic transform has nonnegative meromorphic order. These orders cannot
agree. Therefore the new theorem proves

\[
\boxed{A\in H_a\quad\Longrightarrow\quad
\zeta(\rho)\ne0\text{ whenever }\Re\rho>a,\ \rho\ne1,
\quad 0\le a<1.}
\]

The logarithmic derivative has a simple pole at a zero of **any positive
multiplicity**. No simplicity hypothesis is used. The point \(s=1\) is
explicitly removed from the continuation domain; its centering term is
retained throughout.

Taking a weight between \(1/2\) and any proposed right-hand zero gives

\[
\boxed{\bigl[\forall a>1/2,\ A\in H_a\bigr]\ \Longrightarrow\ \mathrm{RH}.}
\]

The same implication holds with \(U\), by the proved lattice-membership
equivalence. An off-line zero also gives the contrapositive obstruction
\(A\notin H_a\) for every \(0\le a<\Re\rho\), \(a<1\).

## 3. All-cutoff critical energy supplies the memberships

Define \(E_f(X)=\int_1^X|f(x)|^2x^{-2}\,dx\), for \(X\ge1\).
For a measurable function continuous on \([1,\infty)\), the new generic
Lean theorem proves

\[
\bigl[\forall X\ge2,\ E_f(X)\le C\log X,\ C\ge0\bigr]
\Longrightarrow
\int_1^\infty|f(x)|^2x^{-s-1}\,dx<\infty\quad(s>1).
\]

With \(g(x)=|f(x)|^2/x^2\), the proof keeps the finite
integration-by-parts equality

\[
\int_1^X g(x)x^{-\eta}\,dx
=E_g(X)X^{-\eta}+\eta\int_1^X E_g(x)x^{-\eta-1}\,dx,
\qquad E_g(X)=\int_1^Xg(x)\,dx.
\]

A power envelope \(E_g(X)\le DX^\varepsilon\), \(\varepsilon<\eta\),
bounds the complete finite integral by
\(D+\eta D/(\eta-\varepsilon)\). Uniform bounds for all finite intervals
then give integrability of the infinite tail. The logarithmic case uses
\(\varepsilon=\eta/2\) and an elementary logarithm-to-power estimate.
No sampled-cutoff or finite-truncation extrapolation is used.

Global continuity and measurability of the actual vector \(A\) are proved
separately: near every positive scale its arithmetic sum has a fixed finite
cutoff, and below 1 it equals the exact linear centering.
Setting \(s=2a>1\) now proves

\[
\boxed{\bigl[\exists C,\ \forall X\ge2,\ E_A(X)\le C\log X\bigr]
\Longrightarrow\mathrm{RH}.}
\]

By exact energy transfer, the same sufficient result holds for \(E_U\).
The old `ActualRHEnergyCriterion` is **not a hypothesis** in these new
implications.

## 4. The complete signed-residual target

The established arithmetic decomposition is \(Q_X=M_X+R_X\), with the
complete model and signed residual retained. The new assembled theorem is

\[
\boxed{\mathrm{ActualModelLogBound}\ \land\
\mathrm{ActualSignedResidualUpperBound}\ \Longrightarrow\mathrm{RH}.}
\]

Here the residual premise is the all-real-cutoff estimate
\(R_X\le C\log X\) for every \(X\ge2\). The actual model logarithmic
estimate remains an explicit arithmetic premise. The analytic RH-energy
provider has been removed from the sufficient direction.

This does **not** discharge the model premise, prove the residual estimate,
or establish the converse RH-to-logarithmic-energy direction. Consequently
the full `ActualRHEnergyCriterion` equivalence remains open in the repository.

## 5. A weaker paper target

The logarithmic bound is stronger than needed for the sufficient direction.
For a nonnegative critical-energy density, the following are equivalent:

\[
\forall a>1/2,\ A\in H_a
\quad\Longleftrightarrow\quad
\forall\varepsilon>0,\ E_A(X)=O_\varepsilon(X^\varepsilon).
\]

The forward implication follows directly from
\(E_A(X)\le X^{2a-1}\int_1^\infty A(x)^2x^{-2a-1}dx\).
For the reverse implication, use exponent \(\varepsilon<2a-1\) in the
complete integration-by-parts formula above. By local integrability, an
asymptotic Big-O bound can be enlarged over the bounded initial interval
before applying the all-cutoff prefix-power lemma. Thus subpower growth already
implies RH. The generic prefix-power integrability theorem and the
membership-to-RH direction are Lean proved; the fully specialized subpower
equivalence and energy-exponent corollary below are paper results here.

More generally, \(E_A(X)=O(X^q)\), \(q\ge0\), excludes every zero with
\(\Re\rho>(1+q)/2\). In particular an off-line zero \(\rho\),
\(\beta=\Re\rho>1/2\), forces

\[
\limsup_{X\to\infty}\frac{\log(1+E_A(X))}{\log X}\ge2\beta-1.
\]

This is an asymptotic exponent obstruction, not a lower bound at every
individual cutoff. Since the exact \(A/U\) energy difference is bounded,
the same obstruction applies to \(U\).

## 6. Formal declarations and remaining premises

| Module | New responsibility |
|---|---|
| `Analysis/LogarithmicPrefixMellin.lean` | Prefix-power and logarithmic-prefix weighted integrability |
| `Analysis/ActualAnnularContinuity.lean` | Global continuity and measurability of the actual prime vector |
| `RH/AnnularMellinContinuation.lean` | Meromorphic germ continuation, weighted zero exclusion, all-damping RH implication |
| `RH/AnnularEnergyRH.lean` | Actual prime/centered energy implications and signed-residual assembly |

The decisive declarations are
`zeta_ne_zero_of_actualAnnular_Ha`,
`riemannHypothesis_of_actualAnnular_all_damping`,
`actualAnnular_Ha_of_primeEnergyUpperBound`,
`riemannHypothesis_of_actualPrimeEnergyUpperBound`,
`riemannHypothesis_of_actualEnergyUpperBound`, and
`riemannHypothesis_of_actualSignedResidualUpperBound`.

These are conditional research reductions. Their substantive hypotheses are
the actual membership or actual energy bounds, and, for signed residuals,
the model estimate. The initial identity and analytic continuation are
proved dependencies. RH, zero simplicity, an explicit-formula provider,
and a local identity provider are absent from their hypotheses.

## 7. Sources and symbolic checks

- [Pinned Mathlib meromorphic-order source](https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/Analysis/Meromorphic/Order.lean)
  supplies the meromorphic identity principle used by the proof.
- [Pinned Mathlib improper-integral source](https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean)
  supplies the bounded-prefix integrability finalizer.
- [NIST DLMF 25.2](https://dlmf.nist.gov/25.2) records the classical
  meromorphic continuation and sole simple pole of zeta at 1.
- [NIST DLMF 25.10](https://dlmf.nist.gov/25.10) records the standard zero
  symmetry; the project already supplies the Lean RH strip criterion.
- Wolfram checked \(M(1)=7/64\), the removable values
  \(M(0)=3\log2/8\), \(M(-1)=\log2\), \(M(-2)=3\log2\), and the three
  deterministic lattice moments in the paper appendix. These calculations
  are evidence for exact expressions, not all-cutoff proof evidence.

No claim of mathematical novelty is based on the absence of a found source.

## 8. Verification scope

The assembled import was checked on the user's Lean server in job
`job_8TUk4RtxzD0U48hNcmUmsvFZFTX6EC0F` with exit code 0 and
`verified: true`. It compiled these four new modules, containing 17 public
theorems. This targeted check is not a full-project validation.

The nine printed decisive declarations, including both generic energy
lemmas and the actual RH and signed-residual implications, depend only on
`propext`, `Classical.choice`, and `Quot.sound`. No project-local axiom,
`sorry`, or `admit` is introduced. These axiom reports do not discharge
the substantive hypotheses displayed in the theorem types.

The introducing checkpoint is the final acceptance gate: it audits the
entire unpublished source delta and incrementally validates the aggregate
`RiemannResearch` target and the explicitly changed child modules before
publishing. The continued chat record records its terminal status, job,
validation scope, and published commit. GitHub-hosted CI is not used as
verification evidence.
