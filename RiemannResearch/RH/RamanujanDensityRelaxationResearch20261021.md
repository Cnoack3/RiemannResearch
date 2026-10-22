# Ramanujan zero signals: relaxed density and actual inverse-Gram control

Date: 2026-10-21. Continuation of commit 0213254f44792aae8e0d0bb3b3d3e7f6153efdfc.

Continuation, 2026-10-22: see [the zero/prime Gram note](RamanujanZeroPrimeGramResearch20261022.md).
The current horizontal signal weight is sharper than the earlier coefficient
recorded below. New screened and prime-coordinate certificates retain the
actual Gram form; the density provider and capacity obligations remain open.

## 1. Scope and formalization boundary

The earlier Ramanujan sampling theorems took the explicit proposition
UniformSelbergDensity (1/4). This continuation replaces that premise in the
Ramanujan consumers by **SublinearHorizontalEnergy** and proves several
weaker sufficient count conditions. It also preserves the actual inverse
Gram form throughout the sampling and normalization steps.

**The classical Selberg density theorem itself is not proved by this
continuation.** The remaining count input is explicit in the Lean types.
No density provider, RH premise, or project-local axiom is manufactured.
The arithmetic capacity-saturation obligation also remains Open.

Primary source for the classical density statement and the reflection
strategy: Ford--Zaharescu, *On the distribution of imaginary parts of zeros of
the Riemann zeta function*, Lemma 2, p. 7, and equation (3.8), p. 9:
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf .
The source states the classical input with exponent 1/4 and logarithmic
loss 1. The relaxed deductions and Gram assembly here follow the
user-directed research calculation of 21 October 2026; no mathematical
novelty claim is intended.

## 2. Actual zeros and the necessary normalization

All sums retain actual zeta zeros \(\rho=\beta+i\gamma\), positive heights
\(0<\gamma\le T\), and analytic multiplicities \(m(\rho)\). Write
\[
N(T)=\sum_{0<\gamma\le T}m(\rho),\qquad
E(T)=\sum_{0<\gamma\le T}m(\rho)(\beta-\tfrac12)^2.
\]
The new minimal scalar moment premise is
\[
\boxed{E(T)/T\longrightarrow0.}
\]
This is the proposition SublinearHorizontalEnergy.

The height normalization is essential. Ordinary equidistribution normalized
by \(N(T)\asymp T\log T\) does not by itself recover the order-\(T\) prime
bias. In particular, \(E(T)/N(T)\to0\) alone cannot be substituted for the
displayed hypothesis in this argument.

Reflection across the critical line preserves both heights and multiplicity.
With \(S_T(u)=\sum m(\rho)e^{iu\gamma}\) and
\(L_T(u)=\sum m(\rho)e^{u(\rho-1/2)}\), its complete signed correction is
\[
L_T(u)-S_T(u)
=\sum_{0<\gamma\le T}m(\rho)e^{iu\gamma}
  \left(\cosh(u(\beta-\tfrac12))-1\right).
\]
The existing reflection estimate gives
\[
|S_T(u)-L_T(u)|\le u^2e^{|u|/2}E(T).
\]
Consequently the new scalar premise gives
\((S_T(u)-L_T(u))/T\to0\) for each fixed \(u\).
The existing unconditional rational Landau limit then supplies the
Ramanujan signal at \(u=\log q\).

## 3. Only one shrinking strip is needed

Let \(B(T,\delta)\) count zero copies with
\(|\beta-\tfrac12|>\delta\). The proved finite inequality is
\[
E(T)\le\delta^2N(T)+\tfrac14 B(T,\delta)\qquad(\delta\ge0).
\]
The repository's unconditional total-count theorem supplies
\(N(T)\le C_0T\log T\) for all sufficiently large \(T\).
It follows that any function \(\delta(T)\) satisfying
\[
\delta(T)\ge0\text{ eventually},\qquad
\delta(T)^2\log T\to0,\qquad
B(T,\delta(T))/T\to0
\]
supplies SublinearHorizontalEnergy.

There is a version using just the single inclusive right-half count:
\[
N_{\ge}(\tfrac12+\delta(T),T)/T\to0.
\]
Actual reflection gives \(B(T,\delta)\le2N_{\ge}(\tfrac12+\delta,T)\).
Zeros exactly at the threshold are handled by the inclusive/strict
inequality; their multiplicities are never assumed absent.

The corresponding declarations are
sublinearHorizontalEnergy_of_shrinkingStrip and
sublinearHorizontalEnergy_of_shrinkingInclusiveCount.

## 4. Every fixed logarithmic loss is sufficient

UniformLogLossDensity \(a,b\) is the explicit count proposition
\[
N_{\ge}(\sigma,T)
\le CT(\log T)^b
 e^{-a(\sigma-1/2)\log T}
\quad(\tfrac12\le\sigma\le1,\ T\ge T_0),
\]
with one constant and threshold independent of \(\sigma\).
The new theorem needs **only \(a>0\)**. The real number \(b\) may be any
fixed logarithmic exponent; there is no upper restriction \(b<2\)
in the final qualitative theorem.

Put
\[
c=\max\{b,0\}+2,\qquad
\delta(T)=\frac ca\frac{\log\log T}{\log T}.
\]
The entire calculation is checked in Lean:
\[
\delta(T)^2\log T
=\frac{c^2}{a^2}\frac{(\log\log T)^2}{\log T}\to0,
\]
\[
\frac{B(T,\delta(T))}{T}
\le2C(\log T)^{b-c}\to0.
\]
Thus a logarithmic loss such as \(b=3\) or \(b=5\) also suffices for the
fixed-conductor signal. A stronger decay constant than 1/4 is not required.

This is a relaxation of the hypothesis needed by the consumer, not a
new bound on the actual zeta zero count. Classical count estimates still
require their own formal analytic proofs.

The old proposition UniformSelbergDensity \(a\) implies
UniformLogLossDensity \(a,1\). Its passage to SublinearHorizontalEnergy is
proved for every \(a>0\).

## 5. Quantitative density profiles for finite frequency bands

For quantitative bounds retain a general supplied right-tail profile
\[
N_>(\tfrac12+t,T)\le M(T)e^{-\lambda(T)t}
\quad(0\le t\le\tfrac12).
\]
For \(0\le\theta<1\), \(T>0\), \(M(T)\ge0\), \(\lambda(T)>0\), and
\(|u|\le\theta\lambda(T)\), the checked transfer is
\[
\left|\frac{S_T(u)-L_T(u)}{T}\right|
\le \frac{2u^2}{1-\theta^2}
       \frac{M(T)}{T\lambda(T)^2}.
\]
In particular, \(\lambda(T)\to\infty\) and
\(M(T)/(T\lambda(T)^2)\to0\) suffice for fixed-mode comparison.
The same profile also supplies the sublinear horizontal moment.

For \(\lambda=a\log T\) and \(M=CT(\log T)^b\), this direct band budget is
\((C/a^2)(\log T)^{b-2}\); hence \(b<2\) gives this particular quantitative
vanishing rate. Section 4 removes that restriction for qualitative
fixed-conductor convergence by splitting the central strip.
The two conclusions have different quantitative strengths.

## 6. Actual Ramanujan Gram budgets and the signed cross term

The finite packet family uses the actual Pareto Hilbert space.
For \(w(n)=n/(n+1)\) and \(Z=\zeta(2)\),
\[
H_{qr}=\mathbb E_P[B_qB_r]=Z\mathbb E_Q[wB_qB_r],\qquad
\ell_q=\Lambda(q),\qquad A=H^{-1}.
\]
The matrix is never replaced by an unweighted-Q or diagonal phase matrix.

Let \(z_T\) be the actual ordinate signal,
\(z_T(q)=-2\pi\sqrt q\,\Re(S_T(\log q)/T)\), and let \(z_T^L\)
be its Landau counterpart. The exact density correction is
\[
d_T(q)=z_T(q)-z_T^L(q)
 =2\pi\sqrt q\,
   \Re\left(\frac{L_T(\log q)-S_T(\log q)}T\right).
\]
For \(e_T^L=z_T^L-\ell\), the complete inverse-metric energy is
\[
\|z_T-\ell\|_A^2
=\|e_T^L\|_A^2+2(e_T^L)^\top A d_T+\|d_T\|_A^2.
\]
The signed cross term is retained.

For any nonnegative coordinate weights \(v_q\), define the explicit cost
\[
\mathcal B_D(v)=\sum_{q,r\in D}|A_{qr}|v_qv_r.
\]
If \(|d_T(q)|\le v_qR(T)\), \(R(T)\ge0\), Lean proves
\[
\|d_T\|_A^2\le R(T)^2\mathcal B_D(v).
\]
Two actual certificates are supplied:
\[
R(T)=E(T)/T,\quad
v_q=2\pi\sqrt q(\log q)^2e^{|\log q|/2},
\]
and, when every conductor is in the stated frequency band,
\[
R(T)=\frac{2M(T)}{(1-\theta^2)T\lambda(T)^2},\quad
v_q=2\pi\sqrt q(\log q)^2.
\]
These are sufficient absolute majorants. The preceding signed energy
identity and the screened identity below preserve cancellations exactly.

## 7. The sharper projective condition in the actual inverse metric

Put
\[
\kappa=\ell^\top A\ell>0,\qquad D(z)=\ell^\top Az,\qquad
\Pi z=z-\frac{D(z)}{\kappa}\ell.
\]
For \(D(z)\ne0\), normalization gives
\[
a_z=\frac{Az}{D(z)},\qquad a_*=\frac{A\ell}{\kappa},\qquad
\ell^\top a_z=1.
\]
The checked exact identities are
\[
\ell^\top A\Pi z=0,\qquad
\|\Pi z\|_A^2=z^\top Az-\frac{(\ell^\top Az)^2}{\kappa},
\]
\[
\boxed{\|a_z-a_*\|_H^2=\frac{\|\Pi z\|_A^2}{D(z)^2}.}
\]
A literal inverse-matrix declaration verifies the full signed rank-one
formula; there is no surrogate inverse in these expressions.

For a fixed finite family, normalized synthesis converges to the optimum
if and only if
\[
\|\Pi z_T\|_A/|D(z_T)|\to0
\]
when the denominator is eventually nonzero. Coordinate convergence and
full error convergence are sufficient but are not necessary for this
projective condition. In particular, radial error cancels under normalization.

For the actual unit target,
\[
\boxed{\|1-F_z\|_P^2
=\kappa^{-1}-1+\frac{\|\Pi z\|_A^2}{D(z)^2}.}
\]
Therefore a screened certificate \(\|\Pi z\|_A\le\eta|D(z)|\)
gives \(\|1-F_z\|_P^2\le\kappa^{-1}-1+\eta^2\).
The finite theorem has no density or RH premise.

For growing finite families, the generic checked consumer proves target
convergence from \(\kappa_j\to1\) and vanishing screened ratios. It does
not require a uniform bound on inverse Gram operators or control of the
radial sampling error.

## 8. Declarations, validation, and research obligations

Source files:

| File | Principal additions or strengthened statements |
| --- | --- |
| Analysis/ActualZeroSublinearEnergy.lean | One-strip and moment criteria; arbitrary fixed log loss; general finite-band profile |
| Analysis/SignalNormalizationStability.lean | Exact vector identity for the screened correction |
| Analysis/FiniteGramSignalStability.lean | Literal screened inverse-matrix formula; projective convergence criterion; growing-capacity consumer |
| RH/RamanujanZeroSignal.lean | Weaker moment hypothesis in existing limits and diagonal cutoff selection; signed density energy and actual Gram certificates |

The changed Ramanujan declarations sampledSignal_tendsto,
sampled_inverseNorm_error_tendsto, coefficients_tendsto, and
exists_strictMono_zero_cutoffs now take SublinearHorizontalEnergy.
They no longer require UniformSelbergDensity (1/4) in their types.

Open analytic obligation: prove an actual provider for the single shrinking
inclusive count in Section 3, or another sufficient scalar or screened
Gram condition. A classical Selberg/Ingham count proof would discharge a
stronger obligation. None of the transfer theorems proves that count.

Open arithmetic obligation: establish saturation of the complete squarefree
packet capacities \(\kappa_D\to1\). The relaxed density estimate and the
prime normalization do not establish saturation.

Open quantitative research: control the explicit costs
\(\mathcal B_D(v)\), or use the full screened signed form, to obtain effective
cutoffs as conductors grow. Fixed-stage convergence already permits
existential increasing cutoffs with arbitrarily prescribed positive relative
inverse-metric budgets, with no uniform condition-number assumption.

All domain-specific premises remain visible in theorem types.
Kernel axiom inspection is distinct from proving those premises.
The successful containing checkpoint is the publication certificate.

Targeted server validation passed job
job_uf5iCmx68d_G_97lUaLH3vpOpDfI5k5D: exit 0, verified=true,
reported execution 16.249 seconds. The check imported all four changed
subject modules and inspected six central declarations; each depended only
on propext, Classical.choice, and Quot.sound. The printed diagonal theorem
type retained SublinearHorizontalEnergy explicitly. Minor unused-tactic
and unused-simp cleanup followed; the containing checkpoint validates the
published final source. Opening and polling time are not kernel-checking
measurements; no exact opening-time measurement was recorded.
