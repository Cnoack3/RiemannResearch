# Actual residual regularity and concrete Lean routes

Date: 2026-09-24.
Source state inspected: 408aad739d7ef4f2401f7f85aaae606d53ca7e70.

## Exact status of the requested theorem

In namespace RiemannResearch.RH.Pareto.CoefficientStabilization, the request

~~~lean
∃ L : ℝ, Summable (fun n =>
  |tailAverage limitResidual n - L| ^ 2)
~~~

is definitionally TailRegular limitResidual. The existing theorem
limitResidual_zero_iff_tailRegular identifies it with limitResidual = 0.
riemannHypothesis_of_tailRegular then concludes Mathlib RiemannHypothesis.
No provider of the requested regularity has been proved here.

Write r = limitResidual and E = ‖r‖². With physical coordinates r(k),
the project's zero-based average is exactly

\[
T_n=(n+1)\sum_{k=n+1}^{\infty}\frac{r(k)}{k(k+1)}.
\]

The established unconditional identities are

\[
T_0=E,\qquad
\sum_{n=0}^{\infty}|T_n-T_{n+1}|^2=E-E^2.
\]

These control differences. They do not establish summability of T_n-L.
For an example satisfying even the displayed normalization, put
u_n=1/sqrt(n+1), A=∑|u_n-u_(n+1)|², E=1/(1+A), and T_n=E u_n.
Then A is positive and finite, T_0=E, and
∑|T_n-T_(n+1)|²=E² A=E-E². Yet T_n is not square-summable around
any constant. This is a counterexample to an inference from those numerical
identities alone, not a counterexample for the actual arithmetic residual;
orthogonality to the arithmetic legal span is not asserted for this example.

Noor's Theorems 9 and 12 prove shifted density and trivial intersection of
the original orthogonal complement with the local Dirichlet space. They do
not put the actual residual in that space. The real coefficient versions
are now present in the inspected project.

## Route 1: the economical existing acceptance target

Prove the following without an RH-strength assumption:

~~~lean
∃ C : ℝ, ∃ᶠ N : ℕ in Filter.atTop,
  (N : ℝ) * residualTailEnergy N ≤ C
~~~

Here residualTailEnergy N is the complete sum over k>N of
|r(k)|²/[k(k+1)]. Equivalently, one finite bound must hold at arbitrarily
large cutoffs. No prescribed decay rate is required.

Existing declarations in RH/ParetoResidualTailDichotomy.lean:

- frequently_bounded_actual_tail_iff_residual_zero
- limitResidual_zero_of_frequently_bounded_actual_tail
- riemannHypothesis_of_frequently_bounded_actual_tail

The PNT provider is already proved in RH/CanonicalMobiusPNT.lean.
It is not an additional open premise. The exact dichotomy is: r=0, or
N * residualTailEnergy N tends to positive infinity.

The source-compatible assembly to the precise requested conclusion is:

~~~lean
import RiemannResearch.RH.ParetoTailAverageCriterion
import RiemannResearch.RH.ParetoResidualTailDichotomy

open Filter
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.Pareto.CoefficientStabilization

example (C : ℝ)
    (h : ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * residualTailEnergy N ≤ C) :
    ∃ L : ℝ, Summable (fun n =>
      |tailAverage limitResidual n - L| ^ 2) :=
  limitResidual_zero_iff_tailRegular.mp
    (limitResidual_zero_of_frequently_bounded_actual_tail C h)
~~~

This is a conditional assembly, not a proof of h. The displayed assembly
is documented from the inspected signatures; it is not recorded as a new
verified declaration in this session.

## Route 2: signed covariance of explicit exact-head interpolants

For each N choose a finite set s_N of indices k≥N and real signed weights
a_(N,k) with sum one. Let

\[
H_N=\sum_{k\in s_N}a_{N,k}\,\mathrm{canonicalMobiusHilbert}(k).
\]

The existing theorems give legality, H_N(j)=1 for 1≤j≤N, and the exact identity

\[
\|H_N\|_P^2=\frac{N}{N+1}+
 \sum_{k,\ell\in s_N}a_{N,k}a_{N,\ell}C_N(k,\ell),
\]
\[
C_N(k,\ell)=
\sum_{j>N}\frac{H^{\mathrm{can}}_k(j)H^{\mathrm{can}}_\ell(j)}{j(j+1)}.
\]

The remaining research input is a cofinal uniform bound on the complete
signed quadratic form. RH/CanonicalMobiusSignedAverages.lean already contains
riemannHypothesis_of_frequently_bounded_signed_covariance.

The optimizer is already formalized in
RH/CanonicalMobiusCovarianceMinimum.lean, including singular covariance
matrices. If C_N z_N=1, define κ_N=1ᵀz_N. The exact minimum is κ_N⁻¹ and
the complete optimized energy is N/(N+1)+κ_N⁻¹. Thus the sharp next target is

\[
\exists\varepsilon>0\quad \kappa_N\ge\varepsilon
\quad\hbox{at arbitrarily large }N.
\]

The existing theorem SignedCovariance.riemannHypothesis_of_capacity_frequently_ge
concludes RH from precisely this input. Finite-stage positivity of κ_N is
already proved and does not give this lower bound.

This is a concrete arithmetic work plan: apply the existing exact CRT/Green
covariance formulas to growing index families, and prove that their optimized
capacity remains bounded away from zero at arbitrarily large cutoffs. Every signed cross term and the complete infinite Pareto
tail must be retained. Positive definiteness or numerical finite-cutoff
success does not prove the required uniform bound. No claim is made that
one particular fixed averaging rule has the needed bound.

## Route 3: quantitative use of the newly completed shifted density

This section is an independently derived elementary Hilbert-space argument,
not a claim of mathematical novelty. It supplies a concrete lemma to
formalize and a precise open rate target.

Work in real coefficient space. Let V be the image under hardyCoordinates
of the closed legal space, a=hardyCoordinates r, S the right shift, and
D=I-S. Then a is orthogonal to V and S is an isometry.

For v∈V set e=Dv-a. Direct expansion gives the exact identity

\[
\boxed{\|a\|^2=\|e\|^2+2\langle e,Sv\rangle.}
\]

Indeed, substitute e=v-Sv-a, expand both terms, cancel ‖v‖²-‖Sv‖²,
and use ⟨a,v⟩=0. Consequently

\[
\|a\|^2\le \|Dv-a\|^2+2\|Dv-a\|\|v\|.
\]

It suffices to construct v_j∈V with

\[
Dv_j\to a,\qquad \|Dv_j-a\|\|v_j\|\to0.
\]

Shifted density supplies approximation, but not the second limit. A bounded
family of lifts would suffice, although the product condition allows some
growth. If E=‖a‖²>0 and δ=‖Dv-a‖>0, the exact obstruction is

\[
\|v\|\ge \frac{E-\delta^2}{2\delta}.
\]

Thus an actual proof must beat this cost along an approximating family.

The finite version also works with a_N=hardyCoordinates(1-F_N) and v in the
image of V_N. Write u_i=hardyCoordinates(g_i),

\[
G_N(i,j)=\langle u_i,u_j\rangle,\quad
A_N(i,j)=\langle Du_i,Du_j\rangle,\quad
h_N(i)=\langle Du_i,a_N\rangle,\quad E_N=\|a_N\|^2.
\]

For λ>0 the positive definite matrix A_N+λ²G_N gives

\[
J_N(\lambda)=
\min_v\{\|Dv-a_N\|^2+\lambda^2\|v\|^2\}
=E_N-h_N^\top(A_N+\lambda^2G_N)^{-1}h_N.
\]

The elementary inequality 2δ‖v‖≤δ²/λ+λ‖v‖² yields

\[
E_N\le\frac{1+\lambda}{\lambda}J_N(\lambda).
\]

For example, a cofinal sequence N_j satisfying

\[
J_{N_j}(1/(j+1))\le1/(j+1)^2
\]

would give E_(N_j)≤(j+2)/(j+1)² and hence residual vanishing.
This finite matrix estimate remains open. The exact lifting identity and
finite minimization formula are unconditional supporting lemmas; neither
alone proves RH.

## Priority and verification boundary

Prioritize Route 2 for explicit arithmetic development, with Route 1 as the
smallest existing acceptance interface. Route 3 identifies the exact
quantitative issue in attempting to upgrade Noor's shifted density.

Source inspection confirms the existing interfaces and their hypotheses.
The fresh direct Lean audit timed out after 90 seconds with no diagnostics
(job_pnhg5V39asPFPi-GrOcvyb0pT_kc9wKB). This is not a refutation.
A first focused candidate for the new elementary lifting lemmas failed at a
symmetry rewrite in its proof of the identity; that candidate was not saved
as a Lean module. The repaired candidate and the direct existing-criterion
audit then timed out after 300 seconds with no diagnostics
(job_r1dnwj9T02R-jw0Vd3tyEk2NrxL4OxsE). No new theorem was kernel-verified
in this session, and no new Lean module is being published. The mathematical
lifting calculation above is proved in prose and awaits successful Lean
verification. These infrastructure/proof-attempt outcomes do not refute any
of the mathematical targets. No unconditional RH statement or regularity
provider is asserted.

Reference supporting Noor's shifted-density and regularity statements:
S. Waleed Noor, A Hardy space analysis of the Báez-Duarte criterion for the RH,
Advances in Mathematics 350 (2019), 242–255, Theorems 9 and 12.
https://arxiv.org/html/1809.09577v4
