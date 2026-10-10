# Exact annular growth exponents and the full signed residual

10 October 2026. Baseline: a7ae31341ce71c6eaf506f787e591bddb20461f7.
Source continuation: RH_Annular_Lean_Chat_Record_20261010(1).md, Section 13.5.

The current baseline already proves eventual subpower energy, its all-damping
membership equivalence, and cofinal violations of lower power envelopes at an
off-line zero. This continuation proves the literal logarithmic limsup result,
an unconditional finite exponent envelope, and transfer to the complete signed
residual. **RH and the actual arithmetic subpower estimate remain Open.**

## Exact equalities first

Use the actual signals and all-real-cutoff energies:
\[
 A(x)=\sum_n\Lambda(n)W(n/x)-\frac7{64}x,\quad
 U(x)=\sum_n(\Lambda(n)-1)W(n/x),\quad A=U+\delta.
\]
The existing checked kernel and lattice identities give
\[
 E_A(X)=E_U(X)+T(X),\qquad E_U(X)=M(X)+R(X),
\]
where
\[
 T(X)=\int_{[1,X]}\frac{2U(x)\delta(x)+\delta(x)^2}{x^2}\,dx,
 \qquad |T(X)|\le\frac{1105}{5832}.
\]
The new assembled declaration retains the complete equality
\(E_A=M+R+T\). Neither the signed lattice cross term nor its square is removed.
\(R\) is the original actual residual, including both singleton terms, the
constant, singular series, actual diagonal, prime powers, and actual cutoffs.

## A finite growth statistic

For a possibly signed real function \(F\), define
\[
 \ell_F(X)=\frac{\log(1+\max(F(X),0))}{\log X},\qquad
 \lambda_F=\limsup_{X\to\infty}\ell_F(X).
\]
Lean initially defines the limsup in the extended reals, so it requires no
unproved boundedness premise. It proves
\[
 \lambda_F=0\quad\Longleftrightarrow\quad
 \forall\varepsilon>0\ \exists C_\varepsilon\
 \forall^{\rm eventually}X,\quad F(X)\le C_\varepsilon X^\varepsilon.
\]
For a signed residual the positive part only makes the logarithm defined.
The arithmetic target remains an upper bound on the complete signed residual;
individual arithmetic terms are not replaced by their absolute values.

For the actual centered signal, every real \(X\ge1\) satisfies
\[
 E_U(X)\le(7/24)^2X(1+\log X)^2.
\]
This follows from the existing actual coefficient estimate
\(|U(x)|\le(7/24)x(1+\log x)\), integration over the complete finite interval,
and \(\Lambda(n)\le\log n\). Consequently
\[
 \boxed{0\le\lambda_{E_A}=\lambda_{E_U}\le1.}
\]
In particular the actual limsup is finite; the extended-real definition is
not an implicit growth assumption. This elementary upper envelope supplies
no critical prime-pair cancellation.

## Off-line zeros force a positive exponent

Every actual zeta zero \(\rho=\beta+i\gamma\) with \(\beta<1\) satisfies
\[
 \boxed{2\beta-1\le\lambda_{E_A}=\lambda_{E_U}.}
\]
For \(\beta>1/2\) the bound is strictly positive. The proof uses the existing
cofinal inequality for every \(0\le p<2\beta-1\), then passes to the limsup.
No simplicity hypothesis is used. This remains an asymptotic growth statement,
rather than a lower bound at every individual cutoff or a forced violation of
an endpoint \(O(X^{2\beta-1})\) envelope.

The new zero-exponent implication is
\[
 \boxed{\lambda_{E_A}=0\Longrightarrow {\rm RH}.}
\]
It uses the already verified membership and meromorphic continuation bridge.
No local identity provider, model hypothesis, or RH-energy provider is added.
The converse RH-to-zero-exponent implication is not established here.

## Weaker signed-residual target

The generic result proves that a perturbation of absolute subpower size
preserves the logarithmic exponent exactly. Thus the explicit premise
\[
 \forall\varepsilon>0,\quad |M(X)|=O_\varepsilon(X^\varepsilon)
 \tag{model premise, Open}
\]
gives
\[
 \boxed{\lambda_R=\lambda_{E_U}=\lambda_{E_A}.}
\]
The preceding logarithmic model bound implies this premise, but is stronger
than required for this exponent transfer. Under the model premise, eventual
subpower upper growth of the complete signed \(R\) is equivalent to actual
subpower energy and implies RH:
\[
 \boxed{
 \bigl[\forall\varepsilon>0,\ |M|=O_\varepsilon(X^\varepsilon)\bigr]
 \ \land\
 \bigl[\forall\varepsilon>0,\ R\le O_\varepsilon(X^\varepsilon)\bigr]
 \Longrightarrow {\rm RH}.
 }
\]
Both displayed arithmetic estimates remain Open. In particular a definition
or a conditional theorem does not furnish either estimate.

## Formal sources and verification

- Analysis/LogarithmicGrowth.lean: generic logarithmic slopes, extended-real
  exponents, subpower characterization, cofinal-to-limsup passage, and exact
  exponent preservation under absolute subpower perturbations.
- RH/AnnularEnergyGrowth.lean: actual equalities, actual prime and centered
  exponent equivalence, unconditional exponent envelope, off-line-zero
  obstruction, and complete residual transfer with an explicit model premise.

The development uses focused imports, no project-local axioms, and no unproved
placeholders. Final acceptance requires the introducing checkpoint's source
audit, aggregate server build, explicitly changed child-module checks, and
successful publication. A queued job alone is not evidence of that acceptance.

Primary background references:
[NIST DLMF 2.5(i)](https://dlmf.nist.gov/2.5) for Mellin analyticity and
[NIST DLMF 25.10(i)](https://dlmf.nist.gov/25.10) for classical zero distribution.
The source references supply background; the actual arithmetic identity and
zero obstruction are proved project dependencies. No mathematical novelty is
claimed solely from a missing literature match.

Wolfram checked the elementary exponent comparisons, the power-tail comparison
integral, and the limiting exponent of \(cX(1+\log X)^2\). Those symbolic
computations are supporting checks; all-cutoff proof evidence comes from Lean.

## What is still missing

The useful arithmetic target is to prove actual subpower control of the full
signed residual, together with subpower absolute model control, or directly
prove \(\lambda_{E_A}=0\). The new unconditional envelope reaches exponent 1,
whereas RH needs exponent 0. This gap is explicit.

The paper's deterministic lattice Mellin entire continuation and exact moments
are not formalized by these growth modules. The full RH-to-logarithmic-energy
converse, explicit-formula obligations, and actual model/residual bounds remain
as recorded in the earlier research notes.

The combined actual application passed server job
`job_0V_cGnOYYHmRKVvPbso7uzPNTPa4dGPr`, exit code 0, verified true,
with no warnings. Both new modules contain 31 public theorems. The checked
application source SHA-256 was
`a05b8d6c21728e3e411248ac42c34d91cbb68d9faab16737e59d219508e5a52a`.

The saved application import and printed decisive theorem types also passed
server job `job_H2Qmba7IWYCI2ajdClZCjByWQYdMMfWZ`, exit code 0 and
verified true. Exhaustive public-theorem foundation reports were inspected in
bounded checks `job_VXTqmXJL0mTrxnumHRObdL3HghYkAx2X` and
`job_TKge6_ayzXDHtudZYrCQcjrT-kl0_pKd`: all 31 declarations list only
`propext`, `Classical.choice`, and `Quot.sound`. The second bounded
receipt supplies the first three reports omitted by the first receipt's
output-length limit. Formatting warnings in the first ephemeral audit are
not part of the persisted source.

Decisive declarations in RH/AnnularEnergyGrowth.lean:

| Declaration | Conclusion or substantive premise |
|---|---|
| actualPrime_energy_eq_complete_residual | Exact E_A=M+R+T at every real cutoff |
| actualPrime_growthExponent_mem_Icc | Actual exponent belongs to [0,1], unconditionally |
| actualPrime_growthExponent_ge_of_zero | A zero forces exponent >=2 beta - 1 |
| zeta_ne_zero_of_actualPrime_growthExponent_bound | An upper exponent bound excludes zeros past its threshold |
| actualPrimeSubpowerEnergy_iff_growthExponent_zero | Actual subpower energy iff zero exponent |
| riemannHypothesis_of_actualPrime_growthExponent_zero | Requires the actual zero-exponent hypothesis |
| actualCentered_growthExponent_eq_residual | Requires absolute subpower size of the actual model |
| riemannHypothesis_of_actualResidual_subpower | Requires both actual model and complete residual subpower bounds |

These foundation reports do not discharge the mathematical hypotheses in
the last three conditional declaration types. The original lattice-Mellin
paper appendix remains separate from this verified growth development.
