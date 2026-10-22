# Subpower annular energy: stronger hypotheses and zero-growth obstruction

10 October 2026. Baseline: `4f2dbfdf396cea0b94d2bd12f3e25d6ef1484d08`.

## Rebuild

The explicit full incremental server build `lake build RiemannResearch --quiet`
succeeded in job `job_gT8jeOHG58CnCV6SPTGhwD6hJqOVMdiE`.
Its elapsed time was 26.364 seconds, including the dependency-cache preflight.
This was a server build using native cached artifacts, not a clean deletion and
recompilation of Mathlib. Dependency versions were retained.

## Stronger arithmetic target

Let
\[
 A(x)=\sum_{n\ge1}\Lambda(n)W(n/x)-\frac7{64}x,\qquad
 E_A(X)=\int_1^X A(x)^2x^{-2}\,dx.
\]
The sum uses the actual compactly supported annular weight and every prime
power. The existing logarithmic sufficient hypothesis is replaced by
\[
 \forall\varepsilon>0\ \exists C_\varepsilon,X_\varepsilon\quad
 \forall X\ge\max(1,X_\varepsilon),\qquad
 E_A(X)\le C_\varepsilon X^\varepsilon.
\]
The constants and cutoffs may depend on the exponent. This is eventual
subpower growth; it is a weaker sufficient premise than a logarithmic bound.

The new Lean equivalence is
\[
 \boxed{\text{eventual subpower }E_A
 \quad\Longleftrightarrow\quad
 \forall a>\tfrac12,\ A\in
 L^2((1,\infty),x^{-2a-1}\,dx).}
\]
The already proved actual Mellin identity and continuation then give RH.
**The subpower arithmetic estimate remains Open. RH is not proved.**
This equivalence is between the two analytic/energy conditions; no RH converse
is asserted.

## Exact generic reverse estimate and eventual forward direction

For any measurable complex function with finite weighted energy at exponent
$s$, any $u\le s$, and every real $X\ge1$, Lean proves finite-prefix
integrability and
\[
 \int_1^X |f(x)|^2x^{-u-1}\,dx
 \le X^{s-u}\int_1^\infty |f(x)|^2x^{-s-1}\,dx.
\]
No continuity hypothesis is needed for this reverse estimate.

For a continuous nonnegative density $g$, an eventual primitive bound
\(\int_1^Xg\le C X^p\), $0\le p<\eta$, gives integrability against
$x^{-\eta}$. The compact head is accounted for by
\[
 D=\max(C,0)+\left|\int_1^{\max(1,X_0)}g(x)\,dx\right|.
\]
No sign hypothesis on the original coefficient $C$ is required. The proof
reuses the complete finite integration-by-parts identity from
`LogarithmicPrefixMellin.lean`; no boundary term is removed from that identity.

## Cofinal obstruction from an off-line zero

If \(\zeta(\rho)=0\), \(\rho=\beta+i\gamma\), and
\(\tfrac12<\beta<1\), the new theorem proves
\[
 \boxed{\forall p\in[0,2\beta-1),\ \forall C,X_0\in\mathbb R, \exists X\ge\max(2,X_0):\quad E_A(X)>C X^p.}
\]
Thus every smaller power envelope fails arbitrarily far out. This gives a
cofinal growth conclusion, beyond merely ruling out one all-cutoff bound.
It does not assert a lower bound at every cutoff or at the endpoint
$p=2\beta-1$. Zero simplicity is not assumed.

## Exact centered-signal transfer

For \(U(x)=\sum_{n\ge1}(\Lambda(n)-1)W(n/x)\) and the actual lattice
correction \(\delta=A-U\), retain the existing full equality
\[
 E_A(X)-E_U(X)
 =\int_{[1,X]}\frac{2U(x)\delta(x)+\delta(x)^2}{x^2}\,dx,
 \qquad |E_A(X)-E_U(X)|\le\frac{1105}{5832}.
\]
The new prime and centered subpower conditions are equivalent using this
bounded signed correction. The cross term and correction square remain in
the source identity; no prime-pair estimate is supplied.

## Formal declarations

`Analysis/SubpowerPrefixMellin.lean`:

- `finiteEnergy_of_prefix_power`
- `integrableOn_density_rpow_of_eventual_prefix_power`
- `finiteEnergy_of_eventual_prefix_power`
- `finiteEnergy_prefix_rpow_le`
- `energy_nonneg`
- `critical_prefix_le_energy`

`RH/AnnularSubpowerEnergy.lean`:

- `actualAnnular_Ha_of_eventual_power_energy`
- `actualPrimeSubpowerEnergy_iff_all_damping`
- `riemannHypothesis_of_actualPrimeSubpowerEnergy`
- `actualPrimeSubpowerEnergy_iff_actualCenteredSubpowerEnergy`
- `riemannHypothesis_of_actualCenteredSubpowerEnergy`
- `zeta_ne_zero_of_actualPrime_eventual_power_energy`
- `actualPrime_energy_cofinal_growth_of_zero`

Final acceptance is the introducing checkpoint's server source audit,
aggregate-project validation, changed-module validation, and publication.
The generic prefix candidate separately passed server job
`job_Y04A9vRuI01HOyvmJED4LetvMG47TLw-`.

The combined proof and all 13 public theorem axiom reports passed server job
`job_6XWki38R7C8-rPF7nxIr_DUz8NdueN8W`, exit code 0, verified true.
Every report listed only `propext`, `Classical.choice`, and `Quot.sound`.
The ephemeral check emitted formatting warnings on long axiom-print commands;
those commands are not persisted in the modules.

The saved application module and its new analytic dependency also passed
server source check `job_xwRD65th-rcum3RwTYqcP2uT-AaS35Yl`, exit code 0,
verified true, with no reported warnings. The checked application SHA-256 was
`b0b0a715b8385df654d23bf7a068fe7d1d86004c3fd910aa225dbe3c5b5ebd59`.
Only Mathlib's Apache-license header-format check is scoped out at the two
module docstrings because this private project has no such license header.
Theorem verification and other linters remain enabled.

## Research support

[NIST DLMF 2.5(i)](https://dlmf.nist.gov/2.5) supplies the classical Mellin
analyticity context; the actual arithmetic identity and zero exclusion are
proved project dependencies. The stronger conclusions here follow directly
from those dependencies and the new prefix estimates. They are not claimed
mathematically novel merely because a matching reference was not found.

Wolfram checked the exact comparison integral
\(\int_1^\infty D x^{p-\eta-1}\,dx=D/(\eta-p)\) for
$0\le p<\eta$, and the exponent identities. Those symbolic checks support
the algebra; the all-cutoff proof evidence comes from Lean.
