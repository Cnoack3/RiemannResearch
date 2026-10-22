## Continuation: prime-only refinements and exact raw arithmetic cancellation

Date: 21 September 2026. Starting published commit:
`f534b782c134f3d87f1780aea7da54c6c3c7506d`.

This continuation determines which refinement columns are nonzero and
evaluates the full unscreened arithmetic matrix on prime rows. It reveals
an unconditional cancellation mechanism before orthogonal screening.
It does not prove divergence of the screened row energy or prove RH.

### Notation

Keep the original Pareto Hilbert space and all infinite tails. Write
\[
Z_n=z_{(n+2)!},\quad E_n=\|Z_n\|^2,\quad
d_n=Z_{n+1}-Z_n,\quad D_n=\|d_n\|^2.
\]
The old tail atom is \(t_{n+1}=\operatorname{tailAtom}(n+1)\),
and its screened innovation is \(r_{n+1}\).
Retain
\[
\delta_n=\operatorname{factorialPrimeDelta}(n)
=\frac{1+E_n/2}{(n+3)^2}>0.
\]
Define two distinct matrices for exposition:
\[
B_{n,m}=\langle t_{n+1},d_m\rangle,\qquad
A_{n,m}=\langle r_{n+1},d_m\rangle.
\]
Only \(A\) is the screened matrix appearing in the established RH criterion.

### Composite refinement columns vanish identically

Lean proves
\[
\boxed{d_n\ne0\quad\Longleftrightarrow\quad n+3\text{ is prime}.}
\]
At a composite step the two consecutive factorials have the same prime
factors. The exact Euler products give equal certificate energies.
The existing orthogonal refinement identity then forces the difference
vector itself to vanish. At a prime step its positive pairing
\(\langle r_{n+1},d_n\rangle=\delta_n\) proves it is nonzero.

Consequently every composite column of the actual screened matrix is zero,
and the full row satisfies the exact identity
\[
\boxed{\sum_{m=0}^{n}A_{n,m}
=\sum_{\substack{0\le m\le n\\m+3\ {\rm prime}}}A_{n,m}.}
\]
This removes composite columns, not composite rows. Composite dictionary
observations and their Schur gains remain in the RH problem.

### Exact refinement energy and the raw prime matrix

At every stage,
\[
D_n=E_{n+1}-E_n.
\]
At prime stages the stronger identity is
\[
\boxed{D_n=\delta_n E_{n+1}.}
\]
This follows from the complete fresh-prime Euler-factor update; no
asymptotic estimate is used.

For every prime row \(n+3\), all raw entries are now evaluated:
\[
\boxed{
B_{n,m}=
\begin{cases}
0,&n<m,\\
\delta_n,&n=m,\\
-\dfrac{D_m}{2(n+3)^2},&m<n.
\end{cases}}
\]
In particular the strict lower entries at earlier prime columns are
strictly negative. They are zero at composite columns.

For the lower entries, both factorial certificates precede the row's
fresh prime. Their exact observations are
\(1/(n+3)-(1+E/2)/(n+3)^2\).
Subtracting them retains the divisor contribution and gives the displayed
negative difference of energies. These are actual Hilbert pairings.

### The complete raw row cancels to a fixed source

Finite telescoping and feasibility of the enlarged factorial certificate give
\[
\boxed{\sum_{m=0}^{n}B_{n,m}
=\operatorname{coprimePrimeDefect}(2!,n+3)
=\frac{1+E_0/2}{(n+3)^2}
\quad(n+3\ {\rm prime}).}
\]
Thus the diagonal is partially cancelled by the negative lower entries.
The exact relative remainder is
\[
\boxed{\frac{\sum_{m=0}^{n}B_{n,m}}{\delta_n}
=\frac{E_0+2}{E_n+2}.}
\]
The already established \(E_n\to+\infty\) implies that this expression
tends to zero. Lean also proves convergence of the actual raw-row ratio
on the filter restricted to prime stages.

These are unconditional results: no RH, not-RH, zeta-zero, or
RH-to-density premise is used.

### What this changes for the RH attempt

The raw arithmetic matrix already exhibits strong cancellation.
Positive prime diagonals therefore cannot justify a uniform relative
lower bound for its raw row sums.

The target remains
\[
\neg\operatorname{Summable}\left(
n\mapsto\frac{(\sum_{m=0}^{n}A_{n,m})^2}{\sigma_{n+1}}\right),
\qquad \sigma_{n+1}=\|r_{n+1}\|^2.
\]
The prior work proves that this target implies RH. It is still **Open**.
The new formulas for \(B\) do not evaluate \(A\): screening subtracts the
projection of each tail atom onto the full earlier dictionary. It can
change both the signed row sum and its normalization.

A concrete next target is to analyze that screening correction using the
explicit raw prime matrix above, retaining all composite dictionary rows.
No conclusion about RH or its negation follows from the raw cancellation
limit alone.

### Lean declarations and acceptance

New module:
`RiemannResearch/RH/ParetoFactorialRefinementArithmetic.lean`.

Namespace:
`RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity`.

The thirteen proved declarations are:

- `factorialPrimeRefinement_energy`;
- `factorialPrimeRefinement_eq_zero_of_not_prime`;
- `factorialPrimeRefinement_ne_zero_iff`;
- `factorialPrimeCrossGram_eq_zero_of_not_prime`;
- `factorialCrossGramRow_eq_prime_sum`;
- `tailAtom_inner_factorialPrimeRefinement_of_lt`;
- `tailAtom_inner_factorialPrimeRefinement_neg`;
- `factorialPrimeRefinement_energy_eq_delta_mul`;
- `tailAtom_factorialRefinement_row_sum`;
- `tailAtom_factorialRefinement_row_ratio`;
- `factorialRefinement_raw_cancellation_ratio_tendsto`;
- `tailAtom_factorialPrimeRefinement_prime_row`;
- `tailAtom_factorialRefinement_prime_row_ratio_tendsto`.

The module is exported from `RiemannResearch.lean`.
The theorem catalog records these arithmetic identities as established and
keeps the screened row-energy nonsummability obligation open.
Final acceptance and publication are recorded in the receipt below.

The coherent source candidate passed with exit code 0 and no warnings in
approximately 31 seconds. Six key axiom audits reported only
`[propext, Classical.choice, Quot.sound]`.
No admitted proof, project-local axiom, or unsafe declaration is introduced.
Verified candidate: `job_RYeNlgZVBgi2lj62mPAqxpt3VbeoARvZ`.
The publishing checkpoint separately validates the installed module.
