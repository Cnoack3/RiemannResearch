# Actual spectral limits, sharp double-log feedback, and relative cumulative gaps

Continuation of the two supplied markdowns, 6 October 2026.
Audited starting commit: `52ecaa8ee0ac2c55a63f75876d2db82ed8d16896`.

## Outcome and exact scope

Eight focused modules extend the actual current repository, rather than
repeating the stale formalization gaps in the attachments. The complete
actual spectral sequence is now connected to the existing RH consumer.
The arithmetic tightness/moment and cumulative signed-budget providers
remain open. No unconditional RH proof is asserted.

All conductors in the actual finite stage, all signed Gram interactions,
terminal boundaries, and complete infinite physical tails are retained.
The spectral tightness equivalence below is with actual closed-span
membership; it does not supply the separately missing RH-to-density converse.

## 1. Close the actual geometric sequence gap

Use `finiteSpace (n+3)` (conductors through `n+4`) and the physical cutoff
`compactHead (n+4)`. Let `v=twoThreeDual`, `p_n` be its full-stage projection,
`y_n` its projection onto the actual head image, and

\[
\delta=\|v-P_Wv\|^2,\quad e_n=\|v-y_n\|^2,\quad
S_n=\|p_n-Q_{n+4}p_n\|^2.
\]

The new cutoff module proves the exact finite energy equality

\[
\|Q_N f\|^2=\sum_{j<N}\rho_j f(j+1)^2,
\]

and consequently `Q_N f -> f` for every actual Hilbert vector. The stronger
moving version allows independently cofinal stage and physical-cutoff
sequences. Strong projection convergence therefore proves `S_n -> 0`
unconditionally, even when the limiting projection is different from `v`.

For the actual compact corrected trial the conductor membership is sharpened
from `finiteSpace N` to `finiteSpace (N-1)`. Its exact reciprocal source is

\[
q_N=14m(N)-13m(\lfloor N/2\rfloor)+3m(\lfloor N/4\rfloor),
\qquad m(N)=\sum_{d\le N}\mu(d)/d.
\]

The equality is proved by finite divisor reindexing. The already formalized
PNT consequence gives `q_N -> 0`. Its physical head error is exactly
`positiveWeight N * (N q_N)^2`, which is at most `q_N^2`.
Best approximation in the actual head image yields `0 <= e_n <= q_(n+4)^2`,
and hence `e_n -> 0`. This supplies a checked geometric limit, not a bound
on the corrected trial's full infinite-tail energy.

The literal full spectrum is defined by `compactSpectrumIndex`,
`compactSpectrumWeight`, and `compactSpectrumEigenvalue`. Its index dimension
changes with the actual stage; no artificial fixed-dimensional spectrum is
supplied as a premise. The existing finite spectral identity now gives

\[
\|v-p_n\|^2=e_n+T_n,\qquad T_n=J_n+S_n,
\]

with both complete correction squares preserved. Thus `T_n -> delta`
unconditionally. For every fixed `R>0`,

\[
\boxed{\sum_{\lambda_{n,i}\ge R}w_{n,i}\longrightarrow\delta.}
\]

This leads to the exact checked equivalence

\[
\boxed{\text{actual complete-source tightness at infinity}
\iff 1\in W.}
\]

The actual theorem `riemannHypothesis_of_actual_compactSpectrum_tight`
requires only that displayed tightness provider. Cutoff convergence,
head-error decay, source realization, eigenvalue nonnegativity, optimizer-tail
decay, and correction convergence are all discharged internally.

## 2. A sharp double-log obstruction and strict feedback criterion

Let `0<sigma_n<1`, `sigma_n -> 0`, and `S_n <= sigma_n`. Define

\[
\Phi(x)=\log(1+\log(1+x)),\quad
M_n=\sum_iw_{n,i}\Phi(\lambda_{n,i}),\quad
D_n=\log(1+\log(1/\sigma_n)).
\]

At `R_n=1/sqrt(sigma_n)` the sharp scalar comparison is

\[
\Phi(R_n)\ge D_n-\log2.
\]

The complete finite envelope, when `D_n>log2`, is

\[
\boxed{T_n\le\sigma_n+\sqrt{\sigma_n}
+\frac{M_n}{D_n-\log2}.}
\]

The normalization loss tends to one, improving the older factor-two
comparison. More strongly, without assuming a limit of the normalized
moment, every `c<delta` satisfies eventually

\[
\boxed{c<M_n/D_n.}
\]

This is the precise eventual-floor formulation of
`liminf M_n/D_n >= delta`. It is checked both for general finite sources
and the literal actual Pareto source.

Consequently it suffices to prove, for some fixed `theta<1` and `E_n -> 0`,

\[
\boxed{M_n/D_n\le E_n+\theta T_n\quad\text{eventually}.}
\]

The actual consumer is
`riemannHypothesis_of_actual_compactSpectrum_doubleLog_feedback`.
Unlike a separately imposed zero-moment limit, this permits a strict
fraction of the full correction on the right. The moment-budget inequality
is still an open arithmetic provider. Positive vanishing envelopes for
`S_n` exist after a finite shift by the unconditional tail limit; the
global envelope assumptions in this theorem are stated explicitly.

## 3. Relative negative cumulative excursions

Retain the actual signed identity `D_i=H_i+L_i`, with decreasing residual
energies `D_i -> delta`. Put

\[
A_M=\sum_{i<M}a_i,\qquad
P_M=\sum_{i<M}\max(-A_{i+1},0)(D_i-D_{i+1}).
\]

The preceding commit checked the exact Abel boundary and the consumer with
`(sum H + Z + P)/A -> 0`. The new result discharges the penalty limit
automatically if, on cofinal horizons `M_k`,

\[
A_{M_k}\to+\infty,\qquad
A_j\ge-C A_{M_k}\ (1\le j\le M_k),\qquad C\ge0.
\]

Indeed the energy decreases are summable, with sum `D_0-delta`.
For each fixed prefix the normalized negative part tends to zero; the
relative floor dominates its weighted summand by `C(D_i-D_(i+1))`.
Tannery dominated convergence proves `P_(M_k)/A_(M_k) -> 0`.
Thus an `O(A)` negative excursion is allowed, not just a bounded or `o(A)`
excursion. The signed head terms need not vanish separately.

The actual consumer
`riemannHypothesis_of_cofinal_cumulative_signed_trial_relative_floor`
retains the full cumulative tail budget

\[
\sum_{i<M_k}[L_i-(1-a_i)D_i]\le Z_{M_k}
\]

and requires only `(sum H + Z)/A -> 0`, alongside the relative floor and
diverging mass. These arithmetic hypotheses remain open.

## 4. Construct the full constrained approximation minimum

`FiniteConstrainedProjection` constructs the optimum by projecting the
observation rows onto the actual finite legal span and solving their full
Gram system. Independence can itself be proved from legal unit-observation
interpolants. The corrected projection is feasible and uniquely minimizing.
For every feasible competitor `f`, the exact equality is

\[
\|x-f\|^2=\|x-f_*\|^2+\|f-f_*\|^2.
\]

If `p` is the unconstrained projection, `r=x-p`, and the required head
repair is `t`, the exact inverse correction is

\[
\|x-f_*\|^2=\|r\|^2+
b^T G_{\rm projected\ observations}^{-1}b.
\]

The new complete optimum comparison for any contractive head map is

\[
\boxed{\|r\|^2+\|Qr\|^2\le E
\le\|r\|^2+C^2\|Qr\|^2\le(1+C^2)\|r\|^2,}
\]

provided an actual legal repair `t` has `Qt=Qr` and `||t||<=C||Qr||`.
The repair norm bound is an explicit hypothesis; the concrete Möbius
interpolation operator and its proposed `O(H)` norm constant are not
formalized by this generic comparison. No asymptotic support schedule or
optimal-energy decay is inferred.

## 5. Verification evidence and literature scope

The coherent core passed `job_qUUJlQU8etUt84mBcPMDDxX4qnrwroTk`, exit 0.
The final extended source and seven decisive axiom audits passed
`job_urIUhfy_-9V-zLyB7PBUWcc-UitqTJhF`, exit 0.
The decisive declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`. Their explicit local arithmetic hypotheses remain visible in
the declaration types and are not discharged by an axiom audit.
No `sorry`, `admit`, project-local axiom, unsafe declaration, or exact
`import Mathlib` is added. One final publication checkpoint validates the
separate modules and their reverse dependents; its terminal result is
recorded in the delivered markdowns. No separate full-project build is claimed.

Wolfram checked the exact compact charge identity for cutoffs 1--40 and a
rational constrained-Gram feasibility/Pythagorean diagnostic, returning
zero mismatches. These checks do not prove an asymptotic arithmetic provider.

Primary sources inspected:

- Ehm, *On certain Gram matrices and their associated series*,
  https://arxiv.org/abs/2405.06349 : context for complete quadratic forms.
- Bettin--Conrey--Farmer, *An optimal choice of Dirichlet polynomials for the
  Nyman--Beurling criterion*, https://arxiv.org/abs/1211.5191 : its optimal
  asymptotic assumes RH and a reciprocal zeta-derivative moment hypothesis.
- Báez-Duarte, *A strengthening ... 2*, https://arxiv.org/abs/math/0205003 :
  conditional damped approximants, not an unconditional provider here.

The newly checked geometry and scalar consumers follow the supplied
arguments and elementary Hilbert/Abel reasoning; no novelty claim is made.

## 6. Next arithmetic task

Estimate the complete actual normalized moment strongly enough to prove the
strict feedback budget above, or prove actual source tightness directly.
Alternatively construct legal cumulative trials with the full signed budget,
relative negative excursion control, and vanishing normalized signed numerator.
The finite spectral realization and its asymptotic geometric assembly no
longer need to be supplied as assumptions. The concrete Möbius repair cap
remains a useful separate finite formalization task.

## 7. Canonical envelope and cofinal arithmetic consumer

The selected sequence-to-RH assembly was already completed in
`257c85b767c95f18a1e171f1e7d2aec1e057ee41`, which supersedes `52ec`.
This continuation reuses those checked declarations.

Define the literal complete-tail envelope
\[
\sigma_n=S_n+\frac1{n+1}.
\]
The actual optimizer-tail limit proves internally that `sigma_n>0`,
`S_n<=sigma_n`, `sigma_n->0`, and eventually `sigma_n<1`.
Finite initial exceptions in the double-log normalization are harmless.
No decay rate is asserted. The separate head-displacement limit
`J_n->delta` is proved by the retained exact identity `T_n=J_n+S_n`.

With
\[
M_n=\sum_iw_{n,i}\log(1+\log(1+\lambda_{n,i})),\qquad
D_n=\log(1+\log(1/\sigma_n)),
\]
the unconditional literal-source obstruction is now
\[
\forall c<\delta,\qquad c<M_n/D_n\quad\text{eventually}.
\]
Its declaration is `compactSpectrum_canonical_doubleLog_lower_floor`.
Every eigenvalue and source weight of the full actual stage is included.

The new consumer
`riemannHypothesis_of_actual_compactSpectrum_cofinal_canonical_feedback`
requires only a cofinal sequence `k_n->infinity`, a fixed `theta<1`,
a remainder `E_n->0`, and the OPEN arithmetic budget
\[
\frac{M_{k_n}}{D_{k_n}}\le E_n+\theta T_{k_n}
\quad\text{eventually}.
\]
Thus the previous four envelope hypotheses are discharged by actual
geometry, and the moment budget need hold only cofinally.
The inequality is not proved: geometry establishes the lower obstruction,
not this strict upper feedback bound. Actual complete-source tightness is
also still open. Neither `S_n->0` nor PNT charge cancellation implies it.
The RH-to-density converse remains a separate formalization gap.

The coherent extension and decisive axiom audits passed
`job_py6zVcoptQjuKlscrXcWI7c75FA4TYOO`, exit 0; the extension's decisive
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
Final publication uses the affected-module checkpoint, not a separate
full-project build.
