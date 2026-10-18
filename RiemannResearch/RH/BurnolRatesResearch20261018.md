# Burnol 2001: exact rates, Q transfer, and the remaining RH estimate

Date: 2026-10-18.
Source: Jean-François Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, arXiv:math/0103058v2, March 2001; published in *Advances in Mathematics* 170 (2002), 56–70. All 17 uploaded pages were read, with visual checks of the conjugations and finite Gram model.

## Outcome and verification scope

The work sharpens finite polynomial rates and discrete lower-bound certificates. It does not prove RH or an unconditional upper estimate tending to zero.

| Result | Status and exact scope |
|---|---|
| Two-moment Pythagorean identity, lower bound, and attained minimum | Lean: `Analysis/FiniteTwoMomentEnergy.lean`, no domain-specific assumptions |
| Double-root decomposition and cubic target exact minimum | Lean: `RH/BurnolDoubleRootModel.lean`, real finite coefficient space |
| Arbitrary legal finite-candidate cutoff transfer | Lean: `RH/BurnolParetoTransfer.lean`, given `ContinuousCutoffLowerBound` |
| Q cutoff transfer retaining the complete metric correction | Lean: `RH/BurnolQCutoffTransfer.lean`, same analytic input, actual Q norms |
| Polynomial divisibility, complex Parseval interpretation, general vanishing-jet hierarchy, repeated-root factorial formula | Ordinary proofs in `BurnolPolynomialRefinements20261018.md`; not claimed as Lean-verified bridges |
| Fixed finite zero-family second-order bound and improved off-critical Q witness | Ordinary analytic proofs in the two appendices; not yet formalized |
| Burnol analytic lower-envelope provider | Open formal integration; the published theorem is not re-proved in Lean here |
| Unconditional legal constant-approximation upper bound tending to zero | Open RH-level obligation |

The coherent precursor snippet passed in job `job_RRfNCSrLWQum2Udpj-sYGHSgwXWHzUnD`. The final split module imports and axiom inspection then passed on the server in job `job_-PHx92YJ8T3gtaXhaeRbdWnAO9cN6sQC`, exit code 0, `verified: true`. The inspected two-moment identity, cubic exact minimum, and Q correction theorem depend only on `propext`, `Classical.choice`, and `Quot.sound`. Publication remains gated by the final checkpoint of changed modules and their local reverse dependents. No local axiom, proof hole, or RH assumption was introduced into the unconditional coefficient identities. The cutoff-transfer theorems explicitly retain their analytic hypothesis.

## 1. What Burnol proves

With D(lambda) the distance from chi_(0,1] to the span of fractional-part functions {theta/t}, lambda<=theta<=1,

\[
\liminf_{\lambda\downarrow0}D(\lambda)^2\log(1/\lambda)
\ge\sum_\rho\frac{m_\rho^2}{|\rho|^2}.
\]

Each zero is counted once with multiplicity squared. Under RH every nontrivial zero contributes through the critical-line construction; if RH fails, the left side diverges, so this lower bound cannot itself prove RH. The normalized zero-jet Gram matrices tend, for each fixed finite family, to blocks H_m=(1/(i+j+1)); the inverse endpoint entry m^2 explains the improvement over the earlier distinct-zero bound.

The polynomial model is stronger structurally: its jet witnesses span the entire orthogonal complement. In the zeta argument an unmeasured orthogonal component may remain. That is the essential obstruction to converting the model into an RH proof.

## 2. Exact finite refinement of the polynomial model

For Q(z)=(1-z)^2, L=N+2, a=P(1), b=P'(1), and deg P<=L, ordinary Parseval and divisibility identify the minimum with

\[
\boxed{E(N,P)=\frac{|a|^2}{L+1}
+\frac{12|b-La/2|^2}{L(L+1)(L+2)}.}
\]

The Lean coefficient theorem retains the full remainder: for real r_j satisfying sum r_j=a and sum j r_j=b, the energy is the displayed scalar expression plus

\[
\sum_{j=0}^L\left(r_j-\frac a{L+1}
-\frac{12(b-La/2)(j-L/2)}{L(L+1)(L+2)}\right)^2.
\]

In particular,

\[
E(N,1-z)=\frac{12}{(N+2)(N+3)(N+4)},\qquad
E(N,1)=\frac{4N+10}{(N+3)(N+4)}.
\]

`cubic_target_exact_minimum` verifies the first formula as an attained finite coefficient minimum. Burnol's stated first-order theorem only gives N E(N,1-z)->0; the exact formula resolves the cubic scale. The general ordinary proof yields N^(-2r-1) when r is the first uncancelled target jet. This is a refinement of the supplied theorem, with no priority claim over the wider approximation literature.

Faster decay for a vanishing target cannot simply be applied to the RH target 1: changing the target requires a proved reconstruction of the constant and control of its full norm.

## 3. Q transfer with the exact correction

Let P(n)=1/[n(n+1)], Q(n)=1/[zeta(2)n^2], and g_d(n)=(n mod d)/d. For r=1-F,

\[
\zeta(2)\|r\|_Q^2=\|r\|_P^2+
\underbrace{\sum_{n\ge1}\frac{|r(n)|^2}{n^2(n+1)}}_{C(r)}.
\]

If every conductor of F is at most N, the continuous bound L at cutoff 1/N gives the Lean-verified conditional transfer

\[
\boxed{L+C(r)\le\zeta(2)\|r\|_Q^2.}
\]

It applies equally to all-conductor and squarefree subsets. For primorial divisor stages the scale is log L_M, with L_M=product_{j<=M}p_j, not log M. The inclusion of approximation spaces gives lower bounds in this direction; it does not transfer a continuous upper bound to a smaller discrete legal space.

## 4. Further analytic improvements with complete ordinary proofs

For each fixed finite critical-line zero family R and T=log(1/lambda), Burnol's estimates yield

\[
\|\Pi_R(\lambda)\chi_1\|^2=S_R/T+O_R(T^{-2}),
\quad D(\lambda)^2\ge S_R/T-C_R/T^2.
\]

The constants depend on the family, including zero separations. The appendix derives this from his pointwise estimates; it is not a uniform expanding-family assertion.

For a hypothetical zero rho with beta=Re rho>1/2, the actual Q witness gives

\[
\|1-F\|_Q^2\ge
\frac1{\zeta(2)\sum_{n\ge1}n^2|n^{-\rho}-(n+1)^{-\rho}|^2}
\ge\frac{2\beta-1}{\zeta(2)|\rho|^2 B(\beta)},
\quad B(\beta)=\sum_{n\ge1}\frac1{n^{2\beta}(n+1)}<1.
\]

The last bound strengthens the elementary global norm-transfer obstruction. `BurnolQWitnessRefinement20261018.md` proves the exact dual norm, Mellin annihilation, finite-tail certification, and the elementary consequence with improvement factor 4 beta/(2 beta+1). These are ordinary proofs, not newly checked Lean statements. Existing `QMellinTransfer.lean` already proves Mellin annihilation and the global bound with its target-dependent metric correction; the cell-compressed norm is the additional analytic estimate here. No dominance over every target-dependent existing correction is claimed.

## 5. Next research steps

1. Formalize the reciprocal-cell representation of the Q Mellin functional and its sharper dual norm, reusing `QMellinTransfer` and the existing Pareto Mellin signature.
2. Establish explicit finite-family Gram perturbation constants. Retain height, multiplicity and separation dependence before considering growing families.
3. Construct arithmetic legal approximants with a complete Q upper error budget. The zero-witness projection supplies only part of the error; the complementary remainder must be retained and bounded.
4. Use the exact repeated-root model as a stress test: if m/sqrt(N)->c, its error tends to 1-exp(-c^2). Fixed-family asymptotics cannot be used uniformly without additional estimates.

The later Bettin–Conrey–Farmer result attains the optimal logarithmic constant under RH and a bound on the negative second moment of zeta'(rho). Those are substantive assumptions, so that result cannot supply the missing unconditional upper bound.

## Sources

- Burnol (uploaded source): https://arxiv.org/abs/math/0103058
- Bettin, Conrey and Farmer (2012/2013): https://arxiv.org/abs/1211.5191
- Repository inputs: `BurnolParetoTransfer.lean`, `QParetoMetric.lean`, `ZetaTwoParetoTransfer.lean`, and `QMellinTransfer.lean`.

Wolfram independently simplified the 2-by-2 moment Gram inverse and confirmed the cubic error expansion 12 N^-3 -108 N^-4 +660 N^-5. Symbolic checks supplement, and do not replace, the proofs.
