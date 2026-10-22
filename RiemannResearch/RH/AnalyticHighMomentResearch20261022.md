# Analytic high moments: prime-polynomial theorem and the remaining zeta input

Date: 22 October 2026.

The exact Tsang theorem for the actual zeta argument remains an open
formalization obligation. This development proves its prime-polynomial
mean-value ingredient and the general integral transfer. It does not assert
that the Selberg approximation is available in Lean.

## Prime-polynomial analytic theorem

Let p be an injective finite family of primes bounded by a natural number X,
let a be arbitrary complex coefficients, let k be a natural number, and A ≤ B.
Write P(t)=Σ_x a_x exp(i t log p_x). The new theorem is

\[
\int_A^B |P(t)|^{2k}\,dt
\le (B-A+52X^k)\,k!\left(\sum_x|a_x|^2\right)^k.
\]

There are no zeta, density, moment, simplicity, or RH assumptions in this
statement. The result includes k=0 and empty coefficient families, with Lean's
usual zeroth-power convention. If 52X^k ≤ B−A, the right side is at most
2(B−A) k! (Σ|a_x|²)^k.

The proof has four explicit steps:

1. Expand P^k over tuples of k primes and regroup by the product n.
2. Unique factorization makes every tuple fiber a set of permutations of one
   prime list. Its cardinality is at most k!, giving
   Σ_n |b_n|² ≤ k! (Σ_x|a_x|²)^k.
3. Integrate the complete finite double sum. The exact identity retains the
   diagonal and every signed off-diagonal term, including both endpoints.
4. The repository's proved `Zeta23.MV.mvDiag_thirteen` bounds the two endpoint
   Hilbert forms by 26 Σ_n |b_n|²/δ_n. The proved logarithmic separation
   δ_n=1/(2n) gives the error 52 X^k Σ_n |b_n|².

The generic weighted mean-value error and its exact signed endpoint identity
are in `Analysis/DirichletMeanSquare.lean`. Combinatorics are in
`Analysis/PrimeMomentDiagonal.lean`; assembly and the short-length corollary are
in `Analysis/PrimeDirichletHighMoment.lean`.

## Integral transfer

`Analysis/HighMomentTransfer.lean` proves

\[
\int |S(t+h)-S(t)|^{2k}\,dt
\le 3^{2k-1}\left(\int |P|^{2k}+\int|R(t+h)|^{2k}+\int|R|^{2k}\right)
\]

from the stated decomposition S(t+h)−S(t)=P(t)+R(t+h)−R(t). The primary theorem
requires integrable powers rather than continuity, so jumps in the actual S
function are permitted. Every component bound remains an explicit hypothesis.
Polynomial budget T(CkL)^k and the two remainder budgets T(Ck²)^k give

\[
J_{2k}\le T[9Ck(L+k)]^k.
\]

This is a conditional research reduction when S is intended to be the actual
zeta argument. It does not prove the component estimates.

## Exact target and open obligations

The proposition `TsangHighMomentAsymptotic S` records, without asserting, the
following dyadic form. There exist C>0 and T₀≥3 such that for every T≥T₀,
integer k≥1, and 0<h<1, with L=log(2+h log T),

\[
\left|J_{2k}-\frac{(2k)!}{2^k\pi^{2k}k!}\,T L^k\right|
\le T(Ck)^k\bigl(k^k+L^{k-1/2}\bigr).
\]

C and T₀ precede k,h,T in the quantifiers. The safe all-k upper scale is
T[Ck(k+L)]^k. The scale T(CkL)^k needs a restriction such as k≲L. For fixed
microscopic h=A/log T, the safe bound grows as T(C_A k²)^k.

Open formalization obligations:

- **Open:** define the actual continuously continued zeta argument (or prove
  an equivalent Riemann–von Mangoldt discrepancy interface). Principal
  `Complex.arg` is not this function.
- **Open:** Selberg's high-moment prime approximation, including the actual
  unconditional zero-density provider. `ActualZeroSelbergDensity.lean`
  currently exposes density as an explicit hypothesis.
- **Open:** the prime-variance asymptotic needed for the exact Gaussian main
  term. Chebyshev's prime bound would suffice for a coarse variance upper
  bound, but not the exact main term.
- **Open:** the complementary large-k S(t)=O(log t) estimate and exact
  asymptotic assembly with uniform quantifiers.

STTB Corollaries 1–2 provide, in ordinary mathematics, a remainder bound
T(ω₀k)^(2k) at cutoff X=T^(3/(88k)), with ω₀=exp(12.8471), for
T≥exp(1760000k), uniformly in shifts 0≤u≤1. Its proof requires substantial
Selberg analysis; it is not supplied by finite moment algebra or by the
Montgomery–Vaughan inequality alone.

## Provenance

The statement and analytic decomposition follow K.-M. Tsang,
*Some Ω-theorems for the Riemann zeta-function*, Acta Arith. 46 (1986),
Theorem 4 and Section 4:
https://matwbn.icm.edu.pl/ksiazki/aa/aa46/aa4646.pdf

The explicit Selberg input and reproduced Tsang theorem are in A. Simonič,
T. S. Trudgian and C. L. Turnage-Butterbaugh,
*Some explicit and unconditional results on gaps between zeroes of the
Riemann zeta-function*, Theorem 2 and Section 3:
https://arxiv.org/abs/2010.10675

The Hilbert-inequality ingredient is the existing repository formalization
of Montgomery–Vaughan, *Hilbert's inequality* (1974), with proved constant 13.
The present work combines that provider with finite integration and unique
factorization; no mathematical novelty is claimed.

## Verification record before publication

- Combined proof candidate: `job_b1mERBtaZPfFm_jSPqCcmKiK7p0do4eR`,
  exit 0, verified=true; reported server verification duration 7.100 seconds.
- Standalone imports of the actual four modules and five central axiom audits:
  `job_RRcFxliqlBKvrMMeo2zTbO61l10bm7AN`, exit 0, verified=true;
  reported server duration 17.707 seconds, including the changed-module build.
- All five audits used only `propext`, `Classical.choice`, and `Quot.sound`.
  This does not discharge hypotheses explicitly present in transfer theorems.
- The final publishing checkpoint separately validates the aggregate project
  and changed modules. Its terminal publication result is the final gate.

Timing: the workspace-opening request was batched with independent reads, so
its individual round-trip duration was not measured. An earlier development
job waited about 223 seconds for the worker; that was queue time, not Lean
checking time. Several intervening status requests timed out in transport.
The verification durations above are the server's reported measurements and
are separate from those delays.
