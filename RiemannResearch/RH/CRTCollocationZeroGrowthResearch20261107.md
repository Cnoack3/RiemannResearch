# CRT collocation, complete leakage, and zeta-zero obstructions

7 November 2026. Continuation of the user-provided
`CRT_Collocation_and_Zero_Growth_2026-11-06.md`.

## Status and primary sources

This development establishes the actual finite full-conductor collocation
construction, exact complete-Q energy and Parseval identities, and conditional
connections to Mathlib's `RiemannHypothesis`. It does **not** prove the required
bound on the canonical collocation norms, or RH.

The primary published source is B. Bagchi, *On Nyman, Beurling and Baez-Duarte's
Hilbert space reformulation of the Riemann hypothesis*, Proceedings of the
Indian Academy of Sciences, Mathematical Sciences **116** (2006), 137–146,
[DOI 10.1007/BF02829783](https://doi.org/10.1007/BF02829783),
[author-paper PDF](https://repository.ias.ac.in/968/1/307.pdf).
Theorem 1 and the equivalent-weight observation supply the interpretation of
the full residue closure. The Mellin calculations in Theorem 2 and the proof
of Theorem 5 supply the zero-annihilator strategy. They do not establish a
uniform inverse bound for the new collocation matrix.

A preceding published source is L. Báez-Duarte, *A strengthening of the
Nyman–Beurling criterion for the Riemann hypothesis*, Rendiconti Lincei,
Matematica e Applicazioni **14** (2003), 5–11,
[preprint math/0202141](https://arxiv.org/abs/math/0202141).
This is background for the restricted discrete approximation criterion, not a
provider for the remaining collocation growth hypothesis.

The finite construction and the quantitative CRT proposal originate in the
user's handoff. No claim of historical novelty is made. Existing project
machinery reused here includes the actual Q Hilbert space, physical difference
operator, complete divisor-wavelet basis, divisor-test totality, weak Hilbert
compactness, full inverse-Gram projections, and the actual Mellin functional.

## 1. Objects and the finite construction

Put Z = zeta(2), Q(n) = 1/(Z n^2) for positive n, and anchor all sequences at
zero at n = 0. Let g_m(n) = fractional_part(n/m), with **all** conductors
allowed. For an integer L >= 2, define

- V_L = span{g_m : m divides L}; g_1 = 0.
- C_L = span{1_{a divides N} : a divides L}, the finite gcd-cell space.
- T_L = the Q-orthogonal projection onto C_L.
- a_L = 1_{L divides N} and h_L = 1 - a_L.

`QCRTFiniteCollocation.lean` proves that T_L restricted to V_L is injective,
and that its image is exactly

    {h in C_L : <h,a_L>_Q = 0}.

In particular there is a **unique actual legal vector** F_L in V_L satisfying
T_L F_L = h_L. The Lean definition `canonical` chooses the unique solution;
it does not postulate a solution or an invertible matrix. For every a dividing L,

    <F_L,1_{a divides N}>_Q = 1/a^2 - 1/L^2,
    E_Q[F_L(aN)] = 1 - a^2/L^2.

This is the conditional-moment system in the handoff. It is different from the
orthogonal-projection normal equations; F_L is not asserted to minimize the
approximation error.

The proof uses D = I-S, where S is the anchored physical backward shift.
The existing project verifies that S is a contraction and D is injective.
The reusable module `Analysis/FiniteAccretiveCollocation.lean` keeps the identity

    2<f,Df> = ||Df||^2 + ||f||^2 - ||Sf||^2.

Thus <f,Df> = 0 forces f = 0. Finite-dimensional injectivity then gives
surjectivity of the collocation system. No quantitative lower singular-value
bound is obtained from this finite-dimensional argument.

## 2. Exact complete error and arithmetic Parseval

Let z_L = F_L-h_L = (I-T_L)F_L and V(L) = ||z_L||_Q^2. The checked identities are

    ||1-F_L||_Q^2 = L^(-2) + V(L),
    ||F_L||_Q^2 = 1 - L^(-2) + V(L).

Every norm contains the complete infinite Q tail.

Write W_r = sum_{a|r} mu(r/a) a^2 1_{a divides N}, so that
||W_r||_Q^2 = J_2(r). The existing divisor Hilbert basis supplies completeness;
the new `QCRTLeakageParseval.lean` proves the Hilbert-space inversion

    sum_{r|L} W_r = L^2 a_L,

and the exact low coordinates

    <F_L,W_r>_Q = 1_{r=1} - J_2(r)/L^2       (r divides L).

Consequently, for Psi_r = W_r/sqrt(J_2(r)),

    <F_L,Psi_r>_Q = 1_{r=1} - sqrt(J_2(r))/L^2.

The normalized display follows by scaling the checked unnormalized formula;
the persisted theorem uses the unnormalized basis. Most importantly, the
complete series identity itself is checked:

    V(L) = sum_{r not dividing L} |<F_L,W_r>_Q|^2/J_2(r).

For L = lcm(1,...,M), this includes both primes larger than M and excessive
powers of primes at most M. No squarefree truncation or omitted prime-power
remainder is used.

## 3. Bounded leakage forces vanishing optimal error and RH

`QCRTBoundedCriterion.lean` proves the following sufficient condition:

    M_j -> infinity, M_j >= 2,
    V(lcm(1,...,M_j)) <= C for every j, for some finite C >= 0
        implies RiemannHypothesis.

The more general statement allows any cutoff sequence L_j -> infinity for
which each positive integer eventually divides L_j.

The key theorem is more general still: bounded vectors in the actual full
legal closure, whose inner products against every divisibility indicator
tend to those of 1, force 1 into that closure. The proof extracts a weak
subsequence **inside the closed legal space** and uses the already proved
totality of all divisibility indicators to identify its limit with 1.

This supplies the missing implication from a norm bound to the desired
projection limit; it is not an inference from the existence of a CRT limit.
It immediately makes the existing full inverse-Gram candidates converge in
the complete Q norm to 1. The LCM tower also exhausts the full legal span, and
the actual orthogonal projections onto V_{lcm(1,...,M)} converge to the full
legal projection unconditionally. Under the bounded-canonical hypothesis,
their complete squared errors tend to zero.

The final RH implication uses the project's existing
`QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure`, whose
conclusion is Mathlib's RH. No converse RH-to-density hypothesis is inserted.
This is a **conditional research reduction**. Its domain-specific hypothesis
is still Open: boundedness of the actual canonical family on a cofinal
subsequence. Neither finite solvability nor weak compactness proves that bound.

The corresponding P-error conclusion follows on paper from equivalent weights
and finite-support exhaustion. This addition checks the Q projection errors
explicitly; it does not add a separately named theorem about P LCM minimizers.

## 4. Exact zero obstruction acting only on leakage

Let ell_s be the existing actual continuous Mellin functional `qMellinContinuous`
on the real Q Hilbert space, with complex values, for Re(s)>1/2. Define the
actual continuous linear map and its norm

    tailMellin(L,s) = ell_s composed with (I-T_L),
    K_L(s) = ||tailMellin(L,s)||.

These are definitions using actual operators, not an assumed detector.
At a zeta zero s != 1 with Re(s)>1/2, the project Mellin residue identity gives
ell_s(F_L)=0 and ell_s(1)=1/s. The new checked signed balance is

    1/s = ell_s(a_L) - ell_s(z_L).

Since T_L z_L = 0, the checked bound is

    1/|s| <= |ell_s(a_L)| + K_L(s) sqrt(V(L)).

This isolates complete leakage from the multiples-of-L endpoint. In
particular, if the right-hand budget tends to zero for every s in the open
right half of the critical strip, RH follows. The Lean theorem
`riemannHypothesis_of_vanishing_mellin_budget` leaves precisely that budget
convergence as its domain-specific hypothesis.

### Paper derivation of the explicit arithmetic rate: not yet formalized here

Let beta=Re(s) lie in (1/2,1),

    kappa_s(n) = integral from n to n+1 of x^(-s-1) dx,
    u_s(n) = conjugate(kappa_s(n))/Q(n),
    D_t(L) = sum_{n>=1, n not dividing L} n^(-t),   t>1.

Work in the complexification of the real Hilbert space when using u_s. The
real T_L extends by projecting real and imaginary parts separately. The
bounds |u_s(n)| <= Z n^(1-beta) and gcd(n,L)<=n imply, with
k_L(n)=u_s(gcd(n,L)),

    ||u_s-k_L||_Q^2 <= 4 Z D_{2 beta}(L).

The error vanishes at every divisor of L; elsewhere each of its two summands
has modulus at most Z n^(1-beta). Since k_L is gcd-measurable and T_L is the
best approximation in that space, this gives

    K_L(s) <= 2 sqrt(Z D_{2 beta}(L)).

Also, absolute summation over multiples of L gives

    |ell_s(a_L)| <= zeta(beta+1) L^(-beta-1).

Together with the checked identity, these would yield the leakage-only bound

    1/|s| <= 2 sqrt(Z D_{2 beta}(L)) sqrt(V(L))
              + zeta(beta+1) L^(-beta-1).

This has a different endpoint constant from the handoff's original
residual-norm inequality. It is not claimed to be uniformly numerically
smaller. The benefit is that it measures only the orthogonal leakage.

Every n<=M divides L_M=lcm(1,...,M), so the elementary integral estimate gives

    D_{2 beta}(L_M) <= M^(1-2 beta)/(2 beta-1).

A zero with real part beta would therefore force sqrt(V(L_M)) to grow at
least as a positive constant times M^(beta-1/2), eventually. A cofinal
subpolynomial bound in M would exclude every such zero. This recovers the
paper-level zero-sensitive direction in the handoff. A polylogarithmic bound
in L_M is a different, much weaker statement and does not close this argument.

The actual K_L inequality and Mellin endpoint rate are not specialized in the
new Lean source. The stronger subpolynomial criterion must not be reported as
newly kernel-checked from this work. The remaining formalization is identified
below, separately from the genuinely open arithmetic growth question.

## 5. Why the present energy estimate does not control leakage

The exact checked contraction identity for the canonical lift is

    ||D F_L-h_L||_Q^2 + (||F_L||_Q^2-||S F_L||_Q^2)
       = ||h_L||_Q^2 = 1-L^(-2).

Combining it with the complete norm identity gives the further checked equality

    ||S F_L||_Q^2 = V(L) + ||D F_L-h_L||_Q^2.

Thus V(L) occurs with coefficient one in both primitive and shifted energy.
It cancels from the contraction defect. A bound on that defect supplies no
bound on V(L) through these identities alone. The equality is preserved in
the formalization; no uncontrolled term is silently dropped.

This is not a counterexample to boundedness of the canonical family. Proving
or disproving that boundedness remains an arithmetic research problem.

## 6. Wolfram full-period computations

Wolfram Language was used to reconstruct the actual finite moment matrices.
For a,m dividing L, put k=m/gcd(a,m). The entries used were

    B(a,m) = (1/(Z k^2)) sum_{r=1}^k fractional_part(a r/m) zeta(2,r/k),
    t(a) = 1-a^2/L^2,

with a ranging over proper divisors of L and m over divisors greater than one.
The coefficients solve Bc=t. For any L-periodic H, the complete expectation
was evaluated as

    E_Q[H] = (1/(Z L^2)) sum_{r=1}^L H(r) zeta(2,r/L).

This retains the entire infinite physical tail analytically. Arbitrary
precision numerical values, rounded here, were:

| L | Number of coefficients | Complete ||1-F_L||_Q^2 | Complete ||F_L||_Q^2 |
|---:|---:|---:|---:|
| 2 | 1 | 0.250000000000000 | 0.750000000000000 |
| 4 | 2 | 0.146642956733035 | 1.021642956733035 |
| 6 | 3 | 0.065473017740848 | 1.009917462185292 |
| 12 | 5 | 0.082601564453877 | 1.068712675564988 |
| 60 | 11 | 0.053729291633512 | 1.053173736077957 |
| 420 | 23 | 0.036804379080269 | 1.036793041211788 |
| 840 | 31 | 0.046198090098666 | 1.046195255631545 |
| 2520 | 47 | 0.029984987806915 | 1.029984672866124 |

The earlier handoff values were reproduced and extended. At L=420,840,2520,
the numerical period minima are approximately -1.2510,-1.5851,-2.7033, so a
positivity-based explanation should not be presumed. The residual energy is
not numerically monotone. None of these floating-point observations is a
Lean theorem, interval certificate, or asymptotic bound.

## 7. Continuation obligations, in priority order

1. **Open arithmetic growth:** prove a finite uniform bound for V(L_M) along
   a cofinal subsequence. This would immediately apply the checked RH theorem.
   A weaker subpolynomial growth bound is enough for the paper-level
   zero-sensitive route once its analytic bridge is formalized.
2. **Open formalization of a paper-proved analytic estimate:** construct the
   actual complexified gcd sampler for the existing Mellin witness, prove its
   weighted norm estimate, and obtain K_L(s)<=2 sqrt(Z D_{2 beta}(L)). Keep the
   physical Q normalization and both real and imaginary parts explicit.
3. **Open formalization of an elementary endpoint/rate:** prove the absolute
   multiples-series estimate and the LCM p-series tail bound. Combine these
   with the checked exact Mellin balance to obtain the explicit zero-growth
   theorem, without adding either estimate as a hidden provider.
4. **Arithmetic rather than purely functional-analytic work:** study the
   inverse finite collocation matrix on the actual target t_L. Uniform bounds
   on the full operator are stronger than necessary. Retain signed arithmetic
   cancellations and use full-tail matrix entries.
5. **Sharper published-input route:** prime-distribution estimates can sharpen
   the divisor tail beyond the crude n>M estimate. This only improves the
   conditional zero obstruction; it still does not bound the canonical lift.

All conditional results retain their hypotheses. No assertion is made that
RH implies boundedness of this particular collocation family.

## 8. Verification and persistence

The implementation is split by mathematical responsibility:

- `Analysis/FiniteAccretiveCollocation.lean`: reusable finite solvability and
  exact contraction energies.
- `RH/QCRTFiniteCollocation.lean`: actual full-conductor construction,
  conditional image, moments, and full energy identities.
- `RH/QCRTLeakageParseval.lean`: arithmetic Hilbert inversion and full leakage.
- `RH/QCRTBoundedCriterion.lean`: weak compactness, LCM exhaustion, optimal
  projection limits, and conditional RH.
- `RH/QCRTZeroObstruction.lean`: actual Mellin map, signed balance, and
  leakage-only zero obstruction.

Before final checkpoint, the combined theorem candidate passed server job
`job_xnrn6F37zEQdZbGd1EwH_SrpUw8S45K6` (server-reported verification 6.963 s).
Its axiom audit for the bounded-LCM RH implication, Mellin obstruction,
vanishing-budget RH implication, and Parseval identity reported only
`propext`, `Classical.choice`, and `Quot.sound`. These are foundations, not a
certificate that the local growth hypotheses hold. The actual Parseval
module separately passed `job_GQ6aKB-vbM_Y-9-22kDIjCgBXgCtcQrB` (5.479 s).

The actual bounded-criterion module, including direct LCM projection errors,
passed `job_1HxFm0Iw7xddW9niMEZk19QAnw-FU7BB` (7.385 s). The actual
Mellin module passed `job_53lqbV5Tc1sh6Ts4u31Q4AW9CVhnQZ7I` (6.908 s).
Explicit owning-module and tactic imports were then added for the final
server validation. Final publication must use `agent_workspace_checkpoint` with
push enabled and wait for its successful terminal validation. A successful
snippet alone does not certify the final repository delta. The final answer
records that checkpoint's job, scope, and exact published commit.

The active retained workspace is
`ws_mwWauOIKeaTQFsXlLf9olVQpDUYrLPst`, based initially on
`33e589172ac2e2f4e1ee4bbb63bced686ba04bee`.
Workspace-opening elapsed time was not recorded and is not reconstructed.
Queue/wait time and server verification time must be reported separately;
no cache, disk, or networking cause is inferred from an end-to-end delay.

## Appendix: reproducible Wolfram Language experiment

```wolfram
(* Full-tail numerical CRT collocation. These are arbitrary-precision
   experiments, not interval certificates or Lean proofs.
   The period weights sum all physical Q tails using Hurwitz zeta. *)
ClearAll[crtCollocation];
crtCollocation[ell_Integer, precision_Integer : 40] /; ell >= 2 := Module[
  {ds, rows, cols, z, mat, rhs, coeff, vals, weights, err, norm},
  ds = Divisors[ell];
  rows = Most[ds];
  cols = Rest[ds];
  z = N[Zeta[2], precision];
  mat = Table[
    With[{k = m/GCD[a, m]},
      N[Sum[FractionalPart[a r/m] Zeta[2, r/k], {r, 1, k}]/(z k^2),
        precision]],
    {a, rows}, {m, cols}];
  rhs = N[1 - rows^2/ell^2, precision];
  coeff = LinearSolve[mat, rhs];
  vals = Table[Sum[coeff[[i]] FractionalPart[n/cols[[i]]],
      {i, Length[cols]}], {n, 1, ell}];
  weights = Table[N[Zeta[2, n/ell]/(z ell^2), precision], {n, 1, ell}];
  err = Total[weights (1 - vals)^2];
  norm = Total[weights vals^2];
  <|"L" -> ell, "Dimension" -> Length[cols], "ErrorSquared" -> err,
    "NormSquared" -> norm, "Leakage" -> (err - 1/ell^2),
    "MinimumOnPeriod" -> Min[vals],
    "MomentResidualInfinityNorm" -> Max[Abs[mat.coeff - rhs]],
    "EnergyIdentityResidual" -> (norm - err - 1 + 2/ell^2)|>
];
crtCollocation /@ {2, 4, 6, 12, 60, 420, 840, 2520}
```
