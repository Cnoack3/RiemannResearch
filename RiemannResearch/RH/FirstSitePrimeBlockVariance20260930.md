# Three-series audit and exact weighted prime-block continuation (2026-09-30)

## Independent verification of the existing continuation

Audited GitHub commit: `1470295a27ba97bb455a4c96be51fe27abdc1cfb`.
Research base: its immediate documentation-only successor
`4f4ede96e4e8fd5167f4f389bf03c64ee47670cc`, which corrects the search target
from reciprocal-prime energy E to the full angular energy Gamma.

The 115-line `Analysis/NonnegativeSeriesTruncation.lean` and 67-line
`RH/ParetoFirstSitePrimeThreeSeries.lean` match the audited commit exactly.
Their source contains no `sorry`, `admit`, project-local axiom, or unsafe
declaration. GitHub returned no combined status entries and no
pull-request-triggered workflow runs; the latter query does not inspect all
possible workflow triggers.

A fresh isolated Lean audit passed, exit code 0, in 21.01 seconds. It checked
the truncation declarations, the exact variance recursion and capacity
identity, and the complete angular channel alternative. All eleven inspected
declarations reported exactly `propext`, `Classical.choice`, and `Quot.sound`.

The full incremental `lake build RiemannResearch --quiet` succeeded on
4f4ede9: 6206 tasks, 19.433 seconds including the dependency cache preflight.
It used matching cached artifacts and reported existing style/header warnings.
This is a successful project build, not a claim of a cache-free rebuild.

The source and exact declaration types distinguish:

- Unconditional deterministic results: clipping, cutoff invariance,
  summability equivalences, and complete finite energy identities.
- Explicit Open provider:
  for every B there exists N with sum_(n<N) min(Gamma_n,1) > B.
  The conditional RH theorem still requires this hypothesis.
- Classical probability interpretation: independent auxiliary symmetric
  signs realize variance increments Gamma_n. The product-space construction
  and the almost-sure three-series theorem are not formalized here.
- The reverse RH-to-capacity direction still requires
  hBaezDuarte : RH -> NaturalApproximation.
  The capacity-to-RH direction has no such analytic hypothesis.

Dan Romik's author's notes, Theorem 10.6, Example 10.7 and Section 16.2,
were inspected directly:
https://www.math.ucdavis.edu/~romik/teaching-pages/mat235a-2013/lecturenotes235A.pdf.
They support the classical symmetric-sign interpretation, not arithmetic
independence. Verdict: the checked deterministic three-series continuation is
a safe research base with its arithmetic provider still Open.

## Exact block identity

Use the original complete weights and signed corrections

    w_n = primeSchurWeight n
    delta_n = factorialPrimeDelta n
    kappa_n = factorialPrimeError n
    U_N = primeSourceBudget N
    X_N = primeCrossBudget N.

For the finite block I=[N,N+k), define

    u = sum_(n in I) w_n delta_n^2
    v = sum_(n in I) w_n kappa_n^2
    x = sum_(n in I) w_n delta_n kappa_n.

The new block scatter S and mean drift H are

    S = sum_(n in I) w_n (kappa_n-(x/u) delta_n)^2
      = v-x^2/u,

    H = U_N u/(U_N+u) (x/u-X_N/U_N)^2.

Real division by zero is used consistently at an empty block source.
The exact identity, for N>0 and every k including zero, is

    sum_(n in I) Gamma_n = S + H.

Both summands are nonnegative. This gives the unconditional block lower
bound sum Gamma >= S; the discarded term is exactly H, not an unrecorded
correlation. The equality keeps the complete historical correlation in H.

For u>0 the internal scatter is the full ordered-pair square:

    S = (1/(2u)) sum_(m,n in I)
          w_m w_n (delta_m kappa_n-delta_n kappa_m)^2.

No prime Schur pivot or factorial source is replaced by a coarse weight.

## A concrete two-row lower bound

For any distinct rows a,b in the block, set

    B(a,b) =
      w_a w_b (delta_a kappa_b-delta_b kappa_a)^2 /
      (w_a delta_a^2+w_b delta_b^2).

The unconditional certificate is

    0 <= B(a,b) <= S <= sum_(n in I) Gamma_n.

A nonprime row has zero weight; its certificate is zero. The denominator
is the two-row source energy, not the larger source energy of the whole block.
The generic two-row regression identity retains the exact additional
slope square before using its nonnegativity for the bound.

The entire screened correction remains inside kappa. Its existing identity is

    kappa_n = inner(tailInnovation(n+1), infiniteCoprimeCertificate(2!))
              + sum_(r<n) factorialPrimeCrossGram n r.

Those signed row sums are squared only after being kept together.

At prime rows, eta_n=schurEta(n+1)=delta_n+kappa_n. Accordingly the new
`primeBlockVariance_eq_survivor_scatter` rewrites S exactly as

    S = sum_(n in I) w_n
          (eta_n-(1+x/u) delta_n)^2.

Thus growth of the factorial source alone cannot produce a scatter lower
bound. The aligned choice kappa=-delta has zero survivor, zero scatter and
zero angular innovation even with divergent source energy. An actual
arithmetic estimate must control separation of the screened survivors.

## Complete dyadic alternative and remaining provider

Let S_j and H_j be S and H on [2^j,2^(j+1)). Exact finite telescoping gives

    W_(2^J) = sum_(j<J) S_j + sum_(j<J) H_j,

    C_(2^J+1) = C_1 + R_(2^J)
                + sum_(j<J) S_j + sum_(j<J) H_j + J_(2^J).

The initial capacity, mean channel and every nonprime gain are retained.
All physical tail and Gram contributions in the original capacity remain in
that quantity; these finite algebraic decompositions introduce no tail cutoff.

The new unconditional equivalence is

    Summable Gamma <-> Summable S_j AND Summable H_j.

Consequently the complete first-site alternative is

    C_N -> infinity
      <-> R_N does not tend to zero
          OR S_j is nonsummable
          OR H_j is nonsummable
          OR the nonprime gain series is nonsummable.

Scatter divergence alone is sufficient but is not asserted necessary.

**Conditional research reductions. Open:** a nonsummable nonnegative
sequence b_j with b_j <= S_j implies RH. The lower comparison may also be
supplied by the already established two-row certificate. In particular,
choosing two distinct rows a_j,b_j in [2^(j+1),2^(j+2)) reduces a sufficient
arithmetic task to the explicit series

    sum_j B(a_j,b_j) = infinity.

The omitted first dyadic block has only one row and finite energy. The
membership and distinctness hypotheses are explicit in
`riemannHypothesis_of_dyadic_prime_pair_separation`; the sole remaining
growth provider there is nonsummability of the actual weighted determinant
series. No such nonsummability has been established.

This carries out the corrected fully weighted block research step. It does
not use coarse E nonsummability, invent arithmetic independence, or import an
upper large-sieve estimate as a lower bound.

## Verification of the new results

Wolfram returned exactly 0 for the difference between both sides of the
weighted block merge identity and, separately, the two-row completion.
These are symbolic algebra checks. Lean kernel verification is the decisive
validation of the formal statements.

The new module is `RH/ParetoFirstSitePrimeBlocks.lean`; the scalar merge and
two-row completion lemmas extend `Analysis/WeightedScalarEnergy.lean`.
The complete coherent candidate, including six axiom audits, passed with
exit code 0 in 4.949 seconds. All six audited declarations reported exactly
propext, Classical.choice and Quot.sound, including the exact dyadic
summability equivalence, full capacity identity and conditional pair-separation
RH endpoint. No sorryAx was present in the successful audit.

Final acceptance and publication use the repository checkpoint, which audits
source and validates changed modules plus their local reverse dependents.
