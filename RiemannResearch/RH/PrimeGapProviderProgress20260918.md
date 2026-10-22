# Prime-gap provider progress — 2026-09-18

## Scope

The requested full formal proofs of Baker–Harman–Pintz and Järviniemi have
not been completed. This update proves the elementary total-mass provider
for actual primes and the exact dyadic summability implication from the two
remaining quantitative estimates. It introduces no substitute axiom.

## Established results

Let p_n = Nat.nth Nat.Prime n and g_n = p_(n+1) - p_n, cast to the reals.

- The enumeration is strictly increasing, consists of primes, and its
  successor is no larger than any larger prime.
- Mathlib's proved Bertrand theorem yields p_(n+1) <= 2 p_n and g_n <= p_n.
- dyadicIndices X contains exactly the indices with X <= p_n <= 2X.
- For every natural X, sum_{n in dyadicIndices X} g_n <= 4X.
  This includes the last gap even if its right endpoint exceeds 2X.
  The proof clips endpoints at 4X, compares a finite subset with the whole
  telescoping sum, and uses Bertrand to bound selected right endpoints.
- The abstract clipping/telescoping theorem is reusable as
  Analysis.GapEnergy.sum_adjacent_gaps_le.

Thus externalTotalMass is discharged for this actual-prime specialization.
The original general theorem for arbitrary gap families retains its premise.

## Exact conditional continuation

For X > 0, assume the two explicit statements

    g_n <= C X^(21/40)                         for X <= p_n <= 2X;
    sum_{X <= p_n <= 2X, g_n >= X^(9/20)} g_n <= D X^(16/25).

The second exponent uses epsilon = 1/100 in Järviniemi's Theorem 1.2.
Lean proves

    sum_{X <= p_n <= 2X} g_n^3
      <= 4 X^(19/10) + C^2 D X^(169/100),

and hence

    X^(-2) sum_{X <= p_n <= 2X} g_n^3
      <= 4 X^(-1/10) + C^2 D X^(-31/100).

For fixed C,D and these bounds at every X=2^k, Lean proves summability
over k. These are conditional results: hmax and hlarge remain in the
declaration types. A clean axiom report does not discharge such premises.

## Remaining obligations

1. Prove a BHP-strength bound for actual consecutive primes in Lean.
2. Prove the exceptional large-gap mass bound in Lean. The source proof
   uses sieve decomposition and sparse Dirichlet-polynomial estimates;
   its numerical components require formal treatment as well.
3. Connect eventual published estimates to all-scale constants by handling
   the finite initial range.
4. Regroup into a global prime-gap sum, transfer to the complete prime-power
   partition, and connect to actual_remainder_summable_of_external_cubic_gap.

The first two are missing formalizations of published mathematics.
The actual signed arithmetic discrepancy bound is a separate unproved
mathematical target; nothing here establishes it.

## Verification evidence

Ephemeral complete candidate job:
job_Gf5I2DSC4nmurwewt44jivftP4ZcRo55.

The tool returned classification success, exit_code 0, verified true.
The printed axiom dependencies of the six main declarations were only
propext, Classical.choice, and Quot.sound. No sorryAx or project-local
axiom appeared. Final project publication is subject to the checkpoint
reported in the conversation; this note does not pre-claim its success.

## Sources

- Mathlib's Bertrand theorem:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Bertrand.html
- Baker–Harman–Pintz, The difference between consecutive primes, II:
  https://doi.org/10.1112/plms/83.3.532
- Järviniemi, On large differences between consecutive primes, Theorem 1.2:
  https://arxiv.org/html/2212.10965v2

The references support the classical statements and provenance; citing them
does not import their proofs into Lean.
