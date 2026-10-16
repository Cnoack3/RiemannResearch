# Exact von Mangoldt–LCM arithmetic: target 2

Date: 16 October 2026.

This development supplies the finite arithmetic part of target 2. Publication
is gated by the server's source audit and Lean validation; the final handoff
records the exact checkpoint result.

## Scope and existing foundations

This addresses research target 2 of
Q_Squarefree_RH_VonMangoldt_LCM_Research_Agenda_2026-10-16.md.

The pinned Mathlib already contains the essential foundations:

- Nat.lcmUpto N is the actual finite LCM of the integers 1 through N,
  with empty LCM equal to one.
- Nat.factorization_lcmUpto gives v_p(C_N) = Nat.log p N for prime p.
- Chebyshev.psi_eq_log_lcmUpto gives psi(N) = log C_N.
- ArithmeticFunction.sum_moebius_mul_log_eq gives the signed divisor identity
  sum_(d|n) mu(d) log d = -Lambda(n).

The new module reuses those checked definitions and results. It does not
redefine the LCM or von Mangoldt function and does not add a duplicate
alias for the existing log-LCM theorem.

## Exact finite identities

Let C_N = lcm(1,...,N). The prime valuation counts exactly the prime powers
that have appeared:
\[
v_p(C_N)=\#\{k\in\{1,\ldots,N\}:p^k\le N\}.
\]

For every positive n,
\[
\log C_n-\log C_{n-1}=\Lambda(n).
\]
For prime p and positive exponent k,
\[
C_{p^k}=p\,C_{p^k-1}.
\]
The running LCM is unchanged at n exactly when n is not a prime power.

The signed summatory formula is
\[
\psi(N)
=-\sum_{d=1}^{N}\mu(d)\log d\,\lfloor N/d\rfloor,
\]
and therefore
\[
\log C_N
=-\sum_{d=1}^{N}\mu(d)\log d\,\lfloor N/d\rfloor.
\]
Natural division is performed before the quotient is cast to the reals.
All coefficients, signs, and the full finite cutoff are retained.

Exponentiation also gives the signed product in the positive reals:
\[
C_N=\prod_{d=1}^{N}d^{-\mu(d)\lfloor N/d\rfloor}.
\]
Negative exponents are integers; no positivity assumption is made about
the Möbius coefficients.

The proof applies Mathlib's exact finite Dirichlet-convolution summation
theorem to the arithmetic function f(d)=mu(d) log d. Its convolution with
the zeta arithmetic function is -Lambda. Thus the summation exchange is
proved by a finite identity rather than by an unproved interchange of
infinite sums.

## Relationship to the RH program

For the damped floor prefix
\[
A_\varepsilon(n)=\sum_{d\le n}
 \mu(d)d^{-\varepsilon}\lfloor n/d\rfloor,
\]
the finite arithmetic needed for its pointwise derivative at zero is
\[
-\sum_{d\le n}\mu(d)\log d\,\lfloor n/d\rfloor
=\psi(n)=\log C_n.
\]
The analytic differentiation theorem belongs to target 3 and is not supplied
merely by this algebraic identity.

This development is unconditional. It provides no global energy estimate,
Hilbert differentiability, RH-to-density analytic provider, or proof of RH.

## Next research tasks

1. Formalize the pointwise damping derivative using the exact signed floor
   identity, then add the reciprocal-zeta centering derivative.
2. Preserve the full signed Taylor remainder and its cross term on finite
   heads before passing to an infinite Hilbert norm.
3. Continue the principal open analytic provider:
   RiemannHypothesis implies DampedHardyApproximation.
4. Match LCM and radical stages to the actual numerical and smooth squarefree
   conductor sets; retain the CRT carry.

## Provenance and verification

Source: the user's research agenda, 16 October 2026.
Classical log-LCM statement: Hong, Qian, and Tan,
The least common multiple of a sequence of products of linear polynomials,
https://arxiv.org/abs/1108.0162v2.
The project proofs reuse the pinned Mathlib revision
51e6992efd06126df61a496bebf8f49482a4e129.
The recovered module passed server file check
`job_j5tdj7MZe2MOjSWy0_4h0WU-KaLzkRE1`: exit code 0, classification success,
all ten declarations checked in 4.839 seconds. The checked source SHA-256 is
`bf7c35106aab842491ec94a4a7cbb2eb5f6be92acc41445fc1d035e75fc93624`.
Axiom inspection of `Nat.cast_lcmUpto_eq_prod_moebius_zpow` returned only
`propext`, `Classical.choice`, and `Quot.sound`. The source scan's
`import Lean.Elab` flag identifies the explicit Omega tactic import.

The earlier checkpoint `job_iYv4b7UfqWZXNVjsOqYYLx0sCl2DSCqy` ended as
interrupted after its worker exited. The recovery publication attempt
`job_J5ygxmV4AuYuVsPu6fewmG6Rpdu9dDJz` encountered integration conflicts
in the shared import list and theorem catalog. Its verified proof source
was preserved and carried unchanged onto current main in a fresh integration
workspace. The final publication checkpoint validates that combined project
before push. GitHub CI is not used.

## Declaration map

| Declaration | Role |
| --- | --- |
| Nat.factorization_lcmUpto_eq_card_prime_powers | Counts the prime powers in each LCM valuation. |
| Nat.log_lcmUpto_succ_sub | Exact successor log-LCM increment. |
| Nat.log_lcmUpto_sub_pred | Positive-index increment with the predecessor. |
| Nat.lcmUpto_prime_pow | Multiplication by the prime at a positive prime power. |
| Nat.lcmUpto_eq_pred_iff_not_isPrimePow | Exact characterization of unchanged LCM stages. |
| Nat.lcmUpto_ne_pred_iff_isPrimePow | Exact characterization of changed LCM stages. |
| Chebyshev.psi_nat_eq_neg_sum_moebius_log_mul_div | Signed summatory Möbius floor identity. |
| Nat.log_lcmUpto_eq_neg_sum_moebius_log_mul_div | Log-LCM version of that identity. |
| Nat.cast_lcmUpto_eq_exp_neg_sum_moebius_log_mul_div | Exponential form, with no discarded terms. |
| Nat.cast_lcmUpto_eq_prod_moebius_zpow | Full product with integer signed exponents. |

The running LCM is generally not squarefree. None of these arithmetic identities
asserts that a prime-power conductor, an LCM conductor, or a divisibility
indicator is a squarefree legal atom.
