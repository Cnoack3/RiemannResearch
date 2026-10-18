# Period-210 strict certificate and signed prime-eleven improvement

Date: 18 October 2026.
Source: the explicit rational coefficients and certificate in
`QLatticeRegularizationResearch20261018.md`, published at
`613e867d2b0d9127386a58280995e5d64d2938c9`, and the user's requested
signed-affine continuation. No mathematical novelty claim is made.

## Verified finite result

Write a=1/zeta(2), Q(n)=a/n² for positive integers, g_d(n)=(n mod d)/d,
and Delta F(n)=F(n)-F(n-1), with F(0)=0. The actual Q-Hilbert objective is

    J_lambda(F)=||Delta F-e_1||_Q²+lambda ||F||_Q².

`QPeriod210Certificate.candidate` encodes exactly the fifteen coefficients:

| d | 10000 c_d |
|---:|---:|
| 2 | 9783 |
| 3 | 9770 |
| 5 | 9549 |
| 6 | -8824 |
| 7 | 9426 |
| 10 | -7399 |
| 14 | -5918 |
| 15 | -5955 |
| 21 | -4698 |
| 30 | 7574 |
| 35 | -4122 |
| 42 | 5233 |
| 70 | 2704 |
| 105 | 363 |
| 210 | -6191 |

Every conductor is squarefree and divides 210. The candidate belongs to
`primorialStage 4`, whose period is 210 under the repository's indexing.
It is 210-periodic, its first value is 221089/262500, and its uniform
absolute maximum is 1224169/1050000, attained at n=109.

The complete derivative energy is exactly

    ||Delta F||_Q² = 52823902806611/115762500000000.

The finite head satisfies

    sum_(n=1)^210 F(n)²/n² < 229/250.

The entire tail is retained:

    ||F||_Q² <= a [sum_(n=1)^210 F(n)²/n² + (7/6)²/210].

The normalizer is certified using the first 100 reciprocal squares and
the existing telescoping tail bounds:

    1028/625 < zeta(2) < 329/200,
    6079/10000 < a < 76/125.

The exact signed objective equality precedes the estimate:

    J_lambda(F) = 52823902806611/115762500000000
                 + a(1-2(221089/262500)) + lambda ||F||_Q².

`candidate_strict_certificate` and `candidate_strict_budget` prove

    J_(1/10)(F) < 3715960194137/38587500000000 < 1/10.

`stage_four_strict_budget` also bounds the actual finite-stage minimizer.
All these declarations are unconditional: no arithmetic estimate is hidden
as a theorem hypothesis. Rational finite arithmetic uses `decide +kernel`;
no floating-point evaluation or native-decide assumption is used.

## Stronger signed affine correction

Set v=g_11 and F_plus=F+(1/3)v. It is squarefree legal in `primorialStage 8`,
whose period is 2310. Define the full signed quantities

    q = ||Delta v||_Q² + (1/10)||v||_Q²,
    b = <e_1-Delta F,Delta v>_Q - (1/10)<F,v>_Q.

The derivative cross term is exactly 103519421/2668050000, and
||Delta g_11||_Q²=20/1331. Two additional kernel-checked rational heads are

    sum_(n=1)^210 F(n)g_11(n)/n² < 29/200,
    sum_(n=1)^210 g_11(n)²/n² < 103/1000.

Since |F|<=7/6 and |g_11|<=10/11, the complete mixed tail is bounded above
by (7/6)(10/11)/210 and the complete square tail by (10/11)²/210.
The finite mixed head retains its sign. These estimates prove

    b > 1360133/185281250,
    0 < q < 188040107/8734687500.

`improved_objective_exact` reuses the established affine correction identity:

    J_(1/10)(F_plus) = J_(1/10)(F) - (2/3)b + q/9.

Consequently `improved_strict_certificate` proves

    J_(1/10)(F_plus) < 469/5000 = 0.0938.

This is a genuine improvement at the same positive penalty, using a new
squarefree conductor and the complete primitive cross term.

## Remaining RH-strength arithmetic inequality: Open

For a positive sequence lambda_N tending to zero, one still needs legal
u_N,v_N in stages M_N>=N with

    q_N = ||Delta v_N||_Q² + lambda_N ||v_N||_Q² > 0,
    b_N = <e_1-Delta u_N,Delta v_N>_Q - lambda_N <u_N,v_N>_Q,
    b_N² > q_N [J_(lambda_N)(u_N)-lambda_N].

Then t_N=b_N/q_N gives a strict certificate. For a specified rational t_N,
the exact sufficient inequality retains the rounding remainder:

    b_N²-(q_N t_N-b_N)² > q_N [J_(lambda_N)(u_N)-lambda_N].

The already verified strict-primorial-budget consumer would turn such a
family into squarefree constant closure and the repository's RH implication.
Neither the period-210 certificate nor its period-2310 improvement supplies
this vanishing-penalty provider. It remains Open.

A useful paper-level obstruction explains why the period must grow. If F is
L-periodic and F(0)=0, put delta=Delta F(1). Then Delta F(L+1)=delta, and
the two sites 1 and L+1 alone imply, for lambda>=0,

    J_lambda(F) >= a[(delta-1)²+delta²/(L+1)²]
                >= a/[1+(L+1)²] > 0.

Thus no fixed period can give strict certificates for lambda_N tending to
zero. This last general obstruction is an informal proof in this record,
not a new Lean declaration in the present change.

## Implementation and verification

- `QDifferenceGram.lean`: exact complete-Q derivative Gram and target pairing.
- `QFiniteEnergyBounds.lean`: rigorous zeta brackets, square and signed mixed
  head-plus-complete-tail estimates in the actual Q-Hilbert space.
- `QPeriod210Certificate.lean`: the fifteen coefficients, legality, periodic
  finite checks, exact maximum and derivative energy, and strict budget.
- `QPeriod210AffineCorrection.lean`: complete signed correction and the 0.0938 bound.

The original certificate passed server job
`job_O2VjyAm5KAIjcFXnHIPWY3-xaGjhoW5t` (exit 0, verified true).
The correction and its imported support modules passed server job
`job_1tCcVqZ6daF8AfO2doorD-WyRtLcxYvD` (exit 0, verified true).
Server axiom-inspection job `job_4RG922irdgPAtHc-KPcP0vwFiEZATneV` succeeded
and printed eight selected declarations, including both strict certificates.
All eight depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The printed strict-certificate types have no substantive hypotheses.
Final source audit and publication validation are separate from these checks.
Publication is gated by the Lean-server checkpoint, with `[skip ci]` in the
commit message; hosted CI is not used as verification evidence.
