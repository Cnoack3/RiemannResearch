# Bagchi audit and exact Q dilation energy

Date: 18 October 2026.

## Sources and scope

The source read in full is Bhaskar Bagchi, *On Nyman, Beurling and
Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis*,
Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), 137–146,
https://arxiv.org/abs/math/0607733. The uploaded arXiv PDF has a misleading
2003 header; the bibliographic publication year is 2006.

Bagchi supports the discrete criterion, its squarefree refinement, and the
integer-dilation strategy. The Q estimates below are an elementary quantitative
extension developed in this audit; no claim of priority is made.

For the integrability criterion also consult J.-F. Burnol, *On an analytic
estimate in the theory of the Riemann zeta function and a theorem of
Baez-Duarte*, https://arxiv.org/abs/math/0202166, Section 4, especially
Corollary 4.1 and Theorem 4.2. Its discrete Q implication is already formalized
in `ZetaTwoDampedEnergyTransfer.lean`; it is not a new result of this update.

## What Bagchi establishes

Put P(n)=1/[n(n+1)], Q(n)=1/[zeta(2)n²], and g_d(n)=(n mod d)/d,
for positive n. All sequence operators below use f(0)=0.

1. Theorems 1 and 7: RH is equivalent to 1 in the full residue closed span,
   and to totality of the full family in L²(P).
2. Remarks 4 and 8: RH is also equivalent to 1 in the closed span of the
   squarefree conductors. This is target membership, not squarefree totality.
3. Page 138: comparable weights preserve both closure membership and totality.
   In particular P(n) <= zeta(2)Q(n) <= 2P(n). The identity of sequences is a
   bounded invertible map, not an isometry; the Gram matrices change.
4. Theorem 2: the RH-to-closure direction uses two strong limits of damped
   Mobius sums. The finite squarefree support is algebraic, but the analytic
   convergence estimates are substantive.
5. The final paragraph proposes D(L)² asymptotic to
   (2+EulerGamma-log(4pi))/log L. The paper labels this an expectation,
   stronger than RH; it is not an established estimate.

The repository already has finite Bagchi cutoffs, exact squarefree support,
the conditional two-stage closure transfer, full P/Q comparisons, and the
implication from squarefree Q closure to RH. The RH-to-squarefree-closure
analytic provider remains open in Lean. Reading a published proof does not
discharge its formal hypotheses.

## Details that must be preserved when formalizing

Bagchi's normalized dilation is T_m=sqrt(m)S_m, where
S_m f(n)=f(floor(n/m)). Thus

    S_m g_d = g_(md) - g_m/d.

The denominator is the input conductor d. The repository's
`floorDilation_qResidue` already has this correct formula. Its Pareto operator
`hilbertDilation` uses yet another normalization, m*S_m; these definitions
must not be conflated.

Squarefree conductors are preserved by this formula when m is squarefree and
coprime to d. General integer dilations do not preserve the squarefree span.
Indeed the continuous four-site functional f(4)-f(3)-f(2)+f(1) annihilates
every squarefree atom, but takes value -1 on g_4. It also annihilates the
constant 1. This explains why squarefree non-totality does not contradict
Bagchi's squarefree RH criterion. Such witnesses already exist in the project.

Two harmless overstatements in the printed analytic proof require explicit
qualifications:

- H_epsilon(s) tends to 1/s almost everywhere on the critical line. At a zero
  of zeta on that line, H_epsilon(s)=0 for positive epsilon under RH. The
  exceptional zeros form a null set, so dominated convergence still applies.
- The displayed zeta-ratio bound on page 141 cannot hold throughout the closed
  half-plane near the pole at s=1. Restrict it to Re(s)=1/2, as required by the
  proof, or exclude a neighborhood of the pole. Keep the rational prefactor
  before making that restriction.

## Exact dilation energy and a sharper bound

Define the complete quotient-block mass

    B_m(k) = sum_(0<=r<m) Q(mk+r).

The block at k=0 is included; its energy vanishes because f(0)=0. The exact
identity is

    ||S_m f||_Q² = sum_(k>=1) B_m(k)|f(k)|².

Since Q(mk+r)<=Q(k)/m² for k>=1, one gets B_m(k)<=Q(k)/m and therefore

    ||S_m f||_Q² <= ||f||_Q²/m.

This improves the former equivalent-weight estimate 2/m. The complete
remainder is retained:

    ||f||_Q²/m - ||S_m f||_Q²
      = sum_(k>=1) [Q(k)/m - B_m(k)]|f(k)|².

Every summand is nonnegative. For positive k the coefficient also equals

    (1/zeta(2)) sum_(0<=r<m)
      r(2mk+r) / [m²k²(mk+r)²].

The constant 1/m is optimal: sequences supported at a single coordinate k
have squared-norm ratio B_m(k)/Q(k), tending to 1/m as k tends to infinity.
For m>1 and nonzero f the inequality is strict, although the operator norm
is attained only as a supremum. The formal declaration for the operator norm
in this update proves the upper bound; this last optimality argument is
recorded here as an ordinary mathematical proof.

## Quantitative recovery of the Pareto geometry

The exact splitting

    1/n² = 1/[n(n+1)] + 1/[n²(n+1)]

and the telescoping Pareto block sum give

    m B_m(k) - P(k)/zeta(2)
      = (m/zeta(2)) sum_(n=mk)^(m(k+1)-1) 1/[n²(n+1)].

Because n>=mk in this block, the right side lies between zero and

    1/[m zeta(2) k²(k+1)] = [Q(k)-P(k)/zeta(2)]/m.

Summing against |f(k)|² retains every block and yields

    0 <= m||S_m f||_Q² - ||f||_P²/zeta(2)
      <= [||f||_Q² - ||f||_P²/zeta(2)]/m
      <= ||f||_Q²/(2m).

Thus normalized Q dilation energies converge to the Pareto quadratic form,
uniformly on Q-bounded sets. Weighted Cauchy–Schwarz also gives the bilinear
bound

    |m<S_m f,S_m g>_Q - <f,g>_P/zeta(2)|
      <= ||f||_Q ||g||_Q/(2m).

The bilinear statement and its finite-Gram consequences are mathematical
corollaries recorded for future formalization, unless separately listed in
the checked declaration ledger.

## Why dilation alone does not prove RH

S_m 1 is the tail indicator 1_(n>=m), not a nonzero constant. Consequently,
for a fixed legal trial F,

    ||S_m(1-F)||_Q² / ||S_m 1||_Q² -> ||1-F||_P².

This follows by applying the preceding limit to 1-F and 1, with
||1||_P²=1. Dilation shrinks the absolute error and target together. The
normalized vectors sqrt(m)S_m f are bounded and weakly tend to zero, while
their squared norms tend to ||f||_P²/zeta(2). This describes energy moving
to the tail, not convergence to the constant.

For finitely many squarefree conductors d, choosing m to be a new prime
preserves legality of all packets g_(md)-g_m/d and transfers their finite
Gram geometry. Any RH construction using this fact must also control the
constant target and signed interactions between packets at different scales.

## RH-focused next obligations

The damped discrepancy has the exact arithmetic form

    F_epsilon(n) = sum_(k<=n) product_(p|k)(1-p^(-epsilon))
                  - n/zeta(1+epsilon).

It equals the pointwise damped squarefree residue sum
-sum_d mu(d)d^(-epsilon)g_d(n). Burnol's criterion, already transferred in
Lean, says finite Q-energy for arbitrarily small positive epsilon is enough
to imply RH; no uniform norm bound is required. This remains a substantive
arithmetic condition. It is not supplied by pointwise convergence or CRT.

Priorities:

1. Prove complete finite energy for a sequence of positive dampings tending
   to zero, or another already identified sufficient arithmetic estimate.
2. For the squarefree optimizer approach, prove the needed signed correction
   decay or an equivalent cofinal energy estimate. Finite Gram improvements
   alone do not provide it.
3. Formalize Bagchi's RH-dependent analytic providers to complete the formal
   converse: the truncated reciprocal-zeta bound and critical-line domination
   for both strong limits. This formalizes a known equivalence; it does not
   establish RH unconditionally.
4. Use the new exact Q/P block comparison to study signed cross-scale packets,
   while retaining their target normalization and full infinite error.

No proof of RH and no unconditional vanishing approximation error is claimed.

## Lean declaration ledger

`QFloorDilationEnergy.lean` contains the new unconditional results. Its
assumptions are only m>0 and membership in the actual Q Hilbert space, plus
k>0 in the individual positive-block lemmas.

- `floorDilation_norm_sq_eq_blocks`: exact full infinite energy.
- `floorDilation_norm_sq_defect`: exact full remainder from the 1/m bound.
- `floorDilation_norm_sq_le_sharp`, `floorDilation_opNorm_le_sharp`: improved
  quadratic and operator-norm upper bounds.
- `qBlockWeight_pareto_defect_eq`: exact finite Q/P block remainder.
- `floorDilation_pareto_defect_eq`, `floorDilation_pareto_defect_le`,
  `floorDilation_pareto_defect_le_half`: full exact difference and quantitative
  estimates, with every infinite tail included.
- `floorDilation_normalized_energy_tendsto`: normalized Q energy tends to
  the Pareto energy divided by zeta(2).
- `floorDilation_relative_energy_tendsto`: the corresponding relative-energy
  limit against the dilated constant; it prevents interpreting the absolute
  contraction as vanishing relative approximation error.

The elementary optimality proof, weak-convergence explanation, bilinear
extension, and fresh-prime finite-Gram discussion above are mathematical
arguments in this record, not additional Lean declarations in this update.
Final project acceptance is the server checkpoint, not the isolated snippets.
