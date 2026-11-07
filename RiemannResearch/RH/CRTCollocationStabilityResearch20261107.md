# CRT collocation stability: proved obstructions and the remaining LCM target

7 November 2026. Continuation of `CRTCollocationZeroGrowthResearch20261107.md`.
All statements concern the actual complete inverse-square Q Hilbert space,
Q(n)=1/(zeta(2)n^2), with all conductors, including prime powers.

## 1. A uniform inverse bound is impossible

For L>=2, let V_L be the span of g_m(n)={n/m}, m|L, let C_L be the gcd-cell
space, and let T_L be its Q-orthogonal projection. The previously checked
finite map T_L:V_L -> C_L intersect 1_(L divides N)^perp is bijective.
That does not give a uniform bound for its inverse.

The following estimates are now formalized:

    ||g_L||_Q^2 >= (L-1)/(zeta(2)L^2),
    ||T_L g_L||_Q^2 <= tau(L)(2+log L)^2/(zeta(2)L^2).

Consequently every squared stability factor C satisfying

    ||f||_Q^2 <= C ||T_L f||_Q^2 for every f in V_L

must satisfy

    L-1 <= C tau(L)(2+log L)^2.

The factor zeta(2) cancels; this improves the initial paper bound. The proof
uses the actual high-conductor atom g_L, with no change to the trial space.
The elementary divisor count tau(L)<=2 sqrt(L) is also checked.
Therefore, along EVERY sequence L_j->infinity, every fixed proposed inverse
bound eventually has an actual legal counterexample:

    for every C>=0, eventually some f in V_(L_j) satisfies
        C ||T_(L_j) f||_Q < ||f||_Q.

Lean declarations: `QGcdCellEstimates.conditional_residue_norm_sq_le`,
`trial_stability_factor_necessary`,
`DivisorCountSqrt.card_divisors_le_two_sqrt`, and
`QCRTInverseInstability.eventually_exists_unstable_trial`.

This rules out uniform stability for arbitrary right-hand sides. It does
NOT show that the special canonical lifts F_L, defined by T_L F_L=1-a_L,
have unbounded norm along the LCM tower.

## 2. Exact cell geometry used by the proof

For d|L, write e_d=1_(gcd(N,L)=d) and p_d=||e_d||_Q^2. The checked formulas are

    1/(zeta(2)d^2) <= p_d <= 1/d^2,
    (T_L f)(d) p_d = <f,e_d>_Q,
    ||T_L f||_Q^2 = sum_(d|L) (T_L f)(d) <f,e_d>_Q
                  <= sum_(d|L) zeta(2)d^2 <f,e_d>_Q^2.

The lower cell mass uses the single physical atom n=d. For positive f, a
cell moment is at most the corresponding divisibility moment. For g_L,
putting b=L/d gives

    <g_L,1_(d divides N)>_Q = d^(-2) <1,g_b>_Q,
    <1,g_b>_Q <= (2+log b)/(zeta(2)b)  for b>=2.

The latter conductor estimate was already in the repository. The b=1 cell
has zero residue moment. Squaring the moment and dividing by its actual
cell mass gives the sharper zeta-normalized projected-norm bound above.

## 3. Actual canonical growth at prime cutoffs

For a prime p, V_p is one dimensional. The actual canonical vector has the
checked exact formula

    F_p = [(1-p^(-2))/<1,g_p>_Q] g_p.

The denominator is proved positive using the existing residue-mean theorem.
The formal lower bounds are

    ||F_p||_Q^2 >= zeta(2)(p-1)(1-p^(-2))^2/(2+log p)^2
                >= (9 zeta(2)/16)(p-1)/(2+log p)^2.

Thus for every sequence of primes p_j->infinity and every fixed B, eventually
||F_(p_j)||_Q>B. This is a theorem about the actual canonical target, rather
than only the worst target of an inverse operator.

A prime sequence is not divisor-exhausting. It therefore supplies no
counterexample to the desired LCM growth hypothesis. It does show that
any proof must use the LCM arithmetic, rather than a bound for every modulus.
Lean: `QCRTPrimeCutoffGrowth.canonical_prime_eq_smul`,
`canonical_prime_norm_sq_lower`, `canonical_prime_norm_sq_lower_uniform`,
and `eventually_prime_canonical_norm_gt`.

Full-tail Wolfram experiments, not interval certificates, give:

| Prime p | Complete squared canonical norm |
|---:|---:|
| 2 | 0.750000000000000 |
| 11 | 1.840665120858226 |
| 101 | 6.591690339568264 |
| 1009 | 33.35684499164719 |

## 4. Nested cutoffs retain a leakage cross term

For L|M, let r_N=F_N-h_N, h_N=1-a_N, a_N=1_(N divides the input).
The following exact identities are checked in `QCRTNestedCutoffs.lean`:

    T_L F_M = 1-(L^2/M^2)a_L,
    T_L(F_M-F_L) = (1-L^2/M^2)a_L,
    ||h_M-h_L||_Q^2 = 1/L^2-1/M^2,
    ||F_M-F_L||_Q^2 = 1/L^2-1/M^2 + ||r_M-r_L||_Q^2,
    <F_M,F_L>_Q = 1-1/L^2 + <r_M,r_L>_Q.

Expanding the remaining squared norm gives

    ||r_M-r_L||_Q^2 = ||r_M||_Q^2+||r_L||_Q^2-2<r_M,r_L>_Q.

The visible target increments telescope. The leakage increments are not
asserted to be orthogonal, independent, or small. Dropping their cross term
would reintroduce the growth gap.

## 5. A concrete arithmetic update agenda

Let L_m=lcm(1,...,m). This changes only when m is a prime power. A sufficient
new estimate would bound the multiplicative squared-norm loss at admission
m=p^k by 1+C/p^k, with one fixed C, using the actual canonical target.
The classical sum of reciprocal primes, together with the convergent higher-
power contribution, gives a reciprocal-prime-power sum O(log log M). Such control
would give a polylogarithmic norm bound and apply the checked RH criterion.
This proposed estimate has NOT been proved or formalized here.

The power k matters: a loss 1+C/p at every admission of a new power of a fixed
small prime accumulates polynomially in M, not polylogarithmically. A bound on
each squared increment alone also does not suffice without a proved control
on cross terms. The exact nested identities above keep that issue visible.

The available shift-defect estimate has an n^(-3)-scale weight. It does not
supply the missing complete n^(-2) energy bound. General compactness and the
existence of a profinite CRT limit do not repair this mismatch.

The focused [machinery audit](CanonicalUpdateMachineryAudit20261107.md) records
the exact existing declarations inspected for this task. The strongest useful
inverse estimate found is the screened physical-head Gram bound
`QSquarefreeSchurCoercivity.squarefreeSchur_inverseGram_le`, with constant at
most 4 Z (1+log H)^2. It does not invert the CRT moment matrix: the actual
canonical signed source and remaining head-null response still need bounds.
The bounded matched Q/P optimizer displacement is a different vector.
Existing conditional-nonlegality and screened-carry invariance theorems also
block treating the canonical sequence as a legal martingale or improving a
screened update solely by changing Bezout representatives.

## 6. A further sampler estimate: paper proof, not yet Lean-verified

For 1<t<2 define

    S_t(L) = sum_(n not dividing L) gcd(n,L)^(2-t)/n^2.

The checked separated sampler bound is

    K_L(s) <= sqrt(zeta(2)) [sqrt(D_(2 beta)(L))+sqrt(S_(2 beta)(L))].

The complete finite Mobius formula for S is checked in QGcdCellEstimates.
The following additional bound is a remaining formalization task:

    S_t(lcm(1,...,M)) <= t zeta(t)/((t-1)M),  1<t<2, M>=1.

Here is the paper derivation. Set q=p^(-t), r=p^(-2), e=v_p(L). Relative to
zeta(t), the divisor mass has local factor E_p=1-q^(e+1). The full gcd-weighted
series has factor

    A_p = E_p + delta_p,
    delta_p = p^(-t e-2)(1-p^(-t))/(1-p^(-2)).

For 1<t<=2, 0<=E_p<=A_p<=1 and delta_p<=p^(-t e-2). The infinite products
converge. Telescoping products gives

    S_t(L) <= zeta(t) sum_p p^(-t e_p-2).

For L=L_M and p<=M, p^(e_p+1)>M, hence
p^(-t e_p-2)<=M^(-t)p^(t-2). Summing over all integers up to M gives at most
1/((t-1)M), since sum_(n<=M)n^(t-2)<=M^(t-1)/(t-1). For p>M, e_p=0 and the
integer tail of p^(-2) is at most 1/M. Adding gives the displayed bound.

The new checked bound D_t(L_M)>=4*32^(-t) M^(1-t)/log M supplies the needed
lower estimate for D. Combined with the still-paper-only S upper bound, this
would give S_t(L_M)/D_t(L_M)->0 for 1<t<2 and asymptotic sampler coefficient one.
The product representation and this stronger S rate have not been formalized
in this continuation. Neither would supply the canonical norm bound.

## 7. Published context and status

Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of
the Riemann hypothesis*, Proc. Indian Acad. Sci. Math. Sci. 116 (2006),
137–146, supplies the full-family density/RH and Mellin framework:
https://arxiv.org/pdf/math/0607733.

Alouges–Darses–Hillion, *Polynomial approximations in a generalized
Nyman–Beurling criterion*, JTNB 34 (2022), 767–785,
https://doi.org/10.5802/jtnb.1227, explicitly separates approximation
construction from the coefficient control needed for RH. Their different
Gram system is not a provider of the CRT norm bound.

Rosser and Schoenfeld, *Approximate formulas for some functions of prime
numbers*, Illinois Journal of Mathematics 6 (1962), 64-94,
https://doi.org/10.1215/ijm/1255631807, equation (2.4), records the classical
reciprocal-prime asymptotic used in the proposed admission-budget discussion.
That discussion remains a research proposal, not a new formal theorem.

All formalized obstructions are unconditional. The decisive LCM canonical
growth condition remains open, and RH is not proved. The theorem catalog and
final server checkpoint record the exact persisted verification scope.
