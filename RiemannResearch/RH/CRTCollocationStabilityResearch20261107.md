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

## 6. Sharper complete sampler estimates: now formalized

For 1<t<=2 let

    S_t(L) = sum_(n not dividing L) gcd(n,L)^(2-t)/n^2,
    D_t(L) = sum_(n not dividing L) n^(-t).

Both quantities retain the entire infinite physical tail. The existing finite
Mobius formula for S remains available in QGcdCellEstimates. The new owning
module NumberTheory/GcdSamplePrimeTail proves the additional estimates here.

Write e_p=v_p(L) and w_p=p^(t-2)(p^(-t))^(e_p+1)=p^(-t e_p-2).
The proof uses a direct prime-power cover. Every escaping positive integer n
has a prime p with p^(e_p+1)|n. For any such p, p*gcd(n,L)|n, hence

    gcd(n,L)^(2-t)/n^2 <= p^(t-2)n^(-t).

The sum of this cover over all multiples of p^(e_p+1) is exactly zeta(t) w_p.
Nonnegative summability justifies summing over every prime and every integer.
Thus the checked bound and exact LCM budget split are

    S_t(L) <= zeta(t) sum_p w_p,
    sum_p w_p(L_M) = sum_(p<=M) w_p(L_M) + sum_(p>M) p^(-2).

The earlier product argument is not needed for this proof. This continuation
does not claim a separate formalization of that infinite-product formula for S.

The original proposed rate is now checked, including the endpoint t=2:

    S_t(L_M) <= t zeta(t)/((t-1)M),  M>=1.

A further checked improvement uses an arbitrary prime threshold K, retaining
the entire large-prime tail. Choosing K=floor(sqrt M), set

    C_t = 1/(t-1) + 2^(t+1)/(t+1),    B = 4(2 log 4+2).

Then, for every M>=2,

    S_t(L_M) <= zeta(t)[C_t M^(-(t+1)/2) + B/(M log M)].

The checked eventual bound is

    S_t(L_M) <= zeta(t)(C_t+B)/(M log M).

Thus the complete sampler tail has order at most 1/(M log M) for each fixed
1<t<=2. No monotonicity of S_t(L_M) is assumed in passing to every cutoff.
The sharper square-cutoff identity retains coefficient
1/(t-1)+1/(t+1) on K^(-t-1), with M=K^2.

The checked lower bound D_t(L_M)>=4*32^(-t) M^(1-t)/log M, together with the
reciprocal sampler bound, proves

    S_t(L_M)/D_t(L_M) -> 0,  1<t<2.

RH/QCRTAsymptoticSampler applies this to the actual projected Mellin map.
For every fixed s with 1/2<Re(s)<1 and every epsilon>0, eventually

    K_(L_M)(s) <= (1+epsilon) sqrt(zeta(2) D_(2 Re(s))(L_M)).

This is an upper bound with asymptotic coefficient one, not an assertion that
the quotient of K by that square root converges to one. The complete endpoint
and canonical leakage remain present in the checked zero obstruction.

If zeta(s)=0, then for every 0<epsilon<1, eventually

    D_(2 Re(s))(L_M) V(L_M)
      >= (1-epsilon)^2 / ((1+epsilon)^2 zeta(2) |s|^2).

Finally, riemannHypothesis_of_cofinal_escape_energy proves Mathlib RH from
the following explicit condition: for every 1<t<2, c>0, and N, there is M>=N
with D_t(L_M)||F_(L_M)||_Q^2<c. This is a conditional research reduction.
The condition on the actual canonical norms remains OPEN. The formal RH
statements use M+2 to keep the canonical cutoff at least two.

These sampler improvements do not establish the canonical norm bound.

## 6A. Sharp sampler order and quantitative Mellin rate

The follow-on declarations in `GcdSampleTail` show that S_t(L) decreases
with t on 1<t<=2, and that S_2(L)=D_2(L) exactly. Consequently
D_2(L)<=S_t(L). Combining this with the existing full Euler-tail lower
bound at exponent two gives, for every M>=32,

    S_t(L_M) >= 1/(256 M log M),    1<t<=2.

With C_S(t)=zeta(t)[1/(t-1)+2^(t+1)/(t+1)+4(2 log 4+2)],
the two-sided eventual estimate is

    1/(256 M log M) <= S_t(L_M) <= C_S(t)/(M log M).

Thus S_t(L_M)=Theta_t(1/(M log M)). The normalized complete energy
M log M S_t(L_M) is eventually between 1/256 and C_S(t), and cannot
converge to zero. These bounds concern the entire positive-coordinate tail.

Set b_t=4*32^(-t) and C_R(t)=C_S(t)/b_t. The logarithm in the earlier
relative sampler upper bound can now be removed:

    S_t(L_M)/D_t(L_M) <= C_R(t) M^(t-2), eventually.

The existing upper bound D_t(L_M)=O_t(M^(1-t)/log M), together with the
new sampler lower bound, also proves a positive constant c_t with

    c_t M^(t-2) <= S_t(L_M)/D_t(L_M) <= C_R(t) M^(t-2)

eventually. Both sides are formalized in
`exists_eventually_sampleTail_div_tail_bounds`.

For each fixed s with beta=Re(s) in (1/2,1), the actual projected Mellin
map therefore satisfies the checked quantitative upper bound

    K_(L_M)(s) <= sqrt(Z D_(2 beta)(L_M))
      [1+sqrt(C_R(2 beta)) M^(beta-1)].

This is `QCRTAsymptoticSampler.eventually_tailMellin_norm_le_power`.
The power is sharp for the separated arithmetic sampler contribution.
There is no corresponding lower bound here for the actual operator:
cancellation between its signed pieces remains possible.

At beta=1, S_2(L)/D_2(L)=1 for every positive finite L, so the
negligible-sampler argument does not extend to that endpoint. At beta=1/2,
the present summability and Hilbert-space Mellin hypotheses do not apply.
All interior estimates are for fixed beta; uniformity across the open
strip is not asserted.

The actual canonical-norm condition remains OPEN. These sharper arithmetic
rates do not furnish the small canonical escape-energy product required
by the conditional RH theorem.

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
