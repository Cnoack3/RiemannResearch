# Three-stage signed sieves: interpolation, physical jumps, and energy obstruction

21 October 2026. Continuation of `SignedSieveRowsObstructionResearch20261020.md`
and commit `471a5a2601bbd859e23a00612b5513680cb6a6bf`.
Working base: `914f1d2a3b0d1722dbef04b3e53f31a1c1f679ac`.

## Outcome and scope

The alternating three-stage system can be nonsingular and exactly match the
target Mellin signature. That algebraic feasibility does not give bounded
energy. A new physical-prime-jump estimate forces complete-Q norm divergence
for cofinal three-stage rows with a fixed nonzero Euler signature. Neither
coefficient variation nor a sign restriction is assumed.

The proof also yields an ordinary mathematical extension to arbitrary finite
row length, including a continuous functional separating the entire fixed-p
raw-sieve span, even enlarged by constants, from F_p. The infinite series
assembly of that stronger statement is **not a Lean declaration in this change**.
The verification record below distinguishes it from checked finite identities
and the checked three-stage application.

This excludes a restricted family of coefficient choices. It does not exclude
F_2 or F_3 from the full squarefree legal closure, and it does not prove RH.
Independently optimized squarefree-divisor coefficients remain the preferred
research direction. Mixing raw sieves with different target primes is also
outside the fixed-p separating-functional conclusion.

## 1. Actual notation

For a prime p, K >= p, and 0 < sigma < 1, write

\[
V_K=\operatorname{sieveVector}(\operatorname{primorial}K,p),\quad
s_K=\frac1p\prod_{q\le K,\ q\ne p}(1-q^{-1}),\quad
E_K=p^{-\sigma}\prod_{q\le K,\ q\ne p}(1-q^{-\sigma}).
\]

All products are over primes. Let Z=zeta(2), Q(n)=1/(Zn^2), n>=1,
and F_p(n)=floor(log_p n). This F_p is not the p-adic valuation.
For 1/2 < sigma < 1,

\[
\Phi_\sigma(f)=\sum_{n\ge1}f(n)[n^{-\sigma}-(n+1)^{-\sigma}],\qquad
\Phi_\sigma(F_p)=\frac1{p^\sigma-1}.
\]

For B=sum w_i V_{K_i}, zero drift sum w_i s_i=0 gives exactly
Phi(B)=zeta(sigma) sum w_i E_i. Target matching asks for

\[
T=\frac1{(p^\sigma-1)\zeta(\sigma)}<0,
\qquad \sum_iw_i=1,\quad \sum_iw_is_i=0,\quad \sum_iw_iE_i=T.
\]

The new energy bounds need only T != 0 and 0 < sigma < 1; they do not
need the target's particular value or the sign of real zeta.

## 2. Exact determinant, solvability, and signs

Write a=s_1, b=s_2, c=s_3 and x=E_1, y=E_2, z=E_3. Then

\[
D=\det\begin{pmatrix}1&1&1\\a&b&c\\x&y&z\end{pmatrix}
=(c-b)x+(a-c)y+(b-a)z.
\]

Set

\[
N_1=bz-cy+(c-b)T,\quad N_2=cx-az+(a-c)T,\quad N_3=ay-bx+(b-a)T.
\]

The exact identities N_1+N_2+N_3=D, aN_1+bN_2+cN_3=0,
and xN_1+yN_2+zN_3=TD give the unique solution w_i=N_i/D when D != 0.
Conversely every solution satisfies Dw_i=N_i, including at D=0.

If a != b and D=0, solvability is equivalent to
ay-bx=(a-b)T. Thus the three points (s_i,E_i) are collinear, and their
line must meet the vertical axis at T. If a>b>c>0, all solutions are

\[
(w_1,w_2,w_3)=\left(-\frac c{a-c},0,\frac a{a-c}\right)
+\lambda(b-c,c-a,a-b).
\]

For actual sieve plateaux, equal slopes also mean equal probes and vectors.
Merge duplicate stages. If all slopes coincide positively, mass one and
zero drift are inconsistent. Distinct integer cutoffs alone do not ensure
distinct primorials or a nonzero determinant.

For strictly decreasing slopes put

\[
I_{12}=\frac{ay-bx}{a-b},\quad I_{13}=\frac{az-cx}{a-c},\quad
I_{23}=\frac{bz-cy}{b-c}.
\]

Then N_1=(b-c)(I_23-T), N_2=(a-c)(T-I_13),
N_3=(a-b)(I_12-T). Also

\[
I_{13}=\frac{c(a-b)}{b(a-c)}I_{12}
+\frac{a(b-c)}{b(a-c)}I_{23},\qquad
I_{23}-I_{12}=-\frac{bD}{(a-b)(b-c)}.
\]

The two coefficients in the first equality are positive and sum to one.

| Position of T | D > 0 | D < 0 |
|---|---|---|
| Below both extreme intercepts | (+,-,+) | (-,+,-) |
| Above both extreme intercepts | (-,+,-) | (+,-,+) |
| Between extreme intercepts, off the three intercepts | One sign change, negative before positive | One sign change, negative before positive |
| At an intercept | One coefficient is zero | One coefficient is zero |

The existing uniform secant decay makes every I_ij uniformly small as the
smallest cutoff tends to infinity. Thus a fixed target T<0 eventually lies
below all of them, so every nonsingular matching row is alternating.
Its variation is exactly (|N_1|+|N_2|+|N_3|)/|D|, and

\[
|w_2|=\frac{b(a-c)}{(a-b)(b-c)}
\frac{|T-I_{13}|}{|I_{23}-I_{12}|}\longrightarrow\infty.
\]

The prefactor is greater than one. This is a coefficient-growth statement;
the complete energy conclusion requires the separate physical-jump argument.
There is also the necessary bound

\[
\sum_i|w_i|\ge |T|/E_1,
\]

so the required variation grows faster than every fixed power of K_1.
The actual Euler curve need not have one convexity sign: consecutive prime
secant slopes satisfy
d_r/d_q=((1-q^{-sigma})/(1-q^{-1}))(r/q)^(1-sigma).
Finite examples below exhibit both determinant signs.

## 3. Complete signed Gram substitution

With G_ij=<V_i,V_j>_Q and beta_i=<V_i,F_p>_Q, exactly

\[
\|B\|_Q^2=\frac{N_1^2G_{11}+N_2^2G_{22}+N_3^2G_{33}
+2N_1N_2G_{12}+2N_1N_3G_{13}+2N_2N_3G_{23}}{D^2},
\]

\[
D^2\|B-F_p\|_Q^2=N^{\mathsf T}GN-2D\sum_iN_i\beta_i+D^2\|F_p\|_Q^2.
\]

Every cross term and target correlation is retained. The new generic Hilbert
identities apply directly to these actual Q vectors. They are a three-term
specialization of `signedSieveVector_norm_sq_exact`, not a diagonal estimate.

## 4. Actual prime jumps give the missing energy control

Let C_K(n) count the positive m<=n with gcd(m,primorial K)=p. The existing
exact sequence identity is V_K(n)=C_K(n)-s_K n. For a prime q>p,

\[
\gcd(pq,\operatorname{primorial}K)=p\iff K<q,
\qquad \Delta V_K(pq)=\mathbf1_{K<q}-s_K.
\]

Thus for **every** finite zero-drift row, with no mass restriction,

\[
\boxed{\Delta B(pq)=W(q):=\sum_{K<q}w_K.}
\]

The complete Hilbert norm controls coordinate evaluation:
|f(n)|<=sqrt(Z)n||f||, hence

\[
\boxed{|\Delta f(pq)|\le2p\sqrt Z\,q\|f\|_Q.}
\]

This is a bound on the actual norm, including all cancellations between raw
vectors. For primes K_1<q_1<=K_2<q_2<=K_3, it bounds w_1 and w_1+w_2.
The exact Abel identity

\[
\sum_iw_iE_i=E_3+w_1(E_1-E_2)+(w_1+w_2)(E_2-E_3)
\]

therefore gives

\[
|\sum_iw_iE_i-E_3|
\le2p\sqrt Z\|B\|_Q[q_1(E_1-E_2)+q_2(E_2-E_3)].
\]

If q_i<=2K_i, positivity and monotonicity yield the actual energy inequality

\[
\boxed{|\sum_iw_iE_i-E_3|
\le4p\sqrt Z\|B\|_Q(K_1E_1+K_2E_2).}
\]

Such short prime witnesses exist whenever the stages are distinct: take a
prime between successive effective prime cutoffs and apply Bertrand if that
prime lies beyond twice the earlier cutoff. For prime K_2 and K_3, this
choice is particularly direct. Plateaux reduce to fewer stages.

## 5. Euler amplification and the three-stage conclusion

The general decay theorem proved in this change is

\[
\forall A\in\mathbb R,\qquad H^A E_{p,H}(\sigma)\longrightarrow0
\quad(0<\sigma<1).
\]

Choose sigma<tau<1 and an integer m with m(1-tau)>A. For sufficiently
large primes q, q^(tau-sigma)>=m, and Bernoulli gives
1-q^(-sigma)<=1-mq^(-tau)<=(1-q^(-tau))^m. Finite exceptional factors
cost one constant. The already formalized positive Euler expansion gives
P_tau(H)<=H^(tau-1), so H^A P_sigma(H) is squeezed to zero.
Removing a fixed prime changes this by a fixed factor. No RH or PNT is used.

For a cofinal matching row, E_3 tends to zero and K_1E_1+K_2E_2 tends to
zero. The boxed bound therefore forces ||B||_Q to tend to infinity for
every fixed T != 0. This applies to either alternating pattern, arbitrary
coefficient variation, arbitrary slope gaps, and arbitrary determinant gaps.
The norm divergence is the formal three-stage application in this change.

The same argument with arbitrary-power decay shows, in ordinary mathematics,
growth faster than any fixed power of the minimum cutoff for exact matching.
The formal application currently records norm divergence, not this stronger
rate statement.

## 6. Stronger ordinary proof: every finite row length

This section is a complete ordinary derivation. The infinite-series assembly
and the resulting global separator are not claimed as Lean-verified here.

For prime q>p set

\[
\delta_q=E_{q-1}-E_q=E_{q-1}q^{-\sigma}>0,\qquad
R_\sigma(H)=\sum_{q>H,\ q\text{ prime}}q\delta_q.
\]

Arbitrary-power Euler decay implies convergence of this series and decay of
R_sigma(H) faster than every fixed power. Explicitly, for any m>2,
E_{q-1}<=C(q-1)^(-m) eventually; then q delta_q<=C' q^(1-sigma-m),
and an ordinary integer p-series bounds the prime tail. Taking m arbitrarily
large gives any desired power.

Exact telescoping and finite interchange give

\[
E_K=\sum_{q>K}\delta_q,\qquad
\boxed{\sum_Kw_KE_K=\sum_{q>p}\delta_qW(q).}
\]

For a zero-drift row with all K>=H,

\[
\boxed{|\sum_Kw_KE_K|\le2p\sqrt Z R_\sigma(H)\|B\|_Q.}
\]

Since pq is not a p-power, Delta F_p(pq)=0. The same inequality holds
with ||B-F_p||_Q on the right. Thus fixed nonzero signature matching forces
both norms to grow faster than every fixed power of H, regardless of row
length, sign pattern, or variation. There is no need to diagonalize G.

For balanced mass-one rows without signature matching, the existing
exact-head Mellin tail estimate instead gives

\[
\frac1{p^\sigma-1}\le\left[
\sqrt{\frac{Z\sigma^2}{2\sigma-1}}H^{1/2-\sigma}
+2p|\zeta(\sigma)|\sqrt Z R_\sigma(H)\right]\|B-F_p\|_Q.
\]

The second coefficient is negligible compared with the first. Eventually
the same earlier lower bound holds for every finite balanced row:

\[
\|B-F_p\|_Q^2\ge
\frac{2\sigma-1}{4Z\sigma^2(p^\sigma-1)^2}H^{2\sigma-1}.
\]

## 7. Ordinary continuous separator, including constants

Define J(f)=sum_{prime q>p} delta_q Delta f(pq). The convergent sum
sum q delta_q and the coordinate bound make J a continuous real linear
functional. Exact telescoping gives

\[
J(V_K)=E_K-s_KE_p,\quad
\Phi_\sigma(V_K)=\zeta(\sigma)(E_K-s_K),\quad V_K(1)=-s_K.
\]

Therefore

\[
L(f)=\Phi_\sigma(f)-\zeta(\sigma)J(f)
+\zeta(\sigma)(E_p-1)f(1)
\]

annihilates every V_K, whereas L(F_p)=1/(p^sigma-1)>0.
Let A(f)=f(p+1)-f(p)-f(1). The integer p+1 is not divisible by p and
lies strictly between p and p^2, so A(V_K)=A(F_p)=0, while A(1)=-1.
Then L_tilde=L+L(1)A annihilates every V_K and constants but not F_p.

Consequently the entire fixed-p raw-sieve span enlarged by constants cannot
approximate F_p in Q norm. This excludes even noncofinal designs within that
restricted span. It does not assert that L_tilde annihilates arbitrary legal
squarefree atoms or sieves with a different target prime.

## 8. Finite tests and cross-term cancellations

Reproducible code and output are saved in the downloadable companion
`ThreeStageSieveCalculations20261021.zip`. Decimal probes and the full
periodic Gram evaluations are exploratory floating computations, not rigorous
interval certificates. The independent Fraction section uses exact arithmetic.

At sigma=3/4:

| p | Cutoffs | Approximate weights | Complete Q energy |
|---|---|---|---:|
| 2 | 2,3,5 | -23.0741, 76.7593, -52.6852 | 57.3160 |
| 2 | 3,5,7 | -59.6723, 158.0988, -97.4265 | 167.1242 |
| 2 | 5,7,11 | 1895.2075, -5379.7545, 3485.5470 | 154203.2777 |
| 2 | 7,11,13 | -228.1896, 512.8360, -283.6465 | 642.9569 |
| 3 | 3,5,7 | same weights as p=2 | 92.7735 |
| 3 | 5,7,11 | same weights as p=2 | 95471.0831 |
| 3 | 7,11,13 | same weights as p=2 | 328.4663 |

Energy is not claimed to increase monotonically with a particular finite
choice of triple. Divergence is a cofinal assertion, uniform enough to prevent
an infinite bounded-energy selection.

For p=2 and cutoffs 5,7,11, the diagonal-only sum is about 8,816,502.76,
while the sum of all nine signed Gram terms is about 154,203.28.
The computation uses the exact periodic identity

\[
G_{ij}=\frac1{ZL^2}\sum_{r=1}^{L}V_i(r)V_j(r)\psi_1(r/L).
\]

This is finite evaluation of the complete periodic norm, not an unproved
convergence strategy involving trigamma. The exact rational example

\[
p=2,\quad K=(2,3,5),\quad w=(-50/7,21,-90/7)
\]

has mass one and zero drift. Its prime jumps are -50/7 at q=3, 97/7 at
q=5, and 1 at q>=7. Its unnormalized squared error through n=30 is

\[
\frac{213584510873223193487293}{38456054887970321476875}.
\]

Using Z<2 yields a rigorous complete normalized error lower bound exceeding
2.7769945655. These Fraction assertions are exact executable checks, not Lean
certificates. This rational row is not asserted to match the target signature.

For common cutoffs K_i>=p, the matching weights are independent of p:
s_{p,K}=P_1(K)/(p-1), E_{p,K}=P_sigma(K)/(p^sigma-1), and both fixed
factors cancel from the two coefficient equations. This is an ordinary exact
observation; the table illustrates it numerically.

## 9. Verification and research agenda

Verification status will be filled from the saved-source server audit and
the single publication checkpoint. No queued request counts as verification.

Priority next steps:

1. Formalize the infinite telescoping Euler-jump functional in Sections 6-7.
   Use the already checked arbitrary-power decay and actual semiprime jump.
   Preserve the complete drift term before applying zero-drift balance.
2. Work with independently optimized coefficients on all squarefree divisors,
   where the fixed-p raw-sieve separator need not vanish. Keep the full signed
   Gram and target correlations in every energy estimate.
3. Pursue the actual rational minimizers and the open signed-tail budget, or
   legal-basis Parseval saturation for F_2 and F_3. A conditional consumer is
   not a provider of its arithmetic estimate.
4. Do not spend further search effort merely increasing alternating row length
   within this fixed-p raw-sieve family. The ordinary all-row obstruction gives
   a concrete reason to change coefficient freedom rather than add stages.

Open: full squarefree legal closure of F_2 and F_3, a successful uniform
complete-energy construction in that larger class, and RH.
