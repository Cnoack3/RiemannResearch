# Common quotient cells, prime selections, and complete-energy certificates
Research date: 2026-10-15. Formalization update: 2026-10-16.
Research record for Christian Noack.

## Scope and status
This record separates exact analytic deductions, finite integer/rational computations,
and Lean verification. The formalization scope and open obligations are recorded below.
No uniform cofinal complete-energy bound or proof of RH is asserted.
The Baker--Harman--Pintz prime-selection consequence is an analytic deduction using
an external theorem, not a formalized prime-gap provider.

The starting source is CanonicalMobiusQuotientCells.lean and
CanonicalMobiusTruncatedCeiling.lean. The new modules are
Analysis/FiniteWeightedVariance.lean, RH/CanonicalMobiusPrimeCells.lean, and
RH/CanonicalMobiusCellCeiling.lean.

## 1. Complete first-cell identity
Let P(n)=1/[n(n+1)] for n>=1. Choose a nonempty finite set of prime boundaries
p_i, put Y_i=p_i-1, a=min p_i, b=max p_i, and assume b<2a.
For real coefficients alpha_i with sum alpha_i=1, set
F=sum alpha_i F_{Y_i}, r=1-F, and
B=sum alpha_i b(Y_i), where b(Y)=(Y+1) sum_{d<=Y} mu(d)/d-M(Y).
Write I={b,b+1,...,2a-1}.

For every n in I, floor(n/p_i)=1, and the exact profile identity is
r(n)=M(n)+B.

For any positive finite weights w on I, define
W=sum_I w(n), T=sum_I w(n)M(n), Z=sum_I w(n)M(n)^2, m=T/W,
V=sum_I w(n)(M(n)-m)^2.
Then all of the following are exact finite equalities:
V=Z-T^2/W,
2 W V=sum_{n,m in I} w(n)w(m)(M(n)-M(m))^2,
sum_I w(n)(M(n)+B)^2=V+W(m+B)^2.

In particular the COMPLETE P residual energy is exactly
$$E_P=V_P+W_P(m_P+B)^2+T_{\mathrm{complement}}.$$
T_complement=sum_{n>=1,n notin I} P(n) r(n)^2,
W_P=1/b-1/(2a).
Every term on the right is nonnegative. Replacing the complement by zero is
not an equality. Changing signed coefficients changes B, not V_P.

If two offsets beta_i=b(Y_i) and beta_j=b(Y_j) differ, the two coefficients
alpha_i=(-m-beta_j)/(beta_i-beta_j),
alpha_j=(beta_i+m)/(beta_i-beta_j)
have sum 1 and achieve first-cell energy exactly V. This local minimization
can produce large coefficients and does not minimize the complement.

## 2. Rigorous elementary upper and lower bounds
The exact difference M(n)-M(m)=sum_{m<d<=n} mu(d), for m<=n, gives
|M(n)-M(m)|<=n-m.
The pairwise variance equality therefore gives V_P(M;I)<=V_P(n;I).

More generally, on [L,U), with 0<L<U, let
W=1/L-1/U and h=sum_{n=L}^{U-1} 1/(n+1).
The coordinate moments and variance are exactly
sum P(n)n=h,
sum P(n)n^2=U-L-h,
V_P(n;[L,U))=U-L-h-h^2/W.
Consequently
0<=V_P(M;[L,U))<=U-L-h-h^2/W
<= (1/L-1/U)(U-L-1)^2/4.
The last inequality follows by centering the coordinate n at (L+U-1)/2.

With ell=2a-b this specializes to the explicit bound
$$0\le V_P(M;I)\le\frac{\ell(\ell-1)^2}{8ab}. $$
This is a local upper bound, not an upper bound on E_P.
When ell=1, the cell is a singleton and V_P is exactly zero.

There are also computable lower bounds. For any distinct u,v in I,
V >= [w(u)w(v)/(w(u)+w(v))] (M(u)-M(v))^2.
For disjoint adjacent pairs contained in I, these lower bounds can be added:
V >= sum_pairs [w(n)w(n+1)/(w(n)+w(n+1))] mu(n+1)^2.
To see this, first bound the energy about any common center on each pair by
its own minimum, add over disjoint pairs, then choose the global mean.
A cell may have zero variance; no universal strictly positive lower bound is claimed.

For Q(n)=1/[zeta(2)n^2], pointwise weight comparison gives
V_P <= zeta(2)V_Q <= (1+1/L)V_P
on any [L,U). The means used in V_P and V_Q are their OWN minimizing means.
This comparison follows by minimizing each weighted energy over its constant
center; assuming the two means are equal would be incorrect.

## 3. An unconditional prime-selection consequence
Baker, Harman, and Pintz, The Difference Between Consecutive Primes, II,
Proc. London Math. Soc. 83 (2001), 532-562, Theorem 1:
https://doi.org/10.1112/plms/83.3.532
Primary paper:
https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf

Theorem 1 supplies a prime in [x-x^(21/40),x] for every sufficiently large x.
For sufficiently large prime a, take b to be the largest prime below 2a.
Since 2a is composite, a<=b<2a, and ell=2a-b<=(2a)^(21/40).
It follows, with no implicit asymptotic constant, that
V_P <= ell(ell-1)^2/(8ab)
<= ell^3/(8a^2)
<= 2^(63/40)/(8 a^(17/40)).
The displayed right side tends to zero along primes a.
Thus first-cell variance alone cannot obstruct ALL cofinal prime-boundary
selections. One can include the endpoints a,b and any additional primes between
them; the first-cell variance is still determined only by the endpoints.

This choice eventually has b>3a/2 and removes the common q>=2 cells.
It does not control the mixed-quotient regions or complete infinite tail.

## 4. Higher cells and the shared-offset obstruction
For integer q>=1 define
I_q=[qb,(q+1)a) intersect N,
H_q(n)=sum_{k=1}^q M(floor(n/k)).
The cell is nonempty exactly when q(b-a)<a. On it,
r(n)=H_q(n)+qB.
For b>a the largest possible q is floor((a-1)/(b-a)).
These cells are pairwise disjoint.

Let W_q, m_q, V_q be the mass, mean, and unnormalized variance of H_q
on any finite collection J of nonempty cells. Put
K=sum_{q in J} W_q q^2,
J_1=sum_{q in J} W_q q m_q,
B_*=-J_1/K,
Delta=sum_{q in J} W_q m_q^2-J_1^2/K.
There is an exact nonnegative pairwise expression
Delta=(1/K) sum_{q<r, q,r in J}
 W_q W_r (r m_q-q m_r)^2.
The complete energy is exactly
$$E_P=\sum_{q\in J} V_q+\Delta+K(B-B_*)^2+T_{\mathrm{outside\ union}}.$$
For two cells the extra obstruction is exactly
W_q W_r(r m_q-q m_r)^2/(W_q q^2+W_r r^2).
Thus adding individual cell variances misses an additional shared-offset cost.

An unconditional finite upper comparator also exists:
H_q(n)-H_q(m)=sum_{k=1}^q sum_{floor(m/k)<d<=floor(n/k)} mu(d),
|H_q(n)-H_q(m)|<=J_q(n)-J_q(m),
J_q(n)=sum_{k=1}^q floor(n/k), m<=n.
Therefore V(H_q;I_q)<=V(J_q;I_q), and
V(H_q;[L,U))<=W [J_q(U-1)-J_q(L)]^2/4.
Equivalently, the exact increment is
H_q(n)-H_q(n-1)=sum_{1<=k<=q, k divides n} mu(n/k), n>=1.

## 5. Reproducible finite experiments
The accompanying Python script uses a linear Mobius sieve and rational outward
rounding. For every weight it brackets the weight by consecutive multiples of
10^(-40), accumulates integer moment intervals, and rounds displayed endpoints
outwards. These are finite numerical certificates implemented in Python;
they are not Lean kernel computations. Small cases were checked against
direct exact Fraction sums.

The selections at scale X start at the first prime a>=X. Four schemes were tested:
the first eight primes, all primes from a through 5a/4, through 7a/4, and below 2a.
Full interval enclosures are in the accompanying JSON file.

For the first eight primes:
| X | a | b | First-cell variance V_P | Uniform first-cell energy | Multi-cell lower bound |
|---:|---:|---:|:---|:---|:---|
| 100 | 101 | 137 | [0.0112448278, 0.0112448279] | [0.0113199170, 0.0113199171] | [0.0130797295, 0.0130797296] |
| 1000 | 1009 | 1049 | [0.0177353118, 0.0177353119] | [0.0179755736, 0.0179755737] | [0.0265623359, 0.0265623360] |
| 10000 | 10007 | 10079 | [0.0185091728, 0.0185091729] | [0.0185092430, 0.0185092431] | [0.0289881581, 0.0289881582] |
| 100000 | 100003 | 100109 | [0.0171384279, 0.0171384280] | [0.0173701164, 0.0173701165] | [0.0300953051, 0.0300953052] |

The multi-cell column includes every available cell through q=6, as well as Delta.
At X=100 only q=1,2 exist. At the other scales all six exist.
All decimals below are enclosed in intervals of width at most 10^(-10) in the JSON.

At scale X=100000, changing the endpoints:
| Selection | Number of primes | b | First-cell variance V_P |
|:---|---:|---:|:---|
| next_8 | 8 | 100109 | [0.0171384279, 0.0171384280] |
| ratio_5_4 | 2143 | 125003 | [0.0107367959, 0.0107367960] |
| ratio_7_4 | 6325 | 175003 | [0.0006871935, 0.0006871936] |
| below_2 | 8393 | 200003 | [0.0000000000, 0.0000000001] |

For fixed a, increasing b shrinks [b,2a), and unnormalized variance is
monotone under inclusion. Selecting more interior primes with unchanged
endpoints leaves this variance exactly unchanged.

The finite values show no divergence certificate for these schemes.
They do not establish a uniform bound, a positive asymptotic lower bound,
or convergence of any candidate family. A positive bounded local floor is
compatible with the UNIFORM bounded-energy criterion for weak closure.

For uniform coefficients on the eight primes, minimizing B on the first cell
would improve that cell's energy by approximately:
0.0000750892, 0.0002402618, 0.0000000702, and 0.0002316885 at the four scales.
The variance survives every signed reweighting of the same family.

## 6. Exact connection with the truncated inverse-Gram ceiling
For one finite canonical family k_i=Y_i, let
A_i=1+2k_i, D=sum_i A_i^2, and sum_i alpha_i=1.
For R>=1 the existing envelope is exactly
Env_R(alpha)=sum_{0<=n<R} P(n)(sum_i alpha_i r_{k_i}(n))^2
             +(D/R) sum_i alpha_i^2.
The existing inverseCeiling is the minimum of this finite augmented quadratic
energy and bounds the complete energy of its own selected coefficients.

If I=[b,2a) is contained in [0,R), the envelope has the exact decomposition
Env_R(alpha)=V_1+W_1(m_1+B)^2
 +sum_{0<=n<R,n notin I} P(n)(sum_i alpha_i r_{k_i}(n))^2
 +(D/R) sum_i alpha_i^2.
All cross terms remain inside the actual signed residual square.
In particular
V_1 <= complete energy of the selected coefficients <= inverseCeiling,
and for ANY normalized witness alpha,
inverseCeiling <= Env_R(alpha).
The lower inequality holds even if R is too small to contain I.

A concrete SUFFICIENT uniform certificate is to choose cofinal prime families,
radii R_j>=2a_j, normalized witnesses alpha_j, and fixed finite nonnegative
constants C_V,C_M,C_G,C_T such that
V_{j,1}<=C_V,
W_{j,1}(m_{j,1}+B_j)^2<=C_M,
sum_{0<=n<R_j,n notin I_{j,1}} P(n)r_j(n)^2<=C_G,
[D_j/R_j] sum_i alpha_{j,i}^2<=C_T.
Then inverseCeiling_j<=C_V+C_M+C_G+C_T, so the certified selected legal
candidates have uniformly bounded COMPLETE residual energy and growing
exact heads. The existing weak-closure criterion then gives squarefree closure
and RH. The required uniform finite-complement estimate is Open.
A multi-cell version replaces the first two terms by
sum V_q+Delta+K(B-B_*)^2; its complement must still be bounded.

For the actual complete energy, without an envelope, uniform bounds on
V_1, the cell mean square, and the FULL complement suffice and are necessary
(up to choosing their common total bound), because their sum is exactly E_P.

For m primes at most b,
D sum_i alpha_i^2 <= m(2b-1)^2 sum_i alpha_i^2.
With uniform alpha_i=1/m this is at most (2b-1)^2.
Thus R_j>=(2b_j-1)^2/C_T suffices for the crude tail allowance when C_T>0.
Even in that case one must still bound the full finite complement all the way
to R_j, including [a_j,b_j) and [2a_j,R_j). The first-cell calculation does
not supply that estimate.

Enlarging the family decreases the TRUE affine minimum of complete energy.
At fixed R it need not decrease this particular diagonal-tail ceiling:
D changes with the family. The certificate must account for that change.

## 7. Research priorities
1. Optimize the retained finite complement together with the scalar B,
   rather than selecting B solely to center the first cell.
2. Compare narrow clusters with endpoints near 2a using complete certified
   envelopes. Do not rank prime selections solely by V_1.
3. Compute the multi-cell incompatibility Delta before optimizing coefficients;
   it is a stronger necessary floor than sum V_q alone.
4. Seek an arithmetic upper estimate for the mixed-quotient complement on
   [a,b) and [2a,R), with the signed squares intact.
5. Track the coefficient budget D sum alpha_i^2/R alongside every finite
   inverse-Gram calculation; choose R from that budget explicitly.
6. Use the Q/P variance comparison to transfer the same local diagnostics.
   No local Q advantage removes the missing complete-energy upper estimate.

## 8. Lean formalization and remaining obligations
The implementation contains 32 public theorem declarations and three definitions
across three modules. Ordinary finite conditions such as positive interval
endpoints, normalized coefficients, nonzero cell mass, and a positive scalar
completion denominator are stated explicitly.

- Analysis/FiniteWeightedVariance.lean: exact centered moments, translation
  energy, pairwise variance, subset and weight comparisons, the diameter
  bound, two-offset completion, and two-coordinate lower bounds.
- RH/CanonicalMobiusPrimeCells.lean: exact common-boundary quotient conditions,
  the first-profile Mertens increment and Lipschitz bound, the coordinate
  variance comparator and exact interval moments,
  first_boundary_variance_le, signedMobiusAverage_first_boundary_full_energy,
  and signedMobiusAverage_two_cells_full_energy.
- RH/CanonicalMobiusCellCeiling.lean: residual_combination_quotient,
  quotient_variance_le_full_energy, envelope_common_cell_identity,
  quotient_variance_le_inverseCeiling, and inverseCeiling_le_cell_certificate.

The complete-energy and finite-envelope equalities retain their entire
complement. The inverse-ceiling certificate is a finite inequality; it supplies
no uniform arithmetic provider along growing families.

Open: establish the uniform cell mean and complementary-energy upper bounds
needed for the cofinal squarefree closure argument. The exact finite identities
and lower-bound obstructions do not discharge these obligations.

The Baker--Harman--Pintz prime-selection consequence, general-q increment
formula, general multi-cell formula beyond the two-cell theorem, and numerical
interval certificates are analytic/computational material, not Lean-verified
providers. The Python computations used rational outward rounding and were
compared with direct exact Fraction sums on three small intervals:
[7,14): V=51547/3578575,
[17,26): V=599440502/91712671281,
[23,30): V=2406/994903.
The 16 prime selections and 20 nonempty q<=6 cells are recorded in the research
bundle Mobius_Common_Cell_Research_2026-10-15.zip. These numerical results have
not been checked by the Lean kernel.

Publication uses the required Lean-server checkpoint; its validation record
identifies the checked source and published commit.
