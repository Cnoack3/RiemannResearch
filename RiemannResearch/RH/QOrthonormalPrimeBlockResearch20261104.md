# Orthonormal residue coordinates and prime-block gains — 4 November 2026

## Published starting points

Let Q(n)=1/(zeta(2)n^2), n>=1, and g_d(n)=(n mod d)/d.
Let V be the closed real span of squarefree g_d, d>=2. No constant is
adjoined. Let (e_k) be the complete-Q Gram–Schmidt basis of V.

Primary sources were considered before the repository:
- B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space
  reformulation of the Riemann hypothesis*, Proc. Indian Acad. Sci.
  (Math. Sci.) 116 (2006), 137–146, Remark 8:
  https://www.isibang.ac.in/~statmath/eprints/2005/isibc200535.pdf
  This supports the squarefree closure criterion. Q and Pareto norms are
  equivalent. RH-to-squarefree-closure remains a literature input here.
- D. Bump, *Hilbert space basics*, Lemma 2.1.1 and Proposition 2.1.2:
  https://sporadic.stanford.edu/bump/group/gr2_1.html
  This supports orthonormal coordinates and Gram–Schmidt.
- V. Albani, P. Elbau, M. V. de Hoop and O. Scherzer, *Optimal Convergence
  Rates Results for Linear Inverse Problems in Hilbert Spaces*, Numer.
  Funct. Anal. Optim. 37 (2016), 521–540,
  doi:10.1080/01630563.2016.1144070.
  This supports Tikhonov normal equations and spectral analysis. Its
  convergence-to-solution statements assume solvability.
- V. N. Temlyakov, *Brief introduction in greedy approximation*,
  Russian Math. Surveys 80:5 (2025), 763–841:
  https://www.mathnet.ru/php/archive.phtml?jrnid=rm&option_lang=eng&paperid=10245&wshow=paper
  This supports adaptive orthogonal approximation. Convergence theorems
  for targets in the dictionary closure cannot assume the membership of 1.
- Euler's prime reciprocal divergence is already in Mathlib:
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/SumPrimeReciprocals.lean
  Mathlib follows the Erdos proof in *Proofs from THE BOOK*.

## Exact coefficient geometry

Put alpha_k=<1,e_k>_Q and delta^2=||1-P_V 1||_Q^2. For every a in l2,
\[
 \left\|1-\sum_k a_k e_k\right\|_Q^2
 =\delta^2+\sum_k(a_k-\alpha_k)^2.
\]
For a finite coefficient vector,
\[
 \left\|1-\sum_{k=1}^N a_k e_k\right\|_Q^2
 =1-\sum_{k=1}^N\alpha_k^2+\sum_{k=1}^N(a_k-\alpha_k)^2.
\]
The finite optimum is exactly a_k=alpha_k, with energy at most one.
The existing QSquarefreeResidueBasis.residueBasis_error_exact
retains the entire infinite orthogonal residual.

An l2 sequence represents a vector of V. Taking a=alpha represents P_V 1;
it does not identify that vector with 1. The unproved saturation is delta=0.

For example e_1=4 g_2/sqrt(3), alpha_1=sqrt(3)/2, and
alpha_1 e_1=2g_2=1_odd. The full squared error is Q(even)=1/4.

## Numerical conductor-order examples

Wolfram evaluated complete periodic Q moments at 60-digit working precision.
These are numerical diagnostics, not interval-certified inequalities or
Lean proofs of decimal values.

| N | Added conductor | alpha_N^2 | Remaining squared error |
|---|---:|---:|---:|
| 1 | 2 | 0.750000000000 | 0.250000000000 |
| 2 | 3 | 0.181314717515 | 0.068685282485 |
| 3 | 5 | 0.041448381449 | 0.027236901036 |
| 4 | 6 | 0.000055334181 | 0.027181566855 |
| 5 | 7 | 0.009923596865 | 0.017257969991 |
| 6 | 10 | 0.000009265561 | 0.017248704430 |

The supplied first three basis-vector coefficients were reproduced.
The relative gain for conductor 6 is approximately 0.00203159 in this order.
This is order-dependent: it does not mean that g_6 is intrinsically unimportant.
After g_2 and g_3 alone, adding g_6 lowers the error from 0.06868528 to
0.05476694. Total gain for a fixed enlarged subspace is basis-independent.

## The prime-block criterion

Let L_m be the product of the first m primes, W_m=span{g_d:1<d|L_m},
P_m its Q-orthogonal projection, R_m=1-P_m 1, E_m=||R_m||_Q^2.
Take W_0={0}, E_0=1.

If p is the next prime, the added atoms are g_(pd), d|L_m. Orthogonalize them
against W_m and within their new block, obtaining eta_(m,j), j=1,...,2^m.
All are finite legal combinations. The exact identity is
\[
 E_m=E_{m+1}+\sum_j|\langle R_m,\eta_{m,j}\rangle_Q|^2.
\]
Pairing eta with R_m is equivalent to pairing it with 1.

Every E_m is strictly positive: functions in W_m vanish at L_m, while
1 does not, and Q(L_m)>0. Define
\[
 \theta_m=\frac{E_m-E_{m+1}}{E_m}\in[0,1).
\]
Then
\[
 E_M=\prod_{m<M}(1-\theta_m),\qquad
 E_M\to0\ \Longleftrightarrow\ \sum_m\theta_m=\infty.
\]
The scalar product equivalence is already in ResidualGainProduct.

A sufficient arithmetic estimate is, for one c>0,
\[
 \sum_j|\langle R_m,\eta_{m,j}\rangle_Q|^2
 \ \ge\ \frac{c}{p_{m+1}}E_m.
\]
It implies
\[
 E_M\le \exp\!\left(-c\sum_{j=1}^M\frac1{p_j}\right)\longrightarrow0.
\]
A bound after finitely many stages also suffices on the tail. The new Lean
scalar consumer uses a bound at every prime, indexed by integer cutoffs;
a tail specialization was not added here.

The c/p estimate is **Open**. It is a sufficient condition, not asserted
equivalent to RH. Nonsummability of the actual gains is the exact criterion.

| New prime | L_m | dim W_m | E_m | theta_(m-1) | p_m theta_(m-1) |
|---:|---:|---:|---:|---:|---:|
| 2 | 2 | 1 | 0.250000000000 | 0.750000000000 | 1.500000000000 |
| 3 | 6 | 3 | 0.054766943370 | 0.780932226519 | 2.342796679557 |
| 5 | 30 | 7 | 0.025400225436 | 0.536212469190 | 2.681062345949 |
| 7 | 210 | 15 | 0.016870436061 | 0.335815498814 | 2.350708491701 |

These four numerical blocks are consistent with c=1; they establish no
uniform positive lower bound.

## Regularization in the orthonormal basis

Let T(a)=Delta(sum a_k e_k), where Delta is anchored physical difference.
Then T:l2 -> L2(Q) is bounded and injective. The primitive Gram is I, but
the derivative Gram D=T* T is generally not diagonal.

For N basis vectors set
\[
 D_{ij}=\langle\Delta e_i,\Delta e_j\rangle_Q,\quad
 b_i=\langle\delta_1,\Delta e_i\rangle_Q=e_i(1)/\zeta(2),\quad
 q=1/\zeta(2).
\]
The exact finite objective and minimizer are
\[
 J_\lambda(a)=q-2b^Ta+a^TD_Na+\lambda a^Ta,\qquad
 a_{N,\lambda}=(D_N+\lambda I)^{-1}b.
\]
The minimum is q-b^T(D_N+lambda I)^(-1)b. The energy penalty is exactly the
sum of coefficient squares, as needed by QPrimitiveEnergyClosure.

If D_N v_j=s_j v_j with an orthonormal eigenbasis, then
\[
 \|a_{N,\lambda}\|_2^2
 =\sum_j\frac{|\langle b,v_j\rangle|^2}{(s_j+\lambda)^2}.
\]
This finite Picard-style diagnostic tracks target mass in small-eigenvalue
directions. The infinite operator has not been shown compact; no countable
eigenbasis of D is assumed.

Seek a bound along a chosen diagonal N_j,lambda_j with lambda_j -> 0,
not for every independent pair N,lambda. Derivative-only finite optimizers
can have diverging primitive norms.

For the first two basis vectors,
\[
 D_2\approx
 \begin{pmatrix}1.3333333333&-0.7564688287\\
 -0.7564688287&1.8661612086\end{pmatrix}.
\]
The existing QDifferenceNoncoercivity result rules out a uniform lower
bound on D as legal spaces grow.

## Reproducible finite computation

For conductors D, take L=lcm(D), v_r(d)=(r mod d)/d, and the exact periodic
weight
\[
 w_L(r)=\frac{\zeta(2,r/L)}{\zeta(2)L^2},\quad 1\le r\le L.
\]
The numerator is Hurwitz zeta. This sums the complete Q tail in each residue
class, solely for finite moments here, not a trigamma convergence argument.

Form G=sum_r w_L(r) v_r v_r^T and m=sum_r w_L(r)v_r. For the upper
Cholesky factor G=R^T R, the basis transformation is R^(-1),
alpha=R^(-T)m, and the squared error is 1-m^T G^(-1)m.
The Wolfram orthonormality discrepancy was below its 58-digit precision scale.

## Verification and open work

New module: Analysis/ResidualPrimeGain.lean.
Namespace: RiemannResearch.Analysis.ResidualGain.
Candidate job_er24iP5yP6mmFKEjahyDuQfNQjjQflit passed:
verified=true, exit_code=0, reported verification duration 7.771 seconds.
The new consumer and inspected existing exact-error and regularized-budget
theorems used only propext, Classical.choice, Quot.sound.
The project checkpoint separately validates the saved source.

**Open:** prove actual relative prime-block gains have a divergent sum,
or prove a complete regularized O(lambda) budget along a selected diagonal.
The c/p sufficient bound is also Open.

The scalar prime-gain implication is formalized. Its application to the
actual residue projection family is a mathematical derivation above, not
a newly formalized RH implication. No RH proof is claimed.
