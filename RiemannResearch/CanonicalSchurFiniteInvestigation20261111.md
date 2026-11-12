# Canonical primorial Schur energies: finite certificates and a Q-only bound

Investigation: 11 November 2026. Publication preparation: 12 November 2026.
The original review was a scoped verified draft. Publication of the recovered
module is subject to the server checkpoint's full-project validation; the
checkpoint receipt supplies the final commit and verification result.

## Conclusion and evidence levels

The canonical iteration produces genuinely small **finite upper endpoints** in the tested stages. It also resolves a real obstruction to one proposed argument: the actual Schur energy is **not antitone under prime admission**. It increases from period 6 to period 30. Later tested admissions decrease it, through period 30030, but this finite trend proves no asymptotic rate.

A new unconditional bound for the actual energy is
\[
 F_n\le \frac{2000}{1017}\zeta(2)\|b_n\|_Q^2,
 \qquad b_n=P^Q_{V_n}B(1-f_n^Q).
\]
It uses the Q projection and complete matrix entries, without a Pareto inverse solve, carry inverse solve, or resolvent iteration. The complete identity behind the bound retains three nonnegative remainders. The formalization also supplies the exact Gram forcing, signed stage-transition identity, combined upper certificate, limiting residual bound, and a conditional RH consumer.

**Evidence:** the algebraic results are formalized in `QPrimorialSchurForcing.lean`; final verification details are recorded below. The numerical intervals use an external rational enclosure program with analytic complete-tail bounds. They have **not** been imported as Lean theorems about the actual canonical energies. The symbolic period-6 formulas and finite matrix reductions below are derived mathematics, independently checked numerically, rather than additional kernel-checked declarations.

The investigation does **not** establish \(E_\infty=0\), displacement vanishing, or RH. In particular, a positive finite lower bound is an obstruction to monotonicity or fixed-stage convergence to zero, **not** an obstruction to RH.

## 1. Exact dictionary, measures, and finite systems

Write \(H=n+3\), \(L=\prod_{p\le H}p\), and
\[
 D_L=\{d>1:d\mid L\},\qquad g_d(k)=\frac{k\bmod d}{d}\quad(k\ge1).
\]
The complete dictionary has \(2^{\pi(H)}-1\) elements. Its Q and Pareto weights are
\[
 Q(k)=\frac1{\zeta(2)k^2},\qquad P(k)=\frac1{k(k+1)},\qquad
 (Bf)(k)=\frac{f(k)}{k+1}.
\]
The exact change of metric is
\[
 \langle f,g\rangle_P
 =\zeta(2)\bigl(\langle f,g\rangle_Q-\langle f,Bg\rangle_Q\bigr).
\]
Here the physical sequences are the same; Lean's `toPareto` transports their Hilbert encodings.

For \(1\le a\le L\), set
\[
 w_Q(a;L)=\frac1{\zeta(2)}\sum_{j\ge0}\frac1{(a+jL)^2},\qquad
 w_P(a;L)=\sum_{j\ge0}\frac1{(a+jL)(a+jL+1)}.
\]
With \(X_{ad}=(a\bmod d)/d\), the **exact finite matrices and forcing vectors** are
\[
 G=X^T\operatorname{diag}(w_Q)X,\quad A=X^T\operatorname{diag}(w_P)X,
 \quad u=X^Tw_Q,\quad v=X^Tw_P.
\]
These finite residue-class sums already contain every positive physical site. There is no unaccounted physical cutoff.

The two canonical solves and errors are
\[
 c_Q=G^{-1}u,\quad c_P=A^{-1}v,\quad \delta=c_Q-c_P,
\]
\[
 E_Q=1-u^TG^{-1}u,\qquad E_P=1-v^TA^{-1}v,
 \qquad \|d\|_Q^2=\delta^TG\delta,
 \quad \|d\|_P^2=\delta^TA\delta.
\]
For any trial coefficients \(c\), the full error is exactly
\[
 \|1-\textstyle\sum_d c_dg_d\|_\nu^2
 =1-2c^Tm_\nu+c^TG_\nu c.
\]
Thus all signed cross terms are retained.

The forcing used in the new theorem is especially simple:
\[
 r=A c_Q-v,\qquad b_{\rm coeff}=\frac1{\zeta(2)}G^{-1}r,
 \qquad \|b\|_Q^2=\frac1{\zeta(2)^2}r^TG^{-1}r.
\]
Consequently,
\[
 \boxed{F_n\le \frac{2000}{1017\zeta(2)}
 (A G^{-1}u-v)^TG^{-1}(A G^{-1}u-v).}
\]
This is an arithmetic upper bound on the actual energy, not a bound on solve error. All matrices are those of the full dictionary.

In these coordinates the existing iteration is exactly
\[
 T=I-\frac4{3\zeta(2)}G^{-1}A,\quad s(a)=\frac43b_{\rm coeff}+Ta,
 \quad C(a)=\frac{18}{17}s(s(a))-\frac1{17}a,\quad a_0=0.
\]

## 2. Complete Schur elimination

Let \(E\) be the coordinate inclusion of prime conductors, \(W=E^TGE\), and \(R=E^TG\). The Q prime component has coefficients
\[
 x=W^{-1}R\delta.
\]
For each composite conductor, subtract its Q projection onto the prime span. The columns of the resulting matrix \(K\) form the Q carry space. Define
\[
 Z=E-K(K^TAK)^{-1}K^TAE,\qquad S=Z^TAZ.
\]
Then \(Zx\) is the Pareto Schur lift, \(S\) is the complete Schur matrix, and
\[
 F=x^TSx.
\]
An equivalent smaller formula avoids explicitly constructing the carry basis:
\[
 M=RA^{-1}R^T,\qquad h=R\delta=E^T(u-GA^{-1}v),
\]
\[
 \boxed{S=WM^{-1}W,\qquad F=h^TM^{-1}h.}
\]
Indeed, the Pareto minimum among vectors with prescribed Q prime pairings \(h\) is attained at \(A^{-1}R^TM^{-1}h\), with energy \(h^TM^{-1}h\). The feasible directions are precisely the carry space. This proves the formula without discarding its composite block.

For an iterate \(a_k\), use \(t_k=W^{-1}Ra_k\). The exact trial energy is
\[
 J(t_k)=2t_k^TSx-t_k^TSt_k,
\]
so the existing a priori endpoint is \(J(t_k)+c\zeta(2)E_Q289^{-k}\), with \(c=966289/8136000\). The posterior endpoint uses the **complete** Q energy of \(a_k-a_{k-1}\).

## 3. Explicit period-6 matrices

The first stage is \(H=3,n=0,L=6,D=(2,3,6)\). Put
\[
 \ell=\frac{L(2,\chi_3)}{\zeta(2)},\qquad
 L(2,\chi_3)=\sum_{j\ge0}\left((3j+1)^{-2}-(3j+2)^{-2}\right).
\]
Direct residue regrouping gives
\[
G=\begin{pmatrix}
3/16&1/6-5\ell/48&3/16-5\ell/24\\
1/6-5\ell/48&20/81-\ell/6&41/162-5\ell/16\\
3/16-5\ell/24&41/162-5\ell/16&419/1296-11\ell/24
\end{pmatrix},
\quad
u=\begin{pmatrix}3/8\\4/9-\ell/6\\35/72-11\ell/24\end{pmatrix}.
\]
Here the displayed vector \(u\) is the Q mean vector. Put \(a=\log2,b=\log3,t=\pi/\sqrt3\). Then
\[
A=\begin{pmatrix}
a/4&a/6+b/12-t/18&a/4+b/24-5t/72\\
a/6+b/12-t/18&2b/9-t/27&a/18+7b/36-2t/27\\
a/4+b/24-5t/72&a/18+7b/36-2t/27&5(a+b)/36-7t/108
\end{pmatrix},
\quad v=\begin{pmatrix}a/2\\b/3\\(a+b)/6\end{pmatrix}.
\]
For example, the six unnormalized Q residue masses divided by \(\zeta(2)\) are
\[
 (1/3+5\ell/8,\;1/9+\ell/8,\;1/12,\;1/9-\ell/8,\;1/3-5\ell/8,\;1/36).
\]
The Pareto masses are
\[
 (t/6+a/3,\;t/12+b/4-a/3,\;t/12-b/4+a/3,
 t/6-a/3,\;-t/4+b/4+a/3,\;1-t/4-b/4-a/3).
\]
Multiplying these weights by the displayed residue vectors verifies every matrix entry. The numerical enclosure program uses elementary series with bounded tails; these symbolic evaluations are not prerequisites for its certificates.

## 4. Certified finite results

Every interval below is rounded outward. The underlying JSON retains finer dyadic endpoints and the full matrices.

| Largest admitted prime H | Lean stage n | Period L | Dimension | Actual Schur energy F: rigorous enclosure |
|---:|---:|---:|---:|---:|
| 3 | 0 | 6 | 3 | [0.000181087426502633, 0.000181087426502634] |
| 5 | 2 | 30 | 7 | [0.000196801939578787, 0.000196801939578788] |
| 7 | 4 | 210 | 15 | [0.000140246568556164, 0.000140246568556165] |
| 11 | 8 | 2310 | 31 | [0.000104279499176019, 0.000104279499176020] |
| 13 | 10 | 30030 | 63 | [0.000084914944565890, 0.000084914944565891] |

The table indices matter: Lean uses a prime cutoff \(n+3\), not the number of primes. Stages between prime admissions repeat the same space.

| Period | Complete Q error EQ, approximate | Certified Pareto error upper | Certified U(n,3) upper | Certified posterior upper using a3-a2 |
|---:|---:|---:|---:|---:|
| 6 | 0.0547669433702622 | 0.078293254002322548 | 0.000181087868417731 | 0.000181087429420563 |
| 30 | 0.0254002254357182 | 0.037483824559636169 | 0.000196802144091844 | 0.000196801942401600 |
| 210 | 0.0168704360610230 | 0.025433972583370402 | 0.000140246704358435 | 0.000140246570764773 |
| 2310 | 0.0135494810654130 | 0.020670658990067073 | 0.000104279608164516 | 0.000104279501039362 |
| 30030 | 0.0117529978963768 | 0.018059970522682712 | 0.000084915039058384 | 0.000084914946203925 |

Thus the actual endpoint, rather than merely its approximation error, is small at these stages. Three cycles nearly resolve the actual energy; further cycles at the same stage converge to its positive value.

For comparison, the new Q-only upper bounds are respectively
\[
 0.000232347165616678,\quad0.000240956018111335,\quad
 0.000202529520877449,\quad0.000163768332619970,\quad
 0.000137275773194917.
\]
These require zero resolvent cycles. They improve the original zero-trial budgets by factors of about 46, 21, 16, 16, and 17 respectively. They remain less sharp than the resolved or posterior certificates.

By the existing monotonicity theorem for the Pareto residual errors, the last complete solve implies
\[
 E_\infty\le E_{10}<0.018059970522683.
\]
This is a bound on **squared** Pareto norm. It is a finite numerical certificate, not a proof that the error vanishes.

The general cubic Schur criterion is much weaker at these small cutoffs: its stage term alone is \(8/13\) at the last stage. The direct Pareto error bound is the strongest finite residual bound obtained here. The value of the Schur route is its scalar arithmetic target, not superiority of that cubic estimate at low stages.

## 5. New complete forcing identity and proof

Let \(\alpha=1017/2000\), \(\beta=983/2000\), \(r=1-f_Q\), \(b=P^Q_VBr\), \(d=f_Q-f_P\), and \(s=L_nx_n\). The exact identity is
\[
\frac{\zeta(2)}\alpha\|b\|_Q^2
=F_n+\|d-s\|_P^2
+\frac{\zeta(2)}\alpha\|b-\alpha d\|_Q^2
+\zeta(2)\left(\beta\|d\|_Q^2-\langle d,Bd\rangle_Q\right).
\]
All three terms after \(F_n\) are nonnegative. The last uses the existing four-site arithmetic certificate for every vector in the squarefree legal closure.

Proof: the Q-only fixed point gives \(d=b+P^Q_VBd\). Pair with \(d\in V\), then use the metric identity:
\[
 \|d\|_P^2=\zeta(2)\langle d,b\rangle_Q.
\]
The exact carry elimination gives
\[
 \|d\|_P^2=F_n+\|d-s\|_P^2.
\]
Expand \(\|b-\alpha d\|_Q^2\), substitute these equalities, and use \(1-\alpha=\beta\). This proves the equality before estimating any term.

The formalization proves the complete Gram forcing for every \(v\in V\):
\[
 \zeta(2)\langle v,b\rangle_Q
 =\langle v,f_Q\rangle_P-\langle v,1\rangle_P.
\]
It then combines the new upper bound with both previous endpoints by taking their minimum, and instantiates the existing limiting-error theorem.

A noncircular arithmetic target is now to bound
\[
 (A G^{-1}u-v)^TG^{-1}(A G^{-1}u-v)
\]
cofinally by numbers tending to zero. This expression is specified without the unknown displacement or the Pareto optimizer. Its **decay is still Open**. Merely redefining the open quantity or solving the finite system more accurately does not supply that decay. No claim of a logically weaker hypothesis than the established displacement criterion is made.

## 6. Successive prime admissions and signed cancellation

Put \(y_n=\operatorname{toPareto}(L_nx_n)\). The formalized exact transition is
\[
 F_m-F_n=2\langle y_n,y_m-y_n\rangle_P+\|y_m-y_n\|_P^2.
\]
The enclosure program transports both coefficient vectors into the enlarged complete dictionary before evaluating this identity.

| Period admission | Twice the signed cross term (approximate) | Increment norm squared (approximate) | Change in F (approximate) |
|---|---:|---:|---:|
| 6 to 30 | +0.000001052647071 | 0.000014661866005 | +0.000015714513076 |
| 30 to 210 | -0.000065656891958 | 0.000009101520935 | -0.000056555371023 |
| 210 to 2310 | -0.000040638734157 | 0.000004671664777 | -0.000035967069380 |
| 2310 to 30030 | -0.000020982008393 | 0.000001617453783 | -0.000019364554610 |

Each sign is certified in `admissions.json`. The first cross term is positive; the next three are negative and dominate the nonnegative increment energy. Bounding all cross terms by absolute values would erase precisely the cancellation observed in those decreases.

For each metric separately, the ordinary block-Gram admission identity is also exact. If the enlarged Gram matrix is \(\begin{pmatrix}G&C\\C^T&D\end{pmatrix}\), with mean vector \((u,w)\), then
\[
 H=D-C^TG^{-1}C,\quad e=w-C^TG^{-1}u,\quad
 E_{\rm old}-E_{\rm new}=e^TH^{-1}e\ge0.
\]
Thus each projection error decreases, while the Schur energy formed from the **difference of the two projections** need not decrease. The certified period-6/30 comparison rules out inferring its monotonicity from nestedness.

## 7. Prime-scale averaging and Ramanujan/CRT checks

For nonnegative weights \(\lambda_p\) on admitted primes with sum 1, the exact normalized-pairing estimate and Schur duality give
\[
 E_P\le\sqrt{C_\lambda F_n}+a_\lambda\sqrt{E_P},\qquad
 C_\lambda=\zeta(2)^2(p\lambda_p)^TM(p\lambda_p),\qquad
 a_\lambda=\sum_p\frac{\lambda_p}{\sqrt p}.
\]
Hence, writing \(t=\sqrt{C_\lambda F_n}\),
\[
 E_P\le\left(\frac{a_\lambda+\sqrt{a_\lambda^2+4t}}2\right)^2.
\]
The program encloses this expression for the largest prime alone and for uniform weights on primes in \([H/2,H]\). At \(H=13\), the resulting upper bounds are below 0.144966033 and 0.161311744, respectively. Both are weaker than the direct complete Pareto solve, below 0.018059971. Uniform prime-block averaging therefore did **not** provide useful additional cancellation in these tests. This does not rule out better signed or optimized weights.

The Ramanujan identity
\[
 \Delta g_d(k)=\frac1d-\mathbf1_{d\mid k}
 =-\frac1d\sum_{\substack{q\mid d\\q>1}}c_q(k)
\]
retains every composite divisor. It is an invertible triangular change of coordinates on the same finite squarefree dictionary. Changing coordinates preserves the full inverse quadratic; it does not by itself reduce it. Haar orthogonality cannot be substituted for either of the nonuniform physical Q/Pareto weights.

The inspected `IntegratedRamanujanRankTwo.lean` explicitly leaves its proposed rank-two identification of the **actual** Gram matrix as hypothesis `hXi`. Consequently it supplies no unconditional matrix simplification usable to force the computed energies downward. No such identification was assumed here.

Likewise, the CRT carry space has been retained in the exact Schur lift. The measured carry energies are positive; an infinite cancellation path for arbitrary carry atoms does not identify the coefficients of this canonical displacement or make its finite Schur energy vanish.

## 8. External certification method and retained artifacts

The original review recorded the following invocation, with Python and
mpmath installed:

```bash
python certify_schur.py --cutoffs 3 5 7 11 13 --output certificates
```

The referenced external program (also named `tools/certify_primorial_schur.py`
in the proposed file list) was not present in the recovered workspace on
12 November. The numerical summary JSON is retained, but this command is
not currently reproducible from this repository alone. The numerical
results below describe the original investigation; they were not rerun
during publication preparation and are not Lean-certified.

Every arithmetic operation used to certify a bound rounds outward on the dyadic grid \(2^{-224}\). Candidate inverses are obtained with mpmath, converted to exact dyadic matrices, and accepted only after a rational Neumann residual test. For an interval matrix \(A\) and a chosen exact matrix \(R\), if
\[
 q\ge\|I-RA\|_\infty,\quad q<1,
\]
then
\[
 \|A^{-1}-R\|_\infty\le\frac{q}{1-q}\|R\|_\infty.
\]
The computation encloses each inverse entry by this bound. Floating-point inverse accuracy is not an assumption.

For each residue, sum the first \(J=32\) lattice terms and put \(x=a+JL\). Euler–Maclaurin with \(m=16\) gives the Q tail center
\[
 \frac1{Lx}+\frac1{2x^2}+\sum_{j=1}^{m}\frac{B_{2j}L^{2j-1}}{x^{2j+1}}
\]
with absolute remainder at most
\[
 \frac{|B_{2m}|L^{2m-1}}{x^{2m+1}}.
\]
The Pareto tail center is
\[
 \frac1L\log(1+1/x)+\frac12\left(\frac1x-\frac1{x+1}\right)
 +\sum_{j=1}^{m}\frac{B_{2j}L^{2j-1}}{2j}
 \left(x^{-2j}-(x+1)^{-2j}\right),
\]
with absolute remainder at most the absolute value of its final displayed Bernoulli term. The logarithm is enclosed by its alternating Taylor polynomial of degree 24 and the first omitted term. Zeta(2) itself is enclosed by the same Q procedure with \(L=a=1,J=64\). Powers are evaluated in scaled variables \(L/x\) to avoid precision loss before multiplication by large powers of \(L\).

The remainder claims follow from the integral Euler–Maclaurin remainder and \(|\widetilde B_{2m}(t)|\le|B_{2m}|\): see [NIST DLMF 2.10.1](https://dlmf.nist.gov/2.10.E1) and [24.9.1](https://dlmf.nist.gov/24.9.E1). These analytic remainder facts and the implementation have not been formally connected to Lean's canonical Gram matrices.

The emitted files include exact dyadic enclosures of all five pairs of Gram matrices, both mean and coefficient vectors, the Schur matrices, forcing vectors, finite energies, iterative endpoints, signed admissions, and inverse-residual audits. Independent high-precision special-function evaluations were used only as cross-checks of sampled complete residue weights.

## 9. Recovered repository changes and verification

Base inspected: `6c4fe3312e24b00813bcc5c329cf28ba0fe14333`, containing the requested endpoint commit `1a7420b1352a4f49dfc62c3bc42b578b25afcb73`.

Recovered additions/edits:

- `RiemannResearch/RH/QPrimorialSchurForcing.lean`: exact Gram forcing, complete forcing-square decomposition, actual energy upper bound, combined endpoint, limiting residual bound, signed transition, and conditional RH consumer.
- `RiemannResearch.lean`: export the new module.
- `RiemannResearch/THEOREM_CATALOG_SQUAREFREE_CRT_DISPLACEMENT_20261109.md`: record the new bound and keep cofinal forcing decay Open.
- `RiemannResearch/CanonicalSchurFiniteInvestigation20261111.md`: this research report.
- `tools/certify_primorial_schur.py`: referenced by the original review, but absent from the recovered workspace and not included in this change.
- `RiemannResearch/CanonicalSchurFiniteCertificates20261111.json`: numerical summary and signed admission evidence.

Final audited acceptance: `job_5_JF7ANAsHxmvXrry5AqiVIr7-yF7JRC`, Bazel/BuildBuddy, exit 0, `verified=true`, 51.773 seconds of server-reported verification time. The scope is an audit snippet importing the final module and its transitive dependencies; it is not the full-project aggregate target. Seven exact `#guard_msgs` assertions require precisely `[propext, Classical.choice, Quot.sound]` for the Gram forcing, complete energy identity, energy bound, limiting residual bound, combined endpoint, conditional RH consumer, and signed transition. The earlier focused module build also succeeded. These server timings are separate from workspace setup, transport, and waiting in the conversation.

Final module SHA-256: `251f90bea402b90f3cf5c815a44796290bdc65c63c82e00c3941c2ff841dcdd5`. The conditional RH theorem still assumes convergence of the correction to zero; its axiom audit does not discharge that hypothesis.

At the original review, no full-project publication checkpoint had been run
and no new commit existed. The user requested publication on 12 November.
The publication checkpoint must validate the entire project and any
integrated source before pushing; its terminal receipt, rather than the
historical scoped receipt above, establishes publication success. The
numerical enclosures remain separate from the kernel-checked identities.

## 10. What would close the RH criterion

A useful next theorem would provide a **uniform arithmetic estimate** driving the complete Q-only inverse quadratic to zero along cofinal stages, or control the signed prime-admission cross terms strongly enough to force \(F_n\to0\). The present computations locate the cancellation and refute a naive monotonicity claim. They do not control all future admissions.

Neither small finite endpoints, accurate iterative solves, finite decreases, nor a change to Ramanujan coordinates proves \(E_\infty=0\). The outstanding step remains a proof of cofinal smallness of an actual energy upper bound.
