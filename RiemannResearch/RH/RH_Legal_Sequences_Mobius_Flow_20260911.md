# Legal sequences for the Pareto reflection criterion

Date: 2026-09-11.

Source: `ParetoReflectionVarianceVerification20260911.md` and the accompanying definitions of the two legal seeds. No Lean was used. The mathematical arguments below are ordinary proofs; the numerical experiments are floating-point exploration, not formal or interval certificates.

**Outcome.** This note gives an explicit finite-dimensional sequence of legal mean-one candidates, a complete coefficient parametrization for matching any finite initial segment, and necessary signed Möbius relations for every successful sequence. It proves that omitting dilation 5, using only nonnegative coefficients, or using only the 2-seed prevents convergence. It does not prove that the candidate variances tend to zero, and does not prove RH.

## 1. Conventions and the target

Let

\[
p_n=\frac1{n(n+1)},\qquad R_L(n)=n\bmod L,
\]

and use the actual two-seed generators

\[
g_{a,m}(n)=D_mR_a(n)=R_{am}(n)-R_m(n)
=m\left\lfloor\frac nm\right\rfloor-am\left\lfloor\frac n{am}\right\rfloor,
\quad a\in\{2,3\},\ m\ge1.
\]

A legal packet is a finite real signed sum

\[
F(n)=\sum_{m\ge1}\bigl(c_{2,m}g_{2,m}(n)+c_{3,m}g_{3,m}(n)\bigr).
\]

Set missing coefficients to zero. Every positive integer dilation is allowed. In particular, the restriction to two seed types does **not** restrict dilations to numbers of the form \(2^i3^j\).

The source gives

\[
\mathbb EF=(\log2)\sum_m c_{2,m}+(\log3)\sum_m c_{3,m}.
\]

For mean-one packets the required quantity is

\[
v(F)=\operatorname{Var}(F(N))=\sum_{n\ge1}p_n(F(n)-1)^2.
\]

The source compares this with its reflection surrogate:

\[
v(F)\le J_Q(F)+\frac{\pi^2}{Q}U_Q(F)\le(1+\pi^2)v(F).
\]

Consequently the two vanishing objectives in the source are equivalent to \(v(F_j)\to0\). We use the full Pareto norm throughout.

## 2. Necessary Möbius relations: what the coefficients must do

Define the finite floor coefficients

\[
\alpha_d=d\left(c_{2,d}+c_{3,d}
-\mathbf1_{2\mid d}c_{2,d/2}
-\mathbf1_{3\mid d}c_{3,d/3}\right).
\tag{2.1}
\]

Then exactly

\[
F(n)=\sum_{d\ge1}\alpha_d\left\lfloor\frac nd\right\rfloor.
\tag{2.2}
\]

Although the generator coefficients can be nonunique, these finite floor coefficients are determined by the function. With \(F(0)=0\), taking integer differences and using divisor Möbius inversion gives

\[
\Delta F(n)=\sum_{d\mid n}\alpha_d,
\qquad
\alpha_d=\sum_{k\mid d}\mu(d/k)\Delta F(k).
\tag{2.3}
\]

**Proposition.** If legal mean-one packets \(F_j\) satisfy \(v(F_j)\to0\), then for every fixed \(d\ge1\),

\[
\boxed{\quad
 d\left(c^{(j)}_{2,d}+c^{(j)}_{3,d}
-\mathbf1_{2\mid d}c^{(j)}_{2,d/2}
-\mathbf1_{3\mid d}c^{(j)}_{3,d/3}\right)\longrightarrow\mu(d).
\quad}
\tag{2.4}
\]

**Proof.** Since each \(p_n>0\),

\[
|F_j(n)-1|^2\le n(n+1)v(F_j)\longrightarrow0.
\]

Thus \(\Delta F_j(1)\to1\) and \(\Delta F_j(k)\to0\) for each fixed \(k>1\). Apply the finite divisor sum in (2.3). This establishes (2.4) without exchanging an infinite sum and a limit.

In particular, for every prime \(p\ge5\),

\[
\boxed{c^{(j)}_{2,p}+c^{(j)}_{3,p}\longrightarrow-\frac1p.}
\tag{2.5}
\]

At every fixed squarefree \(d\) coprime to 6, the analogous limit is \(\mu(d)/d\). These are constraints on aggregated coefficients at the same dilation, not assertions that each of the two coefficients separately converges.

A quantitative form for primes is especially simple. From (2.3),

\[
p(c_{2,p}+c_{3,p})=F(p)-F(p-1)-F(1).
\]

Writing \(e_n=F(n)-1\) and applying weighted Cauchy–Schwarz,

\[
\boxed{
 v(F)\ge
 \frac{|p(c_{2,p}+c_{3,p})+1|^2}{2p^2+2}.
}
\tag{2.6}
\]

The denominator is exactly \(p(p+1)+(p-1)p+2\).

Two immediate consequences:

* If dilation \(m=5\) is omitted, then \(v(F)\ge1/52\), even with arbitrary signs at every other dilation.
* If all generator coefficients are nonnegative, then \(v(F)\ge1/52\) as well.

Thus neither positive averaging alone nor dilations restricted to \(2^i3^j\) can close the criterion. Both negative coefficients and the other prime dilations are necessary. This conclusion does not impose a quantitative cutoff for when a particular prime must enter a sequence; it concerns each fixed prime as the approximation error tends to zero.

## 3. A finite family with an exactly correct initial segment

Write \(b_{a,m}=m c_{a,m}\). Fix \(K\), take \(b_{a,m}=0\) for \(m>K\), and choose \(b_{2,m},b_{3,m}\) successively so that

\[
\boxed{
 b_{2,m}+b_{3,m}
 =\mu(m)+2\mathbf1_{2\mid m}b_{2,m/2}
       +3\mathbf1_{3\mid m}b_{3,m/3},
 \quad1\le m\le K.
}
\tag{3.1}
\]

At each index the sum is prescribed and its split between the two seeds is free. Hence this is an explicit parametrization with \(K\) real splitting parameters. Equation (2.1) gives \(\alpha_m=\mu(m)\) for \(m\le K\), so

\[
F_K(n)=\sum_{d\le n}\mu(d)\left\lfloor\frac nd\right\rfloor=1,
\qquad1\le n\le K.
\tag{3.2}
\]

The last identity follows by reversing the finite divisor sum.

The associated boundary terms are also explicit:

\[
\begin{aligned}
F_K(n)
={}&\sum_{d\le K}\mu(d)\left\lfloor\frac nd\right\rfloor\\
&-2\sum_{K/2<m\le K}b_{2,m}\left\lfloor\frac n{2m}\right\rfloor
-3\sum_{K/3<m\le K}b_{3,m}\left\lfloor\frac n{3m}\right\rfloor.
\end{aligned}
\tag{3.3}
\]

This identifies the actual signed boundary correction. It is not legitimate to discard either sum or their mixed energy. The floor expression as a whole is bounded because it is a finite legal packet.

### Exact mean correction is always possible

The legal direction

\[
h_K=g_{3,K}-g_{2,K}=R_{3K}-R_{2K}
\]

vanishes for \(n<2K\) and has mean \(\log(3/2)\). Therefore

\[
\widetilde F_K
=F_K+\frac{1-\mathbb EF_K}{\log(3/2)}h_K
\tag{3.4}
\]

is still exactly 1 on \(1\le n\le K\), is finite and legal, and has mean exactly 1. Thus **finite legality, exact initial matching, and exact normalization are simultaneously achievable for every K.**

The correction is not free in norm. For the continuous step realization described in Section 7, change of variables gives

\[
\|h_K\|_{L^2(p)}^2=K\|h_1\|_{L^2(p)}^2.
\]

An uncontrolled mean discrepancy can therefore incur a growing tail cost. The full energy after (3.4) retains its cross term with \(F_K-1\).

A useful extension is to allow all \(m\le M\), with \(M>K\), impose (3.1) only for \(m\le K\), and use the remaining coefficients to reduce the complete tail. Generators with \(m>K\) vanish on the prescribed initial segment.

### A concrete sufficient tail estimate

For any resulting mean-one packet equal to 1 up to K, set

\[
A_{K,j}=\frac1{2^jK}
\sum_{2^jK<n\le2^{j+1}K}|F_K(n)-1|^2.
\]

Then

\[
\boxed{
 v(F_K)\le\frac1K\sum_{j\ge0}2^{-j}A_{K,j}.
}
\tag{3.5}
\]

This follows from \(n(n+1)\ge(2^jK)^2\) on the indicated block. No sign or covariance has been removed from the squared packet.

For example, it would suffice to construct the splitting and tail coefficients with

\[
A_{K,j}\le B_K2^{\theta j},\qquad\theta<1,\quad B_K=o(K).
\tag{3.6}
\]

Then \(v(F_K)\le B_K/[K(1-2^{\theta-1})]\to0\), and the source's RH implication applies. This estimate is **unproved**. It makes precise the allowable growth of the entire signed boundary correction across scales; exact initial matching alone establishes none of it.

## 4. A fully specified sequence of mean-one candidates

For a practical default, permit both seeds and all \(1\le m\le M\), without requiring an exactly correct initial segment. List these \(2M\) generators as \(g_i\). Define

\[
G_M(i,j)=\mathbb E[g_i(N)g_j(N)],\qquad\ell_i=\mathbb E g_i=\log a_i.
\]

Use the full infinite Pareto second moment, not the uniform CRT Gram matrix. Let \(G_M^\dagger\) be the Moore–Penrose inverse. Set

\[
S_M=\ell^TG_M^\dagger\ell,
\qquad
\boxed{c_M=\frac{G_M^\dagger\ell}{S_M},\qquad
 F_M=\sum_i(c_M)_i g_i.}
\tag{4.1}
\]

These are actual legal coefficients and \(\mathbb EF_M=1\). The finite formula is well-defined: \(\ell\) lies in the range of \(G_M\), because a zero-norm packet also has zero mean, and at least one generator has nonzero mean.

The variational identity is

\[
\boxed{
 v(F_M)=\min_{\ell^Tc=1}(c^TG_Mc-1)=\frac1{S_M}-1.
}
\tag{4.2}
\]

It follows either by Cauchy–Schwarz in the Gram inner product or by Lagrange multipliers on its range. Pseudoinverses merely handle exact generator dependencies, such as

\[
g_{2,m}+g_{3,2m}=g_{3,m}+g_{2,3m}.
\]

The candidate variances are nonincreasing in M because the legal spaces are nested. This construction does not by itself show that their limit is zero. The remaining statement is \(S_M\to1\). If any sequence in the same two-seed legal family works, this minimizing sequence works as well, since every finite packet occurs in some space in the exhaustion.

### Computing the exact infinite-tail matrix

For \(g_i=g_{a,m}\), \(g_j=g_{b,k}\), take the pairwise period

\[
q=\operatorname{lcm}(am,bk).
\]

For \(1\le r\le q\),

\[
W_q(r)=\sum_{t\ge0}\frac1{(r+tq)(r+tq+1)}
=\frac{\psi((r+1)/q)-\psi(r/q)}q.
\tag{4.3}
\]

Then

\[
G_M(i,j)=\sum_{r=1}^q W_q(r)g_i(r)g_j(r).
\tag{4.4}
\]

The representative r=q accounts for the zero residue; its generator values happen to vanish. This formulation retains every progression tail, every mixed term, and the actual legality constraints. Pairwise periods avoid constructing the much larger common period of all generators.

### Exploratory calculations

The table uses floating-point evaluations of (4.3)–(4.4), eigenvalue rank detection, and constrained least squares. These are numerical estimates, not rigorous upper-bound certificates and not evidence of an asymptotic rate.

| Largest dilation M | Minimum mean-one variance, seed 2 only | Minimum mean-one variance, seeds 2 and 3 | Both seeds, additionally F(n)=1 for n<=M/2 |
|---:|---:|---:|---:|
| 4 | 0.14749207 | 0.05379571 | 0.05460851 |
| 8 | 0.13617899 | 0.04316302 | 0.04722448 |
| 16 | 0.13132609 | 0.03599825 | 0.05804627 |
| 32 | 0.12828058 | 0.03345237 | 0.06541049 |
| 64 | 0.12693869 | 0.02991841 | 0.07957119 |

Mean and initial-segment constraint residuals were below 8e-15. An independent direct summation for M=4 through n=1,000,000 gave squared error 0.05379548850, with an elementary omitted-tail upper bound of 0.00001263529 from the coefficient amplitude bound. This is consistent with the full-tail matrix value 0.05379571183; it does not turn the entire table into interval-certified data.

For a concrete small example, in the order (a,m)=(2,1),(3,1),(2,2),(3,2),(2,3),(3,3),(2,4),(3,4), the M=4 coefficients are approximately

\[
(0.5505014734,\ 0.4227936391,\ 0.1462439351,\ -0.0605722498,
 0.0671355845,\ 0.0354776176,\ 0.0336077669,\ 0.0093808330).
\]

These printed decimal coefficients are approximate; (4.1) is the exact definition. Their negative coefficient illustrates why signed fitting matters.

The table suggests that forcing a correct initial segment proportional to available dilation range can be counterproductive. It does not rule out exact-initial-segment constructions with a more generous dilation range or better asymptotic analysis.

## 5. An incremental target with exact mixed terms

Let F_M be the optimizer in Section 4 and set e=F_M-1. Let V_M be the mean-zero subspace of the old legal space. At an enlargement, make each new generator mean-zero by subtracting its mean times \(g_{2,1}/\log2\), then project off V_M. Denote the resulting directions by u_i. Define

\[
B_{ij}=\langle u_i,u_j\rangle_p,
\qquad h_i=\langle e,u_i\rangle_p.
\]

Because e is orthogonal to V_M, projection onto the enlarged affine space gives exactly

\[
\boxed{v(F_{\rm new})=v(F_M)-h^TB^\dagger h.}
\tag{5.1}
\]

The vector h is in the range of B; dependencies among the new directions cause no problem. The matrix B contains all residual covariances.

Along \(M_j=2^j\), put

\[
\delta_j=\frac{h_j^TB_j^\dagger h_j}{v(F_{M_j})}.
\]

Finite legal packets cannot equal 1 everywhere, since they vanish at positive multiples of a common period. Thus the finite variances remain positive, and

\[
v(F_{M_J})=v(F_{M_0})\prod_{j<J}(1-\delta_j).
\tag{5.2}
\]

A sufficient arithmetic estimate would be

\[
\delta_j\ge\frac{c}{j+1}\quad\text{eventually, for some }c>0.
\tag{5.3}
\]

This would yield decay on the order of \(J^{-c}\), hence a power of \(1/\log M_J\). A scale-independent contraction is not required. More generally, divergence of \(\sum_j\delta_j\) is equivalent to the zero product, since no factor is zero. Neither (5.3) nor that divergence has been established here. They are precise remaining estimates, not automatic consequences of finite-dimensional projection.

## 6. Why making the period large does not solve the problem

For a fixed periodic F, replacing an even common period Q by an integer multiple leaves its uniform variance U_Q(F) unchanged. Therefore \(U_Q(F)/Q\) can be made arbitrarily small without improving F.

The source's exact identity then forces

\[
J_Q(F)=v(F)-T_Q(F)\longrightarrow v(F).
\]

Thus period enlargement alone shifts the same error into the calibration term. The Jordan diagonalization is valuable for understanding legal coefficient energy, but a vanishing Jordan-energy-to-period ratio, achieved merely by inflating the period, is not an approximation advance.

## 7. Mellin obstruction for one seed, and necessary cross-seed moments

Realize a packet as \(f(x)=F(\lfloor x\rfloor)\) for x>=1. Exactly,

\[
\int_1^\infty|f(x)-1|^2\frac{dx}{x^2}=v(F).
\]

For Re(s)>0, with a removable value at s=1,

\[
\int_1^\infty g_{a,m}(\lfloor x\rfloor)x^{-s-1}\,dx
=\frac{\zeta(s)}s m^{1-s}(1-a^{1-s}).
\tag{7.1}
\]

One can first integrate the floor expression for Re(s)>1 and then continue analytically; the bounded step function gives analyticity of the left side for Re(s)>0.

For a 2-seed-only packet this integral vanishes at

\[
s_*=1+\frac{2\pi i}{\log2}.
\]

The constant 1 has transform 1/s_*. Cauchy–Schwarz in the Pareto Hilbert space yields

\[
\boxed{v(F)\ge\frac1{1+(2\pi/\log2)^2}\approx0.01202369.}
\tag{7.2}
\]

In fact (7.2) bounds the squared approximation error even without imposing mean one. It rules out every sequence using the 2-seed alone, independently of coefficient choice or subsequence.

For both seeds write

\[
P_{a,j}(s)=\sum_m c^{(j)}_{a,m}m^{1-s}.
\]

If v(F_j)->0, then for every fixed Re(s)>1/2,

\[
\boxed{
\zeta(s)\left[(1-2^{1-s})P_{2,j}(s)+(1-3^{1-s})P_{3,j}(s)\right]\longrightarrow1.
}
\tag{7.3}
\]

The deviation from 1 has magnitude at most

\[
\frac{|s|}{\sqrt{2\Re(s)-1}}\sqrt{v(F_j)}.
\]

At each nonzero dyadic resonance \(s_k=1+2\pi i k/\log2\), (7.3) specifically requires

\[
\boxed{
\sum_m c^{(j)}_{3,m}e^{-2\pi i k\log m/\log2}
\longrightarrow\frac1{\zeta(s_k)(1-3^{1-s_k})}.
}
\tag{7.4}
\]

There is a corresponding condition on the 2-channel at the triadic resonances. The denominator in (7.4) is nonzero: zeta has no zeros on Re(s)=1, and log2/log3 is irrational. At s=1, the removable expression in (7.3) is precisely the mean normalization.

This explains a substantive job for the second seed: it must supply the missing Mellin values of the first seed, through a distribution of signed dilation coefficients. Merely having no common artificial resonance is not a proof of approximation. In particular, at a hypothetical zeta zero with real part >1/2, (7.3) cannot hold: this is the remaining genuine RH obstruction.

## 8. Relation to known failed exact-initial-segment sequences

Setting b_{3,m}=0 in (3.1) uniquely gives

\[
b_{2,m}=\sum_{2^r\mid m}2^r\mu(m/2^r).
\]

For m=2^v u with u odd,

\[
b_{2,m}=2^{\max(v-1,0)}\mu(u).
\]

This is the first Vasyunin correction studied by Báez-Duarte. His paper proves that the sequence fails even to converge in L1, despite matching the constant on every growing initial interval. [Luis Báez-Duarte, *A divergent Vasyunin correction*](https://arxiv.org/abs/math/0506318).

Its failure is visible directly: at m=2^v, v>=1, the new coefficient of g_{2,m} is 1/2, so the L1 norm of the difference between consecutive packets is (log2)/2, not something tending to zero. The Mellin obstruction (7.2) also rules out rescuing one-seed approximation by choosing a subsequence or entirely different one-seed coefficients.

The proposed two-seed splitting and tail optimization must therefore be judged by their full norm, not by their initial matching property. Earlier arithmetic work on the Nyman–Beurling criterion also emphasizes the distinction between pointwise/L1 approximation and the needed L2 convergence. [Luis Báez-Duarte, *Arithmetical Aspects of Beurling's Real Variable Reformulation of the Riemann Hypothesis*](https://arxiv.org/abs/math/0011254).

## 9. Recommended bounded research target

Use the unrestricted full-Pareto optimizer (4.1) as the baseline sequence. Its coefficients automatically have the correct legal provenance, and it minimizes the actual error at each finite dilation range. Analyze its changes under enlargement with (5.1), while monitoring the necessary local Möbius relations (2.4) and the cross-seed Mellin moments (7.4).

For a more explicitly arithmetic construction, use (3.1) to prescribe a slowly growing exact initial segment and optimize the remaining splitting and larger-dilation coefficients against the full Pareto tail. The concrete sought theorem is a bound such as (3.6), or an incremental gain such as (5.3), for those **actual** coefficients.

Established here: the coefficient constraints, the obstruction bounds, finite feasibility, exact optimizer and projection formulas, and the sufficient-tail implication. Open: the all-scale tail bound or gain estimate that would force the variance to vanish. No claim of mathematical novelty is made without a broader literature comparison.
