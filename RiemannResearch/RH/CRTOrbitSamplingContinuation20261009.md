# Infinite CRT, orbit exhaustion, and a doubling-invariance criterion for RH

## 1. Result and scope

CRT uniqueness and exhaustion of all finite congruence classes do not, by themselves, prove RH. In fact, the limiting integer DPP already contains infinitely many points in every arithmetic progression, unconditionally. The distinction is between hitting all finite congruence neighbourhoods of an integer and occupying that integer itself.

There is, however, a precise orbit-invariance statement that would prove RH:
\[
\boxed{\mathrm{RH}\iff A_2S\subseteq S,\qquad (A_2f)(n)=f(2n).}
\]
This equivalence is proved below. The invariance assertion itself remains unproved.

The note also tests a natural construction from exhaustive unit orbits. Its legal, mean-corrected residue combinations converge pointwise to the constant, but their squared approximation errors grow at least on the order of \(y/(\log y)^2\). Thus that particular construction does not prove RH.

Sections 1--9 retain the original mathematical derivations. Sections 10--15
record the 9 October 2026 Lean continuation and distinguish formal results
from the remaining paper results and open arithmetic obligations.

## 2. Fixed arithmetic and DPP notation

Let
\[
w_n=\frac1{n(n+1)},\qquad H=\ell^2(\mathbb N_{\ge1},w),
\qquad g_d(n)=\frac{n\bmod d}{d}.
\]
Write
\[
S_N=\operatorname{span}\{g_2,\ldots,g_{N+1}\},
\qquad S=\overline{\bigcup_NS_N}^{\,H}.
\]
Let \(Vf(n)=\sqrt{w_n}f(n)\), so \(V:H\to\ell^2(\mathbb N_{\ge1})\) is unitary. The integer projection DPPs have counting-measure kernels
\[
Q_N=VP_{S_N}V^{-1},\qquad Q_\infty=VP_SV^{-1}.
\]
The approximation theorem supplies
\[
\mathrm{RH}\iff\mathbf1\in S\iff S=H.
\]
See [Bagchi, Theorem 1](https://arxiv.org/pdf/math/0607733). Standard DPP count and variance identities are in [Hough–Krishnapur–Peres–Virág](https://arxiv.org/pdf/math/0503110).

## 3. What CRT with an infinite modulus actually means

Choose \(M_j=j!\). The compatible residue systems form
\[
\widehat{\mathbb Z}
=\varprojlim_j\mathbb Z/M_j\mathbb Z
\cong\prod_p\mathbb Z_p.
\]
An ordinary integer is uniquely determined by all its residues: if \(n-m\) is divisible by every \(M_j\), then \(n=m\). But not every compatible residue system comes from an ordinary integer. The ordinary integers form a countable dense subset of the uncountable profinite ring.

The additive action of \(\mathbb Z\) on \(\widehat{\mathbb Z}\) has orbits \(x+\mathbb Z\). Each has trivial stabilizer and is countable and dense. There are uncountably many distinct orbits. Thus a dense orbit is not an exhaustive enumeration of the profinite ring.

An explicit escape example is
\[
n_j=1+j!.
\]
Then \(n_j\to\infty\) as ordinary integers, but \(n_j\to1\) in \(\widehat{\mathbb Z}\). Every fixed congruence eventually agrees with \(1\), although \(n_j\ne1\) for every \(j\).

Similarly,
\[
A=\mathbb N_{\ge1}\setminus\{1\}
\]
meets every residue class modulo every finite modulus infinitely often, while omitting \(1\). Hence
\[
\forall j\ \exists n_j\in A:\ n_j\equiv1\pmod{M_j}
\]
does not imply
\[
\exists n\in A\ \forall j:\ n\equiv1\pmod{M_j}.
\]
The second assertion would force \(n=1\). Replacing the first by the second is an invalid interchange of quantifiers.

## 4. The limiting DPP exhausts every finite CRT class unconditionally

**Theorem.** For every \(q\ge1\) and every residue \(a\bmod q\),
\[
\boxed{\#\bigl(\Xi_\infty\cap\{n\ge1:n\equiv a\pmod q\}\bigr)=\infty
\quad\text{almost surely}.}
\]
This holds simultaneously for all \(q,a\), without assuming RH.

**Proof.** Put \(x_d=\sqrt d\,g_d\in S\). Splitting its norm at \(d\) gives
\[
\|x_d\|_H^2
\le\frac1d\sum_{n<d}\frac n{n+1}
+d\sum_{n\ge d}\frac1{n(n+1)}\le2.
\]
At each fixed coordinate, \(x_d(n)=n/\sqrt d\to0\). Thus \(x_d\rightharpoonup0\) in \(H\).

Let \(A=\{n\ge1:n\equiv a\pmod q\}\), and put \(y_d=Vx_d\). Then \(y_d\rightharpoonup0\), \(Q_\infty y_d=y_d\), and
\[
\|\mathbf1_Ay_d\|_{\ell^2}^2
\ge\frac1d\sum_{\substack{n<d\\n\in A}}\frac n{n+1}
\longrightarrow\frac1q.
\]
Consequently \(\mathbf1_AQ_\infty\) is not compact: it sends a bounded weakly null sequence to vectors whose norms do not tend to zero. Its positive product
\[
(\mathbf1_AQ_\infty)(\mathbf1_AQ_\infty)^*
=\mathbf1_AQ_\infty\mathbf1_A
\]
is therefore not trace class. In particular,
\[
\sum_{n\in A}Q_\infty(n,n)=\infty.
\]

For the finite subsets \(A_R=A\cap[1,R]\), let
\(X_R=|\Xi_\infty\cap A_R|\) and \(\mu_R=\mathbb E X_R\). Then \(\mu_R\to\infty\), while the DPP variance formula gives
\[
\operatorname{Var}(X_R)\le\mu_R.
\]
For every fixed integer \(K\), Chebyshev's inequality gives
\[
\mathbb P(|\Xi_\infty\cap A|\le K)
\le\mathbb P(X_R\le K)
\le\frac{\mu_R}{(\mu_R-K)^2}\longrightarrow0.
\]
Thus the count is infinite almost surely. There are only countably many pairs \((q,a)\), proving the simultaneous assertion. \(\square\)

This theorem gives actual orbit exhaustion at every fixed finite level. It does not give the diagonal assertion that the required class is selected when the modulus grows with the finite-rank cutoff. Nor does it prove that a fixed integer is occupied.

## 5. Orbit–stabilizer: what it counts and what it does not

The unit group \(G_M=(\mathbb Z/M\mathbb Z)^\times\) acts by multiplication on \(\mathbb Z/M\mathbb Z\). Its orbits are precisely the gcd classes
\[
O_{M,a}=\{r\bmod M:\gcd(r,M)=a\},\qquad a\mid M.
\]
For a point in this orbit,
\[
\boxed{|O_{M,a}|=\varphi(M/a),\qquad
|\operatorname{Stab}(r)|=\frac{\varphi(M)}{\varphi(M/a)}.}
\]
Indeed, write \(r=ab\) with \(b\) a unit modulo \(M/a\); reduction from units modulo \(M\) onto units modulo \(M/a\) is surjective. Orbit–stabilizer then gives the formulas.

At the profinite level, unit orbits are determined by the complete vector of prime valuations. The orbit \(n\widehat{\mathbb Z}^{\times}\) of a positive integer \(n\) meets the positive integers only at \(n\), by unique factorization. This uniqueness is valid, but hitting every such limiting orbit is already the requirement of occupying every integer.

For example, the finite unit-orbit conditions
\[
\gcd(n,M_j)=1
\]
shrink, on the positive integers, to \(n=1\). Each finite set of such conditions is met by infinitely many DPP points by Section 4. Those points can change with \(j\); their existence does not supply a single point satisfying every condition.

Orbit sizes give probabilities under a uniform law. Our relevant class weights are instead
\[
W_M(r)=\sum_{\substack{n\ge1\\n\equiv r\ (M)}}\frac1{n(n+1)},
\]
and the DPP also includes Gram-determinant weights. Neither weight is supplied by orbit cardinality. In particular, the class \(0\) has zero inclusion probability at a common period of the finite residue generators, so that finite DPP is not invariant under the transitive additive rotation of the classes.

The actual profinite probability measure is
\[
\nu=\sum_{n\ge1}\frac{\delta_n}{n(n+1)}.
\]
It is not Haar measure: \(\nu(\{1\})=1/2\), while Haar measure is nonatomic. For instance, \(W_M(1)\to1/2\), whereas the Haar mass of that cylinder is \(1/M\to0\).

## 6. Full CRT information does recover every vector, but enlarges the predictor space

Let \(\mathcal F_j\) be the sigma-field on the positive integers generated by reduction modulo \(M_j\). These sigma-fields increase and jointly distinguish every integer. Therefore
\[
\mathbb E_\nu[f\mid\mathcal F_j]\longrightarrow f\quad\text{in }L^2(\nu)
\]
for every \(f\in H\). These are projections onto the **full spaces of periodic functions**, not onto the legal residue spans \(S_N\).

For a particularly explicit example, put
\[
c_M(n)=\mathbf1_{\{n\equiv1\ (M)\}}.
\]
Then
\[
\|c_M-\delta_1\|_H^2
=\sum_{k\ge1}w_{1+kM}\le\frac{\zeta(2)}{M^2}.
\]
Thus full cylinder indicators approximate the target easily. Establishing their approximation by legal residue combinations is a separate requirement. For \(M\ge3\), \(c_M\) is not even an exact finite linear combination of the \(g_d\): every such combination has an even periodic backward first difference, with \(\Delta f(n)=f(n)-f(n-1)\), since
\[
\Delta g_d(n)=\frac1d-\mathbf1_{\{d\mid n\}},
\]
whereas \(\Delta c_M(1)=1\) and \(\Delta c_M(-1)\ne1\). Equality on positive integers would force equality of the periodic extensions on all integers.

The projective consistency of the scalar weights \(W_M\) also does not make the finite-rank residue DPPs a single projective system under reduction: changing the rank changes their kernels and cardinalities. Their already established infinite integer limit comes from strong convergence of the projections.

## 7. A natural exhaustive-orbit legal construction has diverging error

Let \(y\ge2\) be an integer and
\[
P_y=\prod_{p\le y}p,\qquad
\delta_y=\frac{\varphi(P_y)}{P_y}
=\prod_{p\le y}(1-1/p).
\]
The unit-orbit indicator \(\mathbf1_{\{\gcd(n,P_y)=1\}}\) converges pointwise, and in \(H\), to \(\delta_1\).

To obtain a legal periodic residue combination, integrate its mean-zero version:
\[
F_y(n)=\sum_{k=1}^n\mathbf1_{\{\gcd(k,P_y)=1\}}-n\delta_y.
\]
Finite inclusion–exclusion gives the exact identity
\[
\boxed{F_y(n)=-\sum_{\substack{d\mid P_y\\d\ge2}}\mu(d)g_d(n).}
\]
Thus \(F_y\) is legal. For \(1\le n\le y\), the only integer coprime to \(P_y\) is \(1\), so
\[
F_y(n)=1-n\delta_y.
\]
Although \(F_y(n)\to1\) for each fixed \(n\), its norm error satisfies
\[
\boxed{
\|F_y-\mathbf1\|_H^2
\ge\delta_y^2\sum_{n=1}^y\frac n{n+1}
=\delta_y^2(y+1-H_{y+1}).
}
\]
The classical estimate \(\sum_{p\le y}1/p=\log\log y+O(1)\), together with convergence of \(\sum_p1/p^2\), gives \(\delta_y\asymp1/\log y\). See [NIST DLMF 27.11.8](https://dlmf.nist.gov/27.11.E8). Therefore
\[
\|F_y-\mathbf1\|_H^2\gtrsim\frac{y}{(\log y)^2}\longrightarrow\infty.
\]
The uncentered counting function grows linearly and is not in \(H\). Subtracting its mean slope makes it a legal bounded periodic function, but creates the displayed growing initial-segment error. This rules out this specific natural orbit construction, not every possible correction or optimization.

## 8. A precise orbit-invariance theorem that would finish RH

Define the bounded sampling operator
\[
(A_2f)(n)=f(2n).
\]
It satisfies
\[
\|A_2f\|_H^2
=\sum_{n\ge1}w_n|f(2n)|^2
\le4\sum_{n\ge1}w_{2n}|f(2n)|^2
\le4\|f\|_H^2.
\]

**Theorem.**
\[
\boxed{\mathrm{RH}\iff A_2S\subseteq S.}
\]

**Proof.** RH implies \(S=H\), giving invariance. Conversely, assume \(A_2S\subseteq S\). Put
\[
d_k=2^k+1,\qquad
h_k(n)=A_2^k g_{d_k}(n).
\]
Then \(h_k\in S\), and the finite orbit identity \(2^k\equiv-1\pmod{d_k}\) gives
\[
\boxed{h_k(n)=\frac{(-n)\bmod d_k}{d_k}.}
\]
For \(1\le n<d_k\), \(h_k(n)=1-n/d_k\), and for every \(n\), \(0\le h_k(n)<1\). Consequently,
\[
\begin{aligned}
\|h_k-\mathbf1\|_H^2
&\le\frac1{d_k^2}\sum_{n<d_k}\frac n{n+1}
+\sum_{n\ge d_k}w_n\\
&\le\frac2{d_k}\longrightarrow0.
\end{aligned}
\]
Closedness gives \(\mathbf1\in S\), hence RH. \(\square\)

This is argument doubling, \(f(n)\mapsto f(2n)\). It is different from the known invariant dilation \(f(n)\mapsto2f(\lfloor n/2\rfloor)\). Invariance under one does not supply invariance under the other.

Nor does finite orbit algebra establish the premise. Already \(A_2g_3\) is not an exact finite legal combination: its periodic first difference takes values \(2/3\) at \(1\) and \(-1/3\) at \(-1\), contradicting the evenness property of finite legal first differences. An approximation theorem in the weighted norm is required.

More precisely, since \(h_k\to\mathbf1\) in \(H\),
\[
\operatorname{dist}_H(h_k,S)\longrightarrow
\operatorname{dist}_H(\mathbf1,S),
\]
so proving \(\operatorname{dist}_H(h_k,S)\to0\) along these particular orbits is already enough, and is itself equivalent to RH.

### Why modular reversal is not a harmless bounded symmetry

On periodic functions define \((Rf)(n)=f(-n)\), using their periodic extension. This definition is independent of the chosen period. Yet
\[
\|g_d\|_H^2\le2/d\longrightarrow0,
\qquad
\|Rg_d-\mathbf1\|_H^2\le2/d\longrightarrow0.
\]
Thus \(R\) has no bounded extension to \(H\): it takes a sequence tending to zero to a sequence tending to \(\mathbf1\). Finite modular symmetry cannot therefore be commuted through the weighted Hilbert closure without an additional argument.

## 9. What remains

Infinite CRT gives unique residue descriptions; orbit–stabilizer gives exact finite counts; and the DPP exhausts every fixed finite congruence class. All three statements have been accounted for, and none supplies single-site saturation.

A productive concrete version of the orbit proposal is to prove \(A_2S\subseteq S\), or just approximate \(A_2^kg_{2^k+1}\) by legal residue combinations with errors tending to zero. The conditional proof in Section 8 then completes RH. This note does not establish that arithmetic approximation step.

## 10. Lean continuation: any one fixed sampling factor (9 October 2026)

The repository already contains `ArgumentDoublingClosure.lean`,
`ArgumentDoublingGenerators.lean`, `DyadicCarryBlocks.lean`, and
`ResidueClosureDensity.lean`. The continuation extends the fixed factor from
two to every integer \(a\ge2\), using the actual repository Pareto Hilbert space.

For \(A_af(n)=f(an)\), the exact physical weight ratio is
\[
w_n=\left(a^2-\frac{a(a-1)}{n+1}\right)w_{an}.
\]
It gives a bounded operator with the sharp norm
\[
\boxed{\|A_a\|=a\quad(a\ge1).}
\]
The upper bound follows by sampling a nonnegative summable energy series.
For sharpness, use a point vector supported at \(a(n+1)\); its squared norm
ratio is \(a^2-a(a-1)/(n+2)\to a^2\).

Set \(d_k=a^k+1\) and \(h_{a,k}=A_a^kg_{d_k}\). As in the original proof,
\(h_{a,k}(n)=1-n/d_k\) for \(0<n<d_k\), and all its values lie in \([0,1]\).
Dominated convergence against the complete physical weight series gives
\(h_{a,k}\to\mathbf1\) in \(H\), for every fixed \(a\ge2\).

The exact closure equivalence is
\[
\boxed{
A_aS\subseteq S\iff\mathbf1\in S\iff S=H,\qquad a\ge2.
}
\]
The reverse implication uses the already formalized fact that containing
the constant makes the **full** residue closure total. Continuity also reduces
invariance to checking the individual generators:
\[
A_aS\subseteq S\iff A_ag_d\in S\quad\text{for every }d\ge2.
\]
The repository's established Mellin obstruction then supplies
\(A_aS\subseteq S\Rightarrow\mathrm{RH}\).

In published mathematics, Bagchi's Theorem 1 gives the full
\(\mathrm{RH}\iff A_aS\subseteq S\). The new Lean endpoint proves the closure
equivalence and the implication to RH; it does **not** introduce the presently
unformalized RH-to-closure converse as an axiom or a hidden hypothesis.

The new declarations are in `RiemannResearch/RH/ArgumentSamplingClosure.lean`:

| Declaration | Exact role |
|---|---|
| `sampling_weight_identity` | Complete physical ratio, retaining its correction |
| `argumentSamplingContinuous_norm` | Sharp operator norm for every positive factor |
| `powerSampledResidue_tendsto_one` | Complete norm convergence for every fixed factor at least two |
| `argumentSamplingInvariant_iff_generators` | Generator test for invariance |
| `argumentSamplingInvariant_iff_one_mem` | Exact equivalence to constant membership |
| `argumentSamplingInvariant_iff_total` | Exact equivalence to full density |
| `riemannHypothesis_of_argumentSampling` | Conditional RH endpoint; invariance remains Open |

## 11. Exact modular-reversal error, including the square correction

For every positive conductor and every natural coordinate, finite modular
arithmetic gives
\[
1-g_d((d-1)n)=g_d(n)+\mathbf1_{d\mid n}.
\]
The two terms on the right have disjoint support. Thus no cross term is
discarded when squaring:
\[
\bigl(1-g_d((d-1)n)\bigr)^2=g_d(n)^2+\mathbf1_{d\mid n}.
\]
After proving summability of the divisibility-site weights, the complete
Hilbert-space identity becomes
\[
\boxed{
\|\mathbf1-Rg_d\|_H^2
=\|g_d\|_H^2+\sum_{k\ge1}\frac1{kd(kd+1)}.
}
\]
Here the zero coordinate is an anchor of zero physical mass; it contributes
nothing to the identity. The infinite correction is retained in full.

`RiemannResearch/RH/ReversedResidueComplement.lean` records the modular
complement, pointwise square, weighted square, complete series, and actual
Hilbert norm equalities. Lean stores the correction as
\(\sum'_n\mathbf1_{d\mid n}w_n\); the displayed positive-multiple series is its
arithmetic reindexing. It also records the following finite functional
certificates, which clarify the squarefree restriction.

### Full residue closure and squarefree closure are different spaces

Let \(T\) be the closed span of squarefree atoms. Define the continuous functional
\[
\ell_4(f)=-f(1)+f(2)+f(3)-f(4).
\]
Exact arithmetic gives, for every conductor \(d\ge2\),
\[
\ell_4(g_d)=\mathbf1_{d=4},\qquad
\ell_4(A_2g_3)=-1,\qquad \ell_4(\mathbf1)=0.
\]
Consequently \(T\ne H\) and \(A_2T\not\subseteq T\), unconditionally.
The functional has norm \(\sqrt{40}\), since its representing vector has
physical coordinates \((-2,6,12,-20)\). Hence
\[
\operatorname{dist}(A_2g_3,T)\ge1/\sqrt{40}.
\]
This does not conflict with Bagchi's squarefree criterion: the constant can
belong to a proper closed subspace. It prevents transferring the full-space
sampling-invariance criterion to the squarefree space. The arithmetic
functional values are formalized; this paragraph's closure and distance
consequences are paper deductions from continuity.

## 12. Factorial CRT separation and the exact quantifier distinction

`RiemannResearch/NumberTheory/FactorialCRTSeparation.lean` proves the stronger
natural-number separation statement
\[
\forall n,m\ge0:\quad
\bigl(\forall j\ge0,\ n\equiv m\pmod{j!}\bigr)\iff n=m.
\]
It proves that \(1+j!\ne1\), agrees with \(1\) modulo \(k!\) whenever \(k\le j\),
and exceeds its index. Every finite prefix therefore admits witnesses beyond
any prescribed ordinary bound. In particular, both halves of
\[
\bigl(\forall j\ \exists n>1:\ n\equiv1\pmod{j!}\bigr)
\quad\text{and}\quad
\neg\bigl(\exists n>1\ \forall j:\ n\equiv1\pmod{j!}\bigr)
\]
are proved unconditionally. These all-integer theorems formalize the original
CRT obstruction directly, without assuming a profinite probability model.

## 13. A stronger paper bound for unconditional CRT exhaustion

The noncompactness argument in Section 4 can be replaced by a quantitative
legal-atom estimate. For \(d\ge2\), split the complete norm at \(d\).
For the head, use \(n/(n+1)\le(d-1)/d\); for the tail, use
\(g_d\le(d-1)/d\) and \(\sum_{n\ge d}w_n=1/d\). This yields
\[
\|g_d\|_H^2\le\frac{2(d-1)^2}{d^3}.
\]
Projection Cauchy–Schwarz, with \(d=n+1\), gives
\[
\boxed{Q_N(n,n)\ge\frac1{2n}\quad(1\le n\le N),
\qquad Q_\infty(n,n)\ge\frac1{2n}.}
\]
Indeed, the weighted squared value of \(g_{n+1}\) at \(n\) is
\(n/(n+1)^3\), while its norm upper bound is \(2n^2/(n+1)^3\).

If \(1\le b\le q\) and \(L=\lfloor N/q\rfloor\), summing over
\(b,b+q,\ldots,b+(L-1)q\) gives
\[
\mathbb E\#(\Xi_N\cap(b+q\mathbb N)\cap[1,N])\ge\frac{H_L}{2q}.
\]
The DPP Bernoulli-count law bounds the probability of an empty progression
prefix by \(\exp(-H_L/(2q))\). This proves fixed-modulus exhaustion with an
explicit rate. It gives no single-site saturation when the modulus grows.

These quantitative DPP estimates are **paper results in this continuation**;
the new Lean modules do not yet claim their kernel verification. The original
DPP count source is [HKPV, Theorem 7](https://arxiv.org/pdf/math/0503110).

## 14. A constructive finite Gram target that keeps every defect

Fix a legal finite space \(V_L\), projection \(P_L\), and \(d=a^k+1\le L\).
Start with \(F_0=g_d\) and iterate legal vectors
\[
F_{j+1}=P_LA_aF_j,\qquad
\delta_j=(I-P_L)A_aF_j.
\]
Writing \(e_j=A_a^jg_d-F_j\), the exact recurrence and telescope are
\[
e_{j+1}=A_ae_j+\delta_j,\qquad
e_k=\sum_{j<k}A_a^{k-1-j}\delta_j.
\]
Therefore
\[
\|\mathbf1-F_k\|_H
\le\|\mathbf1-Rg_d\|_H+
\sum_{j<k}a^{k-1-j}\|\delta_j\|_H.
\]
With Gram matrix \(G\), mixed matrix \(C_{ij}=\langle g_i,A_ag_j\rangle\),
and sampled Gram matrix \(B_{ij}=\langle A_ag_i,A_ag_j\rangle\), write
\(F_j=\sum_i c_{j,i}g_i\). Then
\[
c_{j+1}=G^{-1}Cc_j,\qquad
\boxed{\|\delta_j\|_H^2=c_j^\top(B-C^\top G^{-1}C)c_j.}
\]
The complete positive defect matrix retains the signed mixed terms.
A sequence of finite cutoffs for which the geometrically amplified defect sum
tends to zero would produce legal approximants to the constant and imply RH.
This rate estimate is **Open**. Small normalized defects without control of
their factors \(a^{k-1-j}\) do not suffice. The telescope and finite-matrix
consumer here are paper results; the present formalization supplies the actual
sampling operator and its sharp amplification norm.

## 15. Verification and publication ledger

All 43 new theorem bodies and 8 definitions passed one coherent Lean source
check, with no errors or warnings. The central `#print axioms` audits reported
only `propext`, `Classical.choice`, and `Quot.sound`:

- `argumentSamplingContinuous_norm`;
- `argumentSamplingInvariant_iff_one_mem`;
- `riemannHypothesis_of_argumentSampling`;
- `reverseResidue_hilbert_error`;
- `factorial_quantifier_distinction`.

No `sorry`, `admit`, project-local axiom, or unsafe declaration appears in the
new modules. The repository export and theorem catalog are updated. Final
change-aware project validation and publication are handled by the checkpoint.

Verification scope: the new source bodies, including the RH consumer, are
checked. Fixed-factor invariance is still an explicit open premise. The
quantitative DPP lower bounds and finite Gram defect telescope in Sections
13--14 are paper results, and the defect-decay provider is Open. No
unconditional proof of RH is claimed.
