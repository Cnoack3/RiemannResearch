# Fixed inverse Gram and signed coefficient criteria for RH

Continuation update: 6 October 2026. Sections 1–10 preserve the supplied handoff. Sections 11–17 develop the actual dyadic adjoint defect, stronger finite and limiting signed bounds, a relaxed RH-equivalent provider, and multiplicity-aware Mellin obstructions. The arithmetic provider remains open. Verification of the new algebraic layer is recorded separately in Section 17; it does not upgrade the older uncompiled drafts. Section 18 records the subsequent verified actual operator and coefficient bridge; the cofinal arithmetic provider and the formal RH converse remain explicit.

Date: 6 October 2026. Continuation of the 5 October handoff. Base: `bc2fd31a9641976a9e34049028419d3ef08f5dfd`.

The continuation replaces the growing-support transfer target by one fixed signed quadratic form of the first two rows of the complete inverse Gram matrix. It also obtains a coercive signed linear combination of the first two optimal coefficients, exact Schur decrements, and finite signed Abel bounds. The unconditional estimates below retain every composite conductor. Saturation remains unproved, so RH remains open. No mathematical novelty claim is made.

## 1. Exact setting and fixed vector

Use the actual Pareto space

\[
H=\ell^2(\mathbb N_{>0},1/[j(j+1)]),\quad
g_d(j)=(j\bmod d)/d,\quad
V_n=\operatorname{span}(g_2,\dots,g_{n+1}).
\]

Let \(P_n\) be its orthogonal projection, \(W=\overline{\bigcup_n V_n}\), and \(R=I-P_W\). Write G_n for the full residue Gram, b_n(d)=log(d)/d for its source, Q_n=||P_n1||²=b_n^T G_n^{-1}b_n, and Q_∞=lim Q_n. The monotone sequence Q_n lies in [0,1]. The first coefficient duals from the actual Möbius-difference formulas are

\[
u_0=(4,-6,0,\ldots),\qquad
u_1=(2,6,-12,0,\ldots).
\]

Their Gram entries are \(14,20,-2\). The vector below differs from the two-dual projection of the constant. Its specific dilation factorization is what permits fixed-support transfer. Define the **fixed** vector

\[
v=3u_0+u_1=(14,-12,-12,0,\ldots),\qquad \|v\|^2=134.
\]

For every \(n\ge2\), biorthogonality and the complete stage-\(n\) inverse give

\[
\mathcal E_n:=\|v-P_nv\|^2
=134-9(G_n^{-1})_{00}-6(G_n^{-1})_{01}-(G_n^{-1})_{11}.
\tag{1}
\]

The prefix is taken **after inversion of the full Gram matrix**, so all composite conductors remain present. Formula (1) is nonnegative and decreases with \(n\).

## 2. Dyadic invariance and the quantitative theorem

For zero-anchored sequences set

\[
(Sf)(j)=f(\lfloor j/2\rfloor),\quad f(0)=0.
\]

The paired-weight telescoping identity

\[
\frac1{2m(2m+1)}+\frac1{(2m+1)(2m+2)}
=\frac1{2m(m+1)}
\]

proves \(\|Sf\|^2=\frac12\|f\|^2\). The pointwise residue identity is

\[
Sg_d=g_{2d}-\frac1d g_2.
\tag{2}
\]

Thus \(W\) is invariant under \(S\), and the quotient compression \(A=RS\) satisfies \(A R=RS\), \(\|A x\|\le2^{-1/2}\|x\|\), and \(R S^m=A^mR\).

Writing \({\bf1}\) for the constant target, one checks coordinate by coordinate that

\[
v=(14I-26S+12S^2){\bf1}
=2(7I-6S)(I-S){\bf1}.
\tag{3}
\]

Let \(r=R{\bf1}\), \(y=(I-A)r\), and \(t=2^{-1/2}\). Then

\[
Rv=2(7I-6A)y,
\quad \|y\|\ge(1-t)\|r\|,
\quad \|7y-6Ay\|\ge(7-6t)\|y\|.
\]

Consequently, with

\[
\kappa=2(7-3\sqrt2)(1-1/\sqrt2)=20-13\sqrt2>0,
\]

the unconditional quantitative estimate is

\[
\boxed{\mathcal E_n\ge\|Rv\|^2\ge\kappa^2\|R{\bf1}\|^2
=(20-13\sqrt2)^2(1-Q_\infty).}
\tag{4}
\]

In particular,

\[
v\in W\iff{\bf1}\in W\iff\mathrm{RH}.
\tag{5}
\]

The reverse implication in the first equivalence follows directly from (3) and invariance; the forward implication follows from (4). The last equivalence is the established Nyman–Beurling–Báez-Duarte/Bagchi criterion. Because \(P_nv\to P_Wv\), (1) and (5) prove

\[
\boxed{\mathrm{RH}\iff
9(G_n^{-1})_{00}+6(G_n^{-1})_{01}+(G_n^{-1})_{11}\longrightarrow134.}
\tag{6}
\]

This uses one fixed signed two-row quadratic form. It does not require a support index tending to infinity. It does not prove the saturation in (6).

For a Lean proof with rational constants, the weaker estimate \(\|A x\|\le(3/4)\|x\|\) implies \(\|Rv\|\ge(5/4)\|r\|\), hence \(\mathcal E_n\ge(25/16)(1-Q_\infty)\). Both implications in (5) already follow from this weaker bound.

## 3. Explicit finite conductor transfer

Set \(q=6/7\) and, for integers \(L\ge0\),

\[
c_\ell=\frac12(1-q^{\ell+1}),\qquad
H_L(z)=\sum_{\ell=0}^L c_\ell z^\ell.
\]

These are the exact coefficients of \(1/(14-26z+12z^2)\). Put

\[
A_L=7(1-q^{L+2}),\quad B_L=6(1-q^{L+1}),\quad A_L-B_L=1.
\]

Polynomial multiplication gives

\[
H_L(z)(14-26z+12z^2)=1-A_L z^{L+1}+B_L z^{L+2}.
\]

The vectors \(S^m{\bf1}\) are nested tail indicators. Therefore

\[
\|{\bf1}-H_L(S)v\|^2
=\frac{1+A_L^2}{2^{L+2}}
\le25\,2^{-(L+1)}.
\tag{7}
\]

Moreover, all \(c_\ell\ge0\), so

\[
\|H_L(S)\|\le\sum_{\ell=0}^L c_\ell2^{-\ell/2}
\le C:=\frac1{20-13\sqrt2}
=\frac{20+13\sqrt2}{62}=0.619109295336294\ldots.
\]

Repeated use of (2) shows \(H_L(S)P_nv\in V_m\), where \(m=2^L(n+1)-1\). Consequently,

\[
\boxed{\sqrt{1-Q_{2^L(n+1)-1}}
\le C\sqrt{\mathcal E_n}
 +\sqrt{\frac{1+A_L^2}{2^{L+2}}}
\le C\sqrt{\mathcal E_n}+5\,2^{-(L+1)/2}.}
\tag{8}
\]

Formula (8) is an unconditional finite certificate with an explicit cost for enlarging conductors. The unproved input is still obtaining arbitrarily small \(\mathcal E_n\).

## 4. Fixed-zero test with no height normalization

Use the complexification of H for this section; the same functional bound applies to real inputs. For \(s=\beta+i\gamma\), \(\beta>1/2\), define the bounded discrete Mellin functional

\[
\mathcal L_s(f)=\frac1s\sum_{j\ge1}f(j)
\bigl(j^{-s}-(j+1)^{-s}\bigr).
\]

Its exact squared norm on the Pareto step subspace is

\[
K_s=\frac1{|s|^2}\sum_{j\ge1}j(j+1)
\left|j^{-s}-(j+1)^{-s}\right|^2
\le\frac1{2\beta-1}.
\tag{9}
\]

The last bound follows by viewing the sum as the orthogonal step projection of the Mellin kernel \(x^{s-1}\) in \(L^2(0,1)\). The discrete norm can be strictly smaller, so the exact \(K_s\) gives a stronger certificate.

The actual legal residue identity is

\[
\mathcal L_s(g_d)=(d^{-1}-d^{-s})\zeta(s)/s.
\]

Thus a hypothetical off-line zero \(\rho=\beta+i\gamma\), \(\beta>1/2\), annihilates every \(V_n\). On the fixed vector,

\[
\mathcal L_s(v)=\frac{14-26\,2^{-s}+12\,4^{-s}}s
=\frac{2(7-6\,2^{-s})(1-2^{-s})}s.
\tag{10}
\]

The numerator has no zeros when \(\operatorname{Re}s>0\): \(|2^{-s}|<1\), whereas its two roots in the variable \(2^{-s}\) are \(1\) and \(7/6\). Cauchy–Schwarz therefore gives the explicit **unscaled** obstruction

\[
\boxed{\mathcal E_n\ge
\frac{|14-26\,2^{-\rho}+12\,4^{-\rho}|^2}{|\rho|^2 K_\rho}
\ge\frac{4(2\beta-1)(7-6\,2^{-\beta})^2(1-2^{-\beta})^2}{|\rho|^2}>0.}
\tag{11}
\]

There is no division by the zero count, no moving height head, and no omission of composites. The obstruction persists at every legal stage. The standard target also obeys \(1-Q_n\ge1/(|\rho|^2K_\rho)\ge(2\beta-1)/|\rho|^2\).

## 5. Primary sources and exact analytic assumptions

- Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann Hypothesis*, Theorem 1 identifies the exact Pareto sequence space and equates RH with constant-target membership and totality. Theorem 7 and its proof give integer-dilation invariance; the Hardy-space evaluation argument supplies the fixed-zero diagnostic. Primary PDF: https://www.isibang.ac.in/~statmath/eprints/2005/isibc200535.pdf . The explicit polynomial (3), finite inverse form (6), and certificate (8) above are deductions made here from those structures and the current project's exact dual formulas.
- Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, Theorem 1.3 proves the unconditional liminf logarithmic lower bound with multiplicity squared. Primary PDF: https://arxiv.org/pdf/math/0103058 . This provides a lower bound, not an unconditional vanishing upper bound.
- Báez-Duarte, *A strengthening of the Nyman-Beurling criterion, 2*: explicit damped Möbius approximation of order \((\log\log n)^{-1/3}\) assumes RH. https://arxiv.org/abs/math/0205003 .
- Bettin–Conrey–Farmer, *An optimal choice of Dirichlet polynomials for the Nyman-Beurling criterion*, Theorem 1 obtains the conjectural \(1/\log N\) squared-distance constant assuming RH and \(\sum_{|\operatorname{Im}\rho|\le T}|\zeta'(\rho)|^{-2}\ll T^{3/2-\delta}\) for some \(\delta>0\). This additionally entails simplicity. Primary author PDF: https://aimath.org/~kaur/publications/80.pdf . These hypotheses cannot be imported into an unconditional RH proof.

## 6. Exact full inverse Schur decrements

Let e_j be the actual normalized Gram–Schmidt mode obtained when g_{j+2} is adjoined, and let t_{d,j} be its legal coefficient at conductor d. Biorthogonality gives t_{d,j}=⟨u_{d-2},e_j⟩. For fixed support a and k≤n, the full inverse has the exact update

$$
(G_{n+1}^{-1})_{i,j}=(G_n^{-1})_{i,j}+t_{i+2,n}t_{j+2,n},\quad i,j<n.
$$

Consequently, for the original physical prefix defect,

$$
E_{k,n+1}(a)=E_{k,n}(a)-\left(\sum_{i<k}a_i t_{i+2,n}\right)^2.
$$

For the distinguished vector this is

$$
\mathcal E_{n+1}=\mathcal E_n-(3t_{2,n}+t_{3,n})^2.
\tag{12}
$$

The two signed rows are combined before squaring. Telescoping preserves them exactly:

$$
\mathcal E_N=\mathcal E_n-\sum_{j=n}^{N-1}(3t_{2,j}+t_{3,j})^2\ge0.
$$

Thus the square gains are summable, with budget at most the initial defect. Exhausting that budget is the open arithmetic assertion; summability alone does not exhaust it.

## 7. Coercivity of a signed linear coefficient combination

The same vector gives a simpler scalar target. Let A=RS be the compressed dyadic dilation, with ||A||≤1/√2, and write A* for its Hilbert adjoint. For every real Hilbert vector x, the following equality keeps both norm-square remainders:

$$
\begin{aligned}
\langle x,(14I-26A+12A^2)x\rangle
={}&6\left\|Ax+A^*x-\frac{13}{12}x\right\|^2
+\frac{167}{24}\|x\|^2\\
&-6\|Ax\|^2-6\|A^*x\|^2.
\end{aligned}
\tag{13}
$$

Both of the subtracted squares are at most ||x||²/2. Hence

$$
\langle x,(14I-26A+12A^2)x\rangle\ge\frac{23}{24}\|x\|^2.
\tag{14}
$$

The constant 23/24 is optimal from the contraction bound alone. Indeed, the real matrix

$$
A_0=\frac1{24}\begin{pmatrix}13&-\sqrt{119}\\\sqrt{119}&13\end{pmatrix}
$$

satisfies A_0* A_0=I/2, and the symmetric part of 14I−26A_0+12A_0² is (23/24)I. Any improvement for the actual arithmetic compression requires information beyond its norm.

Taking x=r=R1 and using Rv=(14I−26A+12A²)r gives the unconditional unscaled estimate

$$
\boxed{\langle r,v\rangle\ge\frac{23}{24}(1-Q_\infty).}
\tag{15}
$$

For the actual optimal legal coefficients c_{n,d}, the existing coefficient extraction and convergence identities imply

$$
L_c:=\lim_{n\to\infty}(3c_{n,2}+c_{n,3}-4)
=-\langle r,v\rangle
\le-\frac{23}{24}(1-Q_\infty)\le0.
\tag{16}
$$

Thus the following single signed arithmetic provider is sufficient for RH:

$$
\forall\epsilon>0,\quad\exists\text{ arbitrarily large }n:
3c_{n,2}+c_{n,3}>4-\epsilon.
\tag{17}
$$

This does not assume convergence of every coefficient to its Möbius value. The two coefficients in (17) are extracted from the complete optimal inverse, including all composites. The provider (17) remains open. In coordinates of the canonical residual, ⟨r,v⟩=7r(1)−2r(2)−r(3), so (15) is also a concrete three-coordinate inequality.

For a finite version of (16), put \(x_n=G_n^{-1}(b_n+G_n\mu_n)\) and retain the two enlargement errors
\[
B_n=13\sqrt2\sqrt{Q_n(Q_{2n+1}-Q_n)}
+6\sqrt{Q_n(Q_{4n+3}-Q_n)}.
\]
The exact legal inclusions \(SP_n1\in V_{2n+1}\) and \(S^2P_n1\in V_{4n+3}\), together with
\(\|P_m1-P_n1\|^2=Q_m-Q_n\), give the unconditional paper estimate
\[
\frac{23}{24}(1-Q_n)-B_n
\le -(3x_{n,2}+x_{n,3})
\le (20+13\sqrt2)(1-Q_n)+B_n.
\tag{20}
\]
Indeed,
\[
\langle r_n,v\rangle
=\langle r_n,p(S)r_n\rangle
-26\langle r_n,SP_n1\rangle+12\langle r_n,S^2P_n1\rangle,
\]
and the last two signed terms are bounded by \(B_n\) only after being displayed.
Monotonicity and boundedness of \(Q_n\) imply \(B_n\to0\) unconditionally. This does not force \(1-Q_n\to0\).


## 8. Finite signed reciprocal Abel bounds

Use the full signed Abel charge A_n=reciprocalCorrectionAbel(n), M_N=Σ_{d≤N}μ(d)/d, target error e_n=1−Q_n, and first-site leverage

$$
K_n=p_n^T G_n^{-1}p_n,\qquad p_{n,d}=1/d.
$$

The existing exact identities are A_n−M_{n+1}=F_n(1)−1 and

$$
F_n(1)=\sum_{j<n}\alpha_j\beta_j,\quad
1-e_n=\sum_{j<n}\alpha_j^2,\quad
K_n=\sum_{j<n}\beta_j^2,
$$

where α_j=⟨e_j,1⟩ and β_j=e_j(1). Therefore finite Cauchy–Schwarz proves, for n≤m,

$$
\boxed{|A_m-A_n-(M_{m+1}-M_{n+1})|^2
\le(e_n-e_m)(K_m-K_n).}
\tag{18}
$$

It also bounds the total absolute variation of the centered charge \(A_j-M_{j+1}=F_j(1)-1\) on that interval: \(\sum_{j=n}^{m-1}|A_{j+1}-A_j-(M_{j+2}-M_{j+1})|\) is at most the square root of the right side. This charges the actual first-site leverage increase, instead of its universal ceiling 2. All Abel endpoint and interior terms remain inside A_n.

The signed Schur description makes the complete screening explicit. Write the new Gram column as h, the new diagonal as a, and define

$$
\sigma=a-h^TG_n^{-1}h>0,\quad
\eta=b_{\mathrm{new}}-h^TG_n^{-1}b_n,\quad
\tau=p_{\mathrm{new}}-h^TG_n^{-1}p_n.
$$

Then the three exact gains are ΔF_n(1)=ητ/σ, ΔQ_n=η²/σ, and ΔK_n=τ²/σ. The signed mixed gains converge absolutely because Q_n≤1 and K_n≤2. Their sum need not be one.

At the limit, the existing M_N→0 and capacity identity 2−K_n=4/(tailCapacity(n)+2) give the paper certificate

$$
\left|\lim_m A_m-A_n+M_{n+1}\right|
\le2\sqrt{\frac{e_n}{\operatorname{tailCapacity}(n)+2}}.
\tag{19}
$$

The missing input remains the one-sided cofinal lower bound for A_n, or equivalently its limiting value zero.

## 9. Finite numerical diagnostics

Wolfram evaluated the complete Gram from periodic residue weights

$$
G_n(d,e)=\sum_{a=1}^{L-1}\frac{(a\bmod d)(a\bmod e)}{deL}
\left[\psi\left(\frac{a+1}{L}\right)-\psi\left(\frac aL\right)\right],\qquad L=\operatorname{lcm}(d,e).
$$

Every conductor 2 through n+1 was included. These are 35-digit arithmetic calculations rounded below, not interval or Lean certificates.

| Legal stage n | Fixed signed defect 𝓔_n | Constant target squared error 1−Q_n |
| --- | ---: | ---: |
| 2 | 75.7414200828 | 0.0957477839 |
| 4 | 26.7152156265 | 0.0363190179 |
| 8 | 17.9315095981 | 0.0240950788 |
| 12 | 14.1018277487 | 0.0198742430 |

The signed statistic 3c_{n,2}+c_{n,3}−4 is approximately 0.8447888418 at stage 2, −0.3481517159 at stage 3, −0.5417372244 at stage 4, and −0.3521528393 at stage 12. Thus a nonnegative bound at every finite stage is false; the open provider is cofinal and asymptotic.

The finite decrease is compatible with either a zero or positive limiting defect. It is diagnostic evidence for normalization, not proof of saturation.

## 10. Verification and continuation

The new results are paper proofs with uncompiled Lean drafts. The verifier connection became inaccessible during the baseline project rebuild. Its final status could not be recovered, so no new kernel verification, completed build, axiom audit, checkpoint, or GitHub publication is claimed.

| Result | Current validation |
| --- | --- |
| Fixed vector membership equivalence, full-inverse formula, Schur decrements, and rational 25/16 obstruction floor | Paper proof; draft `ParetoTwoCoordinateDefect.lean` and `ParetoPhysicalDualSchurDefect.lean`. |
| Exact adjoint square and 23/24 signed coercivity, coefficient limit, and conditional RH consumer | Paper proof; draft `ContractiveQuadraticCoercivity.lean` and `ParetoTwoCoordinateSignedCoercivity.lean`. |
| Finite signed Abel difference and mode variation bounds with actual leverage gains | Paper proof; draft `ParetoSignedReciprocalBands.lean`. |
| Sharp norm constant, constructive finite legal approximants, fixed-zero Mellin obstruction, finite enlargement bound (20), and limiting Abel certificate (19) | Paper only; no corresponding new Lean verification. |
| Small-stage Gram and sign diagnostics | Wolfram numerical checks, not interval or kernel certificates. |

The accompanying draft bundle contains these five modules, a combined verification snippet with eight proposed axiom checks, and resumption instructions. The formalization must be compiled and its assumptions audited before publication. The conditional consumers keep their substantive arithmetic providers explicit. In particular, the proposed formal equivalence concerns membership of the constant target in the closed legal span; it does not silently assume a formal RH-to-membership converse.

RH remains open. Neither the fixed defect saturation nor the cofinal signed coefficient lower bound has been established.

The next mathematical target is the provider (17), or saturation of the fixed full-inverse quadratic form (6). The exact square-gain identity (12) supplies its arithmetic budget. The lower estimates (4), (11), and (15) ensure that a fixed hypothetical off-line zero cannot disappear through zero-count normalization or a moving height cutoff.

Seek an unconditional upper bound for the fixed signed defect or an actual cofinal lower bound for 3c_{n,2}+c_{n,3}. Any source-error estimate must include the complete inverse amplification. A density estimate is useful only after proving a transfer that controls one of these unscaled quantities. The first-site band bound (18) gives an independent arithmetic diagnostic while preserving its exact endpoint and square terms.

## 11. The actual dyadic adjoint gives an exact positive remainder

Throughout the continuation put \(P=P_W\), \(R=I-P\), \(F=P{\bf1}\), \(r=R{\bf1}\), and
\[
e=\|r\|^2=1-Q_\infty,\qquad q=\|F\|^2=1-e.
\]
Work in the real Hilbert space in Sections 11–15. Section 16 uses its complexification.

The adjoint of the **actual** zero-anchored dyadic operator is
\[
(S^*x)(m)=\frac{m+1}{2(2m+1)}x(2m)
             +\frac{m}{2(2m+1)}x(2m+1),\qquad m\ge1.
\tag{21}
\]
To verify this, pair \(S f\) against a finitely supported sequence and use
\(w_m(S^*x)(m)=w_{2m}x(2m)+w_{2m+1}x(2m+1)\), where \(w_j=1/[j(j+1)]\). Density extends the identity to all \(x\in H\). In particular \(S^*S=I/2\) and \(S^*{\bf1}={\bf1}/2\).

The weighted variance identity on every pair yields the exact norm defect
\[
\boxed{\frac12\|x\|^2-\|S^*x\|^2
=\frac{x(1)^2}{4}
 +\frac14\sum_{m\ge1}\frac{(x(2m)-x(2m+1))^2}{(2m+1)^2}.}
\tag{22}
\]
Indeed the normalized pair weights are \((m+1)/(2m+1)\) and \(m/(2m+1)\); multiplying their variance by \(w_m/4\) gives the displayed denominator. The first-site contribution is \(w_1x(1)^2/2=x(1)^2/4\). Summing the nonnegative pair identities proves convergence and the equality.

Equivalently, \(2SS^*\) is the orthogonal projection onto the range of \(S\), and
\[
\|x-2SS^*x\|^2
=\frac{x(1)^2}{2}
 +\frac12\sum_{m\ge1}\frac{(x(2m)-x(2m+1))^2}{(2m+1)^2}.
\tag{23}
\]

Since \(SW\subset W\), \(S^*\) preserves \(W^\perp\). For \(A=RS|_{W^\perp}\), therefore \(A^*x=S^*x\) and
\[
\frac12\|x\|^2-\|Ax\|^2=\|PSx\|^2\qquad(x\in W^\perp).
\]
Using these two exact deficiencies in (13), with \(p(z)=14-26z+12z^2\), gives
\[
\boxed{\begin{aligned}
\langle x,p(A)x\rangle={}&\frac{23}{24}\|x\|^2
 +6\left\|(A+A^*)x-\frac{13}{12}x\right\|^2
 +6\|PSx\|^2\\
&+\frac32x(1)^2
 +\frac32\sum_{m\ge1}\frac{(x(2m)-x(2m+1))^2}{(2m+1)^2}.
\end{aligned}}
\tag{24}
\]
Thus the contraction-only bound discards identifiable positive remainders in the actual arithmetic space. The identity \(S^*{\bf1}={\bf1}/2\) does not justify replacing \(A^*r\) by \(r/2\); no such replacement is used here.

## 12. Canonical projection leakage strengthens the signed obstruction

Set \(z=r(1)\) and \(J=\langle r,v\rangle\). Because \(SF\in W\), \(S{\bf1}={\bf1}-\delta_1\), and \(\langle r,{\bf1}\rangle=e\),
\[
\langle r,Ar\rangle=e-z/2.
\tag{25}
\]
Here \(\delta_1\) denotes the sequence equal to one at the first site and zero elsewhere. Also
\[
\langle PSr,F\rangle
=\langle Sr,{\bf1}-r\rangle
=e/2-(e-z/2)=(z-e)/2.
\tag{26}
\]

Unconditionally \(q>0\): the projection onto \(g_2\) alone has squared norm \(\log2>0\), since \(G(2,2)=\log2/4\) and \(b_2=\log2/2\). Hence \(0\le e\le1-\log2<1\). If \(e=0\), all subsequent residual conclusions are immediate. Assume \(0<e<1\) for the identities containing \(1/e\).

Let
\[
U=(A+A^*)r-\frac{13}{12}r,\qquad C=PSr,
\]
\[
U_\perp=U-\left(\frac{11}{12}-\frac{z}{e}\right)r,
\qquad
C_\perp=C-\frac{z-e}{2q}F.
\]
These are exact orthogonal remainders. Equations (24)–(26), together with \(Rv=p(A)r\), give
\[
\begin{aligned}
J={}&\frac{23}{24}e+\frac6e\left(z-\frac{11e}{12}\right)^2
 +\frac{3(z-e)^2}{2(1-e)}+\frac32z^2\\
&+6\|U_\perp\|^2+6\|C_\perp\|^2
 +\frac32\sum_{m\ge1}\frac{(r(2m)-r(2m+1))^2}{(2m+1)^2}.
\end{aligned}
\tag{27}
\]

Write
\[
D(e)=4-2e-e^2,\quad
\Phi(e)=\frac{e(23+19e-27e^2)}{6D(e)},\quad
z_*(e)=\frac{e(11-8e)}{3D(e)}.
\]
Since \(D(e)>0\) for \(0\le e<1\), completing the scalar square in (27) yields the exact equality
\[
\boxed{\begin{aligned}
J={}&\Phi(e)+\frac{3D(e)}{2e(1-e)}(z-z_*(e))^2
 +6\|U_\perp\|^2+6\|C_\perp\|^2\\
&+\frac32\sum_{m\ge1}\frac{(r(2m)-r(2m+1))^2}{(2m+1)^2}.
\end{aligned}}
\tag{28}
\]
In particular the strengthened unconditional signed bound is
\[
\boxed{J\ge\Phi(e)
=\frac{23}{24}e+\frac{e^2(122-85e)}{24D(e)}.}
\tag{29}
\]
Define \(\Phi(0)=0\); then the inequality also holds when \(e=0\). Its surplus is strictly positive for every \(0<e<1\), and is \(61e^2/48+O(e^3)\) near zero.

There is a useful intermediate check obtained by discarding projection leakage before minimization:
\[
J\ge\frac{e(23+36e)}{6(4+e)}
=\frac{23e}{24}+\frac{121e^2}{24(4+e)}.
\tag{30}
\]
The additional improvement in (29) over (30) is exactly
\[
\frac{e^2(1+3e)^2}{6D(e)(4+e)}>0\qquad(e>0).
\]
This does not contradict the abstract sharpness in Section 7: the new surplus uses the canonical target and the actual dilation, and has order \(e^2\), rather than giving a larger uniform linear constant from the contraction assumption alone.

## 13. A relaxed, still exact RH-equivalent arithmetic provider

Let
\[
J_n=4-3c_{n,2}-c_{n,3}=\langle {\bf1}-P_n{\bf1},v\rangle,
\qquad e_n=1-Q_n,
\]
and define the compensated signed statistic
\[
T_n=3c_{n,2}+c_{n,3}-4+\frac{23}{24}(1-Q_n).
\tag{31}
\]
These coefficients always come from the inverse of the complete stage \(n\) Gram matrix. As \(n\to\infty\),
\[
T_n\longrightarrow-J+\frac{23}{24}e
\le-\frac{e^2(122-85e)}{24D(e)}.
\tag{32}
\]
Consequently
\[
\boxed{\mathrm{RH}\iff
\forall\varepsilon>0\ \forall N\ \exists n\ge\max(N,2):
\quad T_n>-\varepsilon.}
\tag{33}
\]
For the forward implication, RH gives \(e=0\), hence \(r=0\), \(J=0\), and \(T_n\to0\). Conversely, the cofinal condition and existence of the limit imply \(\lim T_n\ge0\); (32) then forces \(e=0\), and the established constant-target criterion gives RH.

The new provider permits
\[
3c_{n,2}+c_{n,3}>4-\frac{23}{24}(1-Q_n)-\varepsilon.
\]
It is weaker than demanding the old lower bound \(4-\varepsilon\). It remains unproved. The known monotonicity of \(Q_n\), convergence of the individual fixed coefficients, and square-gain summability do not establish this lower bound.

The exact mixed Schur gains put (33) into an arithmetic budget. For each \(j\ge2\), let \(e_j\) be the newly adjoined normalized mode and write
\[
\alpha_j=\langle {\bf1},e_j\rangle,
\qquad u_j=3t_{2,j}+t_{3,j}.
\]
Then
\[
\boxed{T_{j+1}-T_j
=\alpha_j u_j-\frac{23}{24}\alpha_j^2
=\frac6{23}u_j^2-\frac{23}{24}
\left(\alpha_j-\frac{12}{23}u_j\right)^2.}
\tag{34}
\]
The first expression retains the signed mixed gain; the second retains both square budgets. Telescoping gives
\[
T_N=T_n+\sum_{j=n}^{N-1}\alpha_j u_j
-\frac{23}{24}(Q_N-Q_n).
\tag{35}
\]
Both series converge absolutely: \(\sum\alpha_j^2\le1\), \(\sum u_j^2\le134\), and Cauchy–Schwarz controls \(\sum|\alpha_j u_j|\). Absolute convergence establishes a finite limit, not its required sign. The remaining provider is the cofinal lower control of the **signed** budget in (35).

## 14. Stronger finite certificates with signed enlargement terms

The finite subspace \(V_n\) is generally not \(S\)-invariant. The following proof uses the full physical operator \(S\), so it does not substitute \(P_n\) for \(P_W\) in the invariant-compression argument.

Put \(F_n=P_n{\bf1}\), \(r_n={\bf1}-F_n\), \(z_n=r_n(1)\), and retain
\[
\delta_n=\langle r_n,SF_n\rangle,\qquad
\delta_{2,n}=\langle r_n,S^2F_n\rangle.
\]
The exact signed identity is
\[
J_n=\langle r_n,p(S)r_n\rangle-26\delta_n+12\delta_{2,n}.
\tag{36}
\]
For every \(x\in H\), (22) and \(S^*S=I/2\) give
\[
\langle x,p(S)x\rangle
=\frac{23}{24}\|x\|^2
 +6\left\|(S+S^*)x-\frac{13}{12}x\right\|^2
 +\frac32x(1)^2
 +\frac32\sum_{m\ge1}\frac{(x(2m)-x(2m+1))^2}{(2m+1)^2}.
\tag{37}
\]

For \(e=e_n\), \(z=z_n\), and \(\delta=\delta_n\), project the middle vector in (37) onto the orthogonal vectors \(r_n,F_n\). Their inner products are, respectively,
\[
11e/12-z-2\delta,\qquad (z-e+4\delta)/2.
\]
Thus, retaining the perpendicular norm and the paired variance, the scalar part is
\[
\frac{23e}{24}+\frac6e\left(z+2\delta-\frac{11e}{12}\right)^2
+\frac32z^2+\frac{3(z-e+4\delta)^2}{2(1-e)}.
\tag{38}
\]
The finite stages have \(0<e_n<1\): the first legal atom gives positive projection, while all residue atoms vanish at common multiples of their conductors, so no finite legal combination equals the constant sequence in \(H\).

The exact scalar completion of (38) has minimum
\[
\Phi(e)-\frac{2e(12-5e)}{D(e)}\delta
+\frac{48}{D(e)}\delta^2,
\]
attained at
\[
z=\frac{e(11-8e)}{3D(e)}-\frac{4(2-e)}{D(e)}\delta.
\]
It follows that the strongest signed scalar certificate developed here is
\[
\boxed{J_n\ge\Phi(e_n)
-\left(26+\frac{2e_n(12-5e_n)}{D(e_n)}\right)\delta_n
+\frac{48}{D(e_n)}\delta_n^2+12\delta_{2,n}.}
\tag{39}
\]
The omitted terms are precisely the nonnegative scalar-completion square, the perpendicular projection square from (37), and its paired-variance series. The signed linear terms and the positive enlargement square remain explicit.

The unconditional legal enlargement estimates are
\[
|\delta_n|\le h_n:=\frac1{\sqrt2}\sqrt{Q_n(Q_{2n+1}-Q_n)},\qquad
|\delta_{2,n}|\le t_n:=\frac12\sqrt{Q_n(Q_{4n+3}-Q_n)}.
\]
Only after (39) has been displayed, a convenient estimate is
\[
\boxed{J_n\ge\Phi(e_n)
-\left(26+\frac{2e_n(12-5e_n)}{D(e_n)}\right)h_n-12t_n.}
\tag{40}
\]
These errors tend to zero unconditionally. The larger error coefficient means (40) is not asserted to dominate every older estimate at each small finite stage; its limit is the stronger bound (29).

Two complementary finite certificates are
\[
J_n\ge\frac{23e_n}{24}+\frac32z_n^2-B_n,
\tag{41}
\]
\[
J_n\ge\frac{23e_n}{24}
+\frac{((11e_n-24h_n)_+)^2}{24(4+e_n)}-B_n,\qquad
B_n=26h_n+12t_n.
\tag{42}
\]
Equation (41) may retain the entire paired-variance sum from (37); (42) uses only the residual direction when projecting the middle vector. No coefficient sign or finite-stage monotonicity is assumed.

Everything in the signed enlargement terms is a finite complete-Gram quantity. For \(a=2,4\), define
\[
\delta_n^{[a]}=\langle r_n,S^{\log_2a}F_n\rangle.
\]
Since \(S^{\log_2a}g_d=g_{ad}-g_a/d\),
\[
\boxed{\delta_n^{[a]}=\frac{Q_n}{a}
-\sum_{d,k=2}^{n+1}c_{n,d}c_{n,k}
\left(G(d,ak)-\frac{G(d,a)}k\right).}
\tag{43}
\]
The labels agree with the earlier signed errors: \(\delta_n^{[2]}=\delta_n\) and \(\delta_n^{[4]}=\delta_{2,n}\). The full inverse amplification is already present in \(c_n=G_n^{-1}b_n\).

## 15. Exact algebraic certificates and what they validate

The scalar leakage completion has a division-free form. Set
\[
\begin{aligned}
\mathscr B(e,z,\delta)={}&23e^2(1-e)
+(1-e)(12z+24\delta-11e)^2\\
&+36e(1-e)z^2+36e(z-e+4\delta)^2.
\end{aligned}
\]
Then
\[
\begin{aligned}
D(e)\mathscr B(e,z,\delta)
&-4e(1-e)\{e(23+19e-27e^2)-12e(12-5e)\delta+288\delta^2\}\\
&=4\{3D(e)z-e(11-8e)+12(2-e)\delta\}^2.
\end{aligned}
\tag{44}
\]
For \(0<e<1\), the hypothesis \(\mathscr B\le24e(1-e)J_0\) therefore implies
\[
e(23+19e-27e^2)-12e(12-5e)\delta+288\delta^2\le6D(e)J_0.
\tag{45}
\]
Taking \(\delta=0\) gives the algebraic part of (29). These are ordered-field implications with their scalar energy premise explicit. Establishing that premise for the actual Hilbert-space objects uses the paper proof above; checking the scalar lemma alone does not kernel-verify that application.

For the compensated consumer, \(0\le e<1\), \(e(23+19e-27e^2)\le6D(e)J\), and \(24J\le23e\) force \(e=0\): otherwise they imply \(e^2(122-85e)\le0\), contradicting positivity. This is the algebraic contradiction used in (33).

## 16. Multizero and multiplicity-aware unscaled Mellin obstructions

The one-zero diagnostic in Section 4 can preserve correlations and all multiplicities. Let \(Z\) be any finite set of distinct actual zeros \(\rho\) with \(\Re\rho>1/2\), and let \(m_\rho\) be their multiplicities. This section is an implication for such zeros, and assumes neither their existence nor simplicity.

Use the complex inner product linear in its first argument. For \(I_j=(1/(j+1),1/j]\), define
\[
a_s(j)=\int_{I_j}x^{s-1}\,dx=\frac{j^{-s}-(j+1)^{-s}}s.
\]
For every index \(i=(\rho,r)\), \(0\le r<m_\rho\), put
\[
a_i(j)=\int_{I_j}x^{\rho-1}(\log x)^r\,dx,\qquad
T_i(f)=\sum_{j\ge1}f(j)a_i(j).
\]
Cellwise Cauchy–Schwarz gives
\[
\|T_i\|^2\le\frac{(2r)!}{(2\Re\rho-1)^{2r+1}}.
\tag{46}
\]
The legal Mellin identity, differentiated fewer than \(m_\rho\) times, shows \(T_i(g_d)=0\) for every conductor \(d\ge2\); boundedness extends this to \(W\). The correct constraints for a multiple zero are these derivative functionals, rather than repeated identical evaluations.

Define the exact discrete Hermitian jet Gram and target vectors by
\[
\mathsf B_Z(i,k)=\sum_{j\ge1}j(j+1)a_i(j)\overline{a_k(j)},
\]
\[
\mathsf h_v(\rho,r)=\left.\frac{d^r}{ds^r}\frac{p(2^{-s})}{s}\right|_{s=\rho},\qquad
\mathsf h_0(\rho,r)=\frac{(-1)^r r!}{\rho^{r+1}}.
\]
This matrix is positive definite. To see independence of the functionals, a vanishing linear combination of all cell integrals has a primitive
\(P(x)=\sum d_{\rho,r}\partial_s^r(x^s/s)|_{s=\rho}\) that vanishes at every \(1/j\). Its limit at zero is zero. If the entire exponential polynomial \(P(e^{-t})\) were nonzero, Jensen's formula and its exponential-type growth bound would allow only \(O(R+\log R)\) zeros in disks of radius \(R\) about a point where it is nonzero. The zeros \(t=\log j\) give exponentially many such zeros. Hence it vanishes identically, and independence of exponential-polynomial terms forces every coefficient to vanish.

Orthogonal projection onto the span of their Riesz representers yields
\[
\boxed{\mathcal E_n\ge\|Rv\|^2\ge
\mathsf h_v^*\mathsf B_Z^{-1}\mathsf h_v,\qquad
1-Q_n\ge e\ge\mathsf h_0^*\mathsf B_Z^{-1}\mathsf h_0.}
\tag{47}
\]
For one simple zero, the first bound reduces exactly to (11). The full matrix retains interzero and multiplicity-jet correlations. Adding one more independent functional, with augmented matrix \(\left(\begin{smallmatrix}\mathsf B&k\\k^*&a\end{smallmatrix}\right)\) and target \(\binom h z\), gives the exact nonnegative Schur gain
\[
\frac{|z-k^*\mathsf B^{-1}h|^2}{a-k^*\mathsf B^{-1}k}.
\tag{48}
\]
Individual zero bounds cannot generally be added as if their representers were orthogonal.

The continuous Mellin jet Gram is
\[
\mathsf C_Z((\rho,r),(\tau,k))
=\frac{(-1)^{r+k}(r+k)!}{(\rho+\overline\tau-1)^{r+k+1}}.
\]
Projection onto step functions gives \(0<\mathsf B_Z\le\mathsf C_Z\), so inversion strengthens the discrete obstruction. The confluent Cauchy determinant, obtained by adjoining the constant-target kernel at \(s=1\), gives
\[
\mathsf h_0^*\mathsf C_Z^{-1}\mathsf h_0
=1-\prod_{\rho\in Z}\left|\frac{1-\rho}{\rho}\right|^{2m_\rho}.
\]
For distinct simple nodes this is the Cauchy determinant ratio; coalescing nodes by difference quotients produces the derivative Gram and the multiplicity exponents. Therefore
\[
\boxed{e\ge1-\prod_{\rho\in Z}\left|\frac{1-\rho}{\rho}\right|^{2m_\rho}.}
\tag{49}
\]
The same right side is a lower bound for every \(1-Q_n\), and multiplied by \(\kappa^2\) it is a lower bound for every \(\mathcal E_n\). Moreover, for \(Q_n>0\),
\[
\boxed{\sum_{\rho\in Z}m_\rho\frac{2\Re\rho-1}{|\rho|^2}
\le-\log Q_n.}
\tag{50}
\]
This follows from \(Q_n\le\prod(1-u_\rho)^{m_\rho}\), where \(u_\rho=(2\Re\rho-1)/|\rho|^2\), and \(-\log(1-u)\ge u\). It constrains unscaled weighted off-line zero mass; it forces that mass to vanish only when \(Q_n\to1\).

There is an explicit monotone finite certificate for the infinite kernel. Truncate the step Gram at \(j\le J\), and add the continuous tail Gram
\[
\mathsf C^{\mathrm{tail}}_{Z,J}((\rho,r),(\tau,k))
=\left.\partial_s^r\partial_{\bar t}^k
\frac{(J+1)^{1-s-\bar t}}{s+\bar t-1}\right|_{s=\rho,t=\tau}.
\]
For \(\mathsf U_{Z,J}=\mathsf B_{Z,J}+\mathsf C^{\mathrm{tail}}_{Z,J}\), cell projection gives
\[
\mathsf B_Z\le\mathsf U_{Z,J+1}\le\mathsf U_{Z,J}\le\mathsf C_Z,\qquad
\mathsf U_{Z,J}\to\mathsf B_Z.
\]
Hence
\[
\mathcal E_n\ge\mathsf h_v^*\mathsf U_{Z,J}^{-1}\mathsf h_v
\nearrow\mathsf h_v^*\mathsf B_Z^{-1}\mathsf h_v.
\tag{51}
\]
The direction matters: inverting the step truncation alone need not give a valid lower obstruction. For one zero, the safe upper bound on its kernel norm is
\[
K_\rho\le\sum_{j=1}^Jj(j+1)|a_\rho(j)|^2
+\frac{(J+1)^{1-2\Re\rho}}{2\Re\rho-1}.
\]

These Mellin results strengthen the obstruction side. No completeness assertion about the zero representers inside \(W^\perp\) is assumed, and no lower obstruction is converted into an upper approximation bound.

## 17. Current validation and continuation target

The current repository base was independently read through GitHub and remained `bc2fd31a9641976a9e34049028419d3ef08f5dfd` during this continuation. The repository instructions require preservation of signed summands, boundary terms, and norm-square remainders; the formulas above follow that policy.

The supporting module `Analysis/DyadicAdjointDefect.lean` was checked in an isolated workspace based on `bc2fd31a9641976a9e34049028419d3ef08f5dfd`. Verification job `job_RBNRvoYxsDQXUORDiNTg1pLi1g5r5iYq` finished successfully with exit code 0 and `verified: true`; the reported elapsed time was 20.04 seconds. All ten declarations passed. Each associated `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`.

| Verified declarations | Exact scope of the check |
| --- | --- |
| `completed_square`, `nonlinear_lower_bound`, `limiting_lower_bound`, `leakage_completed_square`, `leakage_lower_bound`, `finite_leakage_completed_square`, `finite_leakage_lower_bound`, `zero_of_compensated_upper` | Scalar square completions and lower-bound or contradiction implications. Their scalar energy premises remain explicit. |
| `weighted_pair_defect` | The finite weighted-pair variance identity supporting (22). This check does not sum the infinite Pareto series. |
| `adjoint_square_identity` | A generic real Hilbert-space identity for four vectors, with its required inner-product premises. This check does not instantiate the actual dyadic operator or its arithmetic compression. |

At commit `dd5e0269ca04ddb8b84b75fbbd0a3ebe2c00cff6`, the actual operator and coefficient applications, including (22), (28), (33), (39), and the Mellin-jet construction, remained paper proofs. Section 18 records the subsequent actual formalization of (22), (28), and the conditional (33) consumer. The ten supporting declarations alone did not establish those Hilbert-space energy premises or close the arithmetic provider. This historical check did not assert that the five older draft modules compiled or that a full-project rebuild completed.

Primary-source grounding: [Bagchi's paper](https://www.isibang.ac.in/~statmath/eprints/2005/isibc200535.pdf), Theorems 1, 2, and 7, supplies the Pareto criterion, step-function interpretation, and dilation setting. The explicit canonical leakage identities, chosen fixed polynomial, compensated statistic, and finite certificates here are deductions from that setting and the project's dual identities. [Burnol's paper](https://arxiv.org/pdf/math/0103058), Theorem 1.3 and Section 5, supports using multiplicity derivative constraints in related approximation problems. Its critical-line logarithmic bound is a different result; its multiplicity-squared constant is not imported into (49).

The next RH task is now the relaxed arithmetic provider (33), or equivalently its exact signed mixed-gain budget (35). A successful proof must bound the complete inverse-derived coefficients, or the aggregate signed mixed gains, from below along an unbounded sequence of legal stages. An upper bound for a normalized zero-density statistic, a source term before inverse amplification, or absolute convergence of the Schur gains does not supply this provider.

The new unconditional result is a stronger obstruction with an exact weaker consumer. It does not prove RH.

## 18. Actual dyadic and compensated coefficient formalization

This continuation instantiates the algebra with the existing complete
`ThresholdHilbert`, actual zero-anchored dyadic dilation, Hilbert adjoint,
closed residue span, and full-norm optimal projections.

- `RH/ActualDyadicAdjointDefect.lean` proves the actual coordinate adjoint
  formula (21), convergence of the complete pair-variance series, exact
  infinite norm defect (22), and full-space positive-square identity (37).
  Its operator and summability premises are constructed, not supplied.
- `RH/DyadicCanonicalLeakage.lean` proves the actual canonical inner
  identities and equation (28). Its theorem
  `canonical_completed_leakage_two_remainders` retains the scalar
  completion square, both orthogonal Hilbert remainder squares, and the
  whole pair-variance series. `limiting_twoThree_leakage_energy_budget`
  proves the previously missing actual Hilbert-to-scalar energy premise.
  The checked scalar `leakage_lower_bound` and
  `zero_of_compensated_upper` are thereby instantiated with actual
  canonical objects. The surplus estimate in (32) is also formalized.
- `RH/CompensatedTwoCoefficientCriterion.lean` proves the actual complete
  inverse-Gram formula for the statistic, its unconditional convergence,
  and its exact limiting negative-square identity. The finite identity
  keeps both signed enlargement terms:
  `T_n = -||B r_n||^2/12 + 13 <r_n,D F_n> - 3 <r_n,D^2 F_n>`,
  where `D=2S` and `B=6I-(13/2)D+3D^2`. These are exactly
  `+26 delta_n-12 delta_(2,n)`; no finite-space dilation invariance is
  assumed.

The formal compensated consumer is
`twoThreeCompensated_cofinal_iff_residual_zero`, together with the equivalent
zero-energy and constant-membership formulations. The cofinal condition
`TwoThreeCompensatedCofinal` remains an explicit **Open arithmetic provider**.
It is not discharged by coefficient convergence or square summability.

The RH implication
`riemannHypothesis_of_twoThreeCompensated_cofinal` uses the existing
membership-to-RH bridge and has only this arithmetic hypothesis.
The formal reverse RH implication still requires the explicit structural
bridge
`hTarget : RiemannHypothesis → hilbertOne ∈ closedSpace`.
Accordingly `riemannHypothesis_iff_twoThreeCompensated_cofinal` exposes
`hTarget`; the unconditional formal equivalence is with residual zero,
not a silently assumed RH-to-density theorem.

Equations (39), the Mellin-jet construction, the cofinal arithmetic estimate
(33)/(35), and the classical RH-to-target-membership converse are not claimed
to have been supplied by this continuation. RH remains open.

The smallest remaining formal statement needed for the reverse implication is:

```lean
theorem one_mem_closedSpace_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    hilbertOne ∈ CoefficientStabilization.closedSpace
```

This is the classical analytic converse, not the cofinal arithmetic provider.
The actual dyadic operator and projection definitions do not prevent the
forward instantiation.

Verification: coherent snippet job `job_CYQwLzZAHN16mkaNGaBWPXRDd0f_0hcJ`
succeeded with exit code 0 and `verified: true` in 8.367 seconds. The ten
main declaration axiom checks reported only `propext`, `Classical.choice`,
and `Quot.sound`; no placeholder axiom occurred. A baseline
`lake build RiemannResearch --quiet` succeeded before this check.
The new modules are exported from `RiemannResearch.lean` for the separate
checkpoint validation of the actual module graph and publication.
