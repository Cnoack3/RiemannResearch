# Two tests on the first projected correction for RH


The first projected correction $b$ now gives two ways to reach RH. The harmonic route asks for a cofinal polylogarithmic bound on its cheaper sign. The absolute-moment route asks for a single finite weighted sum on $b$, using a translate of the full Lee–Leong exponent which removes the former positive square-root margin. Both have equivalents in terms of finite projections. The two required estimates on the actual correction are open.

| Evidence | What it supplies |
|---|---|
| Lean project | The projection identities, harmonic error bounds, square-energy bound, finite-stage criteria, and the translated weighted-moment implication with the named Mertens premise. |
| Published mathematics | Lee–Leong's ordinary Mertens estimate for the weighted forward argument and Báez-Duarte's squarefree-supported approximation for the converse under RH. |
| Independent numerical certificate | The explicit finite trial at conductor $80$ bounds the true infinite-space residual by $0.085414803$ in norm. |
| Paper deductions | The matching lower bound for this particular uniform envelope, the lacunary squarefree obstruction and the common dyadic subsequence bounds. |

The [concurrent finite Gram and implicit truncation results](RH/FiniteGramDisplacementResearch20261105.md) give a prescribed finite Gram test on the displacement and a separate route from the stronger Proposition 5.2. The printed-estimate argument below works directly from Theorem 1.1(12). The $M=10$ interval computations independently reproduce the prefix entries in the finite Gram experiment.

**Which absolute moment suffices?** With $t=\log n$ and $f(t)=F(n)$, the arithmetic assumption determines the available weight. Each line below concerns the same $b=\Pi Br_Q$. The factor $1/n$ is part of every physical moment.

| Arithmetic input | Sufficient absolute moment on the correction | Where to look |
|---|---|---|
| Lee–Leong Theorem 1.1(12) | $\sum_n \lvert b(n)\rvert t^2 e^{-f(t-f(t))}/n<\infty$. The explicit sufficient weight $e^{-F(n)+(3/5)F(n)^2/\log n}$ is also available. | [Translated-moment proof](RH/MertensDelayedMoment.lean) · [Sharp comparison](RH/MertensDelayedSharpEndpoint.lean) |
| Implicit optimized cutoff obtained from Proposition 5.2 and §5.4 | For **any one fixed** $s\in\mathbb R$, $\sum_n \lvert b(n)\rvert e^{-F(n)-s\sqrt{\Phi(n)}}/n<\infty$. In particular $s=0$ retains the exact printed weight, and $s>0$ gives a still smaller weight. | [First correction and finite heads](RH/QFirstCorrectionImplicitMoment.lean) · [Derivation from the published proposition](RH/MertensImplicitTruncationResearch20261105.md) |

The repository records the two analytic inputs as named propositions. The publication supplies the mathematical estimates. A kernel-checked provider for each external input used in the forward argument remains open. With the implicit assumption, the finite-head criterion states that one constant bounds the $e^{-F(n)-s\sqrt{\Phi(n)}}/n$ partial moments of $b_M$ over arbitrarily large conductor stages at each fixed physical cutoff. A pointwise bound $|b(n)|=O(e^{F(n)+s\sqrt{\Phi(n)}})$ also suffices, by using a slightly larger $s$ in the moment.

## The same vector in both tests

Let $Q(n)=1/(\zeta(2)n^2)$ and $P(n)=1/[n(n+1)]$ on the positive integers, let $V$ be the closed $L^2(Q)$ span of the residues $g_m(n)=\{n/m\}$ for squarefree $m\ge2$, and write $\Pi$ for its orthogonal projection. Put $r=1-\Pi 1$, $Bf(n)=f(n)/(n+1)$, and $b=\Pi Br$. The centered resolvent approximants to the displacement $d=f_Q-f_P$ between the two projections of $1$ in the $Q$ and $P$ norms start with $u_0=0$ and $u_1=4b/3$. For each closed finite stage $V_M$ let $r_M=1-\Pi_M1$ and $b_M=\Pi_M B r_M$. These are the finite projections appearing in the two tests. Conductor bound and physical cutoff are independent indices.

The exact identity behind both arguments is
$$
s=Br-b\in V^\perp,\qquad
\langle 1,s\rangle_Q=\langle r,Br\rangle_Q
=\sum_{n\ge1}\frac{|r(n)|^2}{\zeta(2)n^2(n+1)}.
$$
Thus zero mean for this specific annihilator forces $r=0$. The repository's squarefree capacity theorem then gives Mathlib's Riemann hypothesis. This positive identity permits a proof at depth one even when no rate of convergence of the full iteration is available.

**One-sided harmonic test.** Write $h(v;X)=\min_{\varepsilon=\pm1}\sum_{n=1}^{X}(\varepsilon v(n))_+/n$. For fixed $C,B_1\ge0$, a bound $h(u_1;X)\le C(\log X)^{B_1}$ at arbitrarily large $X$ forces $r=0$. The proof pairs the signed coefficients of $s$ with the squarefree Möbius head and a prime residue, choosing the cheaper sign at each cutoff. Both charge tails enter the finite inequality. The repository supplies the arithmetic for this forward direction. An entirely finite equivalent of $r=0$ is
$$
\forall X_0\;\exists X\ge X_0\;\forall M_0\;\exists M\ge M_0:\quad h(b_M;X)\le 1 .
$$
For each fixed $X$, $b_M\to b$ in each physical coordinate, so the finite prefix converges. If $r=0$ the limiting prefix is zero and the positive threshold supplies slack. The converse applies the cofinal prime-probe estimate. The same equivalence holds with any fixed positive threshold. A sequence of computations must address both quantifiers.

**Full Lee–Leong moment test.** On the eventual real domain write
$$
\Phi(x)=\frac{(\log x)^{3/5}}{(\log\log x)^{1/5}},\quad A=\left(\frac{5}{3(53.99)^3}\right)^{1/5},\quad
F(x)=A\frac{(\log x)^{3/5}}{(\log\log x-\log 53.99)^{1/5}},\quad H_\delta=F-\delta\sqrt\Phi .
$$
For any fixed $\delta>0$, put $J_\delta(v)=\sum_{n\ge n_0}e^{-H_\delta(n)}|v(n)|/n$ with fixed sufficiently large $n_0$. Finite initial terms and the fixed $1/\zeta(2)$ normalization do not affect summability. Under the published Mertens estimate, $J_\delta(b)<\infty$ is equivalent to $r=0$. The full moment of $u_1$ is $4/3$ times that of $b$. The proof transfers the Mertens envelope to any orthogonal difference $Bv-z$ with finite moment on $z$, then specializes to $v=r,z=b$. The reverse implication from $r=0$ is immediate. To replace $r=0$ by RH in the reverse direction, the Lean declaration also takes Báez-Duarte's approximation under RH as an explicit hypothesis. [Lee and Leong, Theorem 1.1, (12)](https://arxiv.org/html/2208.06141v5) · [Báez-Duarte, explicit Möbius approximants](https://arxiv.org/pdf/math/0205003) · [Bagchi, Remark 8 on squarefree support](https://arxiv.org/pdf/math/0607733)

The finite equivalent of $J_\delta(b)<\infty$ requires **one constant** $C$ such that for every $K$, arbitrarily large $M$ satisfy
$$
\sum_{n_0\le n<K}\frac{e^{-H_\delta(n)}}n |b_M(n)|\le C .
$$
The stage subsequence may depend on $K$. A bounded diagonal with both indices tending to infinity is sufficient by positivity. The alternate displacement test takes $I_j=[2^j,2^{j+1})$ and replaces $d$ on $I_j$ by $u_j$. For bounded nonnegative damping $w$, the error on one shell is at most $\|w\|_\infty\sqrt{\zeta(2)}\|d\|(\sqrt{2}/3)^j$. Summing makes the replacement exact at the level of summability. In particular, if $A_j=\sum_{n\in I_j}|u_j(n)|/n$, a bound $A_j\le C e^{H_\delta(2^j)}/(1+j)^{1+\epsilon}$ for some $\epsilon>0$ suffices. These shell approximants use the full projector; the preceding $b_M$ test uses only finite conductor stages.

## Bounds on the harmonic approximants

The prefix is Lipschitz in the physical Hilbert norm with constant $\sqrt{\zeta(2)X}$. Self-adjointness and the fact that $r\perp V$ give the stronger simultaneous control
$$
2\sqrt{j+1}\,\|d-u_j\|_Q\le 3^{-j}\|r\|_Q .
$$
In fact with $T=\Pi(4B-I)|_V$, $C_0=\Pi(4B-I)|_{V^\perp}$, one has $3d=C_0r+Td$ and $d-u_j=3^{-j}T^jd$. The defect $\|T^jx\|^2-\|T^{j+1}x\|^2$ decreases in $j$ and controls the squared norm of the adjoint coupling to $V^\perp$. This yields the square-root gain. In particular if $X\le9^j$, the error in $h$ is at most $\sqrt{\zeta(2)}\|r\|/(2\sqrt{j+1})$. The unconditional size bound from the Hilbert norm is $h(u_{j(X)};X)=o(\sqrt X)$ for $X\le9^{j(X)}$. The cofinal polylog bound remains an arithmetic problem about these particular projections.


The squared errors also obey the finite inequality
$$
4\sum_{k<N}9^k\|d-u_k\|_Q^2\le\|r\|_Q^2 .
$$
Consequently, for any cutoffs $X_k\le9^k$, the sum of squared harmonic-prefix discrepancies is bounded by $\zeta(2)\|r\|_Q^2/4$. As a concrete universal normalization, $2g_2$ agrees with $1$ on odd integers and vanishes on even integers, whose $Q$ mass is $1/4$. Lean checks $\|r\|_Q\le1/2$ and $\|d\|_Q^2\le1/32$.

## Finite computation and arithmetic targets

Write $g_m(n)=\{n/m\}$ and take **every squarefree** $2\le m\le M$. Let $d_M=f_{Q,M}-f_{P,M}$ be the difference of the two projections of $1$ onto this finite span. For $h(v;X)=\min_{\varepsilon=\pm1}\sum_{n\le X}(\varepsilon v(n))_+/n$, the following are certified finite-span results. They give no error bound for replacing the infinite projection by a fixed conductor cutoff.

| $M$ | $X$ | $j$ | $h(d_M;X)$ | $h(u_{M,1};X)$ | $h(u_{M,j};X)$ |
|---:|---:|---:|---:|---:|---:|
| 20 | 9 | 1 | .00320995 | .00338986 | .00338986 |
| 20 | 81 | 2 | .01686408 | .01819261 | .01582417 |
| 20 | 729 | 3 | .03008835 | .03251600 | .03009194 |
| 20 | 6561 | 4 | .04380192 | .04749639 | .04360599 |
| 80 | 9 | 1 | .00348579 | .00399957 | .00399957 |
| 80 | 81 | 2 | .01050125 | .01211370 | .00990706 |
| 80 | 729 | 3 | .03010575 | .03394990 | .03023009 |
| 80 | 6561 | 4 | .04807225 | .05395528 | .04781742 |

The table rounds to eight decimals (absolute error $<5.1\times10^{-9}$). At depth four the iteration error in $h$ is about $0.000196$ for $M=20$ and $0.000255$ for $M=80$. The change between the two conductors is larger. Neither difference estimates the error at infinite conductor. Every fixed finite vector is bounded and hence automatically has $h(v;X)=O_M(\log X)$; the dependence on $M$ is the issue.

**Reproduction.** The [numerical supplement](https://chatgpt.com/library?file_id=libfile_ed86bb1ebf3c819193f113757766e382&account_id=personal) includes the script and signed results. Run the script with Python 3 and NumPy.

```sh
python cert_harm.py 10 20 40 80 --csv harmonic_certificates.csv
```

The CSV includes both harmonic signs, an absolute error bound including decimal rounding, and certified sign counts. Use the unnormalized weight $Q_0(n)=n^{-2}$ (same projector as $Q$) and $P(n)=1/[n(n+1)]$. Write $G_Q,G_P$ for the two Gram matrices and $q,p$ for their inner products with $1$. The coefficient vectors are $\alpha=G_Q^{-1}q$, $\beta=G_P^{-1}p$; $d_M$ has coefficients $\alpha-\beta$. Starting at $u_{M,0}=0$, in coordinates the centered iteration is
$$
u_{M,j+1}=u_{M,j}+\tfrac43 G_Q^{-1}\{G_P(\alpha-u_{M,j})-p\}.
$$

For a Gram entry of period $L=\mathrm{lcm}(i,j)$, the script groups all physical sites into their $L$ residue classes. It sums the first 64 terms per class and encloses the remaining series by Euler–Maclaurin through $B_{20}$. For a class starting its tail at $s=64L+a$, its remainder is at most $|B_{20}|L^{19}/s^{21}$ for either weight (the $P$ bound uses $1/n-1/(n+1)$). The $P$ integral uses the alternating expansion of $\log(1+1/s)$ through degree 24. Integer rounding at scale $10^{45}$ and then $10^{30}$ gives a uniform entry error $<2\times10^{-30}$ for $M\le80$. The script checks approximate inverses by bounding $\|I-BG\|_\infty<1$, verifies solve residuals with integers, and propagates their bounds using $\|I-\tfrac43G_Q^{-1}G_P\|_{G_Q}\le1/3$. Before display rounding, the largest prefix uncertainty was $<3\times10^{-14}$. This is a reproducible numerical certificate, separate from Lean verification.

## A coefficient test for each route

Suppose $v=\sum_m c_mg_m$ is a finite vector. Positivity of the atoms gives a **one-sign** harmonic estimate
$$
h(v;X)\le\min_{\varepsilon=\pm1}\sum_m(\varepsilon c_m)_+ T_X(m),\qquad
T_X(m)=\sum_{n\le X}\min(1/m,1/n)
\le\begin{cases}1+\log(X/m),&m\le X,\\X/m,&m>X.\end{cases}
$$
Thus coefficients at conductors far above $X$ incur only $X/m$. Apply this to $d_M$, take $\liminf_{M\to\infty}$ at each fixed $X$ (finite projections converge in physical coordinates), then seek a polylogarithmic bound for arbitrarily large $X$. No rate of conductor convergence is needed for this ordering of limits.

For the full Lee–Leong moment, set $H_\delta=F-\delta\sqrt\Phi$ as in the research agenda, with fixed $\delta>0$ and a sufficiently large fixed $n_0$. The **exact cost of one atom** is
$$
K_\delta(m)=\sum_{n\ge n_0}g_m(n)e^{-H_\delta(n)}/n.
$$
The triangle inequality gives $J_\delta(d_M)\le\sum_m |c_{M,m}|K_\delta(m)$. Fatou's lemma shows that a bounded liminf of these coefficient budgets gives $J_\delta(d)<\infty$. The moment criterion then applies with its published arithmetic premise.

There is a useful scale for the cost:
$$
K_\delta(m)\sim \frac{5}{6A}(\log m)^{2/5}(\log\log m)^{1/5}e^{-H_\delta(m)}\quad(m\to\infty).
$$
Indeed, write $h(t)=H_\delta(e^t)$ and $y=\log m$. Direct differentiation gives $h'(t)\sim (3A/5)t^{-2/5}(\log t)^{-1/5}$ and $h''/(h')^2\to0$. Eventually $0<h'\le1/2$, so the part $n<m$, where $g_m(n)=n/m$, is $O(e^{-h(y)})$ by $e^{-h(\log n)}\le e^{-h(y)}(m/n)^{1/2}$; finitely many initial terms are harmless. For $n\ge m$, subtract the period mean $(m-1)/(2m)$ of $g_m$. Its centered partial sums have absolute value at most $m$, so summation by parts against the decreasing weight $e^{-H_\delta(n)}/n$ costs $O(e^{-h(y)})$. Integral comparison and l'Hôpital's rule give $\sum_{n\ge m}e^{-H_\delta(n)}/n\sim\int_y^\infty e^{-h(t)}dt\sim e^{-h(y)}/h'(y)$. This proves the displayed equivalent.

These two coefficient estimates are paper deductions. Their hypotheses on the actual finite Gram solutions remain open. The moment budget discards coefficient cancellation; failure of that sufficient test would leave the scalar displacement moment open.

The same coefficient tests apply to $b_M$. In that case only the residual projected under $Q$ is needed as input. For the one-step columns in the table, $h(b_M;X)=3h(u_{M,1};X)/4$.

**What a finite computation *does* bound at infinite conductor.** A legal trial vector can be used directly in the variational upper bound for the true residual. For a rational vector $a$ on the squarefree conductors through $M$, put $v=\sum_m a_m g_m$, use the unnormalized Gram matrix $G$ and target column $q$ under $1/n^2$, and let $Z=\zeta(2)$. Then
$$
\|r_Q\|_Q^2\le \|1-v\|_Q^2=\frac{Z-2q^\mathsf{T}a+a^\mathsf{T}Ga}{Z},
\qquad 8\|d\|_Q^2\le\|r_Q\|_Q^2 .
$$
If all entries (including $Z$) have error at most $\epsilon$, add $\epsilon(1+\|a\|_1)^2$ to the computed numerator and divide by the lower endpoint for $Z$. No accuracy assumption on the trial solve is required. With the script's rational coefficients and $\epsilon=2\cdot10^{-30}$, the following are upper bounds rounded outward:

| $M$ | $\lVert r_Q\rVert_Q$ | $\lVert d\rVert_Q$ |
|---:|---:|---:|
| 10 | 0.131334324 | 0.046433696 |
| 20 | 0.107328179 | 0.037946242 |
| 40 | 0.093291014 | 0.032983355 |
| 80 | 0.085414803 | 0.030198694 |

Thus the actual harmonic-prefix approximation error on $X\le9^j$ is at most $\min(0.03874,0.05478/\sqrt{j+1})$. These numerical constants bound the error of the infinite-space *resolvent*, not the error of replacing it by the $M=80$ projection. They certify an upper bound on a norm that can still be zero.

## The translated Lee–Leong weight and its exponent loss

This deduction uses exactly the repository's two-branch Möbius error envelope. Write $t=\log n$, $c=\log 53.99$ and $f(t)=A t^{3/5}(\log t-c)^{-1/5}$ on its eventual domain. The published Mertens estimate gives $\varepsilon_N=25.85(\log N)e^{-f(\log N)}$ for sufficiently large $N$. It decreases to zero, since $t f'(t)\to\infty$. Define, for large $n$,
$$
 G(n)= (\log n)^2 \exp[-f(\log n-f(\log n))].
$$
Extend $G$ positively on the omitted finite head. Then the full absolute moment with this damping, $\sum_{n\ge1} G(n)|z(n)|/n<\infty$, suffices in the cutoff-pairing theorem for $z=b$ or $z=d$.

Indeed the envelope vanishes for $n\le N$. Otherwise put $s=\log N\le t$. If $s\le t-f(t)$ then its first branch is $3N\le3n e^{-f(t)}\le3nG(n)$. If $s>t-f(t)$, eventual monotonicity gives $f(s)\ge f(t-f(t))$. In the other branch $\varepsilon_N\le25.85t e^{-f(t-f(t))}$, while $\log(1/\varepsilon_N)=f(s)-\log(25.85s)\le f(t)\le t$ eventually. Thus this branch is at most $2+C nG(n)$ for a fixed $C$. The remaining scalar moment $\sum G(n)/n$ converges by comparison with $(n(\log n)^2)^{-1}$, since $f(t-f(t))/\log t\to\infty$. All other hypotheses are those of the repository's exponential-cutoff pairing with $E(N)=\log \varepsilon_N$; the forward direction uses the published Mertens estimate only. More explicitly, the new `annihilator_mean_zero_of_exponential_cutoff_moment` takes $E\to-\infty$, eventual monotonicity, $|M(x)|\le x e^{E(x)}$, the displayed envelope majorant, and the two sums $\sum Q(n)W(n)$ and $\sum Q(n)W(n)|z(n)|$, with $W(n)=nG(n)$. Its dominated-convergence argument uses a fixed multiple of the summable majorant $Q(n)[2+C W(n)](1+|z(n)|)$: the weight-free terms are finite by $\sum Q=1$ and Cauchy–Schwarz in $L^2(Q)$. The extra constant bounds the physical coordinates of $Bv$, as in the generalized pairing lemma. The defect is eventually zero at each fixed site. The orthogonal-pairing theorem applies to $Bv-z\in V^\perp$; use $(v,z)=(r_Q,b)$ or the repository's displacement witness $(r_P,d)$. The corresponding checked mean-to-residual implication then yields $r_Q=0$ and hence RH. No Báez–Duarte hypothesis is required forward. This gives a sufficient condition, not an unconditional bound on $b$ or $d$.

The size of the loss can also be read explicitly:
$$
 \log G(n)=-f(t)+ f(t)f'(t)+2\log t+o(1),\qquad
 f(t)f'(t)=\frac{f(t)^2}{t}
 \left(\frac35-\frac1{5(\log t-c)}\right).
$$
Taylor's remainder is $O(f(t)^3/t^2)=o(1)$ because $f''(u)=O(f(t)/t^2)$ uniformly for $t-f(t)\le u\le t$. In particular $G(n)\le C'\exp[-f(t)+(3/5)f(t)^2/t]$ eventually: the negative correction $f(t)^2/[5t(\log t-c)]$ dominates $2\log t$. This loss is $o(\sqrt{\Phi(n)})$, hence smaller than every fixed positive square-root margin. The exact no-loss weight $e^{-f(t)}$ is not reached. Lean verifies the moment criterion for the displayed translated weight, its scalar summability, and its eventual domination by every previous positive square-root margin. It also verifies the explicit upper loss $(2A)^2\Phi(n)^2/\log n+2\log\log n$. The secant proof in Lean also yields the endpoint upper loss $(3/5)F(x)^2/\log x$, including a further factor $(\log x)^{-2}$ in the majorant. The Taylor expansion and matching lower bound for this particular cutoff envelope are paper deductions.

**What this cutoff estimate cannot improve.** For the same raw $\varepsilon_N$ and the same two-branch envelope, the order $nG(n)$ is necessary if a bound is to be uniform in $N$. Choose $N=\lfloor nG(n)\rfloor$; this tends to infinity and is less than $n$. Then $s=\log N=t-f(t-f(t))+2\log t+o(1)$, so $s/t\to1$ and $s-(t-f(t))=O(f(t)^2/t+\log t)$. Since $f'=O(f(t)/t)$ in this window, $f(s)-f(t-f(t))=O(f(t)^3/t^2+(f(t)/t)\log t)=o(1)$. The first branch is asymptotic to $3nG(n)$; the second is at least $n\varepsilon_Nt\sim25.85nG(n)$. In particular their minimum is bounded below by a fixed positive multiple of $nG(n)$. Since $\log G(n)+f(t)\sim(3/5)f(t)^2/t$, no fixed $\kappa<3/5$ can give a uniform majorant $O(1+n\exp[-f(t)+\kappa f(t)^2/t])$ for this envelope. A sharper Mertens bound, cancellation of signed physical terms, or a different cutoff argument is not excluded.


## What fails for general squarefree vectors

**Paper proposition: Hilbert energy and squarefree legality alone do not bound either route.** Let $V$ be the actual squarefree closure in $L^2(Q)$, $g_p(n)=\{n/p\}$ for primes $p$. There exists $u\in V$ with both $S_+(u;X)$ and $S_-(u;X)$ at least $c\sqrt X/(\log X)^2$ for all sufficiently large $X$. Its full Lee–Leong absolute moment diverges for every fixed $\delta>0$. There also exists a nonnegative $v\in V$ with $h(v;X)=0$ for all $X$ and all these moments divergent. Neither example is the actual correction or displacement.

**Proof.** Set $B=2^{17}$ and use Bertrand’s theorem to choose $B^j<p_j<2B^j$, $j\ge1$, so $R=2^{16}<p_{j+1}/p_j<2^{18}=S$. Put $a_j=\sqrt{p_j}/j^2$ and $u=\sum_{j\ge1}(-1)^j a_jg_{p_j}$. The repository proves $\|g_p\|_Q^2\le 2/[\zeta(2)p]$ (`RiemannResearch.RH.ZetaTwoHilbert.qResidue_norm_sq_le_two_div` in `QConductorCoefficientMass.lean`). Thus the series converges absolutely in $L^2(Q)$, its sum lies in $V$, and continuous coordinate evaluation gives the indicated pointwise series.

On $I_j=[p_j/2,3p_j/4]\cap\mathbb N$, the main term has magnitude at least $a_j/2$. Applying $g_{p_k}(n)\le1$ to the earlier terms bounds their sum by

$$a_j\sum_{h=1}^{j-1}R^{-h/2}\bigl(j/(j-h)\bigr)^2\le a_j\sum_{h\ge1}(4/256)^h=a_j/63,$$

since $j/(j-h)\le1+h\le2^h$. For later terms $g_{p_k}(n)=n/p_k$, so their sum of magnitudes is at most $a_j\sum_{h\ge1}R^{-h/2}=a_j/255$. Consequently $(-1)^j u(n)\ge a_j/4$ on $I_j$, whose sign-specific harmonic contribution is at least $a_j/32$ because $\#I_j\ge p_j/8$. At $p_j\le X<p_{j+1}$ use both $I_j$ and $I_{j-1}$: their signs differ, $p_{j-1}>X/S^2$, and $j\le\log X/\log B$. This proves the stated lower bounds (and even positive lower densities for both signs). Since $H_\delta(n)=o(\log n)$, eventually $e^{-H_\delta(n)}\ge n^{-1/8}$, and the weighted absolute contribution of $I_j$ is at least $p_j^{3/8}/(32j^2)$. Finally set $v=\sum_j a_jg_{p_j}$. It is nonnegative and retains the same lower bound from each $I_j$. Scaling the examples fits any prescribed positive norm bound.

## An unconditional analytic bound at common cutoffs for all resolvent depths

Write $Q(n)=1/[\zeta(2)n^2]$ for $n\ge1$ and let $\Pi$ project onto the closed span of the natural squarefree residue vectors. Put
$S(u;X)=\sum_{n=1}^X|u(n)|/n$, $u_m=\mathrm{resolventApprox}(m)$, and $b=\Pi B_0r_Q$, where $r_Q=1-\Pi 1$ and $(B_0 f)(n)=f(n)/(n+1)$. The centered iteration is $u_0=0$, $u_{m+1}=4b/3+Ru_m$, with $R=(4/3)\Pi(B_0-I/4)$; the spectrum of the diagonal $B_0$ is contained in $[0,1/2]$, so $\|R\|\le1/3$.
If $q=2^{-1/2}$, then
$$
 \sum_{j\ge0}\frac{[\sup_{m\ge0}S(u_m;2^j)]^2}{2^j}
 \le \frac{4\zeta(2)}{(1-q)^2}\|b\|_Q^2 .
$$
The supremum may additionally include the limiting displacement $d$. This is a mathematical deduction, separate from the server-checked statements.

Indeed $u_0=0$ and the increments are $u_{m+1}-u_m=R^m(4b/3)$, where $\|R\|\le1/3$. Define the nonnegative physical majorant $U(n)=\sum_{m\ge0}|(u_{m+1}-u_m)(n)|$. Minkowski for finite partial sums followed by monotone convergence gives $\|U\|_Q\le\sum_{m\ge0}(4/3)3^{-m}\|b\|_Q=2\|b\|_Q$. The majorant bounds every iterate and, by continuous coordinate evaluation, also its limit. For $I_0=\{1\}$ and $I_k=(2^{k-1},2^k]\cap\mathbb N$ ($k\ge1$), set $E_k^2=\sum_{n\in I_k}|U(n)|^2/n^2$. Then $\sum_k E_k^2=\zeta(2)\|U\|_Q^2$. Cauchy–Schwarz on each shell yields
$$
2^{-j/2} S(U;2^j)\le \sum_{k=0}^j q^{j-k}E_k.
$$
Squaring by weighted Cauchy–Schwarz and summing nonnegative terms bounds the squared $\ell^2$ norm of the right side by $(1-q)^{-2}\sum_k E_k^2$, as claimed.

Consequently there exist common dyadic cutoffs $X=2^j\to\infty$ along which
$$
\sup_{m\ge0}S(u_m;X)=o\!\left(\sqrt{\frac{X}{\log X\,\log\log X}}\right).
$$
Otherwise the summands in the displayed energy estimate would eventually dominate a positive multiple of $1/(j\log j)$, whose series diverges. The same argument permits any positive weight $w_j$ with $\sum_j1/w_j=\infty$, replacing the target at $X=2^j$ by $2^{j/2}/\sqrt{w_j}$. The little-oh is subsequential; no rate of locating the cutoffs is asserted. Even this simultaneous estimate is far above the open polylogarithmic criterion.

## Near-sharpness inside the squarefree closure

There is a vector $v$ in that same closed squarefree span such that the smaller of its two signed prefixes satisfies
$$
h(v;X):=\min_{\varepsilon=\pm1}\sum_{n\le X}\frac{(\varepsilon v(n))_+}{n}
\gg \frac{\sqrt X}{\sqrt{\log X}\,\log\log X}
$$
at **every** sufficiently large $X$. Here and throughout, harmonic sums begin at $n=1$. This example is not the actual projection correction $b$ or displacement $d$.

Let $g_p(n)=\{n/p\}$ and $e_p=\sqrt p\,g_p$. For every prime $p$, $g_p$ belongs to the squarefree span. For $p\le q$, split the positive inner product at $p,q$:
$$
\zeta(2)\langle e_p,e_q\rangle_Q
\le \sqrt{p/q}\,[2+\log(q/p)] .
$$
Before multiplying by $\sqrt{pq}$, the range $n\le p$ contributes at most $p/(pq)=1/q$; the middle range contributes at most $q^{-1}\sum_{p<n\le q}1/n\le\log(q/p)/q$; the last range at most $\sum_{n>q}n^{-2}\le 1/q$.

Take $B=2^{17}$. Bertrand’s postulate gives primes $B^j<p_j<2B^j$ for $j\ge1$, hence $R<p_{j+1}/p_j<S$ with $R=2^{16}$ and $S=2^{18}$. Thus the Gram entries of the scaled atoms $e_{p_j}$ are bounded in absolute value by the summable row kernel
$$
K_h=\zeta(2)^{-1}(2+|h|\log S)R^{-|h|/2},\qquad h\in\mathbb Z.
$$
For finitely supported coefficients, $2|c_jc_k|\le c_j^2+c_k^2$ shows that $\|\sum_j c_je_{p_j}\|_Q^2\le (\sum_hK_h)\sum_j|c_j|^2$. In particular the series
$$v=\sum_{j\ge1}(-1)^j a_j g_{p_j},\qquad a_j=\frac{\sqrt{p_j}}{\sqrt j\log(2j)},$$
converges in the closed squarefree span, since $\sum 1/[j\log^2(2j)]<\infty$. Continuity of each coordinate evaluation identifies its pointwise values with the displayed series.

On $I_j=[p_j/2,3p_j/4]\cap\mathbb N$ the main term has sign $(-1)^j$ and magnitude at least $a_j/2$. For $h\ge1$ with $j-h\ge1$, one has $j/(j-h)\le1+h$ and $\log(2j)/\log(2(j-h))\le1+h$, since $1+h\le2^h$. Hence
$$
a_{j-h}/a_j\le R^{-h/2}(1+h)^2\le (4/256)^h.
$$
Using $g_{p_k}\le1$, all earlier terms together therefore cost at most $a_j/63$. For $k=j+h>j$, $n\in I_j$ implies $g_{p_k}(n)=n/p_k$ and $a_k n/p_k\le a_j R^{-h/2}$. All later terms cost at most $a_j/255$. It follows that $(-1)^j v(n)\ge a_j/4$ on $I_j$. There are at least $p_j/8$ integers in this interval, so it contributes at least $a_j/32$ to that sign’s harmonic prefix.

For $p_j\le X<p_{j+1}$ both $I_j$ and $I_{j-1}$ have been included. Their signs are opposite, $p_{j-1}>X/S^2$, and $j\le\log X/\log B$. These inequalities give the stated lower bound for *both* signs. In particular legality and Hilbert energy cannot by themselves force even a cofinal $O(\sqrt X/(\log X)^{1/2+\varepsilon})$ bound for any fixed $\varepsilon>0$. A bound at the polylogarithmic scale must use additional properties of the actual projected source.

## Two ways to reduce the work per dyadic shell

**Paper deduction: truncate the source with an explicit error.** For the same squarefree projection $\Pi$ and any $f\in L^2(Q)$, put $u=\Pi B_0f$ and $u_M=\Pi B_0(\mathbf1_{m\le M}f)$. Since $B_0(m)=1/(m+1)$ and the first omitted site is $M+1$,

$$\|u-u_M\|_Q\le\|B_0(\mathbf1_{m>M} f)\|_Q\le\frac{\|\mathbf1_{m>M}f\|_Q}{M+2}\le\frac{\|f\|_Q}{M+2}.$$

Thus $|h(u;X)-h(u_M;X)|\le \sqrt{\zeta(2)X}\,\|f\|_Q/(M+2)$; this is $o(1)$, using the middle bound, when $M=\lceil\sqrt X\rceil$. Both $f=r_Q$ (giving the correction $b$) and $f=r_P$ (giving the displacement $d$) are available. The approximation truncates the projection's **input**; its output still has infinitely many physical coordinates.

On a dyadic block $I_j=[2^j,2^{j+1})$ choose $M_j=\lceil 2^{j/2}\rceil$. Eventual monotonicity of $H_\delta$ and Cauchy–Schwarz on $2^j$ sites show that replacing $u$ by $u_{M_j}$ changes the weighted absolute block moment by at most $\sqrt{\zeta(2)}\,\|f\|_Q e^{-H_\delta(2^j)}$. These errors are summable because $H_\delta(2^j)\gg j^{3/5}/(\log j)^{1/5}\gg \log j$. If $K(n,m)$ is the reproducing kernel of the legal space in the physical $Q$ coordinates, the new, still open target is therefore a weighted bound on the **specific** finite sums $u_{M_j}(n)=\sum_{m\le M_j}Q(m)K(n,m)f(m)/(m+1)$. The Hilbert estimate justifies discarding the remaining input sites, but does not supply that bound.

A smaller sufficient source cutoff follows by splitting the input into disjoint annuli. Write $c_j=2^{j/2}e^{-H_\delta(2^j)}$, $D_k=\sum_{j\le k} c_j$, and let $M_j$ be nondecreasing and tend to infinity. Splitting the omitted input into $F_k=\mathbf 1_{M_k<m\le M_{k+1}}f$ and interchanging nonnegative sums bounds the total block error by

$$\sqrt{\zeta(2)}\sum_k\frac{D_k}{M_k+2}\|F_k\|_Q\le\sqrt{\zeta(2)}\left(\sum_k(D_k/(M_k+2))^2\right)^{1/2}\|f\|_Q.$$

In particular $M_k=\lceil D_k\sqrt{k+2}\,\log(k+2)\rceil$ suffices. For the printed profile $H_\delta(2^{k+1})-H_\delta(2^k)=o(1)$ by differentiation, so $c_{k+1}/c_k\to\sqrt2$ and $D_k=O(c_k)$. Thus the cutoff can be taken of order $2^{k/2}e^{-H_\delta(2^k)}\sqrt{k}\log k$, substantially below the simpler square-root cutoff. This controls the error only; it places no corresponding bound on the retained finite kernel sum.

**An explicit iteration budget for the full weight (analytic refinement).**
Write $d_m$ for the exact centered resolvent at depth $m$, $I_j=[2^j,2^{j+1})$, $H_j=H_\delta(2^j)$, and
$w(n)=\zeta(2)^{-1}e^{-H_\delta(n)}$. For any depth schedule $m_j$ and all sufficiently large $j$, the error in the weighted absolute mass of $I_j$ is bounded by
$$
\begin{aligned}
\left|\sum_{n\in I_j}w(n)\frac{|d(n)|-|d_{m_j}(n)|}{n}\right|
&\le \frac{\|d\|_Q}{\sqrt{\zeta(2)}}e^{-H_j}2^{j/2}3^{-m_j}.
\end{aligned}
$$
Indeed $w$ is eventually decreasing, finite Cauchy–Schwarz contributes $\sqrt{\zeta(2)2^j}$, and the Hilbert error is at most $3^{-m_j}\|d\|_Q$. The checked depth-$j$ theorem does not need damping to make its error summable: its ratio is $\sqrt2/3<1$.

At the actual full weight one can reduce the depth below $j\log2/(2\log3)$. For any $s>1$, eventually it suffices to use
$$
 m_j=\max\!\left(0,\left\lceil
 \frac{j\log2/2-H_j+s\log(j+1)}{\log3}\right\rceil\right).
$$
Direct substitution gives a summable error $O((j+1)^{-s})$. For example, $s=2$ saves essentially $H_j/\log3$ iterations relative to the undamped threshold. This is a sufficient schedule; no optimality is asserted. The coefficient of $j$ is about $0.31546$. The subtracted profile term is of order $j^{3/5}(\log j)^{-1/5}$, so the depth still tends to infinity. One concrete open arithmetic estimate is
$$
 e^{-H_j}\sum_{n\in I_j}\frac{|d_{m_j}(n)|}{n}\ \le\ b_j,\qquad \sum_j b_j<\infty .
$$
No norm argument here proves this bound. Each finite depth still uses the exact infinite-dimensional legal projection.

**Sharper schedule with simultaneous energy.** Since $4\sum_m9^m\|d-d_m\|_Q^2\le\|r\|_Q^2$ holds, Cauchy–Schwarz across all output sites replaces the $\ell^1$ error budget above by an $\ell^2$ budget. Let $m(n)=m_j$ on $I_j$. The first factor in Cauchy–Schwarz is the square sum of $e^{-H_\delta(n)}3^{-m(n)}$; for the other factor group sites by their common depth:
$$
\sum_n\frac{9^{m(n)}|(d-d_{m(n)})(n)|^2}{n^2}
\le \zeta(2)\sum_m9^m\|d-d_m\|_Q^2.
$$
This argument allows arbitrarily repeated depths. Omitting finitely many initial shells, the total substitution error is at most
$$
\frac{\|r\|_Q}{2\sqrt{\zeta(2)}}
\left(\sum_j 2^j e^{-2H_j}9^{-m_j}\right)^{1/2}.
$$
So the same displayed schedule works for every $s>1/2$. At the logarithmic endpoint one may instead add $\frac12\log(j+1)+t\log\log(j+3)$ in the numerator, $t>1/2$. Only the error of replacing $d$ is estimated.

## Research agenda and proof obligations

1. **Bound the cheaper sign of the finite first correction.** Solve the two finite $Q$ projection equations defining $b_M$, retain the signed cross terms, and seek the same $C,B_1$ along unbounded physical cutoffs and arbitrarily large conductor stages at each cutoff. The constant threshold $1$ is an equivalent option. The forward harmonic proof has no external number-theoretic hypothesis.
2. **Measure the finite weighted cost.** Use the translated weight $G(n)/n$ with the exact physical masses of $b_M$. The older positive-margin tests also suffice. On a fixed head $K$, check whether the bound survives as $M$ increases. Aim for one common bound over all $K$. The coefficient cost $K_\delta(m)$ gives a sufficient comparison and an explicit way to price high conductors. If absolute values of coefficients cost too much, retain cancellation inside each physical value before taking its absolute value.
3. **Distinguish the two limiting problems.** For a conductor diagonal, either prove a uniformly bounded weighted partial moment directly or bound its deviation from the limiting moment. For iteration depth, the square-energy theorem controls that latter error across the disjoint shells. It supplies no conductor-convergence rate for the finite Gram systems.
4. **Close the arithmetic input in Lean.** For the exact printed weight or an additional positive reserve, supply the Proposition 5.2 specialization `LeeLeongImplicitTruncation`. For the translated weight, supply Theorem 1.1.  The full-weight implication takes `LeeLeongMertensEstimate` explicitly. Theorem 1.1(12) supplies the published mathematical result. A checked provider with its stated constants, prefactor and valid range completes the external input. Under RH, Báez-Duarte supplies the separate converse. Neither literature result bounds the actual correction without a further argument.

The uniform estimates in items 1 and 2 remain open. The finite experiments and lacunary counterexamples are independent mathematical or computational checks; the Lean modules formalize the projection estimates, finite-stage tests, and RH transfers listed in the [catalog](THEOREM_CATALOG_MERTENS_DISPLACEMENT_20261105.md).
