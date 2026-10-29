# Exact-head repair, conductor growth, and a failed H=320 lift

Research memorandum, 29 October 2026.

The target is a finite signed squarefree residue combination F_H with F_H(n)=1 for every 1<=n<=H and complete Q energy at most 1+5/(8H), for H=5*4^j. This investigation does not establish that all-stage provider.

The paper proves an explicit repair operator and an asymptotic obstruction to polynomial conductor cutoffs. It also checks a specific attempted lift from the published H=80 witness to H=320 and shows that this lift fails. The obstruction concerns the largest individual conductor, not the CRT period.

## Mathematical and verification status

- The exact signed repair, its complete error identity, and its norm estimate using the actual finite operator norm are formalized in `QSquarefreeQuantitativeRepair.lean`. The input accuracy is an explicit hypothesis; no input-existence theorem is asserted.
- The explicit polynomial amplification estimate 15 H^(3/2), and its sufficient input accuracy 1/(60 H^(5/2)), are paper proofs below. This polynomial estimate is not claimed as a Lean declaration.
- `QExactHeadConductorBarrier.lean` formalizes the exact Q-to-Pareto error transfer, the complete error upper estimate, and the conductor-growth implication. Its Burnol lower-envelope hypothesis is explicit and is not supplied by the Lean module.
- Burnol's published theorem supplies that analytic lower bound for the paper argument. Thus the paper rules out fixed-polynomial conductor growth; the Lean conclusion retains that external analytic input as a hypothesis.
- The two H=320 energy lower certificates are independently executed Python integer checks. They are not Lean numerical theorems. The script verifies every prefix value by recurrence and direct summation.
- The original actual-vector H=80 certificate is still separate. This work does not certify its 126 coefficients or long energy prefix in Lean. No general H=320 witness, all-stage provider, uniform cofinal energy bound, or RH proof is claimed.

## A. Constructive repair and the attempted next stage

### Statement

Write

\[
 Z=\zeta(2)=\sum_{n\ge1}n^{-2},\qquad
 r_d(n)=\frac{n\bmod d}{d},\qquad
 \|f\|_Q^2=\frac1Z\sum_{n\ge1}\frac{|f(n)|^2}{n^2}.
\]

Let \(a_d\in\mathbb R\) be finitely supported on squarefree integers \(d\ge2\), and let \(f=\sum a_dr_d\). Missing coefficients are zero. Let \(H\ge2\) be an integer, and choose a prime \(p>H\). No normalization or exact-head assumption is imposed on \(f\).

Set

\[
 s=\sum_{d\ge2}\frac{a_d}{d}=f(1),\qquad
 \delta_d=-\mu(d)-a_d\quad(2\le d\le H),
\]

\[
 \eta=1-s-\sum_{2\le d\le H}\frac{\delta_d}{d},\qquad
 R_Hf=f+\sum_{2\le d\le H}\delta_dr_d+p\eta r_p.
\]

Then \(R_Hf\) is a finite squarefree residue combination and

\[
 R_Hf(n)=1\qquad(1\le n\le H).
\]

It also satisfies the complete infinite-norm estimate

\[
 \boxed{\quad
 \|R_Hf-1\|_Q
 \le \left[1+2\sqrt2 Z H^{3/2}
       +\sqrt{2p}(1+2ZH)\right]\|f-1\|_Q.
 \quad}
\tag{1}
\]

By Bertrand's postulate we may choose \(H<p<2H\), giving the convenient bound

\[
 \boxed{\|R_Hf-1\|_Q\le15H^{3/2}\|f-1\|_Q.}
\tag{2}
\]

Consequently, a raw squarefree approximant satisfying

\[
 \|f-1\|_Q\le\frac1{60H^{5/2}}
\tag{3}
\]

produces an exact-head witness with

\[
 \|R_Hf\|_Q^2\le1+\frac5{8H}.
\tag{4}
\]

All sums defining the operator retain their signs. None of these estimates discards energy beyond a finite cutoff.

Primality of \(p\) is stronger than needed: the proof only needs a squarefree correction conductor \(D>H\), with \(p\) replaced by \(D\) in (1). For an even dyadic head \(H\ge20\), choose a prime \(H/2<q<H\) and put \(D=2q\). Then \(H<D<2H\), \(D\) is squarefree, and every prime factor of the correction conductor is below \(H\). Thus this repair itself need not enlarge the prime set beyond the primes below the head. The difficulty of finding a sufficiently accurate raw input within that fixed prime set remains separate.

### Proof of exact-head repair

If \(d\) is nonsquarefree, both \(\mu(d)\) and \(a_d\) vanish, so \(\delta_d=0\). The new conductor \(p\) is prime. Thus squarefree support is preserved. The coefficients after repair equal \(-\mu(d)\) for \(2\le d\le H\), because \(p>H\), and their weighted sum is exactly one by the definition of \(\eta\).

For \(1\le n\le H\), use \(r_d(n)=n/d-\lfloor n/d\rfloor\). Terms with \(d>n\) have zero floor. Therefore

\[
 R_Hf(n)=n+\sum_{2\le d\le n}\mu(d)\lfloor n/d\rfloor
 =\sum_{d\le n}\mu(d)\lfloor n/d\rfloor=1.
\]

The last equality follows by rearranging the finite sum as
\(\sum_{m\le n}\sum_{d\mid m}\mu(d)\), whose sole nonzero term is \(m=1\).

### Coefficient recovery and its quantitative bound

Put \(\varepsilon=\|f-1\|_Q\), define \(e(0)=0\), and set \(e(n)=f(n)-1\) for \(n\ge1\). Evaluation in the weighted norm gives

\[
 |e(n)|\le\sqrt Z\,n\varepsilon\qquad(n\ge1).
\tag{5}
\]

Let \(f(0)=0\). For each positive integer \(n\),

\[
 f(n)-f(n-1)=s-\sum_{\substack{d\mid n\\d\ge2}}a_d.
\tag{6}
\]

For \(n\ge2\), finite divisor inversion applied to (6) yields

\[
 a_n=-\sum_{k\mid n}\mu(n/k)\bigl(f(k)-f(k-1)\bigr).
\]

Subtract the corresponding coefficients \(-\mu(n)\) of the head target. Since the target step sequence is zero at zero and one at every positive integer, its difference is one at \(k=1\) and zero otherwise. Hence

\[
 \delta_n=\sum_{k\mid n}\mu(n/k)\bigl(e(k)-e(k-1)\bigr).
\tag{7}
\]

Using \(|\mu|\le1\) and (5),

\[
 |\delta_n|\le2\sqrt Z\,\sigma_1(n)\varepsilon,
 \qquad \sigma_1(n)=\sum_{k\mid n}k.
\tag{8}
\]

Two elementary finite divisor sums satisfy

\[
 \sum_{n\le H}\frac{\sigma_1(n)}n
 =\sum_{km\le H}\frac1m
 \le H\sum_{m\le H}\frac1{m^2}\le ZH,
\tag{9}
\]

\[
 \sum_{n\le H}\frac{\sigma_1(n)}{\sqrt n}
 =\sum_{km\le H}\frac{\sqrt k}{\sqrt m}
 \le H^{3/2}\sum_{m\le H}\frac1{m^2}
 \le ZH^{3/2}.
\tag{10}
\]

For (10), bound the number of eligible \(k\)'s by \(H/m\) and every \(\sqrt k\) by \(\sqrt{H/m}\).

Since \(s-1=e(1)\), (8)--(9) give

\[
 |\eta|\le\sqrt Z\,(1+2ZH)\varepsilon.
\tag{11}
\]

### Full norm of a residue atom

For every integer \(d\ge2\),

\[
 Z\|r_d\|_Q^2
 \le\frac{d-1}{d^2}+\sum_{n>d}\frac1{n^2}
 \le\frac{d-1}{d^2}+\frac1d
 <\frac2d.
\tag{12}
\]

Here \(r_d(n)=n/d\) for \(1\le n<d\), \(r_d(d)=0\), and \(|r_d(n)|\le1\) afterwards. The infinite tail is bounded by the telescoping series
\(\sum_{n>d}1/[n(n-1)]=1/d\).
Thus \(\|r_d\|_Q\le\sqrt{2/(Zd)}\).

The triangle inequality, (8), (10), (11), and (12) now give

\[
 \begin{aligned}
 \|R_Hf-1\|_Q
 &\le\varepsilon+\sum_{2\le d\le H}|\delta_d|\|r_d\|_Q
          +p|\eta|\|r_p\|_Q\\
 &\le\bigl[1+2\sqrt2 ZH^{3/2}
          +\sqrt{2p}(1+2ZH)\bigr]\varepsilon.
 \end{aligned}
\]

This proves (1). If \(p\le2H\), its bracket is at most
\(1+(2\sqrt2+4)ZH^{3/2}+2\sqrt H\).
Use \(\sqrt2<3/2\), \(Z<5/3\), and \(H\ge1\) to bound this by
\((1+35/3+2)H^{3/2}=(44/3)H^{3/2}<15H^{3/2}\).
For an elementary check of \(Z<5/3\), sum the first five terms and telescope the remaining tail:
\(Z\le5269/3600+1/5=5989/3600<5/3\).

### The energy consequence

Under (3), (2) gives \(\|R_Hf-1\|_Q\le1/(4H)\). Since \(\|1\|_Q=1\),

\[
 \|R_Hf\|_Q^2
 \le\left(1+\frac1{4H}\right)^2
 =1+\frac1{2H}+\frac1{16H^2}
 \le1+\frac5{8H}.
\]

The final inequality holds already for \(H\ge1\). In fact the displayed estimate is at most \(1+9/(16H)\).

### A coarser bound with only integer powers

For a simpler formalization, (7), \(\sqrt Z<2\), and \(\sigma_1(d)\le d^2\) imply \(|\delta_d|\le4d^2\varepsilon\). Use \(\|r_d\|_Q\le1\), \(\sum_{d\le H}d^2\le H^3\), and \(\sum_{d\le H}d\le H^2\). Then

\[
 |\eta|\le(2+4H^2)\varepsilon,
\]

and, with \(p\le2H\),

\[
 \|R_Hf-1\|_Q\le(1+4H^3+4H+8H^3)\varepsilon
 \le17H^3\varepsilon.
\]

Thus the entirely rational input tolerance \(\varepsilon\le1/(68H^4)\) also suffices for (4).

### What this does and does not construct

This is an explicit rule transforming a sufficiently accurate raw squarefree approximation into an exact-head witness. If raw finite squarefree approximants converge to one in the Q norm, choose one within (3) for each dyadic \(H=5\cdot4^k\), then apply the rule. Every resulting finite squarefree support divides a sufficiently large primorial, so it is legal for an existential cofinal-stage provider. This argument does not put the support inside the particular primorial through \(H\); it allows the stage to grow as needed.

Under RH, a classical conditional source of raw approximants is Báez-Duarte's damped Möbius family. His paper proves convergence in the continuous Nyman--Beurling Hilbert space for coefficients of the form \(-\mu(d)d^{-c/\log\log N}\), with a norm error of order \((\log\log N)^{-1/3}\). These coefficients have squarefree support. See Luis Báez-Duarte, *A strengthening of the Nyman--Beurling criterion for the Riemann hypothesis, 2*, arXiv:math/0205003, abstract and Theorem 1.1: https://arxiv.org/pdf/math/0205003 . This citation supports the conditional approximation input, not the elementary repair proof above.

Here is the elementary bridge for that input. Write
\(g(t)=\sum_{d\ge2}a_d\{t/d\}-\{t\}\), \(b=s-1\), and use the continuous norm with measure \(dt/t^2\). For \(n\le t<n+1\),
\(g(t)=f(n)+b(t-n)\); for \(0<t<1\), \(g(t)=bt\).
Integrating \(|1-f(n)|^2\le2|1-g(t)|^2+2b^2\) over each unit interval, and using \(1/n^2\le2/[n(n+1)]\), gives

\[
 \sum_{n\ge1}\frac{|1-f(n)|^2}{n^2}
 \le4\int_1^\infty\frac{|1-g(t)|^2}{t^2}\,dt+4b^2
 =4\|\mathbf1_{[1,\infty)}-g\|_{L^2(dt/t^2)}^2.
\]

Thus continuous convergence implies Q convergence. Combining its stated conditional rate with (2) gives a possible sufficient support scale \(\log\log N\gg H^{15/2}\), with constants inherited from that conditional theorem. This very large scale is a sufficient bound from crude repairs, not a necessity or an efficient prescription.

The missing unconditional statement is precisely that one can supply such accurate raw approximants. Assuming it merely moves the difficult RH-related convergence claim into the input. The H=80 finite certificate supplies one successful finite energy witness; it supplies neither the required convergence nor quantitative input tolerances for arbitrarily large H.

### Direct H=80 to H=320 repair: a failed concrete test

Apply this operator to the published H=80 witness, choose the new head H=320 and the prime p=331. All original conductors are at most 300, so the operator overwrites every original coefficient. The resulting coefficients are

\[
 c_d=-\mu(d)\ (2\le d\le320),\qquad
 c_{331}=331\sum_{d\le320}\frac{\mu(d)}d,
\]

with every other coefficient zero. These satisfy the exact-head equations but fail the target energy inequality. An exact integer check in the checker in `ExactHeadRepair320Check20261029.md` bounds the raw energy prefix through 2048 below by

\[
 \sum_{n=1}^{2048}\frac{F(n)^2}{n^2}
 \ge\frac{104700971949}{62500000000}.
\]

This is a downward-rounded bound with scale \(10^{12}\), obtained by summing individual integer floors. Since \(Z<5/3\) and all omitted energy terms are nonnegative, the complete Q energy satisfies

\[
 E_Q>\frac{314102915847}{312500000000}
 =\frac{513}{512}+\frac{1985128569}{625000000000}
 >\frac{513}{512}.
\]

The script checks every exact-head equation and every prefix value by both an integer recurrence and direct summation. This is an externally checked arithmetic certificate, not a Lean verification. It rules out this specified direct repair (p=331) only; it does not rule out the H=320 stage or other tail choices.

The same failure occurs with the squarefree correction conductor \(D=326=2\cdot163\), which already divides the primorial through 317. The exact downward-rounded raw prefix through 2048 is at least \(1675647282981/10^{12}\). Consequently

\[
 E_Q>\frac{5026941848943}{5000000000000}
 =\frac{513}{512}+\frac{17176223943}{5000000000000}.
\]

This version keeps the correction inside the expected prime set for H=320; its failure is not caused by introducing the prime 331.


## B. Necessary growth of the largest conductor

### Statement

Let \(H_j\to\infty\) be positive integers; the intended schedule is \(H_j=5\cdot4^j\). For each \(j\), take a finitely supported real coefficient family \((c_{j,d})_{d\ge2}\), and write

\[
F_j(n)=\sum_{d\ge2}c_{j,d}\frac{n\bmod d}{d},\qquad
E_j=\frac1{\zeta(2)}\sum_{n\ge1}\frac{F_j(n)^2}{n^2}.
\]

Assume

\[
F_j(n)=1\quad(1\le n\le H_j),\qquad
E_j\le1+\frac a{H_j},\qquad a\ge0.
\tag{1}
\]

Let \(N_j=\max\{d:c_{j,d}\ne0\}\) be the **largest individual conductor**, not their least common multiple. Then

\[
\liminf_{j\to\infty}\frac{\log N_j}{H_j}
\ge \frac{C_*}{(1+\sqrt{1+a\zeta(2)})^2}>0,
\tag{2}
\]

where

\[
C_*:=\sum_{\substack{\rho\text{ distinct}\\\Re\rho=1/2}}
\frac{m(\rho)^2}{|\rho|^2}
\]

is Burnol's positive constant. One can instead use any positive constant furnished by a finite set of critical-line zeros, which avoids any question about an infinite value of the sum. If the sum is infinite, (2) is interpreted by applying the result to every finite subsum. The elementary weaker version is

\[
\liminf_j\frac{\log N_j}{H_j}\ge
\frac{C_*}{4+2a\zeta(2)}.
\tag{3}
\]

Thus a family satisfying (1) cannot have \(\log N_j=o(H_j)\). In particular it cannot use \(N_j\le H_j^k\) for any fixed \(k\), or \(N_j\le C H_j\) for fixed \(C\). The conclusion applies to arbitrary signed coefficients; imposing squarefree support only restricts the admissible family further.

For the requested \(a=5/8\), the denominator in (2) is approximately \(5.8762999295\); that in (3) is approximately \(6.0561675836\). These decimal values are explanatory, not certificate inputs. Do not substitute \(2+\gamma-\log(4\pi)\) for \(C_*\) without the corresponding RH and simplicity qualifications. No explicit finite threshold for \(H\) is supplied by this asymptotic argument.

### 1. Exact slope and interpolation

Fix a family and suppress \(j\). Every conductor satisfies \(d\ge2\). Since \(1\bmod d=1\), exactness at \(n=1\) gives

\[
\sum_{d\ge2}\frac{c_d}{d}=1.
\tag{4}
\]

For \(x\ge0\), write \(x=n+u\), where \(n=\lfloor x\rfloor\) and \(0\le u<1\). Because \(0\le n\bmod d\le d-1\),

\[
\left\{\frac{x}{d}\right\}
=\frac{n\bmod d+u}{d}.
\]

Consequently (4) gives the exact identity

\[
\sum_{d\ge2}c_d\left\{\frac{x}{d}\right\}-\{x\}
=F(n)+u\sum_{d\ge2}\frac{c_d}{d}-u
=F(\lfloor x\rfloor).
\tag{5}
\]

In particular the left side is zero for \(0\le x<1\). No approximation or truncation is used here.

Define on \((0,\infty)\)

\[
g(t)=\sum_{d\ge2}c_d\left\{\frac1{dt}\right\}
-\left\{\frac1t\right\},\qquad
\chi(t)=\mathbf1_{(0,1]}(t).
\]

All summands belong to \(L^2((0,\infty),dt)\): they are bounded near zero and are \(1/(dt)\) for large \(t\). Moreover \(g(t)=0\) for \(t>1\). For \(1/(n+1)<t\le1/n\), formula (5) gives \(g(t)=F(n)\), apart from irrelevant endpoint conventions. Therefore

\[
\|\chi-g\|_{L^2}^2
=\sum_{n\ge1}(F(n)-1)^2
\left(\frac1n-\frac1{n+1}\right)
=\sum_{n\ge1}\frac{(F(n)-1)^2}{n(n+1)}.
\tag{6}
\]

Finite support makes \(F\) bounded, so every series in this note converges absolutely. Exactness through \(H\) makes the error vanish for \(t>1/(H+1)\), up to endpoints, and makes all summands with \(n\le H\) in (6) zero.

### 2. Complete energy controls the complete approximation error

Set

\[
T=\sum_{n>H}\frac1{n^2},\qquad
A=\sum_{n>H}\frac{F(n)^2}{n^2}.
\]

The exact head and the definition of \(E\) yield

\[
A-T=\zeta(2)(E-1).
\tag{7}
\]

The integral estimate gives \(T\le1/H\). Hence (1) implies

\[
0\le A\le T+\frac{a\zeta(2)}H
\le\frac{1+a\zeta(2)}H.
\tag{8}
\]

Keeping the signed mixed term, put

\[
M=\sum_{n>H}\frac{F(n)}{n^2}.
\]

Cauchy–Schwarz gives \(|M|\le\sqrt{AT}\). It follows from (6) that

\[
\begin{aligned}
\|\chi-g\|_{L^2}^2
&\le\sum_{n>H}\frac{(F(n)-1)^2}{n^2}\\
&=A+T-2M\\
&\le(\sqrt A+\sqrt T)^2\\
&\le\frac{(1+\sqrt{1+a\zeta(2)})^2}{H}.
\end{aligned}
\tag{9}
\]

The easier algebraic alternative uses \((F-1)^2\le2F^2+2\), obtaining

\[
\|\chi-g\|_{L^2}^2\le2A+2T
\le\frac{4+2a\zeta(2)}H.
\tag{10}
\]

These are complete infinite error estimates. In particular, they do not identify the energy excess with the error squared and do not discard any mixed contribution with an unjustified sign.

### 3. The conductor cutoff enters through a classical lower bound

For \(0<\lambda<1\), let

\[
B_\lambda=\operatorname{span}\left\{
t\mapsto\{\theta/t\}:\lambda\le\theta\le1
\right\}\subset L^2((0,\infty),dt),
\qquad
D(\lambda)=\inf_{b\in B_\lambda}\|\chi-b\|_{L^2}.
\]

If all the nonzero \(c_d\) have \(d\le N\), every \(\theta=1/d\) and the additional \(\theta=1\) in \(g\) lie in \([1/N,1]\). Thus \(g\in B_{1/N}\), and (9) implies

\[
D(1/N)^2\le\frac{C_a}{H},\qquad
C_a=(1+\sqrt{1+a\zeta(2)})^2.
\tag{11}
\]

Burnol's theorem states

\[
\liminf_{N\to\infty}D(1/N)^2\log N\ge C_*.
\tag{12}
\]

The paper states its theorem for arbitrary real \(\lambda\downarrow0\), so the integer subsequence used here is allowed. Burnol explains that if RH fails the left side is infinite; the positive critical-line lower bound used here is unconditional. Bettin–Conrey–Farmer give the critical-line formulation explicitly.

We also verify that \(N_j\to\infty\), rather than assume it. The elementary jump identity is

\[
F(n)-F(n-1)
=\sum_{d\ge2}\frac{c_d}{d}
-\sum_{\substack{d\mid n\\d\ge2}}c_d.
\tag{13}
\]

At a prime \(p\le H\), exactness gives a zero jump (for \(p\ge2\)), so (4) and (13) imply \(c_p=1\). Hence \(N\) is at least the largest prime at most \(H\). The unboundedness of primes implies \(N_j\to\infty\).

Now multiply (11) by \(\log N_j\ge0\) and take lower limits:

\[
C_a\liminf_j\frac{\log N_j}{H_j}
\ge\liminf_jD(1/N_j)^2\log N_j
\ge C_*.
\]

This is (2). Replacing (9) by (10) proves (3).

### 4. Exactly what this rules out

- A pattern that always uses only conductors \(d\le CH\), or \(d\le H^k\) for a fixed \(k\), cannot satisfy the proposed complete-energy target for an unbounded sequence of heads. Changing coefficient signs, imposing squarefreeness, or optimizing the coefficients cannot remove this asymptotic obstruction.
- The largest conductor \(N\) is not the CRT period \(L=\operatorname{lcm}\{d:c_d\ne0\}\). A dictionary with \(d\le300\) can have an enormous period; Burnol's lower bound still sees \(N=300\).
- A prime cutoff is also different: allowing every squarefree conductor built from primes at most \(H\) permits conductors as large as the primorial through \(H\), on an exponential scale. Such a dictionary is not excluded by the argument.
- The obstruction is asymptotic. It neither invalidates the actual \(H=80,N=300\) certificate nor proves that a particular \(H=320\) dictionary fails.
- It does not disprove the requested all-stage provider with unrestricted finite conductor sets. It identifies a necessary scale for a viable construction.
- A constant pointwise bound \(|F_j(n)|\le B\), uniform in both \(j\) and \(n\), would similarly give \(\|\chi-g_j\|^2\le(B+1)^2/H_j\). It would therefore require exponentially growing conductors and would already yield Nyman–Beurling convergence. The externally proved bound 20 for the single \(H=80\) witness supplies no such uniform family.

### References and attribution

1. Jean-François Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, Advances in Mathematics 170 (2002), 56–70; arXiv:math/0103058, Theorem 1.3, with the spaces defined before Theorem 1.1. This supplies the asymptotic lower bound (12), not a proof of the proposed upper bound. <https://arxiv.org/pdf/math/0103058>
2. S. Bettin, J. B. Conrey, and D. W. Farmer, *An optimal choice of Dirichlet polynomials for the Nyman–Beurling criterion*, arXiv:1211.5191, introduction, pp. 1–2. This gives the critical-line formulation of Burnol's bound and explains the RH/simplicity qualifications for the numerical constant. <https://arxiv.org/pdf/1211.5191>

The interpolation identities and their application to the exact-head energy target are derived explicitly above. No originality claim is made.


## C. Precise remaining obligation and formal declarations

For the requested dyadic heads, the paper repair reduces the upper-bound problem to supplying a finite squarefree f_H with complete Q error at most 1/(60 H^(5/2)). Conversely, any all-stage exact-head energy family gives complete error tending to zero by Section B. Thus the repair does not remove the approximation problem; it isolates it. Together with the classical damped Mobius approximation under RH and the Nyman--Beurling converse, this is an RH-equivalent existence problem at the paper level. No unconditional input provider is proved here.

The formal repair uses the explicitly defined finite continuous linear operator T=repairOperator H p. Its certified sufficient input tolerance is 1/(4 H (1+norm(T))); the polynomial upper bound on norm(T) remains paper-level. The definition of T preserves the actual signed Mobius coefficients and the slope correction, and uses complete Q norms.

Declarations in namespace RiemannResearch.RH.QSquarefreeQuantitativeRepair:

- coefficient_eq_charge, repairOperator_apply, repairOperator_eq_interpolant: literal arithmetic formula and identification with the existing head interpolant.
- repaired_exact_head, repaired_legal: exact physical head and squarefree legality, including composite squarefree correction conductors.
- repaired_error_identity: complete signed error equality, including the mixed term and norm-square remainder.
- repaired_error_le, repaired_energy_of_accuracy: actual finite operator norm bound and the resulting 1+5/(8H) energy inequality, conditional only on the displayed input-accuracy hypothesis.

Declarations in namespace RiemannResearch.RH.QExactHeadConductorBarrier:

- finite_error_transfer_identity: exact complete Q-to-Pareto equality, including the positive metric correction.
- scaled_error_le_of_head_energy: zetaTwo times complete Q error squared is at most ((5/4)*zetaTwo+4)/H.
- finite_error_lower_transfer, log_conductor_lower: the external ContinuousCutoffLowerBound transfers to the actual signed finite vector and forces a logarithmic conductor cost.
- no_subexponential_family: conditional research reduction excluding log(N_j)/H_j tending to zero. Its assumptions include the external lower envelope, N_j tending to infinity, positive heads, support bounded by N_j, exact heads, and the energy budgets. Section B proves N_j tending to infinity for the actual all-stage setup; that implication is not included in this Lean declaration.

Isolated Lean verification succeeded for the barrier module in job job_6msTMDjdozcOdefnv4zSQd99WSo_NEaN (server verification time 39.266 seconds) and for the repair module in job job_S5w0x2XrfKR5K1TsGf3UTkg6CLcXsgaR (6.926 seconds). The printed main declaration dependencies were only propext, Classical.choice, and Quot.sound. The Burnol hypothesis and input-accuracy hypotheses are in theorem types and are not discharged by an axiom listing. Final project publication is performed through a separate checkpoint, whose terminal result is reported with the published commit.

The workspace resumed the existing token rather than making a new clone. Its opening round-trip time was not separately instrumented. Server execution durations above are not measurements of pure kernel-checking time; they include the server's verification workflow. Accepted-job queue delays were negligible, and polling latency is separate from execution.
