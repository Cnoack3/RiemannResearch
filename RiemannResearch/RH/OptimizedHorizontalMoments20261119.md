# Explicit horizontal moments from Conrey's shifted mollified mean square

Let $N(T)$ count the nontrivial zeros with $0<\gamma\le T$, including their analytic multiplicities. Give each copy mass $1/N(T)$, and set
\[
 X_T=(\log T)|\beta-1/2|,\qquad S_T(u)=\mathbb E_T[(X_T-u)_+].
\]
For each fixed $u>0$, Conrey's Gaussian shifted mean square gives the bound
\[
 \limsup_{T\to\infty} S_T(u)\le
 F(u):=\log\frac{1-e^{-22u/7}}{1-e^{-8u/7}}. \tag{1}
\]
The value at zero extends continuously to $F(0)=\log(11/4)$. The profile concerns a fixed scaled threshold after taking a limit in height. The usual finite-height Selberg density input still has the strict range $a<8/7$.

## Gaussian moment and its passage to a dyadic interval

Fix $0<\theta<4/7$, a real polynomial $P(0)=0,P(1)=1$, and a dyadic base $H$. Put $L_H=\log H$, $y=H^\theta$, and
\[
 B_H(s)=\sum_{n\le y}\mu(n)n^{-s}P(1-\log n/\log y).
\]
For $v$ in a fixed bounded real interval and $H\le w\le2H$, the Proposition of Conrey's §5 with both shifts $v/L_H$ and both polynomials $P$ gives
\[
 G_H(w)=\frac{1}{\sqrt\pi\Delta}\int_{\mathbb R}e^{-(t-w)^2/\Delta^2}
 |\zeta(1/2+v/L_H+it)B_H(1/2+it)|^2\,dt
 =m_P(v,\theta)+o(1),
\]
uniformly in $w,v$, with $\Delta=H^{1-\eta}$ for fixed sufficiently small $\eta>0$ depending on $\theta$. Differentiating his displayed main term in the two polynomial translations gives
\[
 m_P(v,\theta)=1+\frac{1-e^{-2v}}{2v\theta}
       \int_0^1 (P'(x)-v\theta P(x))^2\,dx . \tag{2}
\]
Theorem 2's proof on the same page explicitly invokes the passage from a uniform Gaussian mean to an unweighted mean. For the upper bound in (1), positivity controls the two edges of the interval. Write $I=[H,2H]$, $d=\Delta\log H=o(H)$, and $f(t)$ for the nonnegative squared modulus above. For $t\in[H+d,2H-d]$, the Gaussian mass over centers $w\in I$ is $1-o(1)$. Positivity and Fubini bound the integral of $f$ over this interior by $(1+o(1))\int_I G_H(w)\,dw$. For $t\in[H,H+d]$, its Gaussian mass over $w\in[H,H+2d]$ is at least a fixed positive constant. Thus the left edge contributes $O(d\sup_I G_H)=o(H)$. The right edge obeys the same bound. This proves
\[
 \int_H^{2H} f(t)\,dt \le H(m_P(v,\theta)+o(1))
\]
uniformly for bounded $v$. [Conrey, J. reine angew. Math. 399 (1989), §5, Proposition and (50), pp. 11–12](https://doi.org/10.1515/crll.1989.399.1) · [published scan at Durham](https://maths.dur.ac.uk/users/herbert.gangl/morethan2_5.PDF)

## Littlewood's rectangle and a common final-height normalization

On the block $H<\gamma\le2H$, let $\sigma=1/2+v/L_H$ and use the analytic function $Z_H(s)=\zeta(s)B_H(s-v/L_H)$. Reflection is used only after estimating the right-sided sum. Jensen's inequality gives
\[
 \int_H^{2H}\log|Z_H(\sigma+it)|\,dt
 \le \tfrac{H}{2}\log m_P(v,\theta)+o(H).
\]
On the right edge, $Z_H(2+it)=1+O(1/L_H)$ uniformly. To see this, compare $B_H(2-v/L_H+it)$ to the absolutely convergent series for $1/\zeta(2+it)$. For $n\le y$, the coefficient discrepancy is $O_{P,\theta,v}((\log n)/L_H)$, by $P(1)=1$ and $n^{v/L_H}\le e^{\theta v}$ for $v\ge0$. The discarded tail is $O(1/y)$.

The horizontal arguments contribute $O(\log H)$. In disks of radius three about $2+iH$ and $2+2iH$, zeta has polynomial growth and the fixed-length-power mollifier has polynomial growth by its defining sum. The right-edge real part exceeds $1/2$ for large $H$. Apply Jensen on a smaller disk to the holomorphic symmetrization whose restriction to the horizontal real parameter is the real part of $Z_H$. Its $O(\log H)$ zeros bound the change in the continuous argument along the edge. The same disk argument on $Z_H$ accounts for zeros at the two boundary heights by perturbing the horizontal edges. A zero at the left edge has zero displacement. Every mollifier zero in the rectangle has nonnegative displacement, so retaining only the zeta zeros gives
\[
 \sum_{H<\gamma\le2H}(\beta-\sigma)_+
 \le \frac{H}{4\pi}\log m_P(v,\theta)+o(H).
\]
These boundary estimates require a fixed power-length mollifier and bounded shifts. The additional length restriction in the comparison calculation of Kim comes from Young's moment theorem. Equation (2) uses Conrey's Gaussian formula with its own range. [Kim, §§2.2–2.5, preprint; Proposition 2.5 uses $\theta<1/2$](https://hexagonmath.org/pdf/2611.00318v1) · [Young, Archiv der Mathematik 95 (2010), Lemma 3](https://doi.org/10.1007/s00013-010-0199-9)

Fix $u>0$ and the final line $\sigma_T=1/2+u/\log T$ for every block. For $J=\lfloor\sqrt{\log T}/\log2\rfloor$ use $H=T/2^{j+1}$, $0\le j<J$, and local shift $v=u\log H/\log T=u+O_u((\log T)^{-1/2})$. The block errors are uniform for these shifts and contribute $o(T)$, since the smallest $H$ tends to infinity and the block lengths sum to at most $T$. Below $T/2^J$, the normalized mark contribution is $O((\log T)e^{-\sqrt{\log T}})$ by Riemann–von Mangoldt and $X_T\le(\log T)/2$. The main terms sum to $T\log m_P(u,\theta)/(4\pi)+o(T)$ for the unscaled right-sided sum. Since $N(T)\sim T\log T/(2\pi)$, multiplication by $\log T/N(T)$ gives half of $\log m_P(u,\theta)$. Functional-equation reflection doubles this for the absolute mark.

## Optimization and moments

Put $k=\theta u>0$. Among endpoint-normalized functions the minimizer of $\int_0^1(P'-kP)^2\$ is $P_*(x)=\sinh(kx)/\sinh k$. For $P=P_*+h$, the cross term vanishes by integration by parts, $h(0)=h(1)=0$, and $P_*''=k^2P_*$. The discrepancy is exactly $\int_0^1(h'-kh)^2\$. The optimal cost is $k(\coth k-1)$. Endpoint-normalized Taylor polynomials of the hyperbolic sine converge to $P_*$ in $C^1[0,1]$. Apply the height limit with each polynomial fixed before taking the polynomial limit. Sending $\theta\uparrow4/7$ last yields (1). The value at $u=0$ follows from $0\le X_T-(X_T-u)_+\le u$.

For every integer $n\ge2$,
\[
 \limsup_{T\to\infty}\mathbb E_T[X_T^n]
 \le n!\,\zeta(n)\big[(7/8)^{n-1}-(7/22)^{n-1}\big]. \tag{3}
\]
Indeed the finite identity is $\mathbb E_T[X_T^n]=n(n-1)\int_0^\infty u^{n-2}S_T(u)\,du$. Any single fixed subcritical Selberg density exponent and Riemann–von Mangoldt give $S_T(u)\ll e^{-c u}$, uniformly in sufficiently large $T$ and all $u\ge0$. This supplies the integrable dominating function for the upper limit. Expanding $F$ as the sum of nonnegative differences $(e^{-8ju/7}-e^{-22ju/7})/j$, Tonelli and the gamma integral give (3). In particular the second-moment cap is $49\pi^2/264\simeq1.83185839$. [Baluyot, *On the Zeros of Riemann's Zeta-function*, Theorem 1.2.1](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320)

## Endpoint tail on fixed microscopic windows

Put $a_*=8/7$. For $x=e^{-a_*v}$ and $v>0$, the numerator in (1) is $1-x^{11/4}$. Since $0<x<1$ and $11/4<3$,
\[
 F(v)\le \log(1+x+x^2)\le \sqrt{2}\,x.
\]
The second inequality follows from $e^{\sqrt{2}\,x}\ge1+\sqrt{2}\,x+x^2$. It extends to $v=0$ by continuity. If $s\ge7/8$, then $(X_T-s+7/8)_+\ge(7/8)\mathbf{1}_{X_T\ge s}$. For $s<7/8$ the probability is at most one. These facts imply, for each fixed $s\ge0$,
\[
 \limsup_{T\to\infty}\mathbb P_T(X_T\ge s)
 \le (8\sqrt{2}\,e/7)e^{-8s/7}. \tag{4}
\]
Writing $C_*=8\sqrt{2}\,e/7$, any fixed $M\ge0$ satisfies
\[
 \limsup_{T\to\infty}\sup_{0\le s\le M}
 e^{8s/7}\mathbb P_T(X_T\ge s)\le C_* .
\]
A mesh of width $\delta$ and monotonicity of the empirical tail give an upper bound $e^{a_*\delta}C_*$ in the height limit. Send $\delta\downarrow0$. Consequently, for every $\epsilon>0$ there is a function $\lambda_\epsilon(T)\to\infty$ such that, for all sufficiently large $T$,
\[
 \sup_{0\le s\le\lambda_\epsilon(T)} e^{8s/7}\mathbb P_T(X_T\ge s)\le C_*+\epsilon.
\]
Take successive height thresholds for the compact intervals $[0,n]$. The proof gives no explicit growth rate for $\lambda_\epsilon$. In the full finite-height Selberg density statement the scaled threshold runs up to $(\log T)/2$.

### Optimizing the endpoint prefactor

Let $m_*=\sup_{v\ge0}e^{8v/7}F(v)$. The fixed shift $h=7/8$ used in (4) gives the prefactor $(8/7)e\,m_*$. Among constant shifts $h>0$ used with the exponential envelope, $h=7/8$ minimizes $e^{8h/7}/h$. The exact rational computation in `verify_conrey_endpoint.py` gives
\[
 1.0673499920<m_*\le 1.0673499921 .
\]
Thus every compact-window and slowly growing window conclusion above holds with $C_*=(8/7)e(1.0673499921)$, approximately $3.3158378151$.

For the upper certificate, set $t=e^{-2v/7}$ and $c=1.0673499921$. Let $P_{17}$ be the Taylor polynomial of the exponential function through degree seventeen. Factor the polynomial
\[
 (1-t^4)P_{17}(ct^4)-(1-t^{11})=t^4(1-t)R(t).
\]
The script converts $R$ to the Bernstein basis and bisects a cell whenever a coefficient is negative. Fifteen dyadic cells suffice, the deepest is at level fourteen and every terminal Bernstein coefficient exceeds $9\cdot10^{-11}$. Since the Bernstein basis is nonnegative on each cell, the polynomial is nonnegative for $0\le t\le1$. Positivity of the omitted exponential series gives the desired quotient bound for $t<1$. Take the continuous limit at $t=1$. For the lower certificate, plug in $t=789633783/10^9$ and $c=1.0673499920$. A degree-sixteen Taylor upper bound with geometric tail proves $e^{ct^4}<(1-t^{11})/(1-t^4)$. Both checks use integer fractions throughout.

A four-cell, degree-four Taylor certificate yields the simpler $m_*\le267/250$, giving the prefactor $(8/7)e(267/250)$. The polynomial source `ConreyStopLossPolynomialEnvelope.lean` encodes this enclosure. The optimum enclosed above concerns the exponential majorant of the particular one-piece mollifier profile.

## Improvement using critical-line copies

Write $d$ for an upper asymptotic fraction of off-line occurrences. The exact inequality
\[
 (x-u)_+\le (x-v)_+ +(v-u)\mathbf 1_{x>0}\qquad(0\le u\le v)
\]
gives $\limsup S_T(u)\le\inf_{v\ge u}(F(v)+d(v-u))$. The repository theorem `eventually_normalized_strictTail_le_third` gives $d=1/3$. With the fixed rational choice $v=8/7$ one obtains
\[
 \limsup_{T\to\infty}\frac1T\sum_{0<\gamma\le T}(\beta-1/2)_+
 \le \frac{\log\big[(1-e^{-176/49})/(1-e^{-64/49})\big]+8/21}{4\pi}.
\]
Conrey's Theorem 3 gives the published upper bound $0.0806$. The displayed expression gives approximately $0.053231$ at this fixed strike. The second-moment cap likewise improves by integrating this linear bound from zero to $v$ and (1) from $v$ onward. All such caps are upper bounds. The conditional ordinate-PCC criterion in §7 of the repository tutorial asks for $\mathbb E_T[X_T^2]\to0$. [Conrey, Bulletin AMS 20 (1989), Theorem 3](https://aimath.org/~kaur/publications/21.pdf) · [Alpöge and Furman, arXiv:2608.13637v2](https://arxiv.org/abs/2608.13637) · [Lamzouri's independent proof, arXiv:2609.02882v2](https://arxiv.org/abs/2609.02882)

### Sharp endpoint constants from the off-line cap

Consider all distributions of nonnegative $X$ such that $\mathbb P(X>0)\le d$ and $\mathbb E[(X-v)_+]\le F(v)$ for $v\ge0$. Let $C(d)$ be the smallest constant for which $e^{8s/7}\mathbb P(X\ge s)\le C(d)$ for every such law and every $s\ge0$. The rational script above proves
\[
 3.302905566 < C(1/3) \le 3.302905567,\qquad
 3.301527974 < C(d_{10}) \le 3.301527976.
\]
The second interval uses $d_{10}=1-66732501992025865314318003264831248651423598405947/99062663304046530894651923264741897583007812500000$, the complement of the externally supplied cumulative ten-point critical-line fraction. Its decimal expansion begins $0.326360711833396$. The first uses the repository's critical-proportion theorem. The upper bounds also hold for the height limsup on compact windows, by applying the inequalities at each fixed threshold before taking a finite mesh.

Write $a=8/7$, choose $t_0\in(0,1)$, and put $v_0=-(7/2)\log t_0$. On $0<s\le v_0+h$, the off-line cap yields $e^{as}\mathbb P(X\ge s)\le e^{ah}d/t_0^4$. Above $v_0+h$ the shifted positive part bounds the tail by $F(s-h)/h$. If $e^{av}F(v)\le m$ for all $v\ge v_0$, the resulting prefactor is at most
\[
 \max\{1,e^{ah}\max(d/t_0^4,m/h)\}.
\]
The script uses $(t_0,h,m)=(0.7202190107,0.8580382279,1.0629848130)$ for $d=1/3$, and $(0.7163736600,0.8574334200,1.0625266759)$ for $d=d_{10}$. All decimals denote exact rationals. The same Bernstein certificate restricted to $[0,t_0]$, with a degree-fourteen exponential Taylor polynomial, proves each bound on $m$. A positive Taylor series with a geometric upper bound for its discarded terms verifies each displayed upper prefactor.

For the lower certificate let $s_d=\min_{v\ge0}(v+F(v)/d)$. The distribution with mass $d$ at $s_d$ and mass $1-d$ at zero satisfies all the assumptions, since $d(s_d-v)_+\le F(v)$ pointwise. Thus $C(d)\ge d e^{as_d}$. With $b=22/7$ and $t=e^{-2v/7}$, the derivatives are
\[
 F'(v)=\frac{b t^{11}}{1-t^{11}}-\frac{a t^4}{1-t^4},\qquad
 F''(v)=\frac{a^2}{4\sinh^2(av/2)}-\frac{b^2}{4\sinh^2(bv/2)}>0.
\]
The last inequality follows because $\sinh x/x$ increases for $x>0$, by its power series. For the two stated values of $d$, signs of $F'(v)+d$ at rational $t=0.70,0.73$ bracket the unique minimizer. Forty-two rational bisections give $t_{\rm left}\le t_d\le t_{\rm right}$. Since $F(v)$ decreases in $v$, the script bounds the exponential from below by
\[
 \frac{d}{t_{\rm right}^4}
 \exp\!\left(\frac ad\log\frac{1-t_{\rm left}^{11}}{1-t_{\rm left}^4}\right).
\]
Positive Taylor polynomials for the logarithm in the variable $(x-1)/(x+1)$ and for the exponential verify the strict lower bounds with rational arithmetic. This identifies the optimum within the displayed intervals for the information supplied by the stop-loss profile and the off-line fraction.

The same tangent optimizes the first-moment displacement cap. Write $\delta_d=\inf_{v\ge0}(F(v)+d v)/(4\pi)=d s_d/(4\pi)$. The rational script encloses both optimized upper bounds,
\[
 0.05323037840 < \delta_{1/3} < 0.05323037841,\qquad
 0.05258782449 < \delta_{d_{10}} < 0.05258782450.
\]
Hence the limsup of the unnormalized right displacement divided by height is at most $0.05323037841$ using the repository's one-third off-line cap, and at most $0.05258782450$ with the external ten-point proportion. The lower ends of these intervals concern the numerical optimized caps. Conrey's comparable Theorem 3 gives $0.0806$. The computation encloses $\pi$ using Machin's identity and alternating arctangent series.

### Exact optimum of the endpoint prefactor

The finite enclosures above surround an exact extremal value. For each of the three off-line fractions in this note, the rational root test in the script places $t_d=e^{-2v_d/7}$ in $(0.70,0.73)$. On $v\ge v_d$ the function $e^{av}F(v)$ is decreasing. To see this, set $z=e^{-av}=t^4$ and $p=11/4$. For $0<z<1$, differentiating the absolutely convergent power series for $H(z)=F(v)/z$ gives
\[
 H'(z)=\sum_{n\ge2}\frac{n-1}{n}z^{n-2}
       -\sum_{n\ge1}\left(p-\frac1n\right)z^{pn-2}.
\]
Retain the first three positive summands and bound the negative tail after $n=1$ by $pz^{2p-2}/(1-z^p)$. Thus $12(1-t^{11})H'(t^4)$ is at least
\[
 (6-21t^3+8t^4+9t^8)(1-t^{11})-33t^{14}.
\]
On $0\le t\le73/100$ the twenty Bernstein coefficients of this degree-nineteen polynomial are all larger than $399/1000$, as verified by exact rational arithmetic in the accompanying script. Hence $H'(z)>0$ throughout the required interval.

Put $h=F(v_d)/d$ so $s_d=v_d+h$. For $0<s\le s_d$ use $\mathbb P(X\ge s)\le d$. For $s\ge s_d$, the shifted stop-loss bound and monotonicity give
\[
 e^{as}\mathbb P(X\ge s)\le \frac{e^{ah}}h e^{a(s-h)}F(s-h)
 \le\frac{e^{ah}}h e^{av_d}F(v_d) = d\,e^{as_d}.
\]
At zero the left side is one. The two-point law given above attains $d e^{as_d}$ at $s_d$, and for our three cases $d e^{as_d}>1$. Therefore the **exact extremal prefactor** for each tabulated off-line fraction is $C(d)=d\exp(a[v_d+F(v_d)/d])$. The ten-digit rational brackets approximate this formula. The same argument gives $\max(1,d e^{as_d})$ whenever an interior root has $t_d\le73/100$.

### Sharp microscopic moment caps

Let $v_d$ be the minimizer above. The strongest pointwise stop-loss bound implied by the profile and the off-line cap is
\[
 F_d(u)=
 \begin{cases} F(v_d)+d(v_d-u),&0\le u\le v_d,\\
 F(u),&v_d\le u. \end{cases}
\]
This follows by minimizing $F(v)+d(v-u)$ for $v\ge u$. The function $F_d$ is itself the stop-loss transform of a law with mass $1-d$ at zero. Its strictly positive tail for $u>0$ is $-F_d'(u)$, which decreases continuously from $d$ to zero. This law satisfies every original constraint and attains $F_d$ at all thresholds. Thus the moments obtained by integrating $F_d$ are sharp among laws satisfying these inputs.

For $n\ge2$ the optimal moment cap is
\[
 M_n(d)=n v_d^{\,n-1}F(v_d)+d v_d^n+
 n(n-1)\int_{v_d}^\infty u^{n-2}F(u)\,du .
\]
The uniform integrability needed for the empirical height limsup is supplied by any fixed subcritical density bound, as for (3). The script encloses the optimal values as follows.

| Off-line cap | Strict enclosure for $M_2(d)$ | Strict enclosure for $M_4(d)$ |
|---|---:|---:|
| $1/3$ | $(1.586614444,\ 1.586614445)$ | $(16.385242327,\ 16.385242328)$ |
| $d_{10}$ | $(1.577263569,\ 1.577263570)$ | $(16.372700918,\ 16.372700919)$ |

For $k=n-2$, integrate the exponential series for $F$ above $v_d$ termwise. This gives the finite polylogarithm sum
\[
 \int_{v_d}^{\infty}u^k F(u)\,du
 =\sum_{j=0}^{k}\frac{k!}{j!}v_d^j
 \left[\frac{\mathrm{Li}_{k-j+2}(t_d^4)}{a^{k-j+1}}-
       \frac{\mathrm{Li}_{k-j+2}(t_d^{11})}{b^{k-j+1}}\right].
\]
Each $\mathrm{Li}_p(z)$ is bounded below by its first 26 positive terms and above by adding $z^{27}/(27^p(1-z))$. Applying the rational bracket for $t_d$ separately to the positive and negative terms verifies the tabulated enclosures. In particular, the second-moment cap falls from $49\pi^2/264$ to at most $1.577263570$ using the external $d_{10}$ input. A proof of the microscopic PCC sufficiency condition would require the second moment to vanish.

**Verification scope.** Equations (1)–(3) and the off-line-fraction refinement are paper deductions from the published shifted Gaussian moment and density theorem. The normalized finite-height exponential bound and the signed exceptional-pair estimate are separate Lean declarations. The optimization identifies the extremum of the stated one-piece mollifier functional. A global optimality or priority claim for the zeta bounds would require a separate comparison.

## Sharp exponent for abstract exceptional-pair deletion

The Lean theorem `ActualMontgomeryExceptionalPairs.eventually_signed_deletion_le` permits every $\kappa<1-7\theta/4$ for $0<\theta<4/7$. It assumes subcritical Selberg density at each fixed $b<8/7$, uniformly bounded fixed moments of microscopic Cauchy rows, and the given absolute majorant on the signed test array. These inputs alone also show why the inequality for $\kappa$ is strict.

For integers $m\to\infty$, choose the positive solution of $T_m\log T_m=4\pi m^2$ and set $L_m=\log T_m$. Put two model copies in each of $m^2$ ordinate cells, centered at $4\pi j/L_m$ for $1\le j\le m^2$. In the first $m$ cells place a reflected pair at the center, with real parts $1/2\pm X_m/L_m$, where $X_m=(7/8)\log m+\sqrt{\log m}$. In each other cell put two distinct critical-line copies at the center and $\pi/L_m$ below it. Then $N=2m^2$, the exceptional fraction is $\delta=1/m$, and $X_m<L_m/2$ for all sufficiently large $m$, because $L_m=2\log m+O(\log\log m)$. Every microscopic Cauchy row has mass bounded independently of $m$: there are at most two copies per cell, and cells $k$ steps apart have phase-scaled separation at least $4\pi|k|-\pi$. All fixed row moments therefore satisfy the required bounds.

The population tail above every positive scaled threshold $s\le X_m$ is $\delta$, and it vanishes above $X_m$. For each fixed $0<b<8/7$,
\[
 \delta e^{bX_m}=m^{-1+7b/8} e^{b\sqrt{\log m}}\longrightarrow0.
\]
Thus each subcritical exponential tail inequality holds uniformly, with its own constant. All fixed positive-part excesses tend to zero as well, so the stop-loss profile supplies no obstruction to this model.

Choose the admissible signed test array to vanish except on the diagonal of the exceptional set, where its value is $N^{-1}e^{2\theta X_m}$ and the microscopic Cauchy weight is exactly one. The normalized deletion is then
\[
 \delta e^{2\theta X_m}
  =\delta^{\,1-7\theta/4}e^{2\theta\sqrt{\log m}} .
\]
Its ratio to $\delta^\kappa$ diverges for $\kappa\ge1-7\theta/4$. Consequently no height-independent endpoint constant follows from these abstract inputs and this class of dominated arrays. Extra information about actual zeta ordinates or the analytic test function can strengthen the estimate in a narrower setting.

## Sensitivity to the November 18 manuscript

Theorem 1 of *Geometric credit in the ordered-moment bound for simple critical-line zeros*, rStation paper 179, reports a lower limiting fraction of 0.67385611 for zeros that are simultaneously simple and on the critical line. Its proof invokes separately cited analytic results and numerical certificates. We treat this manuscript fraction as an additional hypothesis. Its proof has not been replayed in this Lean development. [Manuscript, version 1](https://rstation.ai/problems/riemann_hypothesis/papers/179/v1)

Taking the rational complement $d=0.32614389$ in the same exact certificate gives the following enclosures. The normalized displacement column is the bound on the limiting sum of positive right displacements per unit height. The moment columns refer to powers of the scaled absolute horizontal displacement, averaged over zero copies.

| Optimal endpoint prefactor | Normalized displacement cap | Second-moment cap | Fourth-moment cap |
|---|---|---|---|
| $(3.301483902,3.301483903]$ | $(0.05256767630,0.05256767631)$ | $(1.576967912,1.576967913)$ | $(16.372297761,16.372297762)$ |

The optimizing strike satisfies $e^{-2v_d/7}\approx0.716253268374826$ and the corresponding mean scaled absolute displacement bound is approximately $0.6605849027998823$. The new final case of `verify_conrey_endpoint.py` proves the four displayed enclosures using rational arithmetic under the stated fraction. The earlier ten-point row uses its own exact rational input.

## Joint bound with the November 19 sampled mean

Theorem 2 and its table in rStation paper 182 report the dyadic upper bound
\[
 \limsup_{T\to\infty}\frac{2\pi}{T}
 \sum_{T<\gamma\le 2T}(\beta-1/2)_+\le0.32133.
\]
This is an additional manuscript input. Appendix F uses separated critical zeros and a sampling-kernel moment. The author's announcement requests independent checks of the Gram normalization and entropy estimate. The manuscript separately lists the weaker journal-input dyadic bound $0.442758582$. Summing dyadic blocks and using the Riemann–von Mangoldt normalization gives the cumulative mean-mark bound $m=0.64266$. Equivalently it gives the positive right-displacement bound $m/(4\pi)<0.05114125787$ per unit height, stronger than either preceding one-piece mean cap. [Manuscript, Appendix F](https://rstation.ai/problems/riemann_hypothesis/papers/182) · [Author's normalization and announcement](https://rstation.ai/r/riemann_hypothesis/posts/90)

Suppose a law satisfies the Conrey stop-loss bound, off-line mass at most $d=1/3$, and mean at most $m$. Let $v_m$ solve $F(v_m)-v_m F'(v_m)=m$, and set $d_m=-F'(v_m)$. Strict convexity gives a unique interior solution for this $m$. Convexity of the stop-loss function itself bounds it by the chord from $(0,m)$ to $(v_m,F(v_m))$ on $[0,v_m]$. This chord is the tangent to $F$ at $v_m$. Hence the maximal stop-loss profile is
\[
 G_m(v)=
 \begin{cases}
 m-d_m v,&0\le v\le v_m,\\
 F(v),&v\ge v_m.
 \end{cases}
\]
It is attained by the law with survival probability $d_m$ on $(0,v_m)$ and $-F'(v)$ on $(v_m,\infty)$. Its remaining mass is at zero, and $d_m<1/3$. This law simultaneously attains the joint moment bounds.

For the exponent-$8/7$ CCDF, set $s_m=m/d_m$ and $h=s_m-v_m=F(v_m)/d_m$. Until $s=m/d$, bound the tail by $d$ for positive $s$; from $m/d$ to $s_m$, bound it by $m/s$. The function $e^{as}/s$ increases on this second interval because $m/d>1/a$. Above $s_m$, use $F(s-h)/h$ and the monotonicity of $e^{av}F(v)$ proved earlier. Thus the exact CCDF prefactor is $d_m e^{a s_m}$, attained by the two-point law placing mass $d_m$ at $s_m$. A generic admissible law may have more than $d_m$ mass arbitrarily near zero, so the first interval still uses $d$.

The script brackets $e^{-2v_m/7}$ strictly between $0.70775425032680$ and $0.70775425032681$. It gives $v_m\approx1.2098042236040583$ and $d_m\approx0.3110653503837449$. These quantities also satisfy every earlier off-line mass cap, so the ten-point and paper 179 proportions give the same joint optimum.

| Optimal CCDF prefactor | Second-moment cap | Third-moment cap | Fourth-moment cap |
|---|---|---|---|
| $(3.298233008,3.298233009)$ | $(1.555657147,1.555657148)$ | $(4.553304063,4.553304064)$ | $(16.342166485,16.342166486)$ |

The enclosures are exact-rational computations for the stated abstract constraints. The sampled mean remains a separate manuscript assertion in this comparison.
