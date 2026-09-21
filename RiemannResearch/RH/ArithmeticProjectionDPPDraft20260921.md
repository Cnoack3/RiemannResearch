# Arithmetic projection DPPs, vacancy criteria, and Mellin scaling limits

Working research draft — 21 September 2026. Markdown archive of the ordinary-mathematics manuscript. See `ArithmeticProjectionDPPFormalization20260921.md` for the exact Lean coverage. Theorem numbering here follows the Markdown conversion.

**Abstract.** We apply standard determinantal point process theory to the weighted residue space in Bagchi's formulation of the Riemann hypothesis. An off-critical zero produces an explicit vector in the orthogonal defect space, giving positive vacancy bounds at every integer, a weighted-hole divergence criterion, and upper bounds on finite interpolation capacities. A finite residue-class representation separates class omission from a quantitatively negligible lifting error. A physical-coordinate cutoff followed by Mellin measurement has a sine-process limit under RH; an exact covariance identity identifies its next-order correction. Without RH, the arithmetic defect remains in the covariance. Every fixed finite-rank defect is invisible in the leading sine limit, while zero-generated defects survive in suitable unscaled and second-order observables. In particular, disappearance of the unscaled expected-count deficit on any fixed bounded Mellin window of positive measure is equivalent to RH. The estimates needed to prove that disappearance, or divergence of the signed capacities, are not established here.

**Status.** This is a mathematical draft with explicit proofs, prepared outside Lean. It has not undergone independent peer review. The standard completeness theorem and DPP machinery are attributed below; the originality of the assembled criteria and refinements requires further literature comparison. No theorem about correlations of the actual zeta zeros or a Hilbert--Pólya spectrum is claimed.

# Setup and the role of existing results

Put $$\label{eq:setup}
 w_n=\frac1{n(n+1)},\qquad
 H=\ell^2(\mathbb N_{\ge1},w),\qquad
 g_d(n)=\frac{n\bmod d}{d}\quad(d\ge2).$$ The inner product is antilinear in its first variable. Define $$S_N=\operatorname{span}\{g_2,\ldots,g_{N+1}\},\qquad
 S=\overline{\bigcup_N S_N},$$ and let $P_N,P$ be the corresponding orthogonal projections. Write $D=I-P$ for the arithmetic defect. Bagchi's weighted sequence-space theorem [Bagchi](https://arxiv.org/abs/math/0607733) Theorem 1 gives $$\label{eq:bagchi}
 \mathrm{RH}\quad\Longleftrightarrow\quad S=H
 \quad\Longleftrightarrow\quad P=I.$$ This is the number-theoretic completeness input to the paper.

Let $V:H\to\ell^2(\mathbb N)$ be $(Vf)(n)=\sqrt{w_n}f(n)$, and put $$b_n=w_n^{-1/2}\mathbf 1_{\{n\}},\qquad
 Q_N=VP_NV^{-1},\qquad Q=VPV^{-1}.$$ The $b_n$ form an orthonormal basis of $H$. The kernels $Q_N$ and $Q$ define discrete projection DPPs $X_N$ and $X$. Existence, projection cardinality, and stochastic domination are standard DPP results [Hough–Krishnapur–Peres–Virág](https://arxiv.org/abs/math/0503110), [Lyons](https://arxiv.org/abs/math/0204325). The hole process $\mathbb N\setminus X$ has kernel $I-Q$. In particular, $$\label{eq:vacancy}
 q_N(n):=\mathbb P(n\notin X_N)=\langle b_n,(I-P_N)b_n\rangle,\qquad
 q(n):=\mathbb P(n\notin X)=\langle b_n,Db_n\rangle.$$ Since $P_N\to P$ strongly, $q_N(n)\downarrow q(n)$.

The generators are finitely independent. Indeed, setting $g_d(0)=0$, $$g_d(n)-g_d(n-1)=d^{-1}-\mathbf 1_{d\mid n}.$$ If a finite linear combination vanishes, its difference at $n=1$ makes the constant term zero. Induction at $n=2,3,\ldots$ then annihilates its coefficients. Thus $\dim S_N=N$ and $|X_N|=N$ almost surely.

Under RH the infinite integer process is deterministic: $X=\mathbb N$ almost surely. Random continuum processes introduced later arise from a change of measurement representation after a cutoff. They are not pointwise pushforwards of this deterministic configuration.

#### Position relative to the literature.

The completeness reformulation is due to the Nyman--Beurling--Báez-Duarte theory, in the form presented by Bagchi. The projection DPP interpretation and basic probabilistic operations use existing theory. Zero-based Hilbert-space obstructions belong to a substantial literature, including Burnol [Burnol](https://arxiv.org/abs/math/0103058); the formulas below give them explicit weighted-sequence and vacancy expressions. Probabilistic Nyman--Beurling criteria also exist [Darses–Hillion](https://arxiv.org/abs/1805.06733), so a probabilistic reformulation alone does not establish originality. The sine process and its random-matrix and free-fermion interpretations are classical [Soshnikov](https://arxiv.org/abs/math/0002099). Our purpose is to give a precise chain of formulas, explain which quantities retain arithmetic information, and isolate the estimate still required for RH.

# Off-critical zeros force integer vacancies

For every $s\in\mathbb C$ define the entire function $$m_s(n)=\int_n^{n+1}x^{-s-1}\,dx
       =\frac{n^{-s}-(n+1)^{-s}}s.$$ The quotient is interpreted by its removable value at $s=0$. For $\Re s>1/2$, the functional $$L_s(f)=\int_1^\infty f(\lfloor x\rfloor)x^{-s-1}\,dx$$ is continuous on $H$: Cauchy--Schwarz with measure $dx/x^2$ gives $$\label{eq:mellinbound}
 |L_s(f)|\le\frac{\lVert f\rVert_H}{\sqrt{2\Re s-1}}.$$ Using $g_d(\lfloor x\rfloor)=d^{-1}\lfloor x\rfloor-\lfloor x/d\rfloor$ first for $\Re s>1$, and then analytic continuation, gives $$\label{eq:genmellin}
 L_s(g_d)=\frac{\zeta(s)}s\bigl(d^{-1}-d^{-s}\bigr),\qquad \Re s>0.$$ The apparent singularity at $s=1$ on the right is removable.

<a id="thm:zero"></a>
**Theorem 1** (Explicit zero-mode obstruction). *Suppose $\zeta(\rho)=0$, where $\rho=\beta+i\gamma$ and $1/2<\beta<1$. Set $$r_\rho(n)=\frac{\overline{m_\rho(n)}}{w_n},\qquad
 c_\rho=\lVert r_\rho\rVert_H^2=\sum_{n\ge1}\frac{|m_\rho(n)|^2}{w_n}.$$ Then $r_\rho\in S^\perp$, $0<c_\rho\le(2\beta-1)^{-1}$, and, with $\Pi_\rho$ its normalized rank-one projection, $$D\ge\Pi_\rho,\qquad I-P_N\ge\Pi_\rho.$$ Consequently, for every $n,N$, $$\label{eq:zerovacancy}
 q_N(n)\ge q(n)\ge
 \frac{|m_\rho(n)|^2}{w_n c_\rho}>0.$$*

*Proof.* Intervalwise Cauchy--Schwarz gives $$|m_\rho(n)|^2\le w_n\int_n^{n+1}x^{-2\beta}\,dx.$$ Summation proves the upper bound on $c_\rho$. Also $\langle r_\rho,f\rangle=L_\rho(f)$, so [\[eq:genmellin\]](#eq:genmellin) proves orthogonality to every generator. Inclusion of its range in $S^\perp\subset S_N^\perp$ gives the projection inequalities. Taking their $b_n$ diagonal entries proves the bound. Finally, $m_\rho(n)\ne0$: the two terms $n^{-\rho}$ and $(n+1)^{-\rho}$ have different absolute values because $\beta>0$. ◻

<a id="cor:criteria"></a>
**Corollary 2** (Every-site and weighted-hole criteria). *For each prescribed integer $n\ge1$, $$\mathrm{RH}\quad\Longleftrightarrow\quad q(n)=0
 \quad\Longleftrightarrow\quad q_N(n)\longrightarrow0.$$ Moreover, $$\label{eq:weightedholes}
 \mathrm{RH}\quad\Longleftrightarrow\quad
 \mathbb E\left[\sum_{n\notin X}n\right]<\infty.$$ Under RH this expectation is zero. If RH is false and $\rho$ is as above, then $$\label{eq:weightedrate}
 \liminf_{M\to\infty}\frac{\mathbb E[\sum_{n\le M,\,n\notin X}n]}{M^{2-2\beta}}
 \ge\frac1{(2-2\beta)c_\rho}.$$*

*Proof.* If RH fails, the functional equation supplies a zero with $1/2<\beta<1$, so Theorem [1](#thm:zero) excludes zero vacancy at every site. Conversely [\[eq:bagchi\]](#eq:bagchi) gives all vacancies zero under RH. For fixed $\rho$, $$\frac{|m_\rho(n)|^2}{w_n}
 =n^{-2\beta}\bigl(1+O_\rho(n^{-1})\bigr).$$ Tonelli's theorem and [\[eq:zerovacancy\]](#eq:zerovacancy), followed by summation of $n^{1-2\beta}$, prove [\[eq:weightedrate\]](#eq:weightedrate) and [\[eq:weightedholes\]](#eq:weightedholes). ◻

*Remark 3*. Equation [\[eq:weightedholes\]](#eq:weightedholes) concerns expectation. Infinite expectation does not assert almost-sure divergence of the weighted sum or infinitely many holes. Also, the every-site criterion uses the arithmetic zero-mode obstruction; it is not a property of arbitrary proper projections.

# A signed capacity criterion and its unresolved estimate

Write $v_N(n)=(g_2(n),\ldots,g_{N+1}(n))^T$ and define the positive definite Gram matrices $$G_N=\sum_{n\ge1}w_n v_N(n)v_N(n)^T,\qquad
 T_N=\sum_{n\ge2}w_n v_N(n)v_N(n)^T.$$ Positivity of $T_N$ follows because a finite residue combination is periodic: if it vanishes for every $n\ge2$, it also vanishes at $n=1$, and finite independence applies. Let $$b^{(N)}=(1/2,1/3,\ldots,1/(N+1))^T,\qquad
 C_N=(b^{(N)})^TT_N^{-1}b^{(N)}.$$ The vector $b^{(N)}$ here is a coefficient-space vector, distinct from the orthonormal coordinate vectors $b_n$.

<a id="prop:capacity"></a>
**Proposition 4** (Exact single-site capacity). *The kernel and first-site vacancy satisfy $$\begin{aligned}
 Q_N(n,m)&=\sqrt{w_nw_m}\,v_N(n)^TG_N^{-1}v_N(m),\label{eq:gramkernel}\\
 q_N(1)&=\frac{\det T_N}{\det G_N}=\frac{2}{C_N+2}.
 \label{eq:capacity}
\end{aligned}$$ In particular, $\mathrm{RH}\Longleftrightarrow C_N\to\infty$.*

*Proof.* The first identity is the Gram formula for an orthogonal projection. Since $G_N=T_N+\tfrac12b^{(N)}(b^{(N)})^T$, the matrix determinant lemma and the rank-one inverse formula give the two forms of $q_N(1)$. Apply Corollary [2](#cor:criteria). ◻

When adding $g_{N+2}$, write $$T_{N+1}=\begin{pmatrix}T_N&t_N\\t_N^T&\tau_N\end{pmatrix},\quad
 \sigma_N=\tau_N-t_N^TT_N^{-1}t_N>0,\quad
 \eta_N=\frac1{N+2}-t_N^TT_N^{-1}b^{(N)}.$$ Block inversion yields the exact identity $$\label{eq:gain}
 C_{N+1}-C_N=\frac{\eta_N^2}{\sigma_N},\qquad
 \mathrm{RH}\quad\Longleftrightarrow\quad
 \sum_{N\ge1}\frac{\eta_N^2}{\sigma_N}=\infty.$$ The Schur denominator is positive, but independence does not supply a useful lower bound on the signed numerator $\eta_N$. The arithmetic problem is to control its cancellation strongly enough to prove divergence. Replacing the signed residual by an unsigned upper bound would not prove the needed lower bound.

<a id="cor:zerocap"></a>
**Corollary 5** (Capacity bound from a zero). *For a zero $\rho$ as in Theorem [1](#thm:zero), every $N$ satisfies $$\label{eq:zerocap}
 C_N+2\le
 \frac{c_\rho|\rho|^2}{|1-2^{-\rho}|^2}
 \le\frac{|\rho|^2}{(2\beta-1)|1-2^{-\rho}|^2}.$$ Thus a rigorously certified lower bound on $C_N$ can exclude specified off-critical zeros. For example, for $0<\varepsilon<1/2$, the inequality $$\label{eq:finitecertificate}
 C_N+2>\frac{1+T^2}{2\varepsilon(1-2^{-1/2})^2}$$ excludes zeros with $\beta\ge1/2+\varepsilon$ and $|\gamma|\le T$.*

*Proof.* At $n=1$, [\[eq:zerovacancy\]](#eq:zerovacancy) is $q_N(1)\ge2|1-2^{-\rho}|^2/(c_\rho|\rho|^2)$. Combine this with [\[eq:capacity\]](#eq:capacity). For the final assertion use $|\rho|^2\le1+T^2$ and $|1-2^{-\rho}|\ge1-2^{-\beta}\ge1-2^{-1/2}$. ◻

No numerical capacity certificate is claimed here. In particular, a floating-point inverse of an increasingly ill-conditioned Gram matrix is not by itself such a certificate.

# Finite residue classes and the lifting error

Let $L=\operatorname{lcm}(2,\ldots,N+1)$ and use representatives $1\le r\le L$. Since $v_N(n)$ is $L$-periodic, $$W_L(r)=\sum_{k\ge0}w_{r+kL},\qquad
 G_N=\sum_{r=1}^L W_L(r)v_N(r)v_N(r)^T.$$ For reference, $W_L(r)=L^{-1}[\psi((r+1)/L)-\psi(r/L)]$, where $\psi$ is the digamma function. This follows by writing $w_n=1/n-1/(n+1)$ and applying its standard convergent difference series.

<a id="prop:crt"></a>
**Proposition 6** (Exact class sampling and lifting). *Define the rank-$N$ kernel on $\{1,\ldots,L\}$ by $$\widetilde Q_N(r,s)=\sqrt{W_L(r)W_L(s)}\,
 v_N(r)^TG_N^{-1}v_N(s).$$ Sample its projection DPP, and, independently for each selected class $r$, choose $r+kL$ with probability $w_{r+kL}/W_L(r)$. The resulting integer configuration has exactly the law of $X_N$.*

*If $p_N=\widetilde Q_N(1,1)$ is the probability of selecting class $1$, then $$\label{eq:crtgap}
 q_N(1)=(1-p_N)+p_N\left(1-\frac{w_1}{W_L(1)}\right),\qquad
 0\le q_N(1)-(1-p_N)\le\frac{2\zeta(2)}{L^2}.$$ Consequently $\mathrm{RH}\Longleftrightarrow p_N\to1$.*

*Proof.* Whiten the rows $\sqrt{w_n}v_N(n)^T$ by $G_N^{-1/2}$. Rows from the same class are parallel, so a nonzero $N$-point determinant cannot use a class twice. For distinct classes its squared determinant factors into the class determinant and the product of the lifting probabilities. This proves equality of the fixed-cardinality DPP laws. The first identity in [\[eq:crtgap\]](#eq:crtgap) follows by considering the two ways site $1$ is absent. Finally, $$1-\frac{w_1}{W_L(1)}
 \le2\sum_{k\ge1}\frac1{(1+kL)(2+kL)}
 \le\frac{2\zeta(2)}{L^2}.$$ Now use the first-site criterion and $L\to\infty$. ◻

The explicit lifting error is negligible. The unresolved arithmetic estimate is the decay of the class-omission probability $1-p_N$.

# Mellin measurement and the leading sine limit

Define an isometry into a closed subspace of $L^2(\mathbb R,dt/(2\pi))$ by $$\label{eq:U}
 (Uf)(t)=\int_1^\infty f(\lfloor x\rfloor)x^{-3/2-it}\,dx.$$ For arbitrary $f\in H$, this has its $L^2$ boundary-transform meaning. Substitution $u=\log x$ identifies it with the Fourier transform of $e^{-u/2}f(\lfloor e^u\rfloor)\mathbf 1_{u\ge0}$, proving the isometry by Plancherel. It is not asserted to be onto the full continuous $L^2$ space.

Let $R_M$ project onto $\operatorname{span}\{b_1,\ldots,b_M\}$ and write $$h_n(t)=Ub_n(t)=\frac{m_{1/2+it}(n)}{\sqrt{w_n}}.$$ The full-space comparison covariance and the actual arithmetic covariance are $$\label{eq:covariances}
 \mathcal A_M^0=UR_MU^*,\qquad
 \mathcal A_M^P=UR_MPR_MU^*.$$ Both define finite-rank continuum DPPs, denoted $Y_M^0,Y_M^P$. The first is a rank-$M$ projection with kernel $$K_M^0(t,u)=\sum_{n\le M}h_n(t)\overline{h_n(u)}.$$ The second is a positive contraction, with expected total count $M-\operatorname{Tr}(R_MDR_M)$; it need not have a deterministic count. Under RH these two processes have the same law.

<a id="thm:sine"></a>
**Theorem 7** (Fixed-center Dyson sine limit). *Fix $t_0\in\mathbb R$, set $L_M=\log(M+1)$ and $t_M(x)=t_0+2\pi x/L_M$. Relative to Lebesgue measure $dx$, the unfolded comparison kernel is $$\kappa_M^0(x,y)=\frac1{L_M}K_M^0(t_M(x),t_M(y)).$$ Locally uniformly in $x,y$, $$\label{eq:sine}
 \kappa_M^0(x,y)=
 S_\phi(x,y)+O_{t_0,R}(L_M^{-1}),\qquad
 S_\phi(x,y)=e^{-\pi i(x-y)}\frac{\sin\pi(x-y)}{\pi(x-y)}.$$ The unfolded DPPs converge locally in law to the unit-intensity sine$_2$ process, including convergence of all fixed-order correlation functions and bounded-interval gap probabilities. Under RH the same assertions hold for $Y_M^P$.*

*Proof.* An exact factorization is $$h_n(t)=n^{-1/2-it}a_n(t),\qquad
 a_n(t)=\sqrt{1+1/n}\int_0^1(1+v/n)^{-3/2-it}\,dv.$$ For bounded $t$, $a_n(t)=1+O(n^{-1})$; also $|a_n(t)|\le\sqrt2$. Thus, locally uniformly in $t,u$, $$K_M^0(t,u)=\sum_{n\le M}n^{-1-i(t-u)}+O(1)
 =\int_1^{M+1}r^{-1-i(t-u)}\,dr+O(1).$$ The sum--integral error is bounded by summing the absolute derivative on each unit interval. After setting $t-u=2\pi(x-y)/L_M$, the integral divided by $L_M$ is exactly $S_\phi(x,y)$. Gauge multiplication by $e^{\pi ix}$ and $e^{-\pi iy}$ removes its phase without changing correlation determinants.

On a bounded interval $B$, the diagonals of $\kappa_M^0$ are uniformly bounded by some $C_B$. Hadamard's inequality bounds every $k$-point correlation determinant by $C_B^k$. The Fredholm series for gaps, and the Laplace-functional series with factors $1-e^{-f}$ for $f\ge0$, are therefore dominated by $\sum_k(C_B|B|)^k/k!$. Dominated convergence proves the asserted process and gap convergence. RH identifies the two covariances in [\[eq:covariances\]](#eq:covariances). ◻

#### Relation to the original arithmetic rank.

For fixed $M$, under RH, $$\lVert UR_M(P_N-I)R_MU^*\rVert_1
 =\sum_{n\le M}q_N(n)\longrightarrow0.$$ Hence the theorem can be realized by first letting arithmetic rank $N\to\infty$ at fixed physical cutoff $M$, then letting $M\to\infty$. A diagonal choice $N(M)$ exists but no effective rate is provided. This is not a theorem about the uncompressed sequence $UP_NU^*$.

#### A high-center variant.

Let $T\to\infty$, $m=\lfloor T\rfloor$, $M=\lfloor T^2\rfloor$, $a_T=\log(m+1)$, and $L_T=\log((M+1)/(m+1))\sim\log T$. At $t=T+2\pi x/L_T$ and $u=T+2\pi y/L_T$, $$\label{eq:highcenter}
 \frac{K_M^0(t,u)}{L_T}
 =e^{-2\pi i(x-y)(a_T/L_T+1/2)}
 \frac{\sin\pi(x-y)}{\pi(x-y)}+O_R(L_T^{-1}).$$ Indeed, for $n\le m$ the difference formula gives $|h_n(t)|\ll\sqrt n/T$, so this part contributes $O(1)$. For $n>m$, $|a_n(t)-1|\ll(1+|t|)/n$, and the total replacement error is $O(T\sum_{n>m}n^{-2})=O(1)$. Integral comparison over $[m+1,M+1]$ now proves [\[eq:highcenter\]](#eq:highcenter). The same Fredholm argument applies. The choice $M\asymp T^2$ creates the spacing $2\pi/\log T$; it does not identify the process with zeta zeros.

# An exact second-order covariance correction {#sec:second}

The leading sine estimate has a sharper form. Let $d\mu(x)=dx/x^2$ on $[1,\infty)$ and $f_t(x)=x^{1/2-it}$. On $I_n=[n,n+1)$ define its weighted cell mean $$\bar f_{n,t}=\frac1{w_n}\int_{I_n}f_t\,d\mu,$$ and set $$\label{eq:B}
 B_n(t,u)=\int_{I_n}(f_t-\bar f_{n,t})
             \overline{(f_u-\bar f_{n,u})}\,d\mu,\qquad
 B(t,u)=\sum_{n\ge1}B_n(t,u).$$

<a id="thm:second"></a>
**Theorem 8** (Ambient second-order term). *The series defining $B$ converges smoothly on compact subsets of $\mathbb R^2$. It is a positive semidefinite kernel and $B(t,t)>0$ for every real $t$. Exactly, $$\label{eq:exactB}
 K_M^0(t,u)=\int_1^{M+1}x^{-1-i(t-u)}\,dx-
                  \sum_{n\le M}B_n(t,u).$$ For $|t|,|u|\le T$, the tail of the series is $O_T(M^{-2})$. Consequently, for fixed $t_0$, $$\label{eq:secondmicro}
 \kappa_M^0(x,y)
 =S_\phi(x,y)-\frac{B(t_0,t_0)}{L_M}
       +O_{t_0,R}(L_M^{-2})$$ uniformly for $|x|,|y|\le R$.*

*Proof.* The covariance identity on one cell gives $$B_n(t,u)=\int_{I_n}x^{-1-i(t-u)}\,dx
                  -h_n(t)\overline{h_n(u)}.$$ This proves [\[eq:exactB\]](#eq:exactB) and positivity. Since $|f_t'(x)|=|1/2-it|x^{-1/2}$, the oscillation on $I_n$ is $O_T(n^{-1/2})$. Multiplication by $\mu(I_n)=w_n=O(n^{-2})$ gives $B_n(t,u)=O_T(n^{-3})$. For mixed $t,u$ derivatives of total order $k$, the analogous bound is $O_{T,k}(n^{-3}(1+\log n)^k)$, proving smooth local convergence. The diagonal is strictly positive because $f_t$ is not constant on any cell. Finally evaluate [\[eq:exactB\]](#eq:exactB) at $t_M(x),t_M(y)$, divide by $L_M$, and use differentiability of $B$ together with the tail estimate. ◻

The term $B$ records the within-cell variance lost when a continuous Mellin mode is replaced by its weighted cell mean. It is determined by the coordinate embedding, before imposing the arithmetic span.

# The arithmetic defect without RH

There is always the exact operator identity $$\label{eq:exactdefect}
 \mathcal A_M^P=\mathcal A_M^0-\mathcal E_M,\qquad
 \mathcal E_M=UR_MDR_MU^*\ge0.$$ Write its kernel as $E_M(t,u)$. If $v_M(t)=\sum_{n\le M}\overline{h_n(t)}b_n$, then $$\label{eq:diagdefect}
 E_M(t,u)=\langle Dv_M(t),Dv_M(u)\rangle,\qquad
 E_M(t,t)=\lVert Dv_M(t)\rVert^2.$$ Operator positivity here does not mean entrywise nonnegativity of the off-diagonal kernel.

For a bounded interval $A$ in unfolded coordinates, the positive local defect has trace $$\label{eq:Delta}
 \Delta_M(A;t_0)=\frac1{L_M}\int_A E_M(t_M(x),t_M(x))\,dx.$$ It is exactly the difference between the expected counts for the unfolded comparison and arithmetic processes. If it tends to zero for every bounded $A$, local trace-norm continuity of Fredholm determinants transfers the sine limit to the arithmetic process. Under RH it is identically zero. For the full arithmetic defect without RH, its vanishing has not been proved here.

<a id="prop:blind"></a>
**Proposition 9** (Blindness to fixed finite-rank defects). *Replace $D$ by any fixed finite-rank orthogonal projection $F$ and $P$ by $I-F$ in [\[eq:covariances\]](#eq:covariances). The resulting unfolded processes still converge to the sine$_2$ process at every fixed center.*

*Proof.* The vectors $v_M(t_M(x))/\sqrt{L_M}$ are uniformly bounded for bounded $x$, by Theorem [7](#thm:sine). Each fixed coordinate tends uniformly to zero. Approximation of any fixed vector by a finite coordinate head shows uniform weak convergence to zero. Projection onto the fixed finite-dimensional range of $F$ therefore tends to zero in norm, uniformly on bounded $x$. Cauchy--Schwarz gives local uniform convergence of the normalized defect kernel to zero. The same determinant domination as in Theorem [7](#thm:sine) proves the conclusion. ◻

For example, $P_0=I-b_1\otimes b_1$ has a certain hole at site $1$, while its Mellin kernel differs by only $h_1(t_M(x))\overline{h_1(t_M(y))}/L_M$. This comparison projection is not identified with $P$. It establishes that a leading sine limit alone cannot distinguish identity from every proper projection.

## A zero mode survives in the next order

For the zero $\rho$ of Theorem [1](#thm:zero), set $$\label{eq:Frho}
 F_\rho(t)=(Ur_\rho)(t)
  =\sum_{n\ge1}\frac{\overline{m_\rho(n)}m_{1/2+it}(n)}{w_n},\qquad
 F_{\rho,M}=UR_Mr_\rho.$$ This series converges absolutely, uniformly for real $t$, since its terms are $O(n^{-\beta-1/2})$. It also converges analytically in the half-plane $\Im t<\beta-1/2$. With $\delta=\beta-1/2$, its value at the interior complex point $\gamma-i\delta$ is $c_\rho>0$. Thus it is not identically zero, and its real zeros are discrete. Moreover, $$\label{eq:Ftail}
 \sup_{t\in\mathbb R}|F_{\rho,M}(t)-F_\rho(t)|
 =O_\rho(M^{1/2-\beta}).$$

<a id="prop:pole"></a>
**Proposition 10** (The zero's displacement in its Mellin profile). *The function $F_\rho$ has a meromorphic continuation to $\Im z<\beta+1/2$ of the form $$\label{eq:pole}
 F_\rho(z)=\frac1{\delta+i(z-\gamma)}+H_\rho(z),$$ where $H_\rho$ is holomorphic on that half-plane. In particular, its continued profile has a genuine pole at $z=\gamma+i\delta$.*

*Proof.* Set $q=1/2+iz+\overline\rho$. Uniformly on compact sets of $z$, $$\frac{\overline{m_\rho(n)}m_{1/2+iz}(n)}{w_n}
 =n^{-q}\bigl(1+O_{\rho,z}(n^{-1})\bigr).$$ Subtracting $\zeta(q)$ from the series leaves a normally convergent holomorphic series on $\Re q>0$. The function $\zeta(q)-1/(q-1)$ is holomorphic there, and $q-1=\delta+i(z-\gamma)$, proving the assertion. ◻

This is an explicit analytic signature of horizontal displacement from the critical line. It does not supply a uniform real-axis lower bound near large $|\gamma|$, because the remainder is not controlled uniformly in $\rho$.

The contribution of $\Pi_\rho$ to the unscaled defect kernel is $F_{\rho,M}(t)\overline{F_{\rho,M}(u)}/c_\rho$. For the comparison projection $I-\Pi_\rho$ this yields the expansion $$\label{eq:zerosecond}
 \kappa_M^{I-\Pi_\rho}(x,y)
 =S_\phi(x,y)-\frac{B(t_0,t_0)+|F_\rho(t_0)|^2/c_\rho}{L_M}
       +O_{\rho,t_0,R}(L_M^{-2}).$$ Here the polynomially decaying tail in [\[eq:Ftail\]](#eq:Ftail), divided by $L_M$, is eventually $O(L_M^{-2})$. Thus the fixed mode changes the second-order coefficient at every center outside a discrete exceptional set, even though it does not change the leading sine process.

For the actual arithmetic projection we have a lower bound, not an asserted full expansion: $$\label{eq:secondlower}
 \liminf_{M\to\infty}L_M\Delta_M(A;t_0)
 \ge\frac{|A|\,|F_\rho(t_0)|^2}{c_\rho}.$$ Indeed $D\ge\Pi_\rho$ bounds the defect diagonal below, and uniform convergence in [\[eq:Ftail\]](#eq:Ftail) proves the displayed inequality. No completeness of the zero modes in $S^\perp$ is assumed. The full defect could contain infinitely many further directions, and no upper bound follows from this rank-one argument.

Even an exceptional center retains the fixed mode at a finite order. If $F_\rho$ has a zero of order $m$ at $t_0$, Taylor expansion and [\[eq:Ftail\]](#eq:Ftail) give, for bounded $A$ of positive measure, $$\label{eq:higherorder}
 \liminf_{M\to\infty}L_M^{2m+1}\Delta_M(A;t_0)
 \ge\frac{(2\pi)^{2m}|F_\rho^{(m)}(t_0)|^2}{c_\rho(m!)^2}
       \int_A x^{2m}\,dx>0.$$ The order $m$ is finite by analyticity. This lower bound also allows $m=0$ and then recovers [\[eq:secondlower\]](#eq:secondlower).

## A fixed-window Mellin deficit criterion for RH

For a bounded measurable $I\subset\mathbb R$ of positive Lebesgue measure, define $$\label{eq:windowdef}
 d_M(I)=\mathbb E|Y_M^0\cap I|-\mathbb E|Y_M^P\cap I|
       =\int_I E_M(t,t)\,\frac{dt}{2\pi}\ge0.$$ Both expectations are finite for each $M$, even though they need not stay bounded as $M\to\infty$.

<a id="thm:window"></a>
**Theorem 11** (Faithful unscaled window criterion). *For every prescribed bounded measurable $I$ of positive measure, $$\label{eq:windowRH}
 \mathrm{RH}\quad\Longleftrightarrow\quad\liminf_{M\to\infty}d_M(I)=0.$$ Under RH all the $d_M(I)$ vanish. If RH fails, any zero $\rho$ with $\Re\rho>1/2$ gives $$\label{eq:windowlower}
 \liminf_{M\to\infty}d_M(I)
 \ge\frac1{c_\rho}\int_I|F_\rho(t)|^2\,\frac{dt}{2\pi}>0.$$*

*Proof.* The first implication follows from $D=0$. If RH fails, choose a right-half-strip zero and apply $D\ge\Pi_\rho$ inside [\[eq:windowdef\]](#eq:windowdef). Uniform convergence of $F_{\rho,M}$ gives the non-strict inequality in [\[eq:windowlower\]](#eq:windowlower). Analyticity and nonvanishing of $F_\rho$ imply that its real zero set has measure zero, so its squared modulus has a strictly positive integral on $I$. ◻

This criterion retains an absolute deficit which leading normalization can erase. It is a proved equivalence, not a proof that the deficit tends to zero. The sequence $d_M(I)$ is not claimed to be monotone or convergent when RH is false.

# Why an uncut Mellin DPP is unavailable

<a id="prop:nonlocal"></a>
**Proposition 12**. *For every bounded measurable $I\subset\mathbb R$ of positive measure, $\mathbf 1_I UPU^*\mathbf 1_I$ is not trace class. This assertion does not assume RH.*

*Proof.* Set $x_d=\sqrt d\,g_d\in S$. Splitting the weighted sum at $n=d$ gives $\lVert x_d\rVert_H^2\le2$. Each fixed coordinate tends to zero, so $x_d\rightharpoonup0$. Equation [\[eq:genmellin\]](#eq:genmellin) gives on the Mellin line $$(Ux_d)(t)=\frac{\zeta(1/2+it)}{1/2+it}
               \bigl(d^{-1/2}-d^{-it}\bigr).$$ Hence, by dominated convergence on $I$, $$\lVert \mathbf 1_I Ux_d\rVert^2\longrightarrow
 \int_I\left|\frac{\zeta(1/2+it)}{1/2+it}\right|^2\frac{dt}{2\pi}>0.$$ Zeros of the analytic zeta function are discrete, so this integral is positive. Because $Px_d=x_d$, the operator $\mathbf 1_I UP$ is not compact. Trace class of $(\mathbf 1_I UP)(\mathbf 1_I UP)^*=\mathbf 1_I UPU^*\mathbf 1_I$ would imply that $\mathbf 1_I UP$ is Hilbert--Schmidt, hence compact, a contradiction. ◻

Thus the uncut continuum projection does not meet the local trace-class requirement for an ordinary locally finite DPP. The integer DPP and every finite-cutoff continuum process remain well defined.

# What would advance the RH argument

The paper provides several equivalent targets, but no estimate proving one of them:

1.  **Signed capacity growth:** prove $C_N\to\infty$, equivalently divergence of the nonnegative series in [\[eq:gain\]](#eq:gain). This requires a lower bound surviving the cancellation in $\eta_N$.

2.  **Residue-class saturation:** prove $1-p_N\to0$. The lifting error is already controlled by [\[eq:crtgap\]](#eq:crtgap).

3.  **An absolute Mellin deficit bound:** prove $\liminf_M d_M(I)=0$ for one prescribed positive-measure bounded window. Control only after division by $\log M$ does not supply this.

A lower bound $C_N\ge a_N$ with a rigorously proved $a_N\to\infty$ would settle RH through existing completeness theory. A theorem giving the sine limit alone would not supply this bound: Proposition [9](#prop:blind) gives explicit counterexamples for general projections. Conversely, a hypothetical off-critical zero imposes the explicit capacity ceiling [\[eq:zerocap\]](#eq:zerocap) and the unscaled deficit floor [\[eq:windowlower\]](#eq:windowlower).

#### Montgomery and Hilbert--Pólya.

The sine kernel satisfies $$\rho_2(x,y)=1-\left(\frac{\sin\pi(x-y)}{\pi(x-y)}\right)^2$$ and is the spectral projection $\mathbf 1_{[-\pi,\pi]}(-i\,d/dx)$ on $L^2(\mathbb R)$, with the differential operator on domain $H^1(\mathbb R)$. This is a continuous-spectrum free operator. A bridge to Montgomery requires identifying statistics of actual zeta ordinates, not just obtaining the same auxiliary limiting law. A Hilbert--Pólya result would require an independently specified arithmetic self-adjoint operator and a proved spectral identity with completed zeta. Neither bridge is constructed here. The distinction between known pair-correlation results and the full conjectural regime is reviewed in [Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh](https://arxiv.org/abs/2306.04799).

#### Publication assessment.

The most coherent prospective contribution is the explicit arithmetic vacancy formulation together with the distinction between leading universality and defect-sensitive observables, particularly Theorems [8](#thm:second) and [11](#thm:window). Determinantal existence, Schur complements, and standard sine-process consequences should be presented as tools rather than independent originality claims. Before submission, the precise novelty of these formulations needs comparison with the zero-obstruction and approximation literature, and the proofs need external specialist review. Nothing in the present draft justifies an upgraded claim of proximity to an RH proof: the decisive arithmetic upper or lower estimate remains open.

## References
- B. Bagchi, *On Nyman, Beurling and Báez-Duarte's Hilbert space reformulation of the Riemann hypothesis* (2006), [arXiv:math/0607733](https://arxiv.org/abs/math/0607733).

- J.-F. Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, Advances in Mathematics **170** (2002), 56--70, [arXiv:math/0103058](https://arxiv.org/abs/math/0103058).

- J. B. Hough, M. Krishnapur, Y. Peres and B. Virág, *Determinantal Processes and Independence*, Probability Surveys **3** (2006), 206--229, [arXiv:math/0503110](https://arxiv.org/abs/math/0503110).

- R. Lyons, *Determinantal probability measures*, Publications Mathématiques de l'IHÉS **98** (2003), 167--212, [arXiv:math/0204325](https://arxiv.org/abs/math/0204325).

- A. Soshnikov, *Determinantal random point fields*, Russian Mathematical Surveys **55** (2000), 923--975, [arXiv:math/0002099](https://arxiv.org/abs/math/0002099).

- S. Darses and E. Hillion, *On probabilistic generalizations of the Nyman--Beurling criterion for the zeta function*, [arXiv:1805.06733](https://arxiv.org/abs/1805.06733).

- S. Baluyot, D. A. Goldston, A. I. Suriajaya and C. L. Turnage-Butterbaugh, *An unconditional Montgomery Theorem for Pair Correlation of Zeros of the Riemann Zeta Function*, [arXiv:2306.04799](https://arxiv.org/abs/2306.04799).
