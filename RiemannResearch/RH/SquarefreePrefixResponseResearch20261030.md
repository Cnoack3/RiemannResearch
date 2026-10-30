# Squarefree prefix responses: range decomposition and the remaining arithmetic bound

Date: 30 October 2026.

Status: paper proofs and exploratory numerical diagnostics. No Lean verification
was attempted for these new statements, as requested. The polylogarithmic bound
below remains **Open**; this note does not prove RH or the earlier mixed-trial
dyadic limit.

The three requested tasks are addressed as follows: decompose the lower-site
correction into multiplicative ranges; expand its actual normal equations over
the complete squarefree dictionary; and attempt a polylogarithmic estimate of
its action on the actual residual. The first two give exact identities. The
third gives rigorous finite inequalities and a shorter-range reduction, but no
uniform arithmetic bound.

## 1. Actual objects and the conditional target

Use the real Hilbert space with

$$
Q(m)=\frac1{\zeta(2)m^2},\qquad
\langle f,h\rangle_Q=\sum_{m\ge1}Q(m)f(m)h(m),\qquad
g_d(m)=\frac{m\bmod d}{d}.
$$

The canonical stage in `ZetaTwoOptimizerStage.lean` is

$$
D_N=\{d:2\le d\le N+1,\ d\text{ squarefree}\},\qquad
V_N=\operatorname{span}\{g_d:d\in D_N\}.
$$

Thus composite squarefree conductors are included. The zero atoms at
nonsquarefree indices are removed only when writing an invertible Gram matrix.
Let

$$
P_N=P_{V_N},\quad F_N=P_N1,\quad r_N=1-F_N,\quad
\varepsilon_N=\|r_N\|_Q^2,\quad
(Bf)(m)=\frac{f(m)}{m+1},\quad b_N=P_NBr_N.
$$

These are the ordinary canonical projections of the constant function. They
are not the constrained primorial minimum-energy optimizers underlying the
mixed-trial certificates. In particular their coefficients are determined by
the normal equations below, not prescribed Mobius coefficients.

For each positive physical site $n$, let $e_n(m)=\mathbf1_{m=n}/Q(n)$,
$k_{N,n}=P_Ne_n$, and $K_N(n,m)=k_{N,n}(m)$. Then

$$
\langle f,e_n\rangle_Q=f(n),\qquad
\|k_{N,n}\|_Q^2=K_N(n,n)\le\zeta(2)n^2.
\tag{1}
$$

Here $0<\varepsilon_N\le1$: the upper bound is projection contraction; for
positivity, all finitely many atoms vanish at a common positive period, while
the constant function does not. The empty stage also has positive residual.

Put $\beta_m=1/(m+1)$. Orthogonality gives the complete centered formula

$$
b_N(n)=\sum_{m\ge1}Q(m)r_N(m)K_N(n,m)(\beta_m-\beta_n).
\tag{2}
$$

All sums in (2) are absolutely convergent by Cauchy--Schwarz. The term $m=n$
is exactly zero. Define its lower and upper parts by $b_N(n)=L_N(n)+U_N(n)$,
where $L_N(n)$ sums over $m<n$ and $U_N(n)$ over $m>n$.

The existing declaration
`QSquarefreeLogResidualTail.riemannHypothesis_of_polylog_moving_head_bound`
consumes a bound

$$
\exists C\ge0,\ A\in\mathbb N,\quad
\forall N,\ 1\le n\le N:\quad
|b_N(n)|\le C(6+\log n)^A.
\tag{3}
$$

It supplies a conditional implication, not the arithmetic provider of (3).

## 2. Multiplicative ranges and exact boundary cancellation

Fix $N,n$. Write

$$
a_m=Q(m)r_N(m)K_N(n,m),\qquad
A_{N,n}(H)=\sum_{m=1}^H a_m,\qquad A_{N,n}(0)=0.
$$

Suppress $N,n$ in this section. The full normal equations imply
$A(\infty)=\langle r_N,k_{N,n}\rangle_Q=0$.

Partition the lower sites into the nonempty ranges
$[u,v]=[2^j,\min(2^{j+1}-1,n-1)]$. For each such range,

$$
\begin{aligned}
\sum_{m=u}^v a_m(\beta_m-\beta_n)
={}&(\beta_v-\beta_n)A(v)-(\beta_u-\beta_n)A(u-1)\\
&+\sum_{H=u}^{v-1}\frac{A(H)}{(H+1)(H+2)}.
\end{aligned}
\tag{4}
$$

Proof: substitute $a_m=A(m)-A(m-1)$ and shift the second finite sum.
The interior difference is $\beta_H-\beta_{H+1}=1/((H+1)(H+2))$.

On summing adjacent ranges, the boundary terms combine with the omitted
interior difference at each junction. At the final endpoint,
$\beta_{n-1}-\beta_n=1/(n(n+1))$. Therefore

$$
\boxed{L_N(n)=\sum_{H=1}^{n-1}
\frac{A_{N,n}(H)}{(H+1)(H+2)}.}
\tag{5}
$$

This identity includes $n=1$, when both sides vanish. Absolute convergence
also permits the complete version

$$
b_N(n)=\sum_{H\ge1}\frac{A_{N,n}(H)}{(H+1)(H+2)}.
\tag{6}
$$

For (6), write $\beta_m=\sum_{H\ge m}1/((H+1)(H+2))$ and interchange the
absolutely convergent sums; the centering term vanishes because $A(\infty)=0$.

Equations (4)--(6) preserve all signs. They do **not** assert that the physical
range contributions have opposite signs. The cancellation of artificial
summation boundaries is an algebraic identity, not an arithmetic estimate.

## 3. Complete normal-equation and divisor expansions

The nonzero atoms $g_d$, for distinct $d\ge2$, are linearly independent.
Indeed, if $f=\sum_dc_dg_d=0$, then $f(1)=\sum_dc_d/d=0$. For $m\ge2$,

$$
f(m)-f(m-1)=\sum_d\frac{c_d}{d}-\sum_{d\mid m}c_d.
$$

Consequently $\sum_{d\mid m}c_d=0$, and induction on the ordered conductors
gives $c_d=0$. Equality in the Hilbert space implies equality at every site
because every weight is positive. Thus the complete nonzero Gram is positive
definite.

With $v(m)=(g_d(m))_{d\in D_N}$, define

$$
G=\sum_{m\ge1}Q(m)v(m)v(m)^T,\qquad
\mu=\sum_{m\ge1}Q(m)v(m),\qquad
\alpha=G^{-1}\mu,\qquad x=G^{-1}v(n).
$$

Then $r_N(m)=1-v(m)^T\alpha$ and $K_N(n,m)=v(m)^Tx$. In particular both
factors in the signed source use the full, coupled inverse Gram.

For a finite prefix, set

$$
G_H=\sum_{m\le H}Q(m)v(m)v(m)^T,\quad
\mu_H=\sum_{m\le H}Q(m)v(m),\quad z_H=\mu_H-G_H\alpha.
$$

The exact prefix identity is

$$
\boxed{A_{N,n}(H)=x^Tz_H
=v(n)^TG^{-1}(\mu_H-G_HG^{-1}\mu).}
\tag{7}
$$

The normal equations give $z_\infty=0$, not $z_H=0$. Equivalently,
$z_H=-(\mu_{>H}-G_{>H}\alpha)$; the complete complementary tail cannot
be deleted.

To expose the arithmetic in each coordinate, define the finite sums

$$
T_N(H)=\sum_{m\le H}mQ(m)r_N(m),\qquad
R_N(t,H)=\sum_{m=t}^HQ(m)r_N(m).
$$

Since $g_d(m)=m/d-\lfloor m/d\rfloor$ and
$\lfloor m/d\rfloor=\sum_{q\ge1}\mathbf1_{qd\le m}$,

$$
(z_H)_d=\frac{T_N(H)}d-
\sum_{q=1}^{\lfloor H/d\rfloor}R_N(qd,H),\qquad d\in D_N.
\tag{8}
$$

Consequently

$$
\boxed{A_{N,n}(H)=K_N(n,1)T_N(H)
-\sum_{\substack{d\in D_N\\d\le H}}x_d
  \sum_{q\le H/d}R_N(qd,H).}
\tag{9}
$$

Every conductor $d>H$ is retained in the first term, since
$K_N(n,1)=\sum_{d\in D_N}x_d/d$. Although those raw atom columns are
proportional on the prefix, their complete Gram interactions still change
$x$ and $\alpha$. Removing them, or removing composite squarefree conductors,
would change the optimizer and the kernel. Equation (8) is a finite-prefix
identity; it does not split an infinite sum into potentially divergent floor
and linear pieces.

### Moving stages

If the next index $d=N+2$ is nonsquarefree, the stage is unchanged. Otherwise
put $w=(I-P_N)g_d$, $\gamma=\|w\|_Q^2>0$, and $t=\langle r_N,w\rangle_Q$.
The actual projection updates are

$$
r_{N+1}=r_N-\frac t\gamma w,\qquad
k_{N+1,n}=k_{N,n}+\frac{w(n)}\gamma w,\qquad
\varepsilon_{N+1}=\varepsilon_N-\frac{t^2}\gamma.
\tag{10}
$$

They follow by projecting onto the orthogonal direct sum
$V_N\oplus\mathbb Rw$. For $\chi_H=\mathbf1_{m\le H}$, expansion of the two
factors gives the exact signed update

$$
\begin{aligned}
A_{N+1,n}(H)-A_{N,n}(H)\\
={}&\frac{w(n)}\gamma\langle\chi_Hr_N,w\rangle_Q
-\frac t\gamma\langle\chi_Hw,k_{N,n}\rangle_Q
-\frac{tw(n)}{\gamma^2}\|\chi_Hw\|_Q^2.
\end{aligned}
\tag{11}
$$

At $H=\infty$, the first and third terms cancel and the middle term is zero.
For a finite prefix none of those simplifications is justified. The telescoping
energy identity controls $\sum t^2/\gamma\le1$, but does not by itself control
the evaluation factors and the three coupled prefix terms in (11).

## 4. A finite inequality for the actual residual

Define

$$
J_N(n)=\sum_{H=1}^{n-1}
\frac{A_{N,n}(H)^2}{(H+1)^2(H+2)},\qquad
h_n=\sum_{H=1}^{n-1}\frac1{H+2}\le\log n.
$$

Weighted Cauchy--Schwarz applied to (5) proves

$$
\boxed{|L_N(n)|^2\le h_nJ_N(n).}
\tag{12}
$$

Indeed, the two factors in each summand are
$A(H)/((H+1)\sqrt{H+2})$ and $1/\sqrt{H+2}$.
The harmonic bound follows, for example, by comparison with
$\int_1^n dx/x$. This is a bound on the actual coupled residual response;
it does not require a uniform norm bound for arbitrary coefficient inputs.
For arbitrary prefix data, Cauchy--Schwarz is sharp when $A(H)$ is a constant
multiple of $H+1$, so the harmonic loss cannot be removed by this algebra alone.

There is also an unconditional prefix bound that uses both parts of the
residual. Put $u_H=\|\chi_Hr_N\|_Q^2$ and $\varepsilon=\varepsilon_N$.
For

$$
y_H=\chi_Hr_N-\frac{u_H}{\varepsilon}r_N,
$$

orthogonality gives $P_Ny_H=P_N\chi_Hr_N$, and direct expansion gives
$\|y_H\|_Q^2=u_H(\varepsilon-u_H)/\varepsilon$. Pythagoras retains the exact
loss square:

$$
\begin{aligned}
\|P_N\chi_Hr_N\|_Q^2
&=z_H^TG^{-1}z_H\\
&=\frac{u_H(\varepsilon-u_H)}{\varepsilon}
  -\|(I-P_N)y_H\|_Q^2.
\end{aligned}
\tag{13}
$$

Since $A_{N,n}(H)=(P_N\chi_Hr_N)(n)$, evaluation Cauchy--Schwarz yields

$$
\boxed{A_{N,n}(H)^2\le K_N(n,n)\left[
\frac{u_H(\varepsilon-u_H)}{\varepsilon}
-\|(I-P_N)y_H\|_Q^2\right]
\le K_N(n,n)\frac{u_H(\varepsilon-u_H)}{\varepsilon}.}
\tag{14}
$$

The last inequality discards a nonnegative square and is therefore explicitly
weaker. Merely using $u_H(\varepsilon-u_H)/\varepsilon\le\varepsilon/4$
and (1) leads to

$$
J_N(n)\le\frac{\zeta(2)n^2\varepsilon_N}{4}
\left(\zeta(2)-\frac32\right),
\tag{15}
$$

because $\sum_{H\ge1}1/((H+1)^2(H+2))=\zeta(2)-3/2$.
This bound is polynomial in $n$, not polylogarithmic. Neither
$\varepsilon_N\le1$ nor the stage energy decrease in (10) repairs it.

## 5. The complete upper tail and a logarithmic cutoff

Let $v_n=\sum_{m\le n}Q(m)K_N(n,m)^2$. The upper-site part satisfies

$$
|U_N(n)|\le\frac{
\sqrt{(\varepsilon_N-u_n)(K_N(n,n)-v_n)}}{n+1}
\le\sqrt{\zeta(2)}.
\tag{16}
$$

This follows from $|\beta_m-\beta_n|\le1/(n+1)$ for $m>n$ and Cauchy--Schwarz
on the complete tail. No numerical truncation is used.

More generally, for $0\le H<n$ define the centered truncated response

$$
T_{N,n}^{\rm corr}(H)=\sum_{m\le H}
Q(m)r_N(m)K_N(n,m)(\beta_m-\beta_n).
$$

For $m>H$, both $\beta_m$ and $\beta_n$ lie in $[0,1/(H+2)]$. Hence

$$
\begin{aligned}
|b_N(n)-T_{N,n}^{\rm corr}(H)|
&\le\frac{\sqrt{K_N(n,n)}}{H+2}
\|\mathbf1_{m>H}r_N\|_Q\\
&\le\sqrt{\zeta(2)}\frac n{H+2}.
\end{aligned}
\tag{17}
$$

Write $\ell(n)=6+\log n$ and choose
$H(n)=\lfloor n/\ell(n)\rfloor$. Then $0\le H(n)<n$ and
$n/(H(n)+2)\le\ell(n)$, so

$$
\boxed{|b_N(n)-T_{N,n}^{\rm corr}(H(n))|
\le\sqrt{\zeta(2)}\ell(n).}
\tag{18}
$$

Thus a fixed polylogarithmic bound is needed only for the signed range
$m\le n/(6+\log n)$. The rest already costs at most one logarithm, uniformly
in $N$, without a convergence rate for residual tails. This is a quantitative
specialization of the repository's existing arbitrary-cutoff localization,
not a new proof of screening or determinant positivity.

For $H\ge1$, another application of (4) writes the remaining response as

$$
T_{N,n}^{\rm corr}(H)=
\frac{n-H}{(H+1)(n+1)}A_{N,n}(H)
+\sum_{h=1}^{H-1}\frac{A_{N,n}(h)}{(h+1)(h+2)}.
\tag{19}
$$

At $H=0$ it is zero. Replacing the evaluation index $n$ by $H$ in the kernel
would change (19); no iterative reduction to a smaller diagonal problem has
been proved.

## 6. What would close the estimate, and what is still missing

Either of the following would suffice, with constants independent of $N,n$:

1. $J_N(n)\le C^2\ell(n)^{2A}$ for $1\le n\le N$. Equations (12) and (16)
   would give $|b_N(n)|\le(C+\sqrt{\zeta(2)})\ell(n)^{A+1}$.
2. The weaker, signed requirement
   $|T_{N,n}^{\rm corr}(H(n))|\le C\ell(n)^A$. Equation (18) would give (3)
   with exponent $\max(A,1)$ and a larger constant.

Both are **Open**. The first may impose unnecessary control on individual
prefixes; it is a sufficient condition, not an established necessary one.
For the second, an explicit sufficient arithmetic estimate would be

$$
\left|v(n)^TG^{-1}(\mu_h-G_hG^{-1}\mu)\right|
\le C(h+1)\ell(n)^A,
\quad 1\le h\le H(n),\quad 1\le n\le N.
\tag{20}
$$

Substituting (20) into (19) costs at most another factor $\ell(n)$, since the
endpoint coefficient contributes at most one and the other weights sum to
at most $\log H(n)$. The precise unresolved issue is this uniform control of
the full inverse Gram acting on **partial** normal-equation errors, or an
estimate of their signed weighted combination that avoids (20).

The complete normal equations cancel the total source. They do not bound its
prefixes. Equations (8)--(11) display where a further divisor correlation or
moving-stage estimate must enter. Taking absolute values separately on the
two terms in (9), or on the three terms in (11), has no demonstrated uniform
saving. The available Hilbert-space bound still contains the evaluation scale
$n$ in (1). A common polylogarithmic estimate has not been derived.

## 7. Numerical check and its limits

The companion `SquarefreePrefixResponseDiagnostics20261030.md` supplies
reproducible float64 calculations of the actual complete Gram matrices for
$N=20,40,80,160,240$. Gram and multiplier moments are evaluated by complete
period formulas; a truncated physical tail is not substituted for the optimizer.
These are exploratory calculations, not interval-certified bounds.

At $N=240$, the largest sampled $|b_N(n)|$ occurs at $n=221$:

$$
b_{240}(221)\approx-0.04890554,\quad
L_{240}(221)\approx-0.04919754,\quad
U_{240}(221)\approx0.00029200.
$$

All eight multiplicative-range contributions to this lower response are
negative. Accordingly there is no cancellation between those ranges in this
sample. This does not disprove an asymptotic bound, but it rejects an assumed
universal opposite-sign pattern as motivation for one. The sampled maximum
of $J_N(n)$ increases across the tested stages; no boundedness or asymptotic
rate is inferred from these finite data.

## 8. Verification and relation to the existing library

- The centered physical kernel identity and unconditional localization are
  already supported by `QSquarefreeCorrectionKernel.lean` and
  `QSquarefreeKernelLocalization.lean`.
- The polylogarithmic implication (3) is the existing conditional theorem
  in `QSquarefreeLogResidualTail.lean`.
- Equations (4)--(20) here have paper derivations; their new assembly was not
  Lean-checked in this change. A symbolic finite Abel check for lengths 2--8
  returned zero discrepancies. Numerical consistency checks are documented
  separately and are not formal proofs.
- No completed screening, Gram determinant, or mixed-trial dominance result
  is claimed anew. The earlier signed dyadic mixed-trial obligation remains
  a distinct open route.

The useful outcome is an exact arithmetic representation, a finite residual
inequality retaining the projection loss square, and a logarithmic bound for
everything outside the shorter head. Establishing the uniform signed estimate
on that head remains the essential arithmetic task.
