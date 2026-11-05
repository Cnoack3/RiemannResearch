# One finite Pareto fit and the Burnol obstruction to a sign test

Let $P(n)=1/[n(n+1)]$ and $Q(n)=1/[\zeta(2)n^2]$, $n\ge1$. For the squarefree conductors $2\le d\le M+1$, let $f_{P,M}$ and $f_{Q,M}$ denote the respective projections of 1, $r_M=1-f_{P,M}$, and $E_M=\|r_M\|_P^2$. For any included conductor $m$ write
$$
 a_{M,m}=\langle g_m,r_M\rangle_Q,\qquad g_m(n)=\{n/m\}.
$$
This scalar requires the Pareto Gram solution and one independently evaluated row of complete $Q$ inner products. The $Q$-normal equation also identifies it with $\langle g_m,f_{Q,M}-f_{P,M}\rangle_Q$.

**Exact arithmetic comparison (paper proof).** Write $w_m(n)=m\lfloor n/m\rfloor/n$. The identities $\zeta(2)Q(n)=(1+1/n)P(n)$ and $\langle g_m,r_M\rangle_P=0$ give
$$
 \zeta(2)m a_{M,m}=\sum_nP(n)r_M(n)\frac{m g_m(n)}n
 =E_M-\sum_{n\ge m}P(n)r_M(n)w_m(n).
$$
In the last equality, $mg_m(n)/n=1-w_m(n)$ and $\langle 1,r_M\rangle_P=E_M$ by orthogonality. Since $0\le w_m\le1$ and $\sum_{n\ge m}P(n)=1/m$ exactly, Cauchy–Schwarz gives
$$
 \left|\zeta(2)m a_{M,m}-E_M\right|
 \le \frac{\|\mathbf1_{[m,\infty)}r_M\|_P}{\sqrt m}
 \le \sqrt{\frac{E_M}{m}} .
$$
The companion Lean development obtains the same exact signed remainder in $Q$ coordinates and the squared upper bound $m(\zeta(2)m a_{M,m}-E_M)^2\le4 E_M$ via equivalence of the norms. The paper argument gives the sharper constant $1$. In particular $a_{M,m}\le0$ implies $E_M\le1/m$.

**Where the published lower bound applies.** Map any sequence $v$ to the function taking value $v(n)$ on $(1/(n+1),1/n]$ and zero on $(1,\infty)$. This embedding in $L^2(0,\infty;dt)$ is isometric for the $P$ norm because those intervals have length $P(n)$. It sends 1 to $\chi=\mathbf1_{(0,1]}$. Up to interval endpoints, it sends $g_d$ exactly to
$$
 t\longmapsto \{1/(dt)\}-\{1/t\}/d.
$$
Indeed write $1/t=n+s$, $0\le s<1$. Then $\{(n+s)/d\}=\{n/d\}+s/d$. For $t>1$ the two terms cancel. Burnol's space $B_\lambda$ consists of all finite combinations of $\{\theta/t\}$, $\lambda\le\theta\le1$. Both parameters $1/d$ and $1$ lie in this interval at $\lambda=1/(M+1)$. Hence the image of the finite squarefree trial space is a subspace of $B_{1/(M+1)}$, and
$$
 E_M\ \ge\ D(1/(M+1))^2.
$$
Burnol's Theorem 1.3 implies $E_M\ge c/\log(M+1)$ for some $c>0$ and all sufficiently large $M$. The result holds unconditionally. In the case where RH fails Burnol explains that the unrestricted approximation distance already stays positive. In the case where RH holds the zero sum in Theorem 1.3 is strictly positive. Bagchi's discrete Hilbert space uses exactly the $P$ appearing here. [Burnol, Theorems 1.1–1.3, pp. 2–3](https://arxiv.org/pdf/math/0103058) · [Bagchi, p. 1 and Remark 8](https://arxiv.org/pdf/math/0607733)

**Consequence.** At the prime diagonal $M=m=p$, all sufficiently large primes satisfy
$$
 a_{p,p}>0,\qquad
 \frac{\zeta(2)p\,a_{p,p}}{E_p}=1+O\!\left(\sqrt{\frac{\log p}{p}}\right).
$$
In particular the implication “infinitely many nonpositive prime entries imply RH” has an impossible antecedent. The viable one-entry criterion is $\liminf_{p\text{ prime}}p\,a_{p,p}=0$, allowing positive entries. By monotonicity and convergence of the Pareto distances, the full prime limit exists and equals $\operatorname{dist}_P(1,V)^2/\zeta(2)$. Thus the one-entry criterion still requires proving that the distances tend to zero. The comparison also yields an unconditional positive lower bound of order $1/\log p$ for the scaled entry $p\,a_{p,p}$.

At a general schedule $M=M(m)$ with $g_m$ included, the same sign obstruction applies whenever $m/\log(M+1)\to\infty$. A schedule with exponentially many conductors relative to its probe would require separate analysis. The comparison with the published lower bound is a paper argument; the library declaration isolates its finite numerical hypothesis.
