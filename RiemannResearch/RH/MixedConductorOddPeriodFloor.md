# An odd-period lower bound for the mixed projection of parity

Put $P(n)=1/[n(n+1)]$, $n\ge1$, and work in the real Hilbert space
$\ell^2(P)$. Write $r_d(n)=n\bmod d$,
$J_q=\sum_{d\mid q}\mu(q/d)r_d$, $J_2(n)=n\bmod2$, and
$z=J_2-(\log2)\mathbf 1$. A conductor is mixed when it has at least
two distinct prime factors. Let $Q\ge1$ be odd. If $c$ belongs to the
closed span of all even mixed packets and all $Q$-periodic sequences,
then
$$
  \|z-c\|_P^2\ \ge\ \frac{21Q}{16(49Q^2-1)}
    > \frac{3}{112Q}.
$$
In particular this applies when all odd conductors used divide $Q$,
regardless of how large the even conductors are. With no odd packets the
floor is $7/256$. Thus in any saturating sequence of finite mixed fits,
the lcm of the odd conductors must tend to infinity. This necessary
condition alone is consistent with saturation.

## The dual functional

For $s\ge1$ define
$$
 A_s(f)=\sum_{n=Q}^{2Q-1}\sum_{u=0}^{2^{s-1}-1}
  [f(2^s n+2^{s-1}+u)-f(2^s n+u)],
 \qquad T_Q(f)=\sum_{s=1}^\infty4^{-s}A_s(f).
$$
The signed coefficients of $A_s$ on the integers in
$[2^sQ,2^{s+1}Q)$ are all $+1$ or $-1$, and the blocks are disjoint.
Weighted Cauchy–Schwarz gives absolute convergence and continuity of
$T_Q$ on the complete space. Its squared dual norm is exactly
$$
\begin{aligned}
 \|T_Q\|^2 &=\sum_{s=1}^\infty16^{-s}
       \sum_{m=2^sQ}^{2^{s+1}Q-1}m(m+1) \\
 &=\sum_{s=1}^\infty16^{-s}\frac{7(2^sQ)^3-2^sQ}{3}
 =\frac{Q(49Q^2-1)}{21}.
\end{aligned}
$$
Equality follows from the Riesz representer, the signed coefficient at
$m$ divided by $P(m)$. The finite sum on $[a,2a)$ follows by
telescoping $(m-1)m(m+1)/3$. The two geometric sums are
$\sum_{s\ge1}2^{-s}=1$ and $\sum_{s\ge1}8^{-s}=1/7$.

## Odd periods and even packets

For every $Q$-periodic $g$, $A_s(g)=0$. For each fixed $u$,
both $2^sn+u$ and $2^sn+2^{s-1}+u$ run through all residue
classes modulo $Q$, because $Q$ is odd. In particular $T_Q(\mathbf1)=0$.

Set $b_m(n)=r_{2m}(n)-r_m(n)$ for $m\ge1$. We claim
$T_Q(b_m)=Q/4$ for every $m$, including $b_1=J_2$.
Put $h_m(n)=m\lfloor n/(2m)\rfloor$. Integer division gives
$h_m(2n+1)=h_m(2n)$ and $b_m(n)=h_m(2n)-2h_m(n)$. Pairing
successive terms in each half of the finer block yields
$$
 A_s(b_m)=\tfrac12 A_{s+1}(h_m)-2A_s(h_m),
 \qquad A_1(h_m)=0.
$$
Consequently $\sum_{s=1}^K4^{-s}A_s(b_m)=2\cdot4^{-(K+1)}A_{K+1}(h_m)$.
There are $Q2^{s-1}$ pairs, each separated by $2^{s-1}$.
For $v(n)=n/2$ this gives $A_s(v)=Q4^s/8$ exactly.
Since $|h_m(n)-v(n)|<m$, the difference between the two signed sums
is bounded by $Q2^s m$, so $4^{-s}A_s(h_m)\longrightarrow Q/8$.
This proves the claim.

Write an even mixed conductor as $q=2^at$ with $a\ge1$ and odd
$t>1$. Splitting the divisor sum according to the exponent of two gives
$$
 J_{2^at}=\sum_{e\mid t}\mu(t/e)
            (r_{2^ae}-r_{2^{a-1}e})
          =\sum_{e\mid t}\mu(t/e)b_{2^{a-1}e}.
$$
Only the exponents $a$ and $a-1$ contribute, with opposite Möbius
values. Since $t>1$, $\sum_{e\mid t}\mu(t/e)=0$. Hence
$T_Q(J_{2^at})=0$. Continuity gives annihilation of the full stated
closed span. Finally $T_Q(z)=Q/4$, so
$\|z-c\|_P^2\ge(Q/4)^2/\|T_Q\|^2$, as claimed.

For an actual finite mixed window, $\mathbf1$ is orthogonal to all
mixed packets and $\|z\|_P^2=\log2-(\log2)^2$. Thus the squared error
of its best fit is exactly the difference between the target capture and
its attained capture. The numerical floor applies to that difference in
the same units.

This is an elementary discrete argument for the finite-odd restriction.
The Pareto normalization, packet definition and mixed mean zero are those
of the repository's integrated Ramanujan and screened-prime-power modules.
