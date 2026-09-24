# The reciprocal-charge Riesz vectors have a positive limiting norm

Status: rigorous mathematical proof; the full limit below has not been
Lean-verified. A draft for the exact upper-window reindexing was explored but has not
been kernel-verified or added as a compiled project module. No novelty claim is made.

Put

\[
m(M)=\sum_{1\le n\le M}\frac{\mu(n)}n,\qquad
a_N(k)=m(\lfloor N/k\rfloor)-m(\lfloor N/(k+1)\rfloor),\qquad
b_N(k)=m(\lfloor N/(k+1)\rfloor).
\]

The existing repository providers give \(m(M)\to0\), \(|m(M)|\le1\),
and \(\sum_{k=1}^N a_N(k)^2\le10\). Define

\[
q_N(k)=\frac{m(\lfloor N/k\rfloor)}k-
       \frac{m(\lfloor N/(k+1)\rfloor)}{k+1}.
\]

The actual reciprocal-charge Riesz vector \(Q_N\) has physical coordinate
\(k(k+1)q_N(k)\) and therefore

\[
\|Q_N\|_P^2=\sum_{k=1}^N k(k+1)q_N(k)^2.
\]

## 1. Exact square-energy separation

Let

\[
I_N=\{k\ge1:k(k+1)\le N\},\qquad
J_N=\{1\le n\le N:N<\lfloor N/n\rfloor(\lfloor N/n\rfloor+1)\}.
\]

The window
\(W_{N,k}=\{n:N/(k+1)<n\le N/k\}\) contains at most one integer
when \(N<k(k+1)\). Different windows are disjoint, and
\(n\in W_{N,k}\) precisely when \(\lfloor N/n\rfloor=k\).
Consequently the following identity is exact:

\[
A_N:=\sum_{k=1}^N a_N(k)^2
=\underbrace{\sum_{k\in I_N}a_N(k)^2}_{L_N}
+\sum_{n\in J_N}\frac{\mu(n)^2}{n^2}.
\]

If \(k(k+1)\le N\), the existing harmonic-window bound gives
\(|a_N(k)|\le2/k\). For every fixed positive \(k\), PNT gives
\(a_N(k)\to0\). Extend the summand defining \(L_N\) by zero outside
\(I_N\); its absolute value is bounded by \(4/k^2\). Dominated
convergence proves \(L_N\to0\).

Every fixed \(n\ge1\) belongs to \(J_N\) once \(N\ge n^2\).
Indeed, write \(N=qn+r\), where \(q=\lfloor N/n\rfloor\),
\(0\le r<n\), and then \(q\ge n\). Thus

\[
N=qn+r<qn+n\le qn+q\le q(q+1).
\]

Since \(\mu(n)^2/n^2\le1/n^2\), dominated convergence yields

\[
\boxed{A_N\longrightarrow S:=\sum_{n=1}^\infty\frac{\mu(n)^2}{n^2}.}
\]

## 2. The remaining exact terms vanish

Define

\[
R_N=\sum_{k=1}^N\frac{a_N(k)^2}{k},\quad
B_N=\sum_{k=1}^N\frac{b_N(k)^2}{k(k+1)},\quad
C_N=\sum_{k=1}^N\frac{a_N(k)b_N(k)}k.
\]

For every positive integer \(K\), the uniform bound \(A_N\le10\) gives

\[
0\le R_N\le\sum_{k=1}^{K}\frac{a_N(k)^2}{k}+
\frac{10}{K+1},
\]

where \(a_N(k)=0\) for \(k>N\). The finite sum tends to zero. First
choosing \(K\), then \(N\), proves \(R_N\to0\).

For each fixed \(k\), \(b_N(k)\to0\), and
\(b_N(k)^2/[k(k+1)]\le1/[k(k+1)]\). This latter series sums to one,
so \(B_N\to0\).

Finite Cauchy--Schwarz, retaining the signed mixed term, gives

\[
C_N^2\le
\left(\sum_{k=1}^N\frac{k+1}{k}a_N(k)^2\right)B_N
=(A_N+R_N)B_N\le20B_N.
\]

Therefore \(C_N\to0\). Finally, direct algebra gives the exact equality

\[
k(k+1)q_N(k)^2=
\frac{k+1}{k}a_N(k)^2+
\frac{2a_N(k)b_N(k)}k+
\frac{b_N(k)^2}{k(k+1)},
\]

and hence

\[
\boxed{\|Q_N\|_P^2=A_N+R_N+2C_N+B_N\longrightarrow S.}
\]

The absolutely convergent Euler product evaluates this constant:

\[
S=\prod_p(1+p^{-2})=\frac{\zeta(2)}{\zeta(4)}
=\frac{15}{\pi^2}.
\]

## Consequence and limitation

Together with the proved weak convergence \(Q_N\rightharpoonup0\), this
shows that the reciprocal-charge functionals cancel on every fixed Hilbert
vector while their representing vectors retain positive energy. In
particular \(Q_N\) does not converge strongly to zero and has no norm
convergent subsequence. This does not supply residual vanishing or RH.

For every fixed cutoff \(K\), the energy on coordinates \(1,\ldots,K\)
tends to zero, while the complete energy tends to \(15/\pi^2\). The
remaining mass is exactly accounted for by the isolated quotient windows.
