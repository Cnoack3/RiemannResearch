# Character moments of the ambient valuation tower

Let \(Q(n)=1/(\zeta(2)n^2)\) and \(P(n)=1/[n(n+1)]\) on the positive integers. Write \(\mathcal F_b=\sigma(v_p(N):p\le b)\), \(R_b=\prod_{p\le b}p\), and \(S=\prod_{p\le b}p^{v_p(N)}\). For mixed packets use \(J_k(n)=\sum_{e\mid k}\mu(k/e)(n\bmod e)\). The arguments also apply to arbitrary periodic profiles, including at nonsquarefree conductors. Complex covariance is linear in its first argument. Write \(\Pi_b^\nu=E_\nu[\,\cdot\mid\mathcal F_b]\), for \(\nu=Q,P\).

## The rough cofactor and its Fourier transform

For a smooth \(s\) and \((z,R_b)=1\), unique factorization gives \(N=sz\) on the fibre \(S=s\). Put \(A_b=\sum_{(z,R_b)=1}z^{-2}=\zeta(2)\prod_{p\le b}(1-p^{-2})\). The joint mass factors directly:
\[
 Q(S=s,Z=z)=\frac{1}{\zeta(2)s^2z^2},\quad
 Q(S=s)=\frac{A_b}{\zeta(2)s^2},\quad Q(Z=z)=\frac{z^{-2}}{A_b}.
\]
Thus \(Z=N/S\) is independent of the whole revealed vector. Choose a common period \(K\) for all packets and first suppose every prime divisor of \(K\) is revealed. Then \(Z\bmod K\in U_K=(\mathbb Z/K)^\times\). For every character on \(U_K\),
\[
 t_b(\chi)=E_Q\chi(Z)=\prod_{p>b}\frac{1-p^{-2}}{1-\chi(p)p^{-2}},\qquad t_b(1)=1 .
\]
Indeed \(v_p\) has law \((1-p^{-2})p^{-2j}\), whose character transform is that geometric factor. On any finite set of primes the transforms multiply. The products of sampled characters stabilize for each integer, so dominated convergence gives the asserted expectation. The deterministic product converges absolutely in the sense \(\sum_p|\text{factor}-1|<\infty\), since each deviation is at most \(2/(p^2-1)\). Its value is nonzero. Equivalently inflate \(\chi\) to modulus \(m=\operatorname{lcm}(K,R_b)\). Zero extension to nonunits gives exactly \(L(2,\chi_m)/L(2,1_m)\). This is the normalized series in Lean.

For a periodic profile \(f\), set
\[
 a^f_\chi(s)=|U_K|^{-1}\sum_{u\in U_K} f(su)\overline{\chi(u)} .
\]
Fourier inversion holds for **every** smooth \(s\), including those sharing factors with \(K\), since the variable being expanded is \(u\). Thus the conditional mean is \(\sum_\chi a^f_\chi(s)t_b(\chi)\). With \(\lambda=\chi\bar\psi\), the raw and centered character Gram matrices are respectively
\[
 T_b(\chi,\psi)=t_b(\lambda),\qquad
 C_b(\chi,\psi)=t_b(\lambda)-t_b(\chi)\overline{t_b(\psi)} .
\]
The raw conditional packet Gram, the Gram of the conditional means, and the conditional residual Gram use respectively \(T_b,\ t_b t_b^*,\ C_b\), contracted as \(\sum_{\chi,\psi}a_\chi^f(s)\overline{a_\psi^g(s)}(\cdots)\). The last matrix is positive semidefinite by the variance identity. For packets of different conductors inflate both to their least common multiple. For any finite dictionary the same polarization yields every mixed term, with arbitrary real or complex coefficients.

## Individual layers and an averaged finite formula

Let \(p>b\) be the next prime, \(h_p(\chi)=(1-p^{-2})/(1-\chi(p)p^{-2})\), and suppose \(p\nmid K\). Given the earlier smooth part \(s\), the new mean is \(\sum_\chi a_\chi^f(s)\chi(p)^{v_p}t_p(\chi)\). Its covariance over \(v_p\) contracts the two coefficient rows with
\[
 D_p(\chi,\psi)=t_p(\chi)\overline{t_p(\psi)}
       [h_p(\chi\bar\psi)-h_p(\chi)\overline{h_p(\psi)}].
\]
Averaging in \(s\) gives the layer Gram. Equivalently, if \(V_b(f,g)=E_Q[(f-\Pi_b^Qf)\overline{(g-\Pi_b^Qg)}]\), then
\[
 e_p(f,g)=V_{p-1}(f,g)-V_p(f,g)
 =E_Q[(\Pi_p^Q-\Pi_{p-1}^Q)f\ \overline{(\Pi_p^Q-\Pi_{p-1}^Q)g}] .
\]
Every diagonal layer is nonnegative. A cross layer can have either sign.

There is also a closed finite sum for \(V_b\) with no sum over smooth integers. For \(d\mid K\) let \(q=K/d\). Expand \(u\mapsto f(du)\) on \(U_q\), with coefficients \(A^f_{d,\chi}\). A row written on \(U_K\) is its inflation and is zero outside the characters factoring through \(U_q\). For characters on \(U_q\), define the **unnormalized** moment
\[
 H_d(\lambda)=E_Q[1_{(N,K)=d}\lambda(N/d)]
              =\frac{L(2,\lambda\bmod q)}{d^2\zeta(2)} .
\]
Here \(H_d(1)=d^{-2}\prod_{p\mid q}(1-p^{-2})\), including at \(q=1\). On \((S,K)=d\), the conditional coefficient equals \(A^f_{d,\chi}\chi(S/d)\). Independence and \((N,K)=(S,K)\) give \(E[1_{(S,K)=d}\lambda(S/d)]t_b(\lambda)=H_d(\lambda)\). Substitution gives
\[
 \boxed{V_b(f,g)=\sum_{d\mid K}\sum_{\chi,\psi\in\widehat U_{K/d}}
 A^f_{d,\chi}\overline{A^g_{d,\psi}}\ H_d(\chi\bar\psi)
 \left(1-\frac{t_b(\chi)\overline{t_b(\psi)}}{t_b(\chi\bar\psi)}\right).}
\]
The factors are well-defined by nonvanishing. The formula covers repeated prime powers in \(K\). The trivial row and column make zero contribution. For each fixed bounded trial \(f\), \(V_b(f,f)\to0\). More explicitly, testing the observed approximation \(f(S)\) gives \(V_b(f,f)\le4\|f\|_\infty^2(1-\prod_{p>b}(1-p^{-2}))\). The constant depends on the trial's supremum norm.

### Initial primes, including primes dividing the conductor

For any \(b\), put \(m=\operatorname{lcm}(K,R_b)\). The cofactor residue probabilities on **all** classes modulo \(K\) are
\[
 w_b(v)=A_b^{-1}\!\!\sum_{\substack{1\le r\le m,\ r\equiv v\bmod K\\(r,R_b)=1}}\ \sum_{j\ge0}(r+jm)^{-2}.
\]
For \(b\) below a conductor prime this includes nonunit classes. Each inner sum is \(m^{-2}\zeta(2,r/m)\). The revealed part has finite residue law \(\pi_b=\delta_1\prod_{p\le b}(1-p^{-2})(I-p^{-2}T_p)^{-1}\), with \(T_p\) acting on row distributions by pushing a residue \(x\) to \(px\bmod K\). Each inverse is a finite rational matrix, also for a nonunit \(p\). Set \(F_b(s)=\sum_v w_b(v) f(sv)\) and similarly \(G_b\). Then for all \(b\),
\[
 V_b(f,g)=\sum_s\pi_b(s)\left[\sum_v w_b(v)f(sv)\overline{g(sv)}
                      -F_b(s)\overline{G_b(s)}\right].
\]
This follows by conditioning on the smooth part; the conditional law of the cofactor remains the same on each fibre. Adjacent differences now give the initial layers as exact expressions, with no extrapolation of a unit-group formula across a conductor prime.

## Periods ten and thirty

Let \(\chi(2)=i\) modulo five, \(\sigma=\chi^2\), \(\eta\) be the sign modulo three, and \(\theta=\eta\sigma\). On each gcd row the following entries give
\(J_K(du)=c+2\Re(a\chi(u))+e\eta(u)+h\theta(u)\), for \(u\in U_K\).
All omitted coefficients are zero. These real expansions determine the conjugate column as \(\bar a\).

| \(K\) | \(d\) | \(c\) | \(a\) | \(e\) | \(h\) |
|---:|---:|---:|---:|---:|---:|
| 10 | 1 | \(3/2\) | \(-5(1+i)/4\) | 0 | 0 |
| 10 | 2 | \(5/2\) | \(5(-1+i)/4\) | 0 | 0 |
| 10 | 5 | 4 | 0 | 0 | 0 |
| 10 | 10 | 0 | 0 | 0 | 0 |
| 30 | 1 | \(9/2\) | \((-10+5i)/4\) | \(-9/4\) | \(15/4\) |
| 30 | 2 | \(7/2\) | \((5+10i)/4\) | \(-9/4\) | \(-15/4\) |
| 30 | 3 | 3 | \((-10-20i)/4\) | 0 | 0 |
| 30 | 5 | 2 | 0 | \(-9\) | 0 |
| 30 | 6 | 5 | \((-20+10i)/4\) | 0 | 0 |
| 30 | 10 | 6 | 0 | \(-9\) | 0 |
| 30 | 15 | 8 | 0 | 0 | 0 |
| 30 | 30 | 0 | 0 | 0 | 0 |

For \(J_{10}\), the units \(1,3,7,9\) give \((-1,-1,4,4)\). For \(J_{30}\), the units \(1,7,11,13,17,19,23,29\) give \((1,-4,-2,1,8,11,13,8)\). All rows come from the Möbius sum. For example, \(J_{30}=r_{30}-r_{15}-r_{10}-r_6+r_5+r_3+r_2\). To obtain a cross Gram on period 30, use the same \(d\mid30\) in both rows. For \(J_{10}\) the corresponding coefficients are the period-ten row at \(d'=(d,10)\), multiplied by the character of \(d/d'\) on \(U_{10/d'}\).

Put \(\rho=L(2,\sigma\bmod5)/\zeta(2)\). For \(b\ge5\) the first example simplifies to
\[
 V_b(J_{10},J_{10})=6(1-|t_b(\chi)|^2)
       +\tfrac{25}{4}\rho\,\Im\!\left(t_b(\chi)^2/t_b(\sigma)\right).
\]
Indeed \(2|a|^2=25/4\) on \(5\nmid N\), of probability \(24/25\). The two squared coefficients are \(25i/8,-25i/8\); the difference of their unnormalized \(\sigma\)-moments is \(\rho\). This accounts for the signed second term.

For \(J_{30}\) the boxed sum uses exactly the four nonconstant columns \((\chi,\bar\chi,\eta,\theta)\) in the table. For a closed single-layer example take \(p=11\). The first two modes are fixed and the last two change sign. Set \(u=t_{11}(\eta)\), \(v=t_{11}(\theta)\), \(w=t_{11}(\sigma)\). Then
\[
 e_{11}(J_{30},J_{30})=
 \left[1-(120/122)^2\right]\left(\tfrac{36}{5}u^2+12v^2
                         -\tfrac{75}{4}\rho\,uv/w\right)>0 .
\]
The first two coefficients in the bracket are \(\sum_d H_d(1)e_d^2\) and \(\sum_d H_d(1)h_d^2\). For the cross coefficient, \(H_1(\sigma)=25\rho/18,\ H_2(\sigma)=5\rho/18\); the products \(e_d h_d\) are \(-135/16,135/16\). Strict positivity also follows directly from the \(5\mid N,\ 3\nmid N\) fibres, where only \(-9\eta\) varies. Both \(e_{11}(J_{10},J_{10})\) and \(e_{11}(J_{10},J_{30})\) vanish.

The all-residue calculation gives the following checks (rounded). The independent gcd-character calculation gives the same omitted Grams at cutoffs 5, 7, and 11.

| Prime | \(e_p(J_{10},J_{10})\) | \(e_p(J_{10},J_{30})\) | \(e_p(J_{30},J_{30})\) |
|---:|---:|---:|---:|
| 2 | 0.537247206 | −0.210019983 | 0.499615772 |
| 3 | 0.609837603 | −0.562805621 | 1.631783938 |
| 5 | 0.702751778 | −0.755841221 | 2.497703561 |
| 7 | 0.340166510 | −0.259429091 | 0.785947364 |
| 11 | 0 | 0 | 0.339885041 |

## Change of measure and complete mixed fits

Use \(B(n)=dP/dQ=\zeta(2)n/(n+1)\). For \(m=\operatorname{lcm}(K,R_b)\), a smooth part \(s\) and \(1\le r\le m\) with \((r,R_b)=1\), the **joint** Pareto mass is
\[
 W_s(r)=\sum_{j\ge0}P\{s(r+jm)\}
   =\frac{\psi((r+1/s)/m)-\psi(r/m)}{sm}.
\]
This follows by partial fractions, or by applying the repository progression identity with step \(sm\) and starting site \(sr\). Write \(D_s=\sum_{(r,R_b)=1}W_s(r)>0\), summing over one positive period. The conditional Pareto distribution is \(W_s(r)/D_s\). Equivalently \(\Pi_b^P f=E_Q[Bf\mid\mathcal F_b]/E_Q[B\mid\mathcal F_b]\). Once every conductor prime is revealed, the weighted character moments are \(t_{b,s}^P(\chi)=D_s^{-1}\sum_r W_s(r)\chi(r)\). Replacing \(t_b\) by \(t_{b,s}^P\) gives the full signed fibre covariance. Average it with the Pareto masses \(D_s\). At every cutoff the residue formula also applies directly with \(f(sr)\), including nonunits. The tilted cofactor law depends on \(s\); multiplying native-Q prime factors would omit this dependence.

There is a uniform quadratic-form comparison. On a fibre define \(v_\nu(f;s)=\operatorname{Var}_\nu(f\mid S=s)\). Minimizing over constant fits and using \(\zeta(2)s/(s+1)\le B(sz)\le\zeta(2)\) gives
\[
 \zeta(2)\frac{s}{s+1}Q(S=s)v_Q(f;s)
 \le P(S=s)v_P(f;s)\le\zeta(2)Q(S=s)v_Q(f;s).
\]
This applies to every joint trial, hence gives matrix inequalities in the positive-semidefinite order. It does not give entrywise inequalities on signed cross terms.

For an actual finite mixed dictionary \(\mathcal D\), take \(K=\operatorname{lcm}(2,\mathcal D)\), \(g=J_2=1_{\rm odd}\) and \(w(r)=[\psi((r+1)/K)-\psi(r/K)]/K\). The complete Pareto Gram \(G_{ij}=\sum_r w(r)J_i(r)J_j(r)\) and moment \(v_i=\sum_r w(r)g(r)J_i(r)\) give squared capture \(v^\top G^\dagger v\), with the Moore–Penrose inverse allowing linear dependence. Equivalently maximize \(2c^\top v-c^\top Gc\). Thus each finite calculation yields a genuine lower bound on the projection onto the full mixed closure \(M\).

For \(\mathcal D=(6,10,15,30)\) the finite optimum is approximately \(0.04310580066528\). Its coefficients are approximately \((-0.11099776,-0.08800004,0.03784767,-0.01015935)\). A rational witness gives the strict lower bound \(0.04310\): put \(Y=-111J_6-88J_{10}+38J_{15}-10J_{30}\), \(A_r=2000(r\bmod2)Y(r)-Y(r)^2\). Then the trial is \(Y/1000\), \(\min_r A_r=-1992900\), and the following exact integer calculation rounds every head summand down. The remaining tail has mass \(1/(N+1)\).

~~~python
from math import prod
D, N = 10**18, 10**6
def packet(n, primes):
    k = prod(primes)
    return sum((-1)**mask.bit_count() * (n % (k // prod(
        p for i, p in enumerate(primes) if mask >> i & 1)))
        for mask in range(1 << len(primes)))
def score(n):
    y = sum(c*packet(n, ps) for c, ps in zip(
        (-111,-88,38,-10), ((2,3),(2,5),(3,5),(2,3,5))))
    return 2000*(n % 2)*y-y*y
A = [score(r) for r in range(30)]
H = sum(D*A[n % 30]//(n*(n+1)) for n in range(1,N+1))
assert (min(A), H) == (-1992900, 43105758818158764267440)
assert H*(N+1) + D*min(A) > 43100*D*(N+1)
~~~

The earlier conductor-8192 enclosure is substantially tighter. Its full integer head was externally replayed; the Lean enclosure takes the corresponding finite inequality. For \(\ell=\log 2,\ z=J_2-\ell\mathbf1\), the mixed mean-zero property gives the exact gap
\[
 \ell(1-\ell)-\|P_M^P J_2\|_P^2=\inf_{m\in M}\|z-m\|_P^2 .
\]
The existing endpoint criterion identifies its vanishing with RH. For \(b\ge2\), \(z\) is already observed. Closing the gap requires finite **mixed** trials \(m_j\) with both \(\|z-\Pi_{b_j}^P m_j\|_P^2\to0\) and \(E_P|m_j-\Pi_{b_j}^P m_j|^2\to0\) along the same sequence. Their sum is the complete error. Ambient convergence controls each fixed trial. It supplies no cofinal construction with both properties. In the mixed largest-prime filtration each of \(J_{10},J_{30}\) already belongs to stage 5.

## Formal scope

[Character moments and the polarized rough series](ValuationCharacterGram.lean) · [Exact finite character syntheses of the physical packets](ValuationCharacterExamples.lean) · [Valuation projections, layers and Pareto progressions](PrimeValuationCovariance.lean) · [Mixed projection enclosure and evidence](../THEOREM_CATALOG_MIXED_CONDUCTOR_CRT_20261109.md)

`observed_fibre_mean` computes the actual Q Hilbert projection by normalized summation on the exact fibre. `sameFibre_iff_rough_multiple` characterizes its sites. `physical_fibre_moment`, `cutoff_hasProd`, and `unitProfile_covariance` give the cofactor mass ratio, its Euler product, and the polarized character Gram on arbitrary unit profiles. The Hilbert layer identity is formal in both metrics. The single finite gcd-stratum formula, its simplified numerical applications, the fibrewise density comparison, and the rational four-packet bound are paper derivations or external calculations. The repository checks the two character tables directly against the physical packets.
