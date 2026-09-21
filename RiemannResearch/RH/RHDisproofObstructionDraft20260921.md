# RH disproof attempt: the exact uniform gap and stronger spectral obstructions

21 September 2026. Ordinary mathematics throughout; no Lean was used.

No disproof of RH is obtained. This note identifies an exact necessary and sufficient missing estimate in the residue-space approach, proves strong convergence of the corresponding finite certificates whenever that estimate holds, and strengthens the earlier finite-mode obstruction to two classes of infinite Mellin mixtures. No novelty claim is made.

## 1. The precise remaining estimate

Write
\[
w_n=\frac1{n(n+1)},\qquad H=\ell^2(\mathbb N_{\ge1},w;\mathbb C),
\qquad g_d(n)=\frac{n\bmod d}{d},
\]
and let \(S\) be the closed span of \(g_d\), \(d\ge2\). Put \(e_1=\mathbf1_{\{1\}}\) and
\[
t_d=g_d-\frac1d e_1.
\]
All norms below include the entire infinite sequence, and all Gram matrices retain every mixed term.

Define
\[
\varepsilon_*=
\inf_{\substack{c\text{ finitely supported}\\\sum_{d\ge2}c_d/d=1}}
\sum_{n\ge2}\frac{\left|\sum_{d\ge2}c_dg_d(n)\right|^2}{n(n+1)}.
\tag{1}
\]
Then
\[
\boxed{\neg\mathrm{RH}\iff\varepsilon_*>0.}
\tag{2}
\]
Equivalently, a disproof in this formulation requires a constant \(\varepsilon>0\) such that, for **every** finitely supported complex coefficient family,
\[
\sum_{n\ge2}\frac{\left|\sum_dc_dg_d(n)\right|^2}{n(n+1)}
\ge\varepsilon\left|\sum_d\frac{c_d}{d}\right|^2.
\tag{3}
\]
The best possible constant in (3) is \(\varepsilon_*\). This is an equivalence, not an established positive lower bound.

**Why (2) is exact.** For \(f=\sum c_dg_d\) with \(f(1)=1\), the sum in (1) is \(\|f-e_1\|_H^2\). Thus \(\varepsilon_*=0\) implies \(e_1\in S\). Conversely, any approximation to \(e_1\) can have its first coordinate corrected exactly by adding \((1-f(1))2g_2\), so \(e_1\in S\) implies \(\varepsilon_*=0\).

The dilation operators \(D_mf(n)=f(\lfloor n/m\rfloor)\), with \(f(0)=0\), are bounded and preserve \(S\), because
\[
D_mg_d=g_{md}-g_m/d,\qquad \|D_mf\|_H^2=\|f\|_H^2/m.
\]
Since \(e_1=1-D_21\) and \(1=\sum_{j\ge0}D_{2^j}e_1\) in \(H\), membership of \(e_1\) and of the constant sequence \(1\) in \(S\) are equivalent. The weighted Nyman–Beurling–Baez-Duarte criterion identifies the latter with RH. See [Bagchi, Theorem 1](https://arxiv.org/pdf/math/0607733).

## 2. Finite certificates: bounded energy is the whole missing step

For \(M\ge2\), let
\[
T_M=\left(\sum_{n\ge2}w_n t_d(n)t_e(n)\right)_{2\le d,e\le M},
\qquad b_M=(1/d)_{2\le d\le M},
\]
\[
C_M=b_M^*T_M^{-1}b_M.
\]
These matrices are positive definite. To see this, a finite combination of the \(g_d\) is periodic, so vanishing on the tail implies vanishing everywhere. Successive differences of such a relation give
\[
\sum_dc_d/d-\sum_{d\mid n}c_d=0.
\]
The equation at \(n=1\), followed by induction over \(n=2,\ldots,M\), forces every coefficient to vanish.

Let \(z_M\) be the minimum-norm sequence satisfying
\[
z_M(1)=0,\qquad
\sum_{n\ge1}w_nz_M(n)g_d(n)=1/d\quad(2\le d\le M).
\tag{4}
\]
It belongs to \(\operatorname{span}(t_2,\ldots,t_M)\), its coefficients are \(T_M^{-1}b_M\), and
\[
\|z_M\|_H^2=C_M.
\]
Constrained quadratic minimization gives
\[
\varepsilon_*=\lim_{M\to\infty}\frac1{C_M},
\qquad
\boxed{\neg\mathrm{RH}\iff\sup_M C_M<\infty.}
\tag{5}
\]
Here \(C_M\) increases and \(1/\infty=0\).

There is an exact convergence identity, stronger than merely extracting a weakly convergent subsequence:
\[
\boxed{\|z_M-z_L\|_H^2=C_M-C_L\qquad(M\ge L).}
\tag{6}
\]
Indeed, \(z_M-z_L\) is orthogonal to \(t_2,\ldots,t_L\), whereas \(z_L\) belongs to their span. Pythagoras proves (6).

Consequently, an upper bound \(C_M\le B\) independent of \(M\) makes \(z_M\) strongly Cauchy. Its limit \(z\) satisfies every equation (4). Then
\[
v=2e_1-z\in S^\perp,\qquad v(1)=2,
\]
which proves \(S\ne H\) and hence disproves RH. Conversely, any such finite-energy tail certificate bounds all \(C_M\) above by \(\|z\|_H^2\).

Thus no further compactness theorem is missing for the canonical finite certificates. The unresolved input is exactly an **unconditional uniform upper bound** on their energies.

Every finite \(C_M\) is finite, irrespective of RH. The positive finite gaps \(1/C_M\) decrease toward the unknown gap; they are upper bounds on it. For example, using only \(g_2\) gives
\[
\varepsilon_2=\log2-\frac12>0.
\]
This does not imply \(\varepsilon_*>0\). A proof that all subsequent gaps remain bounded below is the missing arithmetic content.

## 3. A stronger obstruction: even bounded-frequency continuum mixtures require actual zeros

For \(s\) with \(\Re s>0\), define the coordinate sequence
\[
u_s(n)=n(n+1)\bigl(n^{-s}-(n+1)^{-s}\bigr).
\tag{7}
\]
It belongs to \(H\) when \(\Re s>1/2\). The basic residue identity is
\[
L_d(u_s):=\sum_{n\ge1}w_nu_s(n)g_d(n)
=(d^{-1}-d^{-s})\zeta(s).
\tag{8}
\]
The left side converges absolutely for \(\Re s>0\). For \(\Re s>1\), summation by parts proves (8) from
\(g_d(n)-g_d(n-1)=1/d-\mathbf1_{d\mid n}\); analytic continuation extends it to \(\Re s>0\), with the singularity at \(s=1\) removable. The analytic properties of zeta used here are recorded in [DLMF §25.2](https://dlmf.nist.gov/25.2).

**Theorem.** Fix \(\sigma\in[1/2,1)\) and \(T<\infty\). Let \(\mu\) be a finite complex Borel measure on \([-T,T]\), and define
\[
v(n)=\int_{-T}^T u_{\sigma+it}(n)\,d\mu(t).
\tag{9}
\]
Then
\[
\boxed{
L_d(v)=0\ \text{for every }d\ge2
\iff
\zeta(\sigma+it)\,d\mu(t)=0.
}
\tag{10}
\]
Thus \(\mu\) must be supported on the actual zeta zeros in the indicated vertical segment. There are finitely many such points, so every annihilating mixture in this class reduces to a finite sum of actual-zero modes.

**Proof.** Formula (8) can be integrated against \(\mu\). Indeed, uniformly for \(|t|\le T\),
\[
|n^{-\sigma-it}-(n+1)^{-\sigma-it}|
\le C_{\sigma,T}n^{-\sigma-1},
\]
which supplies an absolutely summable bound for the pairings with \(g_d\).

Set
\[
d\nu(t)=\zeta(\sigma+it)d\mu(t),\qquad B=\nu([-T,T]),
\qquad F(z)=\int e^{-itz}\,d\nu(t).
\]
The annihilation equations become
\[
F(\log d)=B d^{\sigma-1}\qquad(d\ge2).
\]
Hence
\[
G(z)=F(z)-B e^{(\sigma-1)z}
\]
is an entire function of exponential type with zeros at all \(\log d\). It satisfies \(|G(z)|\le A e^{K|z|}\) for some constants \(A,K\).

A nonzero entire function with this bound has only \(O(R)\) zeros in \(|z|\le R\), counting multiplicities. For completeness, factor out its possible zero at zero and apply Jensen's formula on the circle of radius \(2R\). Every zero within radius \(R\) contributes at least \(\log2\), while the upper bound for the Jensen integral is \(O(R)\). But \(\log d\le R\) supplies \(\lfloor e^R\rfloor-1\) distinct zeros. Therefore \(G\equiv0\).

On the real axis \(|F(x)|\le\|\nu\|_{\mathrm{TV}}\). Since \(\sigma<1\), letting \(x\to-\infty\) in \(F(x)=B e^{(\sigma-1)x}\) forces \(B=0\). Thus \(F\equiv0\). Its derivatives at zero show that every polynomial moment of \(\nu\) vanishes; polynomial density in \(C([-T,T])\) yields \(\nu=0\).

It follows that \(\mu\) is supported where \(\zeta(\sigma+it)=0\). Analyticity makes that zero set finite on this compact segment. The reverse implication in (10) follows immediately from (8). This proves the theorem.

For \(\sigma>1/2\), (9) is also a legitimate Bochner integral in \(H\): the kernel is continuous and bounded in \(H\) on the compact parameter interval. At \(\sigma=1/2\), the coordinatewise definition and the absolutely convergent pairings suffice; individual modes need not belong to \(H\).

## 4. On the critical line, the bounded-frequency annihilator must vanish

At \(\sigma=1/2\), theorem (10) expresses any annihilating mixture (9) as
\[
v=\sum_{j=1}^m a_j u_{s_j},\qquad s_j=1/2+i\gamma_j,
\]
with distinct ordinates. The expansion
\[
u_{s_j}(n)=s_j n^{1-s_j}+O(n^{-1/2})
\]
gives
\[
\sum_{n\le N}w_n|v(n)|^2
=\left(\sum_{j=1}^m|a_js_j|^2\right)\log N+O(1).
\tag{11}
\]
The diagonal terms produce the harmonic sum. Every off-diagonal leading term has a bounded partial sum \(\sum_{n\le N}n^{-1-i(\gamma_j-\gamma_k)}\); all remainder terms are summable.

Therefore
\[
\boxed{
\sigma=1/2,\quad v\in H,\quad L_d(v)=0\ (d\ge2)
\quad\Longrightarrow\quad \mu=0, v=0.
}
\tag{12}
\]
This covers continuous as well as discrete finite measures of bounded frequency. Continuous critical-line mixtures can have finite energy before the annihilation constraints are imposed; (12) states that imposing all of those constraints rules out a nonzero finite-energy result in this class.

## 5. Even unbounded-frequency discrete mixtures fail under absolute coefficient control

The logarithmic divergence extends to a countably infinite class with no bound on the ordinates.

**Theorem.** Let \(s_j=1/2+i\gamma_j\) have distinct ordinates and suppose
\[
\sum_j |a_js_j|<\infty.
\tag{13}
\]
Define \(v(n)=\sum_j a_j u_{s_j}(n)\), a coordinatewise absolutely convergent sum. Then
\[
\boxed{
\lim_{N\to\infty}\frac1{\log N}
\sum_{n\le N}\frac{|v(n)|^2}{n(n+1)}
=\sum_j |a_js_j|^2.
}
\tag{14}
\]
Every nonzero coefficient family therefore has infinite \(H\)-energy. The assertion holds whether or not the parameters are zeta zeros.

**Proof.** Set \(b_j=a_js_j\) and
\[
F(x)=\sum_j b_j e^{-i\gamma_jx}.
\]
Absolute convergence makes \(F\) bounded and uniformly continuous. Integrating each difference in (7), and using (13) to interchange the sum and integral, gives
\[
v(n)=n(n+1)\int_n^{n+1}x^{-3/2}F(\log x)\,dx.
\]
The interval in logarithmic coordinates has length \(\log(1+1/n)\to0\), and
\[
\frac{n(n+1)}{\sqrt n}\int_n^{n+1}x^{-3/2}\,dx
=\frac{2\sqrt{n+1}}{\sqrt{n+1}+\sqrt n}\longrightarrow1.
\]
Thus
\[
v(n)/\sqrt n=F(\log n)+o(1).
\]
Consequently the partial energy differs from
\(\sum_{n\le N}|F(\log n)|^2/n\) by \(o(\log N)\).

Uniformly approximate \(F\) by finite trigonometric sums. For each such sum, the logarithmically averaged diagonal terms converge to \(\sum|b_j|^2\), while every off-diagonal term converges to zero because its partial sums are bounded. The uniform approximation controls the error in these averages independently of \(N\). Passing first to the limit in \(N\), then in the finite approximation, proves (14).

The remainder in (14) is \(o(\log N)\); an \(O(1)\) remainder is not asserted for an arbitrary infinite family.

## 6. What the new obstructions settle, and what remains open

The conclusions have precise scopes:

| Construction | Proved obstruction |
|---|---|
| Finite certificates for increasingly many generators | Their norms must have a common finite upper bound to yield a disproof. If that bound holds, (6) already supplies strong convergence. |
| Finite-measure mixtures on a fixed vertical segment with \(1/2<\sigma<1\) | Exact annihilation forces the measure to be supported on actual off-line zeros. |
| Finite-measure mixtures on a bounded segment of the critical line | Exact annihilation and finite energy force the mixture to be zero. |
| Countable critical-line mixtures with \(\sum|a_js_j|<\infty\) | Every nonzero mixture has logarithmically divergent energy, even for unbounded frequencies. |

These theorems do not cover every infinite construction. Unbounded-frequency continuous measures, more conditionally convergent representations, or direct constructions of an arbitrary \(H\)-vector remain outside the spectral obstructions proved here. They would still need a nonzero normalization, finite energy, and all exact arithmetic identities.

For example, if arbitrary approximants satisfy
\[
v_k(1)=2,\qquad \sup_k\|v_k\|_H<\infty,
\qquad L_d(v_k)\longrightarrow0\quad\text{for every fixed }d,
\]
weak compactness supplies a nonzero vector in \(S^\perp\), hence a disproof. Constructing such a uniformly bounded normalized family is not established here. Small individual residuals without that bound do not suffice.

The prior conditional consequences—vacancy floors, growing head energy, certificate irregularity, and Mellin poles—do not supply the missing uniform estimate. A conjunction of consequences of \(\neg\mathrm{RH}\) does not prove its premise. A contradiction derived from that premise would prove RH.

The sharp unresolved target within this framework is still
\[
\boxed{
\exists B<\infty\ \forall M\ge2:\quad
b_M^*T_M^{-1}b_M\le B,
}
\]
equivalently \(\varepsilon_*>0\). No such unconditional bound, and no off-line zero, has been established by this attempt.

## References

- [Bhaskar Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis, Theorem 1](https://arxiv.org/pdf/math/0607733): the weighted residue-space criterion used in Section 1.
- [NIST Digital Library of Mathematical Functions, §25.2](https://dlmf.nist.gov/25.2): the analytic continuation of zeta used in (8).
- Prior working note: `RH_Disproof_Attempt_Uniform_Gap_and_Mellin_Mode_Obstruction_2026-09-21.md`. The present note adds the strong finite-certificate convergence identity, bounded-frequency measure rigidity, and the countably infinite critical-line divergence theorem, with ordinary mathematical proofs above.
