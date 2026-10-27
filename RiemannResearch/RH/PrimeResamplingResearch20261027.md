# Prime resampling, the controlled raw source, and the remaining projection problem

Research consolidation, 27 October 2026. The main unconditional result is
\[
\boxed{\mathcal D(\sqrt a\,Br_N)\le e_N/32\le1/32.}
\tag{1}
\]
The actual smoothed residual already has uniformly bounded total
prime-resampling energy. What remains unproved is a corresponding common
bound after the legal squarefree projection. Such a bound would force the
limiting residual to vanish and imply RH.

**Formal verification boundary.** The finite reversible-jump signed identity
and exit-rate bound are in `Analysis/ReversibleJumpEnergy.lean`. The complete
rate-weighted reciprocal-source bound and finite-jump assembly are in
`RH/QReciprocalWeightedEnergy.lean`. The parity centered-norm identity and
mean-independence equivalence are in `RH/QParityProjectionDefect.lean`.
These deterministic statements have Lean proofs. All countable prime-probability results in this note,
including (1), are paper derivations unless explicitly updated otherwise.
No proof of RH or converse implication from RH to squarefree density is claimed.

## 1. Definitions and the unconditional source bound

On the positive integers put
\[
Q(n)=\frac1{\zeta(2)n^2},\quad
a(n)=\frac{n}{(8+\log n)^2},\quad a(0)=0,\quad
(Bf)(n)=\frac{f(n)}{n+1},\quad A=\mathbb E_Qa(X)<\infty.
\]
For the actual legal squarefree stages write
\[
r_N=(I-P_N)1,\quad e_N=\|r_N\|_Q^2\le1,\quad
s_N=Br_N,\quad b_N=P_Ns_N.
\]
Repository inputs are \(r_N\to r\), \(b_N\to b=P_VBr\) in \(L^2(Q)\),
the quarter contraction \(\|b_N\|_Q\le\|r_N\|_Q/4\), and the implication
\[
\mathbb E_Q[a(X)b(X)^2]<\infty\ \Longrightarrow\ r=0
\ \Longrightarrow\ \mathrm{RH}.
\tag{2}
\]
Since every atom has positive \(Q\)-mass, this convergence is also
coordinatewise. The repository's regularity theorem also applies to
admissible profiles comparable to \(n/(1+\log n)^k\), for every \(k>1\).

The prime valuations \(V_p\) are independent geometric variables:
\[
\Pr(V_p=k)=(1-p^{-2})p^{-2k},\qquad k\ge0.
\]
Borel--Cantelli gives finite support almost surely, since
\(\sum_p\Pr(V_p>0)=\sum_pp^{-2}<\infty\). Euler's product identifies
\(X=\prod_pp^{V_p}\) with the law \(Q\). Let \(X^{(p)}\) replace only
\(V_p\) by an independent copy. For a real function \(g\), define
\[
\mathcal D(g)=\frac12\sum_p\mathbb E
 [(g(X)-g(X^{(p)}))^2]\in[0,\infty].
\]
This is independence of valuations, not unrestricted residue classes.

The conditional probability of a nontrivial replacement at prime \(p\) is
\(\rho_p(n)=1-(1-p^{-2})p^{-2v_p(n)}\). Its total rate satisfies
\[
K(n):=\sum_p\rho_p(n)\le\omega(n)+\sum_pp^{-2}\le n.
\]
Exchangeability and \((u-v)^2\le2(u^2+v^2)\), applied only when the
replacement changes the integer, give the extended inequality
\[
\boxed{\mathcal D(g)\le2\mathbb E_Q[K(X)g(X)^2].}
\tag{3}
\]
Thus for every \(f\in L^2(Q)\) and every \(0\le w\le a\),
\[
K(n)\frac{w(n)}{(n+1)^2}\le\frac{n^2}{64(n+1)^2}\le\frac1{64},
\qquad
\boxed{\mathcal D(\sqrt w\,Bf)\le\|f\|_Q^2/32.}
\tag{4}
\]
This proves (1), including uniformly capped or finite-support raw sources.

## 2. Exact signed identities and a nonnegative arithmetic formula

Let \(C_pg=\mathbb E[g\mid\sigma(V_q:q\ne p)]\). For \(g\in L^2(Q)\),
\[
\mathcal D_p(g)=\|g-C_pg\|_Q^2
=\mathbb Eg^2-\mathbb E(C_pg)^2.
\tag{5}
\]
For a finite prime set \(F\), summing gives
\(\mathcal D_F(g)=|F|\mathbb Eg^2-\sum_{p\in F}\mathbb E(C_pg)^2\).
One must not separately sum the signed terms over all primes and subtract
two infinite quantities.

The finite reversible-jump identity behind this calculation is elementary.
If \(Q_i k_{ij}=Q_jk_{ji}\ge0\), with \(k_{ii}=0\) and
\(\kappa_i=\sum_jk_{ij}\), then
\[
\frac12\sum_{i,j}Q_i k_{ij}(g_i-g_j)^2
=\sum_iQ_i\kappa_i g_i^2-\sum_{i,j}Q_i k_{ij}g_i g_j
\le2\sum_iQ_i\kappa_i g_i^2.
\tag{6}
\]
The diagonal is removed before summing exit rates: adding resampling
self-loops over infinitely many primes would create an infinite total
rate without changing any squared difference.

For the full prime law, Tonelli gives identities without signed summation:
\[
\mathcal D_p(g)=\frac{1-p^{-2}}{2\zeta(2)}
\sum_{\substack{m\ge1\\p\nmid m}}\frac1{m^2}
\sum_{k,\ell\ge0}p^{-2(k+\ell)}[g(mp^k)-g(mp^\ell)]^2,
\]
and, by matching the two triangular halves and setting \(\ell=k+j\),
\[
\boxed{\mathcal D(g)=\sum_p(1-p^{-2})\sum_{n\ge1}
Q(n)p^{-2v_p(n)}\sum_{j\ge1}p^{-2j}[g(np^j)-g(n)]^2.}
\tag{7}
\]
These exact formulas allow infinity and expose the arithmetic increments
that a projection estimate must control.

In fact \(A_K:=\mathbb E_Q[Ka]<\infty\). The integral test gives
\[
A_K\le\left(\sum_pp^{-2}\right)A
+\frac9{8\zeta(2)}\sum_p\frac1{p(8+\log p)}<\infty.
\]
The last sum is \(\int_0^\infty e^{-8t}\sum_pp^{-1-t}\,dt\), bounded by
\(\int_0^\infty e^{-8t}\log(1+1/t)\,dt<\infty\) using the Euler product.
Consequently \(\mathcal D(\sqrt a f)\le2A_K\|f\|_\infty^2\).
Each finite-stage periodic correction has finite energy; separate
finiteness does not supply a common bound across stages.

Individual legal atoms \(g_d(n)=(n\bmod d)/d\) also satisfy
\(\mathcal D_p(g_d)\le1/(p^2+1)\), because
\(\Pr(V_p\ne V_p')=2/(p^2+1)\) and \(0\le g_d<1\).
For a prime conductor there is the exact identity
\(\mathcal D_p(g_p)=p^{-2}\|g_p\|_Q^2\).
These atom estimates do not control the inverse Gram matrix for a
many-atom projection on the actual smoothed forcing.

## 3. What three-series and the zero-one law actually prove

The independent series
\[
L=\log X=\sum_pV_p\log p
\]
is almost surely a finite sum. Three-series also applies: with threshold
one, every prime \(p\ge3\) contributes zero to the two truncated-moment
series, and the large-jump probabilities sum to \(\sum_{p\ge3}p^{-2}\).
Thus there is no convergence or cancellation difficulty for this series.
Its quantitative properties are
\[
\mathbb EL=\sum_p\frac{\log p}{p^2-1}=-\frac{\zeta'(2)}{\zeta(2)},\qquad
\mathcal D(L)=\operatorname{Var}(L)
=\sum_p\frac{(\log p)^2p^{-2}}{(1-p^{-2})^2}<\infty,
\]
\[
\mathbb Ee^{\lambda L}=
\begin{cases}\zeta(2-\lambda)/\zeta(2),&\lambda<1,\\
\infty,&\lambda\ge1.\end{cases}
\tag{8}
\]
These statements do not automatically control the nonlinear correction
\(b_N(X)\) or its weighted resampling increments.

All finite-support valuation configurations belong to one equivalence
class under finite coordinate changes. They form a conull set, so a
function invariant under such changes is constant almost surely. A
tail-measurable residual would therefore be constant, and its
orthogonality to \(g_2=\tfrac12\mathbf1_{X\text{ odd}}\) would force zero.
The required tail measurability is not known. This single-equivalence-class
argument does not require independence; it also applies to the mixture
law below because finite-support configurations remain conull.

The exact obstruction already occurs at prime two. Since
\(C_2g_2=\tfrac38\,1\), every stage containing \(g_2\) satisfies
\[
\boxed{(C_2P_N-P_NC_2)g_2=\tfrac38 r_N,\qquad
(C_2P_V-P_VC_2)g_2=\tfrac38 r.}
\tag{9}
\]
Thus commuting at this single atom would already prove the desired
density statement. Full finite-stage \(C_2\)-invariance is impossible:
finite legal combinations vanish on a common conductor multiple, whereas
the constant function does not.

There is also an exact scalar dependence. Put \(J=\mathbf1_{2\mid X}\)
and \(e=\|r\|_Q^2=\mathbb Er\). Orthogonality to \(g_2\) gives
\[
\mathbb E[r\mid\sigma(J)]=4eJ,\qquad
\bigl\|\mathbb E[r\mid\sigma(J)]-e\bigr\|_Q^2=3e^2.
\tag{10}
\]
The same identities hold with \(r_N,e_N\). A nonzero residual necessarily
retains parity dependence. Neither independence from parity nor
commutation with prime averaging follows from ordinary orthogonal projection.
In particular, \(P_N\) itself is not a conditional-expectation operator.

## 4. Extended Poincare and an exact limiting criterion

For every \(g\in L^1(Q)\), including functions without a known second moment,
\[
\boxed{\mathbb E[(g-\mathbb Eg)^2]\le\mathcal D(g).}
\tag{11}
\]
For \(g\in L^2\), condition on the first \(m\) primes, apply finite
Efron--Stein, use conditional Jensen for the resampling differences, and
pass to the \(L^2\) martingale limit. For general integrable \(g\), clip
to \(g_R=\max(-R,\min(g,R))\). Clipping is 1-Lipschitz, so
\(\mathcal D(g_R)\le\mathcal D(g)\); also \(g_R\to g\) in \(L^1\).
Fatou applied to \((g_R-\mathbb Eg_R)^2\) proves (11).

For \(g=\sqrt a\,b\), Cauchy--Schwarz gives
\(\mathbb E|g|\le\sqrt A\|b\|_Q\), and therefore
\[
\mathbb E[a b^2]\le\mathcal D(\sqrt a\,b)+A\|b\|_Q^2
\le\mathcal D(\sqrt a\,b)+A\|r\|_Q^2/16.
\]
Together with (2), this proves the exact paper criterion
\[
\boxed{r=0\ \Longleftrightarrow\ \mathcal D(\sqrt a\,b)<\infty
\ \Longleftrightarrow\ \mathcal D(\sqrt a\,b)=0.}
\tag{12}
\]
Finite energy is not generally zero energy: for example,
\(\mathbf1_{V_2>0}\) has finite positive energy. The arithmetic theorem
(2), rather than a zero-one argument alone, is essential in (12).

## 5. Finite heads and the original positive raw moment

For \(h_{N,H}=\sqrt a\,b_N\mathbf1_{X\le H}\) and
\(E_{N,H}=\mathbb E[a b_N^2\mathbf1_{X\le H}]\),
\[
E_{N,H}\le\mathcal D(h_{N,H})+Ae_N/16,\qquad
\mathcal D(h_{N,H})\le2\sum_{n\le H}Q(n)K(n)a(n)b_N(n)^2.
\tag{13}
\]
Consequently the following cofinal criterion is exact:
\[
\boxed{r=0\ \Longleftrightarrow
\exists C<\infty\ \forall H,N_0\ \exists N\ge N_0:
\mathcal D(h_{N,H})\le C.}
\tag{14}
\]
For sufficiency, take the coordinatewise limit at each head in (13),
then use monotone convergence and (2). For necessity, \(r=0\) implies
\(b_N(n)\to0\), so the finite upper sum tends to zero at every fixed head.
Equivalently, \(r=0\) iff some slow \(H(N)\to\infty\) makes
\(\mathcal D(h_{N,H(N)})\to0\). If \(r\ne0\), every expanding head
instead has \(\mathcal D(h_{N,H(N)})\to\infty\).

For comparison with the original quantity, put \(c_H(n)=a(\min(n,H))\),
\(Z_N=b_N(s_N-b_N)\), \(M_N(t)=\mathbb E[Z_N\mathbf1_{X\le t}]\),
and \(\Phi_N^\pm(H)=\sum_{t<H}\Delta a(t)[\pm M_N(t)]_+\).
With \(X_N(H)=\mathbb E[c_Hb_N^2]\) and
\(A_N^\pm(H)=\mathbb E[c_H(\pm Z_N)_+]\), the exact signed identities are
\[
\Phi_N^+-\Phi_N^-=A_N^--A_N^+,
\qquad \Phi_N^+-X_N=\Phi_N^--\mathbb E[c_Hb_Ns_N].
\tag{15}
\]
The previous raw-moment calculation gives
\(0\le A_N^--\Phi_N^+\le A_N^+\le e_N/1024\) and
\(|\Phi_N^+-X_N|\le e_N/256\).
Applying (11) to \(\sqrt{c_H}b_N\) yields
\[
\Phi_N^+(H)\le\mathcal D(\sqrt{c_H}b_N)+Ae_N/16+e_N/256.
\tag{16}
\]
A common cofinal bound on this globally capped energy is sufficient.
The finite-support cutoff criterion (14) also has the proved reverse direction.

## 6. Local prime increments and quantitative integrability

A concrete sufficient arithmetic estimate, at cofinally many stages with
one common \(L\), is
\[
|b_N(pn)-b_N(n)|\le L\log p\qquad(n\ge1,\ p\text{ prime}).
\tag{17}
\]
Telescoping a prime factorization gives
\(|b_N(n)|\le A_0+L\log n\), where
\(A_0=\sqrt{\zeta(2)}/4\) follows from quarter contraction at \(n=1\).
Hence, whenever \(\kappa L<1\),
\[
\mathbb E_Qe^{\kappa|b_N|}
\le e^{\kappa A_0}\frac{\zeta(2-\kappa L)}{\zeta(2)}.
\tag{18}
\]
Fatou gives the same bound for \(b\).

More generally, any bound \(\mathbb E e^{\kappa|b|^p}<\infty\), with
\(p,\kappa>0\), implies regularity for every admissible logarithmic
profile exponent \(k>1+2/p\), and therefore \(r=0\) by the repository's
all-profile theorem. An elementary proof uses, for \(u,v\ge0\),
\[
uv\le(2/\kappa)^{1/q}u\log(e+u)^{1/q}
+(2/(\kappa q e))^{1/q}e^{\kappa v^q},\qquad q=p/2,
\]
with \(v=b^2\) and \(u\) the chosen profile. The deterministic first
moment is finite exactly when \(k>1+1/q\). A common exponential bound
along cofinally many stages is sufficient by Fatou; separate boundedness
of each periodic stage is insufficient. Condition (17) is unproved.

For the fixed exponent-two profile alone, generic Gaussian exponential
moments do not suffice: \(b(n)^2=\log n/\log(e+\log n)\) has
\(\mathbb E_Qe^{\kappa b^2}<\infty\) for every \(\kappa>0\), but
\(\mathbb E_Q[a b^2]=\infty\). This is not a possible nonzero actual
limiting correction, because the other-profile arithmetic theorem excludes it.
Plain entropy control only supplies logarithmic weighted energy and does
not repair this fixed-profile obstacle.

## 7. The critical weight is a mixture of different zeta laws

Write \(Q_s(n)=n^{-s}/\zeta(s)\), \(s>1\). The Laplace identity and Tonelli give
\[
\boxed{\mathbb E_{Q_2}[a b^2]=\frac1{\zeta(2)}\int_0^\infty
t e^{-8t}\zeta(1+t)\,\mathbb E_{Q_{1+t}}[b^2]\,dt.}
\tag{19}
\]
Thus the normalized weighted law \(aQ_2/A\) is a mixture of \(Q_{1+t}\),
with density \(t e^{-8t}\zeta(1+t)/(\zeta(2)A)\). The elementary bounds
\(1\le t\zeta(1+t)\le1+t\) show that this density approaches a positive
constant at zero. Conditional on \(t\), prime valuations are independent
with geometric parameters \(p^{-1-t}\). Mixing makes them dependent;
distinct prime activation indicators have positive covariance because both
activation probabilities decrease strictly with the same random parameter.

Every \(Q_s\), \(s>1\), and the normalized weighted law \(aQ_2/A\)
assign positive mass to every positive integer. They therefore have the
same null sets. Almost-sure assertions about functions on the physical
integer space agree across all these laws, although their second moments
and weighted integrability can differ. Almost-sure finiteness cannot by
itself control the expectation in (19).

For \(b\in L^2(Q_2)\), the part of (19) with \(t\ge1\) is bounded by
\(\|b\|_{Q_2}^2\int_1^\infty te^{-8t}\,dt\). Therefore
\[
\boxed{\mathbb E_{Q_2}[a b^2]<\infty
\ \Longleftrightarrow\ \int_0^1\mathbb E_{Q_{1+t}}[b^2]\,dt<\infty.}
\tag{20}
\]
The issue is stability as the zeta parameter approaches its pole.
The known \(Q_2\) contraction does not make \(P_N\) contract other \(Q_s\) norms.

A sufficient provider is a common bound
\(\mathbb E_{Q_{1+t}}b_N^2\le Ct^{-\alpha}\), \(0<t<1\), with
\(\alpha<1\), at cofinally many stages. It has a precise covariance target.
For the bounded finite-stage function set \(F_N(s)=\mathbb E_{Q_s}b_N^2\).
Differentiating its absolutely convergent series gives
\[
F_N'(s)=-\operatorname{Cov}_{Q_s}(b_N^2,\log X).
\]
If one fixed \(0\le\alpha<1\) satisfies, at cofinally many stages,
\[
\operatorname{Cov}_{Q_s}(b_N^2,\log X)
\le\frac{\alpha}{s-1}F_N(s),\qquad 1<s<2,
\tag{21}
\]
integration yields \(F_N(1+t)\le F_N(2)t^{-\alpha}\le t^{-\alpha}/16\).
The zero function is immediate; otherwise \(F_N(s)>0\) permits division.
Equations (19)--(20) then give a common weighted-energy bound, hence
\(r=0\) and RH. No covariance estimate (21) is established here.

## 8. Remaining arithmetic problem and research agenda

One direct sufficient transfer estimate is
\[
\mathcal D(\sqrt a\,P_NBr_N)
\le C\bigl(\mathcal D(\sqrt a\,Br_N)+e_N\bigr)
\tag{22}
\]
with one common \(C\). Equation (4) bounds its right side by \(33C/32\);
Fatou and (12) would finish. Abstract orthogonal projection does not give
(22), and the exact commutator (9) blocks assuming resampling invariance.

The useful next targets are the actual squarefree Gram matrix on the
smoothed forcing, the prime increments in (7) or (17), or the near-pole
covariance estimate (21). The finite-head cofinal condition (14) is a
weaker exact target when complete-stage bounds are too strong. Finite
numerical experiments can test these quantities and distinguish candidate
estimates; proving uniform control requires new arithmetic input.

## Primary references

- Gabor Lugosi, *Concentration-of-measure inequalities*, 9 February 2006,
  Theorem 8, printed page 16: finite resampling Efron--Stein.
  https://www2.stat.duke.edu/~sschmid/Courses/Stat376/Papers/ConcentrationMeasureInequalities.pdf
- Alessandro Rinaldo, *Advanced Probability*, lecture notes 6, Theorems
  1, 5, and 12: zero-one law, Borel--Cantelli, and three-series.
  https://www.stat.cmu.edu/~arinaldo/Teaching/36710-36752/Lecture_Notes/lec_notes_6.pdf

- L. Decreusefond and H. Halconruy, *Malliavin and Dirichlet structures for
  independent random variables*, Corollary 3.5: countable-product Poincare.
  https://arxiv.org/abs/1707.07915
- Adrien Peltzer, *The Riemann Zeta Distribution*, 2019, Sections 1.3.2 and
  1.4.1: independent geometric prime exponents and the logarithmic law.
  https://escholarship.org/uc/item/2df682sh

The arithmetic specializations of the probability operators, clipping extension,
and mixture and covariance arguments are paper derivations. The explicitly
identified finite algebra, rate multiplier, and parity identities are formalized.
