# Prime tensors, weighted CRT, and the exact RH obligation

Research memorandum for the 2 November 2026 project. Prepared for Christian Noack.

## Status and scope

This memorandum follows all eight agendas in the supplied *Prime Tensors,
Weighted CRT, and Legal Approximation to One* project. It establishes several
stronger structural results on paper and records a separately identified Lean
subset. It does not prove RH. In particular, numerical improvements and
RH-conditional results are not unconditional providers of vanishing error.

Bagchi [6], Remark 8, already identifies squarefree legal constant closure
with RH. We apply this published equivalence to Q and give an explicit
norm-controlled transfer for quantitative certificates. The analytic provider
remains unformalized.

| Agenda | Result obtained | Remaining scope |
|---|---|---|
| A: gcd foundation | Exact cells, conditional means, projection identity, sharp oscillation tail, and PNT cutoff asymptotic | Full arithmetic conditional-expectation identification is on paper |
| B: CRT and transfers | Rational finite-prime algorithm, explicit coupling error, character parity sparsity | No universal low-rank legal Gram factorization |
| C: optimization | Exact scalar/block gains, reproducible complete-moment fits, rational candidate enclosure | Capacity divergence remains equivalent to RH |
| D: collective tails | Exact signed covariance and anchored PSD remainder; sharp cellwise bounds | No unconditional growing family with vanishing bound |
| E: exact heads | Explicit elementary O(H) bound; existing repository theorem strengthens this to o(H); under RH, exact-head mean-neutral error tends to zero | No fixed power saving below exponent one is established unconditionally |
| F: measure/Cesàro comparison | Exact finite Cesàro Gram; counterexample to a uniform reverse estimate even in the mean-neutral legal span | A family-specific transfer requires further arithmetic input |
| G: dual/operators | Classification of unit multiplications preserving finite legal spaces; legal staircase operator | Dual rigidity is still an equivalent RH target |
| H: formalization | See the focused theorem catalog and checkpoint records | On-paper results below are not all formalized |

## 1. Definitions

Put Z=ζ(2), Q(n)=1/(Zn²), P(n)=1/[n(n+1)] for n≥1. Let

$$g_d(n)=\frac{n\bmod d}{d},\qquad
\mathcal L_{sf}=\operatorname{span}_{\mathbb R}\{g_d:d\ge2,
\ d\text{ squarefree}\},\qquad V_{sf}=\overline{\mathcal L_{sf}}^{L^2(Q)}.$$

The norm comparison is

$$\frac Z2\|f\|_Q^2\le\|f\|_P^2\le Z\|f\|_Q^2.$$

Each finite legal function is bounded and periodic, vanishes on multiples
of a squarefree common period, and hence is not identically one.
Prime valuations under Q are independent geometric variables with
Pr(v_p(N)=k)=(1-p⁻²)p⁻²ᵏ. This standard probability model is supported by
Cranston–Peltzer [1]. Ordinary residue classes do not acquire product
uniform measure from CRT.

The complete divisor basis already in the repository is

$$W_r(n)=\sum_{a\mid r}\mu(r/a)a^2 1_{a\mid n},\quad
J_2(r)=r^2\prod_{p\mid r}(1-p^{-2}),\quad e_r=W_r/\sqrt{J_2(r)}.$$

In particular e₁=1. Write A_{r,d}=⟨g_d,e_r⟩_Q, G_{d,e}=⟨g_d,g_e⟩_Q,
b_d=⟨g_d,1⟩_Q, and F_c=Σ_d c_d g_d. All Gram entries below include the
entire physical tail.
Let Π_M project onto span{e_r:r|M}. Write D_B={d:2≤d≤B, d squarefree}
and C_B=C_(D_B). For a finite legal dictionary D, define the column certificate

$$B_{D,M}(c)=\sum_{r\mid M}|\langle1-F_c,e_r\rangle_Q|^2+
\left(\sum_{d\in D}|c_d|\,\|(I-\Pi_M)g_d\|_Q\right)^2.$$

## 2. Published reverse implication and quantitative transfer

Bagchi's equivalent-weight observation after Theorem 1 applies to Q.
We spell out the Möbius transfer to track complete errors.

Let ρ_d(x)={1/(dx)}, χ=1_(0,1], and H=L²(0,∞). Báez-Duarte [2] proves
under RH that the finite Möbius sums
−Σ_{d≤N} μ(d)d^−ε ρ_d approximate χ, taking N to infinity and then
ε down to zero. We use the actual Möbius-supported construction, not merely
the theorem that unrestricted integer dilations suffice.

For arbitrary finite real coefficients define Φ=Σ c_dρ_d,
C=Σ c_d/d, and F=Σ_{d≥2}c_dg_d. On the step interval
1/(n+1)<x≤1/n, almost everywhere,

$$JF(x)=\Phi(x)-C\rho_1(x),\qquad
\Phi(x)=C/x\quad(x>1).$$

Consequently, with α=∫₀¹ρ₁²≤1,

$$\|\chi-\Phi\|_H^2=\|1-\Phi\|_{L^2(0,1)}^2+C^2,$$
$$\|1-F\|_P^2\le(1+\alpha)\|\chi-\Phi\|_H^2
\le2\|\chi-\Phi\|_H^2,$$
$$\boxed{\|1-F\|_Q^2\le\frac4Z\|\chi-\Phi\|_H^2.}$$

The middle bound follows from the triangle inequality followed by
(u+√α v)²≤(1+α)(u²+v²). The tail C/x pays for the charge correction;
an independent estimate on the coefficient sum is unnecessary. Since μ(d)
vanishes at nonsquarefree d, F is squarefree legal. This proves on paper
RH⇒1∈V_sf. The converse follows from the legal Mellin obstruction already
implemented in the repository. Therefore

$$\boxed{\mathrm{RH}\iff 1\in V_{sf}(Q)\iff1\in V_{sf}(P).}$$

This matches the published criterion [6]. The full analytic provider has not been
formalized by the new Lean modules in this task.

A stronger quantitative benchmark comes from Balazard–de Roton [3],
Propositions 1–3. Under RH, for every δ>0 their damped Möbius coefficients
give complete squared H-error O_δ((log log N)^(5/2+δ)/√log N). The displayed
transfer gives the same order for squared Q-error. The damping can be
chosen as ε_N=25(log log N)^(5/2+δ)/√log N for sufficiently large N.
The dependence on RH remains essential in the cited estimates.

For these coefficients ||c||₁≤N. The elementary choice T=N³ and
M=lcm(1,…,T) makes the original universal tensor penalty at most 1/(ZN).
Thus the finite tensor certificate also tends to zero under RH: the
certificate's existence is no stronger than the published approximation
problem. The enormous cutoff is an existence argument, not an efficient
numerical prescription.
The unconditional PNT refinement in Section 3 permits T=N² instead, with
penalty O(1/log N), still below the displayed RH-conditional error scale.

## 3. Gcd projection, exact conditional means, and optimal universal constant

For M≥1 and a|M set

$$c_M(a)=\prod_{p\mid M/a}(1-p^{-2}),\qquad
w_M(a)=\frac{c_M(a)}{a^2},\qquad q(a)=\frac1{Za^2}.$$

The span of e_r for r|M equals the functions of gcd(N,M). Indeed triangular
Möbius inversion identifies it with the divisor indicators 1_{r|N}, r|M.
Each indicator depends on the gcd. Conversely the gcd-cell indicator is

$$1_{\gcd(n,M)=a}=\sum_{b\mid\operatorname{rad}(M/a)}\mu(b)1_{ab\mid n}.$$

Every ab on the right divides M. Taking expectations proves w_M(a), and
changing variables n=abk proves, for integrable F,

$$E[F(N)\mid\gcd(N,M)=a]
=\frac{a^{-2}}{w_M(a)}\sum_{b\mid\operatorname{rad}(M/a)}
\frac{\mu(b)}{b^2}E[F(abN)].$$

Thus Π_M=E[·|gcd(N,M)] is exactly the stated wavelet projection, including
M=1. For F∈L²(Q) the exact discarded energy is

$$\|(I-\Pi_M)F\|_Q^2=\sum_{a\mid M}w_M(a)\operatorname{Var}(F\mid a)
=\frac12\sum_{a\mid M}\frac1{w_M(a)}
\sum_{\substack{m,n\ge1\\\gcd(m,M)=\gcd(n,M)=a}}
Q(m)Q(n)(F(m)-F(n))^2.$$

Nonnegative summation or L² integrability justifies expansion and limits.
The same conditional means give exactly the same retained energy as the
wavelet coefficients.

Each cell has a distinguished atom N=a of conditional mass
t_a=q(a)/w_M(a)=1/[Zc_M(a)]≥1/Z>1/2. The last inequality follows from
ζ(2)<2 by comparison with Σ_{n≥2}1/[n(n−1)]. If a variable in [A,B] has
an atom of mass t≥1/2, its variance is at most t(1−t)(B−A)². To prove this,
normalize A=0,B=1, let x be the atom's value, m the mean off that atom,
and v the corresponding second moment. Then 0≤x,m≤1 and v≤m. For
V=t x²+(1−t)m−[t x+(1−t)m]², the identity

$$t(1-t)-V=(1-x)(1-t)(1-m)[t-(1-t)m]
+x(1-t)m[t-(1-t)(1-m)]+t(1-t)x(1-x)$$

has only nonnegative terms. Replacing m in the second moment by v adds
(1−t)(m−v) to the gap. Endpoint values attain equality.

It follows that the sharp global oscillation constant is

$$\boxed{\|(I-\Pi_M)F\|_Q^2\le\kappa_M\operatorname{osc}(F)^2,
\qquad \kappa_M=\sum_{a\mid M}q(a)\left(1-\frac{q(a)}{w_M(a)}\right).}$$

The function 1_{N∤M} attains this bound among unrestricted bounded
observables; sharpness is not asserted within a fixed legal dictionary.
Moreover 0≤κ_M≤δ_M=Pr(N∤M).
For a legal combination, osc(F_c)≤Σ|c_d|(d−1)/d. Thus this strengthens
the original δ_M||c||₁² bound. A still stronger certificate uses the
oscillation O_a on each gcd cell:

$$\|(I-\Pi_M)F\|_Q^2\le\sum_{a\mid M}
q(a)\left(1-\frac{q(a)}{w_M(a)}\right)O_a^2.$$

For squarefree legal period L, the residues occurring in cell a are exactly
those satisfying, for p|gcd(L,M), p|r iff p|a. CRT proves sufficiency as
well as necessity. Therefore each O_a is a finite max-minus-min, retaining
the signed synthesis before estimation. For instance this recognizes the
zero tail of g₂ when M is even.

The sharp constant itself can be evaluated without enumerating all divisors.
For p^m exactly dividing M, put q=p⁻². Multiplicativity of the two divisor
sums gives the finite products

$$A_M=\prod_{p^m\parallel M}\frac{1-q^{m+1}}{1-q},\qquad
B_M=\prod_{p^m\parallel M}\left(\frac{1-q^m}{(1-q)^2}+q^m\right),$$
$$\delta_M=1-A_M/Z,\qquad\kappa_M=A_M/Z-B_M/Z^2.$$

In the second sum, exponents j<m contribute q^j/(1−q) and j=m
contributes q^m; summing that geometric progression proves its local factor.
These formulas make the optimal universal constant computable even when
the number of divisors of M_T is prohibitive.

With M=lcm(1,…,T), δ_M≤1/(ZT). Choosing a candidate first and then T
shows that the infimum of either complete certificate is zero if and only
if 1∈V_sf. This argument makes no assertion about coefficient growth for
a prescribed simultaneous schedule.

There is a sharper unconditional asymptotic. For integer T→∞, write
M_T=lcm(1,…,T), δ_T=δ_(M_T), κ_T=κ_(M_T), and

$$r_T=1-\frac1{Z\prod_{p\le T}(1-p^{-2})}.$$

This is the probability that a prime greater than T divides N. If
m_p=⌊log_p T⌋, independence gives

$$\delta_T=1-(1-r_T)\prod_{p\le T}(1-p^{-2(m_p+1)}).$$

The internal overshoot sum Σ_(p≤T)p^(-2(m_p+1)) is O(T^(-3/2)):
for p≤√T each term is below T⁻² and there are at most √T such primes;
for p>√T sum p⁻⁴ is bounded by the corresponding integer tail.
Thus δ_T=r_T+O(T^(-3/2)). For a≤√T, every prime p≤T divides M_T/a:
if p|a, then p^(v_p(a)+1)≤ap≤a²≤T; otherwise this is immediate.
Hence t_a=1−r_T on all those cells and

$$r_T\sum_{a\le\sqrt T}Q(a)\le\kappa_T\le\delta_T.$$

Since r_T≤1/T and the omitted sum is O(T^(-1/2)), also
κ_T=r_T+O(T^(-3/2)). Finally the prime number theorem and partial
summation give Σ_(p>T)p⁻²∼1/(T log T); expanding the convergent Euler
product changes this by O((Σ_(p>T)p⁻²)²). Therefore

$$\boxed{\kappa_T\sim\delta_T\sim\frac1{T\log T}.}$$

This is an on-paper application of the unconditional PNT, not a new Lean
asymptotic theorem. It improves the universal cutoff rate, while leaving the
signed retained energy entirely uncontrolled. For ||c||₁≤N and T=N²,
N²δ_T∼1/(2 log N); a smaller cutoff penalty alone still does not prove RH.

## 4. Complete signed tail covariance and finite optimization

For any retained finite orthonormal row family Λ let z_d=(I−Π_Λ)g_d and
K_{d,e}=⟨z_d,z_e⟩. Then exactly

$$K=G-A_\Lambda^T A_\Lambda\succeq0,\qquad
\left\|\sum_dc_dz_d\right\|^2=c^TKc,$$
$$\|1-F_c\|_Q^2=\|e_1-A_\Lambda c\|_2^2+c^TKc\quad(1\in\Lambda).$$

The column bound is cᵀKc≤(Σ|c_d|√K_dd)². Grouping the z_d into blocks
keeps the exact within-block covariance and applies the triangle inequality
only between blocks: the bound is (Σ_B√(c_BᵀK_BB c_B))². Merging blocks
cannot increase it, by the triangle inequality for their actual residual
vectors. For any u_d>0 a genuine matrix majorant is

$$K\preceq\left(\sum_dK_{dd}/u_d\right)\operatorname{diag}(u_d).$$

This follows from weighted Cauchy–Schwarz on the residual vectors. The
absolute-value column estimate does not imply a rank-one PSD majorant;
such a majorant would force rank K≤1. Already the covariance of g₂,g₃
at M=1 has rank two: a zero-variance combination is constant, and evaluation
at residues 0,2,3 modulo 6 forces both coefficients to vanish.

The column certificate is also monotone under adding analysis rows. For one
new unit row e orthogonal to Λ, put a_d=⟨g_d,e⟩ and t_d=||z_d||. Its exact
decrease, with coefficients fixed and the constant row already retained, is

$$\left(\sum_d|c_d|t_d\right)^2-
\left(\sum_d|c_d|\sqrt{t_d^2-a_d^2}\right)^2-
\left(\sum_dc_da_d\right)^2\ge0.$$

Apply the triangle inequality in the Euclidean plane to vectors
|c_d|(√(t_d²−a_d²), |a_d|); their norm sum is Σ|c_d|t_d.
The squared norm of their sum bounds the last two terms. This proves an
adaptive row-gain rule using complete column tails. Repeating handles
finite row blocks. Moreover, for every fixed finite dictionary D,

$$\inf_{M,c}B_{D,M}(c)=\min_c\|1-F_c\|_Q^2.$$

The lower bound is the certificate inequality. For the reverse bound, fix a
complete-Gram minimizing vector and let M=M_T grow: its finite column
tails tend to zero, so its certificates tend to its actual error. This is
an equality of finite-dictionary optima, not a proof that growing-dictionary
errors tend to zero.

There is also an exact signed anchored majorant for gcd cutoffs. Let
v(n)=(g_d(n))_d, μ_a=E[v|gcd=a], and
R=E[(v(N)−v(gcd(N,M)))(v(N)−v(gcd(N,M)))ᵀ]. Then

$$\boxed{R-K=\sum_{a\mid M}w_M(a)(\mu_a-v(a))(\mu_a-v(a))^T\succeq0.}$$

This is conditional bias-variance decomposition. It supplies a true PSD
upper bound while preserving the signed differences F(N)−F(gcd(N,M)).

For a finite legal dictionary the normal equations give ε_D=1−bᵀG†b>0
and capacity C_D=(1−ε_D)/ε_D. If a new block has residual-column Gram H
and residual-target correlations s, its exact improvement is sᵀH†s.
Indeed a vector in ker H synthesizes zero and is orthogonal to s, so the
normal equations for the block are solvable; completion of squares proves
the identity. The scalar case is |⟨r,q⟩|²/||q||² for q≠0, and zero
when q=0. Exhaustion gives
capacity divergence exactly when the limiting target error vanishes.
An unconditional lower bound forcing accumulated gains to exhaust the
initial error is still missing.

## 5. Exact heads, neutrality, and the energy exponent

For H≥1, s_H=Σ_{d≤H}μ(d)/d satisfies |s_H|≤1. This follows from
H s_H=1+Σ_{d≤H}μ(d){H/d}; the d=1 term is zero and the other H−1 terms
have magnitude at most one. Choose a prime H<D≤2H (Bertrand, including
H=1 directly) and put

$$A_H=-\sum_{d\le H}\mu(d)g_d+D s_Hg_D.$$

Möbius inversion gives A_H(n)=1 for 1≤n≤H. Its coefficient ℓ¹ norm is at
most 3H−1, whence the unconditional complete-energy estimate

$$\boxed{\|A_H\|_Q^2\le1+\frac{(3H-1)^2}{ZH}\le1+\frac{9H}{Z}.}$$

This establishes squared-energy exponent one; it does not improve the known
zero-free strip. An exponent 1−δ would already exclude zeros with real
part greater than 1−δ/2. Exponents must not be confused with norm exponents.

The repository already contains a stronger unconditional result:
`QSquarefreeSublinearHeads.exactHead_sublinear` and
`exactHead_error_sublinear` prove energy and error o(H) for the canonical
Möbius heads. Restricting to H=p−1, p prime, makes their repair conductor
squarefree; `arbitrarily_small_linear_cost` states the resulting cofinal
legal conclusion. These use the existing PNT-based canonical energy proof.
Thus the elementary estimate above is an explicit benchmark, not a new
asymptotic record. An o(H) bound can still have logarithmic exponent one;
the gap to H^ε for every ε>0 remains.

Zero period mean does not change the legal closure. For squarefree conductors
D,E with E≥2D and D>H,

$$h_{D,E}=\frac{2(Dg_D-Eg_E)}{D-E}$$

has head zero through D−1 and period mean one. Its coefficients have
absolute values at most 2 and 4. Also
||g_d||²_Q≤2/(Zd): split at d, using g_d(n)=n/d below d and g_d≤1 above d.
Therefore ||h_{D,E}||_Q→0 as D→∞. Subtracting the period mean of any fixed
legal F times h_{D,E} imposes mean neutrality with arbitrarily small Q cost
and preserves any prescribed fixed head. It also yields mean-neutral exact
heads with the same O(H) energy order.

There is a stronger qualitative result under density. Let E_H:V_sf→R^H
be evaluation on the first H sites. It is bounded, with norm at most
a_H=√Z H, since Σ_{n≤H}|f(n)|²≤ZH²||f||²_Q. The range W_H=E_H(ℒ_sf) is finite dimensional
and closed. If 1∈V_sf, then E_H1∈W_H. Lift a basis of W_H to legal
functions to obtain a finite-rank right inverse S_H with finite norm b_H.
For legal f close to one,

$$F=f+S_H(E_H(1-f)),\qquad
\|1-F\|_Q\le(1+b_Ha_H)\|1-f\|_Q.$$

Choose f sufficiently close for each H. Then F_H is exact on its first H
sites and ||1−F_H||_Q→0. Apply the preceding neutralization with a further
error tending to zero. No uniform estimate on b_H has been assumed.

Combining with Section 2 gives the on-paper equivalences

$$\mathrm{RH}\iff1\in V_{sf}\iff C_B\to\infty
\iff\inf_{D,M,c}B_{D,M}(c)=0$$

and equivalence to the existence of mean-neutral, squarefree legal exact
heads of lengths H_j→∞ with Q-error tending to zero, or merely with
uniformly bounded Q energy. It is also equivalent to existence of cofinal
legal exact heads (H_j→∞) with

$$\liminf_j\frac{\log(1+\|F_j\|_Q^2)}{\log H_j}=0.$$

For the last converse, an off-line zero ρ with σ=Reρ>1/2 gives
||1−F_j||²_P≥(2σ−1)(H_j+1)^(2σ−1)/|ρ|² by Mellin continuity and
Cauchy–Schwarz on (0,1/(H_j+1)]. Norm comparison contradicts zero lower
logarithmic growth. The functional equation completes the RH implication.

These are equivalences, not unconditional estimates for the coefficients
or the right inverses.

## 6. Cesàro energy: exact evaluation and a legal counterexample

Let λ(k)=2/[(k+1)(k+2)] and CF(k)=k⁻¹Σ_{n≤k}F(n). The conditional-iid
model gives J(F)=Σλ(k)CF(k)²≤||F||²_P. The map is injective, because
F(k)=kCF(k)−(k−1)CF(k−1), but it is not bounded below on the legal space.

For d≥1 define

$$F_d=d g_d-(d+1)g_{d+1}=(n\bmod d)-(n\bmod(d+1)).$$

It vanishes for n<d, has F_d(d)=−d, and its prefix sums obey
−k≤Σ_{n≤k}F_d(n)≤0. Here is a full elementary proof. The period is
L=d(d+1), with total −L/2. On 0≤k<L write k=t(d+1)+r, 0≤r≤d,
0≤t≤d−1, and put D(k)=−Σ_{n≤k}F_d(n).

- If t+r≤d−1, direct arithmetic progression summation gives
  D=t(2d−1−2r−t)/2. Its bracket lies between 0 and 2d, hence 0≤D≤td≤k.
- Otherwise set s=t+r−d, so 0≤s≤t and k=d(t+1)+s. Then
  D=d+s(d−t)+t(t−1)/2≥0, and
  k−D≥t(t+3)/2≥0, using s≤t and d−t−1≥0.

Adding whole periods proves the result for every k. Thus −1≤CF_d≤0.
Choose disjoint adjacent-squarefree pairs d,d+1 and e,e+1, with e>d+1,
and set G=F_d−F_e. This is a four-atom squarefree legal function, has zero
period mean, vanishes below d, and satisfies G(d)=−d and |CG|≤1. Hence

$$\boxed{J(G)\le\frac2{d+1},\qquad
\|G\|_Q^2\ge\frac1Z,\qquad \|G\|_P^2\ge\frac d{d+1}.}$$

Adjacent squarefree pairs are unbounded by an elementary sieve. Bad d≤X
are covered by p²|d or p²|d+1, giving at most
2XΣ_p p⁻²+O(√X) bad integers. Moreover

$$\sum_p p^{-2}\le\frac14+\frac19+\frac1{25}+\frac1{49}+\frac1{14}
=\frac{21739}{44100}<\frac12.$$

The last two terms bound the odd-integer tail starting at seven by its
first term and an integral. Thus at least (311/22050)X−O(√X) pairs are
good. No twin-prime hypothesis is involved.

Normalizing G gives unit-Q-norm mean-neutral legal functions with J→0.
Therefore no fixed K can satisfy ||F||²_Q≤KJ(F), even on this restricted
legal class with arbitrarily long zero heads. These are zero heads, so this
does not contradict exact-head-one RH criteria. The Cesàro operator has
nonclosed range on the closed legal subspace, not a nontrivial kernel.

For an L-periodic F with mean m, define a_r=Σ_{n=1}^rF(n)−mr, 0≤r<L.
Then CF(k)=m+a_{k mod L}/k and exactly

$$J(F)=m^2+2m\sum_ra_rK_L(r)+\sum_ra_r^2W_L(r),$$

where K_L(r)=Σ_{k≥1,k≡r(L)}2/[k(k+1)(k+2)] and
W_L(r)=Σ_{k≥1,k≡r(L)}2/[k²(k+1)(k+2)]. These are positive complete
progression weights; polarization gives the Cesàro Gram. They can be
evaluated by digamma/Hurwitz zeta or enclosed by rational tails. The exact
partial fractions are

$$\frac2{k(k+1)(k+2)}=\frac1k-\frac2{k+1}+\frac1{k+2},$$
$$\frac2{k^2(k+1)(k+2)}=\frac1{k^2}-\frac3{2k}+\frac2{k+1}-\frac1{2(k+2)}.$$

For one residue atom its centered prefix is r(r−d+2)/(2d), 0≤r<d,
with magnitude at most d/8. A mean-neutral legal F consequently has
Cesàro tail after T bounded by (Σ|c_d|d)²/(96T³). This improves the
coarse bound in the project document; related sharper cubic estimates
already occur in the repository.

## 7. Transfer operators, parity, and legality

The dual problem has an exact, convergent tensor formulation. For h∈L²(Q),
let y_r=⟨h,e_r⟩ and h_d(a)=E[g_d(aN)]. Then

$$\langle h,g_d\rangle_Q=\sum_{r\ge1}\frac{y_r}{\sqrt{J_2(r)}}
\sum_{a\mid r}\mu(r/a)h_d(a).$$

Cauchy–Schwarz on the two square-summable coefficient sequences proves
absolute convergence. Hilbert orthogonal-complement duality says
1∈V_sf exactly when vanishing of these sums for all squarefree d≥2 forces
y₁=0. It does not require y=0. Bagchi's criterion identifies this rigidity
statement with RH; the displayed exact relations do not prove it
unconditionally.

For a finite prime set S, let N_S retain only the valuations in S. The
probability that N_S differs from N is

$$r_S=1-\frac1{Z\prod_{p\in S}(1-p^{-2})}\le\sum_{p\notin S}p^{-2}.$$

Coupling gives |E f(xN)−E f(xN_S)|≤r_S osc(f), uniformly in the starting
residue x. If Y≥1 and all primes through Y are included, r_S≤1/⌊Y⌋. This also
gives for an m-column dictionary the PSD bounds
−m r_S I≤G−G_S≤m r_S I.

Each geometric averaging operator is a rational finite matrix. If R^(a+t)=R^a,
q=p⁻², then

$$K_p=(1-q)\sum_{k<a}q^kR^k+
\frac{(1-q)q^a}{1-q^t}\sum_{j<t}q^jR^{a+j}.$$

For p coprime to L take a=0 and t=ord_L(p); for squarefree L and p|L
take a=1 and t=ord_(L/p)(p), with t=1 when L/p=1. Grouping the geometric
series into preperiod and cycles proves the formula. Thus finite prime
products and complete residue-weight formulas are independent moment
evaluation methods with explicit truncation control.

On each unit stratum modulo e≥2, the fractional residue u/e has principal
character coefficient 1/2. A nonprincipal even character has coefficient
zero: pairing u and e−u reduces the sum to the complete character sum,
which vanishes. This removes all nonprincipal even characters exactly.
The odd-character terms and the actual weighted Euler factors still matter.
For e>2, at most 1+φ(e)/2 character coefficients remain, out of φ(e).
This is an exact storage reduction for each scalar observable, not a claim
that the full weighted legal Gram matrix has correspondingly small rank.

There is a sharp legality obstruction. For squarefree L and gcd(q,L)=1,

$$R_q(U_L)\subseteq U_L\quad\Longleftrightarrow\quad q\equiv1\pmod L.$$

Here U_L is the span of g_d for d|L, d≥2. In fact there is a complete
finite legality test: an L-periodic f with f(0)=0 belongs to U_L if and
only if Δf(n)=f(n)−f(n−1) depends only on gcd(n,L). Necessity follows
from Δg_d(n)=1/d−1_(d|n). For sufficiency, divisor Möbius inversion writes
Δf(n)=Σ_(a|gcd(n,L))β_a. Its zero sum over one period implies
Σ_(a|L)β_a/a=0. Hence
Δf=Σ_(a|L,a≥2)(−β_a)Δg_a; integrating from f(0)=0 proves the test.
Thus the legal space has dimension τ(L)−1. Squarefreeness of L makes
all of these conductors legal in the present synthesis model.

For a legal f, Δf(n)=Σc_d/d−Σ_{d|gcd(n,L)}c_d is constant on units
modulo L. If R_qg_p is legal for p|L, CRT forces its difference to be
constant at residues 1,…,p−1. Put r=q mod p. At one this difference is
r/p; telescoping to p−1 gives (p−1)r/p=(p−r)/p, so r=1. This holds for
every p|L. The converse is immediate. This classifies individual unit
multiplications; averages and nonunit multiplications need separate tests.

A useful legal operator with a restricted domain is
S_af(n)=f(⌊n/a⌋), f(0)=0. Direct division gives

$$S_ag_d=g_{ad}-g_a/d,\quad S_aS_b=S_{ab},\quad
\|S_af\|_P^2=\|f\|_P^2/a,\quad \|S_af\|_Q^2\le\|f\|_Q^2/a.$$

The Pareto block mass telescopes to P(k)/a on ak≤n<a(k+1); the Q block
mass is at most Q(k)/a. For squarefree a and conductors coprime to a this
preserves squarefree legality. An exact head becomes a block of ones after
an initial block of zeros. Existing floor-trial modules already pursue this
operator; it should not be advertised as a new density proof.
Bagchi's Theorem 7 also uses this normalized Pareto staircase [6]. The restricted squarefree domain
must still be respected when using that operator here.

## 8. Quantitative loss of squarefree analysis rows

Every squarefree divisor wavelet has equal values at 2 and 4. For any
Hilbert vector h with that equality, retaining those two physical sites gives

$$\|g_3-h\|_Q^2\ge\frac1{4Z}(2/3-x)^2+\frac1{16Z}(1/3-x)^2
=\frac1{180Z}+\frac5{16Z}(x-3/5)^2.$$

Evaluation is continuous, so the same positive lower bound holds on the
closed span of all squarefree analysis rows. This proves quantitatively that
prime-power rows cannot be discarded, even when the synthesis atom is legal.

There is also an exact on-paper value for projection onto rad(N):

$$\|g_3-E[g_3\mid\operatorname{rad}(N)]\|_Q^2
=\frac2{81}\left[1-\prod_{p\equiv2\ (3)}
\left(1-\frac4{(p^2+1)^2}\right)\right]\ge\frac8{2025}.$$

Indeed g₃=1_{3∤N}(1/2−χ₃(N)/6). Conditional positive prime exponents
remain geometric, and for p≡2 mod 3 their parity mean is
−(p²−1)/(p²+1). Squaring the conditional character mean and averaging
independent prime-presence flags yields each displayed Euler factor.
The p=3 factor is 8/9; bounded convergence justifies the product.

## 9. Reproducible diagnostics and a complete rational certificate

The companion diagnostic archive contains the Python files and their outputs.
Their source is also reproduced in `PrimeTensorCRTReproduction20261102.md`.
After extracting the archive, run from its directory
`python prime_tensor_crt_diagnostics.py`, followed by
`python prime_tensor_crt_extended_diagnostics.py`; they write the corresponding
JSON records. NumPy and SciPy are required for floating diagnostics.
The recorded run used Python 3.12.14, NumPy 2.3.5, and SciPy 1.17.0.
`prime_tensor_cutoff_diagnostics.wl` reproduces the independent Wolfram check.

The companion Python program evaluates full residue moments, caches twisted
means, reconstructs divisor-wavelet rows, fits three dictionary types, and
records conditioning and normal-equation residuals. Floating results are
diagnostics only. Examples:

| Dictionary | Complete squared Q-error, floating |
|---|---:|
| {2,3,6} | 0.05476694337026 |
| All squarefree 2≤d≤10 | 0.01724870442984 |
| All squarefree 2≤d≤30 | 0.00986693038917 |
| Nontrivial divisors of 30 | 0.02540022543572 |
| Nontrivial divisors of 210 | 0.01687043606102 |
| Eight-step adaptive subset of squarefree d≤30 | 0.01401690119029 |

The adaptive set was {2,3,5,6,7,10,11,13}. Dictionary sizes and largest
conductors differ; these rows do not demonstrate an asymptotic ranking.

The extended program holds this eight-atom dictionary fixed and compares
complete and penalized optimization at M=60:

| Objective minimized | Certificate at its computed minimizer | Actual complete squared Q-error |
|---|---:|---:|
| Complete Gram error | exact error | 0.01401690119 |
| Retained error + δ_M||c||₁² | 0.3892760332 | 0.1744854883 |
| Retained error + κ_M(Σ|c_d|(d−1)/d)² | 0.1896899168 | 0.06984716151 |
| Retained error + column-tail penalty | 0.03146995079 | 0.02174719762 |

These are floating optimization diagnostics, not exact optimizer proofs.
The split-variable convex programs reported success and projected-gradient
residuals below 2.3×10⁻⁸. Feasible exact-head constrained full-energy minima
for H=3,6,10 were approximately 0.90739308, 0.97735407, 1.02057384;
constraint residuals were below 4×10⁻¹⁵. Minimizing energy with fixed heads
is a different objective from minimizing target error.

Greedy selection among analysis rows 1 through 60 reduced the fixed Gram
candidate's column certificate from 0.86515 to 0.03286 while its actual
error stayed fixed. This separates better certification from better synthesis.

An independent Fraction-arithmetic transfer product modulo six, using
primes through 19, normalizes exactly to one. Integral-test bounds on ζ(2)
give 0.01026686<r_S<0.01026747. The resulting rational coupling enclosures
contain all nine tested complete means and Gram moments, whose comparison
values were evaluated independently using polygamma. The geometric product
and its enclosures are exact; the polygamma inclusion comparisons are floating.

The fixed rational vector

$$c_2=1045918/10^6,\quad c_3=1069558/10^6,\quad c_6=604750/10^6$$

has a complete rigorous enclosure

$$\boxed{0.05476<\|1-c_2g_2-c_3g_3-c_6g_6\|_Q^2<0.05478.}$$

For each r=1,…,6, the code sums 100 rational terms of Σ_{k≥0}(6k+r)⁻².
Its omitted tail lies between 1/[6(600+r)] and that quantity plus
1/(600+r)². The denominator ζ(2) is enclosed using 100 terms and tails
1/101 and 1/100. Multiplying by the exact squared residual in each residue
and dividing outward proves the enclosure. All assertions use Python's
arbitrary-precision rational arithmetic. The integral-test tail argument is
on paper; this computation is not claimed as a Lean-checked infinite sum.

Independently, Lean's `QTensorCertificate.Benchmark.complete_norm_lt`
proves the complete squared Q-error is below 59/1000. It uses the exact
first-period reciprocal energy 53001021710221/900000000000000 and the
existing complete periodic norm comparison. This includes every omitted
physical site. Its checked bound is weaker than the separate Python interval.

Wolfram independently checked the variance algebra, Cesàro case inequalities,
partial fractions, and local character factor. Its decimal κ_M diagnostics
agree with the formulas (T=4: κ≈0.09661440984 versus δ≈0.11343964313).
Diagnostics and rounding are kept separate from certificates.
The companion Wolfram script also evaluates the new finite-product formula:
at T=100, κ_T≈0.00207281581143 and δ_T≈0.00209783689936; at T=10000,
κ_T≈9.91702686674×10⁻⁶ and δ_T≈9.91864725036×10⁻⁶. These values illustrate
the proved asymptotic and are not used to prove it.

## 10. Lean scope and the remaining link

The new Lean modules are separately scoped. `FiniteTensorTail` verifies the
complete orthonormal-row split, signed residual Gram positivity, and column
certificate. `QSquarefreeAnalysisObstruction` formalizes the positive two-site
error on the closed squarefree-wavelet span. `QTensorCertificate` specializes
the complete certificate to actual Q rows and legal columns and supplies a
conditional consumer of Mathlib's RH. `QDivisorGcdCutoff` verifies the
finite wavelet/divisor span equality and gcd invariance. `HeavyAtomVariance`
checks the scalar sharp variance bound. All five modules passed development
verification, with only the standard axioms propext, Classical.choice and
Quot.sound in the audited endpoints. Saved-source publication is recorded
by the server checkpoints and the focused theorem catalog.
The rational benchmark in `QTensorCertificate.Benchmark` separately passed
Lean verification with the same standard axiom list.
The full published reverse theorem, sharp summed gcd estimate, four-atom
Cesàro construction, and operator classification remain on-paper proofs in
this memorandum unless explicitly listed in that catalog.

The unconditional analytic information obtained here is insufficient to
make the signed complete error vanish for a growing legal family. One must
still prove an arithmetic provider, for example

$$\forall\eta>0\ \exists D,c,\Lambda:\quad
|1-b^Tc|^2+\sum_{r\in\Lambda\setminus\{1\}}|(Ac)_r|^2+c^TR_\Lambda c<\eta,
\quad K_\Lambda\preceq R_\Lambda,$$

with actual squarefree legal coefficients, or prove zero lower logarithmic
growth for actual cofinal exact-head functions. These conditions imply RH;
Sections 2 and 5 show they are also consequences of RH. Published estimates
conditional on RH cannot be inserted as unconditional providers. Prime
independence, CRT, exact finite optimization, and finite certificates do not
by themselves establish the required signed cancellation.

## References and provenance

1. M. Cranston and A. Peltzer, *On properties of the Riemann zeta distribution*,
   Rocky Mountain Journal of Mathematics 52 (2022), DOI
   [10.1216/rmj.2022.52.843](https://doi.org/10.1216/rmj.2022.52.843).
   Supports the independent geometric valuation model.
2. L. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the
   Riemann hypothesis*, Rendiconti Lincei, series 9, 14 (2003), 5–11.
   Inspected author versions: [math/0202141](https://arxiv.org/pdf/math/0202141),
   pp. 4–6, and [math/0205003](https://arxiv.org/pdf/math/0205003), Proposition 3.1.
   Supplies the RH-conditional Möbius-supported approximation.
3. M. Balazard and A. de Roton, *Sur un critère de Báez-Duarte pour l'hypothèse
   de Riemann*, International Journal of Number Theory 6 (2010), 883–903,
   DOI [10.1142/S1793042110003307](https://doi.org/10.1142/S1793042110003307).
   Inspected [author manuscript](https://arxiv.org/pdf/0812.1689), especially
   Propositions 1–3. Supplies the stronger RH-conditional rate.
4. J.-F. Burnol, *A lower bound in an approximation problem involving the zeros
   of the Riemann zeta function*, Advances in Mathematics 170 (2002), 56–70,
   DOI [10.1006/aima.2001.2066](https://doi.org/10.1006/aima.2001.2066).
   Its lower-bound scale prevents interpreting rapid cutoff-tail decay as
   rapid decay in the largest legal conductor.
5. C. Noack, RiemannResearch, inspected base
   [d082427c3a34](https://github.com/Cnoack3/RiemannResearch/commit/d082427c3a34170c6d35fead5a8d70272978ba20).
   Existing complete basis, capacity, Mellin, exact-head, and Cesàro consumers
   were inspected at their actual source. See the focused verification ledger
   for the distinct newly checked subset.

6. B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space
   reformulation of the Riemann hypothesis*, Proceedings of the Indian
   Academy of Sciences (Mathematical Sciences) 116 (2006), 137–146,
   DOI [10.1007/BF02829783](https://doi.org/10.1007/BF02829783).
   [Author manuscript](https://arxiv.org/pdf/math/0607733), Remarks 4 and 8,
   Theorem 7, and the equivalent-weight discussion after Theorem 1.
   [Publisher copy](https://repository.ias.ac.in/968/1/307.pdf) confirms
   the publication year; the arXiv copy has an inconsistent first-page date.

No novelty claim is made for independently derived structural lemmas.
