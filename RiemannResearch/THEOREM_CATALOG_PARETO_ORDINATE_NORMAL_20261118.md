# Pareto normal equations, the von Mangoldt source and RH

At stage $n$ the conductors are $2,\ldots,n+1$. Write $P(k)=1/[k(k+1)]$ for $k\ge1$. These weights sum to one. The inner product is $\langle f,g\rangle_P=\sum_{k\ge1}P(k)f(k)g(k)$. Let $V$ be the closed span of all normalized residues $g_d(k)=(k\bmod d)/d$, $d\ge2$, and put $e_\infty=\operatorname{dist}_P(1,V)^2$.

## The same projection in three bases

Write $R_d=d g_d$. Möbius inversion and the divisor formula for Ramanujan sums give, for $q>1$,
$$
 J_q(k)=\sum_{d\mid q}\mu(q/d)R_d(k)=-\sum_{h=1}^k c_q(h),
 \qquad R_d=\sum_{\substack{q\mid d\\q>1}}J_q .
$$
The cutoff contains every divisor greater than one of each of its conductors, so these three dictionaries give the same finite space and the same projection of the constant.

| Rows $v_d$ | Source $b_d=\langle v_d,1\rangle_P$ |
| --- | --- |
| $g_d$ | $(\log d)/d$ |
| $R_d$ | $\log d$ |
| $J_d$ | $\sum_{k\mid d}\mu(d/k)\log k=\Lambda(d)$ |

In each row of the table let $G_{ij}=\langle v_i,v_j\rangle_P$. It is positive definite. The fitted coefficients are $a_*=G^{-1}b$, the candidate is $Ja_*=\sum_q a_{*,q}J_q$ in packet coordinates, and the captured mass and squared error are
$$
 m_n=b^\top G^{-1}b=\|Ja_*\|_P^2,\qquad e_n=1-m_n.
$$
Thus $0\le m_n<1$, $m_n$ increases, and $e_n\downarrow e_\infty$. For any trial $a$, with the signed normal defect $d=Ga-b$,
$$
 \|1-Ja\|_P^2=e_n+(a-a_*)^\top G(a-a_*)=e_n+d^\top G^{-1}d .
$$
The von Mangoldt mark is $\log p$ at every $p^j,\ j\ge1$, and zero at a conductor having two distinct prime factors. All of those mixed rows and cross terms occur in $G$. [Means](RH/ParetoResidueMean.lean) · [Basis change](RH/RamanujanFiniteSpanBridge.lean) · [Canonical normal equations](RH/RamanujanCanonicalOptimizer.lean) · [Exact defect](RH/RamanujanNormalDefect.lean)

## Centered equations and Schur increments

Set $C=G-bb^\top$. For these periodic arithmetic rows the centered covariance is positive definite. Its unique solution $Cz=b$, its signal-to-noise ratio $I_n=b^\top z$, and its determinant give
$$
 z=\frac{a_*}{1-m_n},\qquad I_n=\frac{m_n}{1-m_n},\qquad
 e_n=\frac1{1+I_n}=\frac{\det C}{\det G}.
$$
For $n\ge1$ the minimum variance subject to $b^\top a=1$ is $1/I_n$, attained at $z/I_n$. Splitting the indices into prime powers $A$ and mixed conductors $M$, elimination in $Cz=b$ leaves the prime-power covariance
$C_{AA}-C_{AM}C_{MM}^{-1}C_{MA}$ and the source $b_A$. This explains how a zero-mark column can improve an approximation. [Centered normal equations](RH/RamanujanSignalNoise.lean) · [Mean-one minimum](RH/RamanujanMeanOptimizer.lean) · [Centered determinant](RH/RamanujanOrdinateNormalEquations.lean)

For a new packet let $k$ be its cross-Gram column, $g$ its diagonal entry, and $b_{\rm new}$ its mark. Write $\sigma_n=g-k^\top G^{-1}k>0$, $\eta_n=b_{\rm new}-k^\top G^{-1}b$, $\Delta_n=\eta_n^2/\sigma_n$, and $\gamma_n=\Delta_n/e_n$. The full signed $\eta_n$ enters the gain. Then
$$
 m_{n+1}-m_n=\Delta_n,\quad
 e_n=\prod_{j<n}(1-\gamma_j),\quad
 e_\infty+\sum_{j\ge n}\Delta_j=e_n .
$$
[Innovation](RH/RamanujanOrthogonalScores.lean) · [Gains and product](RH/RamanujanSaturationCriteria.lean) · [Remaining gain identity](RH/RamanujanSixMass.lean)

## Equivalent limits and the RH direction

Each condition below is equivalent to $e_\infty=0$. Each implies Mathlib's Riemann hypothesis in Lean without an analytic premise. For the reverse implication the repository's two-way RH declarations take the explicit input $\mathrm{RH}\Rightarrow\texttt{BaezDuarte.NaturalApproximation}$. Báez-Duarte proves this implication in the literature. The natural-approximation to Pareto-closure equivalence is formalized. [Published theorem](https://arxiv.org/abs/math/0205003) · [Formal bridge](RH/BaezDuarteNaturalApproximation.lean) · [Mellin implication](RH/ThresholdRiemannHypothesis.lean)

| Condition | Precise version |
| --- | --- |
| Closure and projections | $1\in V$, equivalently $V=L^2(P)$ for this dictionary. The exhaustive projections of $1$ converge to $1$. The indicator of any one nonempty initial interval belongs to $V$ iff $1$ does. [Initial intervals](RH/ParetoInitialIntervalCriterion.lean) |
| Uncentered, centered, determinant and variance | $m_n\to1$, $e_n\to0$, $I_n\to+\infty$, $\det C_n/\det G_n\to0$, or minimum mean-one variance tending to zero. The finite identities above give these equivalences. |
| Gains | $\sum_n\Delta_n=1$, $\prod_{j<n}(1-\gamma_j)\to0$, or $\sum_n\gamma_n=+\infty$. These are the gains for projection of the constant. [Saturation criteria](RH/RamanujanSaturationCriteria.lean) |
| Möbius coordinates | For **every** fixed $d>1$, $d\sum_{d\mid q,\ 2\le q\le n+1}\mu(q/d)a_{*,q}\to-\mu(d)$. This is the coefficient of the normalized residue $g_d$. The mass, norm and coefficient tests hold along every cofinal reindexing on a nontrivial filter. [Coefficient limits](RH/RamanujanCoefficientLimits.lean) |
| Dual inverse-Gram diagonals | For every fixed residue coordinate $i$, the corresponding padded inverse-Gram diagonal tends to the squared norm of its coefficient functional's Riesz vector. The first two targets are $14$ and $20$. [Dual criterion](RH/ParetoInverseGramDual.lean) |
| Mixed-conductor projection | For $M=\overline{\mathrm{span}}\{J_q:q>1,\ q\text{ has at least two prime factors}\}$, $u=(J_2-\Pi_M J_2)/\log 2=1$, equivalently $\|\Pi_MJ_2\|_P^2=\log 2-(\log 2)^2$. The finite mixed captures tend to this target iff $1\in V$. The fully screened covariance mass is $o(N^2)$ iff $1\in V$. [Rank-one reduction](RH/MixedConductorRankOne.lean) |
| First-site equations | Complete first-site tail capacity tends to $+\infty$, equivalently first-site vacancy tends to zero. Its mismatch, prime cancellation variance and composite gain budgets have unbounded sum. The packet at the site satisfies $J_q(1)=-\mu(q)$. The finite DPP quadratic is $q_n=w_{L_n}(1)\mu^\top G_n^{-1}\mu$, with $w_L(1)=\sum_{j\ge0}P(1+jL)$. [Capacity criterion](RH/ParetoFirstSiteRHConsequences.lean) · [Vacancy](RH/IntegerDPPClosure.lean) · [Quadratic](RH/RamanujanFiniteSpanBridge.lean) |
| Other fitted systems | The $Q(k)=1/(\zeta(2)k^2)$ system uses $b^Q_q=\sum_{d\mid q}\mu(q/d)d\langle1,g_d\rangle_Q$. Its exhaustive mass, Möbius-coordinate limits and relative-gain divergence have the corresponding RH equivalences. [Q equations](RH/QRamanujanCanonicalOptimizer.lean) · [Q criteria](RH/QRamanujanSaturationCriteria.lean) |

For growing regularized observations the vanishing penalized minimum is equivalent to $e_\infty=0$ **and** vanishing soft cost. A vanishing canonical budget supplies the cost condition. For trials matching $1$ exactly on a physical head, the tail product uses the limiting residual's tail energy times the trial's complete squared error. With eventual head matching, that product tending to zero is equivalent to $e_\infty=0$. These formulations retain their budget and feasibility hypotheses. [Regularized equations](RH/RamanujanRegularizationCriteria.lean) · [Exact-head equations](RH/RamanujanExactHeadFilterCriteria.lean)

## Composite conductors and the screened line

For the closed span $M_{\rm all}$ of every composite packet, the conductor $4$ has
Pareto mean $\log 2$. The mixed packets span the mean kernel in $V$, hence
$M_{\rm all}=V$ and screening against all composites annihilates every packet.
[All-composite closure](RH/CompositePacketClosure.lean)

For the mixed closure $M$, whose indices have at least two distinct prime divisors,
let $W$ be the algebraic span of the screened prime powers.
The mean on $V$ has kernel $M$ and bounded linear section $a\mapsto au$,
where $u=(J_2-P_MJ_2)/\log 2$. Then $W=\mathbb Ru$ and
$M^\perp=W\oplus^\perp V^\perp=\mathbb R1+V^\perp$. The nonzero mixed packet $J_6$ lies in the
ambient $W^\perp$. [Categorical split and ambient complement](RH/MixedConductorRankOne.lean)

**Conditional research reduction.** The proposed identity
$M^\perp=W+\mathbb R1$ is equivalent to $V^\perp=\mathbb R(1-P_V1)$.
Containment of $V^\perp$ in any real line implies RH because a right-hand
zero and its distinct conjugate would yield two independent Mellin functionals.
The spanning identity is open. Identifying $W=\mathbb R1$ from this criterion
also uses the published reverse natural approximation implication as an explicit Lean
hypothesis. [Conditional span criterion](RH/MixedConductorSpanCriterion.lean)

The orthogonal projection is $P_V1=(1-e_\infty)u$, and $u=P_V1$ holds exactly when $u=1$.
A uniform bound on either side of the physical values $u(k)$, for $k\ge1$, implies $u=1$.
Indeed one-sided boundedness of a legal annihilator gives an absolute first-moment tail of
order $1/N$ by dyadic parity testing. The prime number theorem then forces its mean to
vanish. Applied to $1-P_V1$, the mean is exactly its squared norm. An unconditional
one-sided bound for $u$ remains open. [Annihilator tail](RH/ParetoAnnihilatorOneSided.lean)
· [Screened parity criterion](RH/ScreenedParityOneSided.lean)

At conductors through 241 the same 147-coefficient trial on 65,536 positive sites
uses a common residue modulo 30 when combining the group envelopes. The complete
tail bound gives $1-\mathrm{packetMass}(n)\le628101568132839/65537000000000000$
for every stage $n\ge240$ and
$\|u-1\|_P^2\le628101568132839/64908898431867161<1/100$.
The head alone contributes at least $8592900483/10^{12}$ to this fixed trial.
[Complete trial and bound](RH/ParetoGroupedResidueMass.lean) ·
[Congruence envelope](RH/ParetoGroupedResidueMassBase.lean) ·
[Integer head certificate](RH/ParetoGroupedResidueMassData.lean)

For $w_k=1/[k(k+1)]$ the exact mean of $u$ gives
$|u(k)-1|^2\le(k(k+1)-1)\|u-1\|_P^2$. Every complete absolute first-moment
tail starting at $N$ is at most $\sqrt{S(N)/N}$, where $S(N)$ is the remaining
weighted square energy. With $z=1-(1-e_\infty)u$ and
$D_N=\{k:\lfloor k/N\rfloor\text{ is odd}\}$ one has
$\sum_{k\in D_N}w_k z(k)=0$ for every positive $N$.

**Conditional research reduction.** A complete $O(1/N)$ weighted first-moment
tail bound for the smaller of the positive and negative tails of $z$ implies $u=1$.
The choice of sign may vary with $N$. Alternatively a common
one-sided constant for the actual mixed trials at cofinally many cutoffs for
each fixed physical site implies $u=1$. Every finite mixed trial $u_m$ vanishes
at $2(m+1)!$, so its uniform distance from one is at least one. Both analytic
inputs are open.
[Physical bounds and cutoff transfer](RH/ScreenedParityPhysicalBounds.lean)

### Quadratic windows for the actual screened packet

Write $F_N=\exp(A\sqrt{\log N})$ with $A>0$. If the normalized screened packet
differs from one, then, under the published Lee–Leong Mertens estimate, every
sufficiently large $[N,N^2]$ contains more than $F_N^2$ sites with $u(n)<-F_N$
and more than $F_N^2$ sites with $u(n)>F_N$. The cofinal implication allows
the controlled sign to vary between windows. For $5A$ strictly below the
repository's classical contour endpoint, its own Mertens theorem supplies the
arithmetic input. The proof uses a bounded legal test covering $[H,H^2]$, a
signed exterior pairing and both ordinary and reciprocal Möbius sums.
[Window theorem and arithmetic hypotheses](RH/QuadraticWindowSignCriterion.lean)

A finite mixed projection gives a certificate for the actual count on a fixed
window. For a set of evaluations take their sum's Riesz vector, remove its
constant component and its finite mixed projection, and use the norm of the
remainder in the centered projection inequality. Alternatively, limiting
strict excursions eventually persist together on every fixed finite window.
[Finite Gram certificate](RH/ScreenedParityDiameter.lean) ·
[Finite-cutoff count transfer](RH/ScreenedParityWindowCounts.lean)

At $N=16$ the actual packet has at most seven values below $-8$. This uses the
certified complete squared distance to one and the minimum site weight in the
window. [Certified finite window](RH/ScreenedParityCertifiedWindow.lean)

**Open.** Prove that arbitrarily large windows pass a one-sided count bound
for some fixed admissible $A$. Equivalently, for the depth and count budget in
the Gram criterion, exhibit compatible mixed cutoffs on unbounded windows.

## What the ordinate bound proves

Fix a prime $p$. At the same height $T$ take all positive-height nontrivial zeta zeros up to $T$, with analytic multiplicity. For each harmonic $h$ the signed Möbius sum of prime-root probes estimates $c_q(h)$. The negative prefix up to $k\bmod q$ gives a complex $q$-periodic packet $Z_{p,q,T}(k)$. Use its real part as a row $\widehat J_q$. Define $\widehat G,\widehat b$ by the **same complete Pareto expectations** as $G,b$, and $\widehat a=\widehat G^{-1}\widehat b$. Write $r(T)=(\log\log T)^2/\log T$. [Ford and Zaharescu](https://arxiv.org/abs/math/0405459) · [Ordinate construction and uniform rate](RH/RamanujanOrdinateRate.lean)

At each fixed stage, $\widehat G-G$ and $\widehat b-b$ are entrywise $O_{p,n}(r(T))$. The determinant of $\widehat G$ is eventually positive and $\widehat a\to a_*$. At those heights the exact true normal defect is
$$
 d=G\widehat a-b=(\widehat b-b)-(\widehat G-G)\widehat a .
$$
Consequently, in the original arithmetic dictionary,
$$
 0\le \|1-J\widehat a\|_P^2-e_n=d^\top G^{-1}d
       =O_{p,n}\!\left(\frac{(\log\log T)^4}{(\log T)^2}\right).
$$
The empirical mass $\widehat m_n(T)=\widehat b^\top\widehat G^{-1}\widehat b$ tends to $m_n$. The empirical centered determinant ratio tends to $e_n$. [Exact defect, squared rate and determinant limit](RH/RamanujanOrdinateNormalEquations.lean)

There are three additional equivalent tests for $e_\infty=0$.

1. **Entirely unrounded ordinate mass.** For every $\epsilon>0$ there exists a **fixed** $n$ with $\widehat m_n(T)>1-\epsilon$ at arbitrarily large $T$. This works for any single fixed probe prime, including $p=2$. The finite threshold does not depend on $T$. See **rawMassSaturation_iff**.
2. **Unrounded fits on growing conductors.** For any prescribed schedule of prime probes $p_n$, there exists $T_n\to\infty$ with $\|1-J\widehat a_n(T_n)\|_P^2\to0$. More generally, for every positive tolerance sequence tending to zero, a diverging height threshold guarantees excess loss at most that tolerance at every stage. The resulting losses tend to $e_\infty$. See **vanishingOrdinateLoss_iff** and **exists_cofinal_raw_loss**.
3. **Nearest-integer rows.** At sufficiently large heights a common cutoff recovers every entry of $G,b,a_*$ and $m_n$ exactly after rounding each real packet value. Along any prime and height schedules obeying that cutoff, the rounded mass tends to one iff $e_\infty=0$. See **exists_cofinal_rounded_normal_equations** and **exists_ordinate_mass_criterion**.

All three forward implications to RH are unconditional. The height thresholds are existential and the rate constant depends on the finite dictionary. The open arithmetic requirement is to force mass arbitrarily close to one. [Ordinate criteria](RH/RamanujanOrdinateNormalEquations.lean)

## Certified mass through conductor six

Wolfram's five-column fit suggests $m_5\simeq0.96379196536309437$. The following rational trial yields a kernel-checked lower bound, using the period $60$ and the full infinite Pareto mass in each residue class.
$$
 f(k)=\frac{43365457R_2(k)+29484414R_3(k)+7603448R_4(k)
                  +15622522R_5(k)-979754R_6(k)}{10^8}.
$$
For each residue $r=1,\ldots,60$ an upper enclosure of $w_{60}(r)(1-f(r))^2$ is rounded upwards in units of $10^{-15}$. The sixty integer bounds sum to $36\,208\,034\,636\,966$. Therefore every $n\ge5$ satisfies
$$
 m_n\ge 0.963791965363034,\qquad
 e_\infty+\sum_{j=n}^{\infty}\Delta_j
   =1-m_n\le 0.036208034636966 .
$$
The upper bound on this entire remaining budget allows positive limiting error. [Exact certificate and Schur budget](RH/RamanujanSixMass.lean)

The matching dual certificate uses signed masses $y_r$ on the same sixty classes. Each of the five moments $\sum_r y_r R_d(r)$ vanishes exactly. For any trial error $u_r=1-\sum_{d=2}^6 c_dR_d(r)$ and $w_r=w_{60}(r)$, completing the square gives
$$
 \sum_r w_r u_r^2=2\sum_r y_r-\sum_r\frac{y_r^2}{w_r}
                  +\sum_r w_r\left(u_r-\frac{y_r}{w_r}\right)^2 .
$$
Lower enclosures on $w_r$ bound the dual cost from above. Both certificates together enclose the exact normal-equation optimum in an interval of width $1.04\times10^{-13}$,
$$
  0.963791965363034\ \le\ m_5\ \le\ 0.963791965363138 .
$$
The upper endpoint applies to stage five. The lower endpoint persists at later stages by monotonicity. [Primal and dual certificates](RH/RamanujanSixMass.lean)

## A stronger remaining-error and mixed-projection bound

A trial in 65 raw residue atoms through conductor 124 yields a stronger bound for the exhaustive space. Its integer coefficient list, divided by $10^6$, is in the Lean source. The numerator of the pointwise residual has absolute value at most $7\,063\,991$. On sites $1,\ldots,32768$ the sum of the outward-rounded squared errors is at most $10\,810\,291\,372/10^{12}$. The remaining Pareto probability is exactly $1/32769$. For every $n\ge123$,
$$
 e_\infty+\sum_{j\ge n}\Delta_j
   = e_n
   \le \frac{10\,810\,291\,372}{10^{12}}
      +\frac{(7\,063\,991/10^6)^2}{32769}
   =\frac{36\,740\,218\,801\,559}{2\,979\,000\,000\,000\,000}
   <0.012333072 .
$$
The centered signal-to-noise ratio at each such stage is at least $2\,942\,259\,781\,198\,441/36\,740\,218\,801\,559 > 80.0828$. [Conductor-124 certificate](RH/RamanujanResidueMass.lean) · [Integer coefficients and head sum](RH/RamanujanResidueMassData.lean)

Let $\ell=\log 2$, $\kappa=\|\Pi_MJ_2\|_P^2$, and $\kappa_*=\ell-\ell^2$. The rank-one mixed reduction and the normal equations give the exact missing energy
$$
 \kappa_*-\kappa=\ell^2\frac{e_\infty}{1-e_\infty}.
$$
In particular, every finite certified $m_n>0$ gives $\kappa\ge\ell-\ell^2/m_n$. Using the conductor-124 trial gives
$$
 \kappa\ge \ell-\ell^2
 \frac{2\,979\,000\,000\,000\,000}{2\,942\,259\,781\,198\,441}
 \quad\text{and}\quad
 \kappa\ge\frac{971793053}{10^9}\,\kappa_* .
$$
Thus the **full** mixed space captures at least **97.1793053%** of the energy required by the RH criterion. Every sufficiently large finite mixed cutoff exceeds **97.17%** of the target. The proof gives an existential cutoff for that statement. By comparison, at mixed cutoff six the exact capture is $(\ell-\pi/(2\sqrt3))^2/(\pi/\sqrt3)$. The conductor-124 trial concerns the fit to the constant in the full arithmetic dictionary. RH would require the remaining mixed deficit to vanish. [Mixed-capture transfer](RH/RamanujanMixedCaptureBudget.lean) · [Exact cutoff-six capture](RH/ScreenedPrimePowerTelescope.lean)

The same estimate has a direct interpretation in terms of zeta ordinates. For every fixed prime probe and fixed stage $n\ge123$, the unrounded ordinate mass eventually exceeds $0.9876669289$. More generally, if $\widehat m_n(T)\ge b>0$ at arbitrarily large heights for one fixed $n$, then $\kappa\ge\ell-\ell^2/b$. [Ordinate-to-projection inequalities](RH/RamanujanMixedCaptureBudget.lean)
