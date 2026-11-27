# Continuous DPP spectral rigidity and the unfolded zeta ordinates

## The sharp threshold

Let $f\in L^1(\mathbb R)$ be real, $0\le f\le1$ almost everywhere and $\int f=1$. Use cycles per unit, so the continuous Hermitian convolution kernel and regular structure factor are

$$
 K(x)=\int e^{2\pi ixt}f(t)\,dt,\qquad
 S(h)=1-\int f(t)f(t+h)\,dt.
$$

For the associated Lebesgue-reference DPP the intensity is one, and the second factorial density at displacement $x$ is $1-|K(x)|^2$. The centered covariance measure in displacement is $\delta_0-|K(x)|^2 dx$. Its Fourier transform is $S(h)dh$. The uncentered second moment also carries the forward atom at frequency zero. All slopes below concern the regular part.

**Theorem.** If $L=\liminf_{h\downarrow0}S(h)/h<2$, there is an $a\in\mathbb R$ such that $f=\mathbf1_{(a,a+1)}$ almost everywhere. In particular,

$$
 K(x)=e^{2\pi i(a+1/2)x}\operatorname{sinc}(\pi x),\qquad
 S(h)=\min(|h|,1),\qquad
 \rho_2(x)=1-\operatorname{sinc}^2(\pi x).
$$

Here $\operatorname{sinc}(z)=\sin(z)/z$ and $\operatorname{sinc}(0)=1$. The phase conjugates each finite kernel matrix by a diagonal unitary. Thus a genuine DPP with this multiplier has the entire sine-process law. The pair conclusion alone needs only the stated representation of its second factorial measure.

**Proof.** Since $f^2\le f$, all products are integrable. Translation invariance gives the exact identity

$$
 S(h)=\int f(1-f)+\tfrac12\int(f(t+h)-f(t))^2\,dt.
$$

Take $h_n>0$ tending to zero and a $c<2$ for which $S(h_n)\le ch_n$. Both terms on the right are nonnegative, so $f=\mathbf1_E$ almost everywhere for a set of measure one. Squared differences of binary values are absolute differences. Therefore $2S(h)=\int |\mathbf1_E(t+h)-\mathbf1_E(t)|\,dt$.

For $h>0$ put $u_h(x)=h^{-1}\int_x^{x+h}\mathbf1_E(t)\,dt$. This locally absolutely continuous function has derivative $(\mathbf1_E(x+h)-\mathbf1_E(x))/h$ almost everywhere. At every Lebesgue point it tends to the binary value as $h\downarrow0$. For any five ordered Lebesgue points $a_0<\cdots<a_4$,

$$
 \sum_{j=1}^4 |u_h(a_j)-u_h(a_{j-1})|\le 2S(h)/h.
$$

Five values $0,1,0,1,0$ would give $4\le2c$ along the chosen sequence. Such a pattern cannot occur. Let $D_1$ be the value-one Lebesgue points. Finite mass supplies value-zero Lebesgue points arbitrarily far on both sides. Thus any Lebesgue point strictly between two points of $D_1$ has value one. On the open interval between $\inf D_1$ and $\sup D_1$ this proves $f=1$ almost everywhere, and outside its closure $f=0$ almost everywhere. Its mass forces both endpoints to be finite and their difference to be one. Integration over this interval gives the displayed phase and sinc, also at $x=0$. Its overlap with its translate has length $(1-|h|)_+$.

The same translation argument with $C_c^1$ test functions gives the classical BV statement directly. Indeed $\int f\varphi'=\lim_{h\downarrow0}\int [f(t-h)-f(t)]\varphi(t)\,dt/h$, hence $\operatorname{Per}(E)\le2L$. In dimension one a set of finite perimeter and finite positive measure is, up to null sets, a finite union of $m\ge1$ bounded intervals with positive lengths and gaps. Each contributes two jumps. For $h$ smaller than all lengths and gaps, the overlap loses exactly $mh$. Thus any finite lower slope is the integer $m$ and the ordinary right limit exists. The five-point proof above establishes the sharp threshold without invoking this classification. The general covariogram variation theorem is due to Galerne. [Galerne (2011)](https://doi.org/10.5566/ias.v30.p39-51)

**A second proof at slope at most one.** For a projection spectrum, $S$ is even and subadditive by the translation formula. It is continuous by continuity of $L^2$ translations. Along a sequence with $S(h_n)/h_n$ tending to a number at most one, take the integer part of $x/h_n$ and telescope to obtain $S(x)\le x$ for $x\ge0$. The overlap $g=1-S$ is nonnegative, so $g(x)\ge(1-|x|)_+$. Both functions integrate to one by Tonelli and the unit mass of the spectrum. Continuity forces equality everywhere. Fourier transformation of the overlap then gives the entire pair formula directly.

**Sharpness.** $E=[0,1/2]\cup[1,3/2]$ has $S(h)=2h$ for $0<h<1/2$. At $x=1/2$ its kernel vanishes because the two equal integrals have opposite phases. The pair density there is $1$, whereas the sine density is $1-4/\pi^2$.

## A number-variance criterion for the same limiting process

Let $V(R)=\operatorname{Var}N([0,R])$ for an intensity-one process with this two-point representation. Plancherel applied to its covariance and the interval indicator gives

$$
 V(R)=\frac{2}{\pi^2}\int_0^\infty S(h)\frac{\sin^2(\pi Rh)}{h^2}\,dh.
$$

If $S(h)\ge c h$ throughout $0<h<b$, the contribution of this interval is at least $(c/\pi^2)\log R-O_{b,c}(1)$. Indeed $\int_0^{b}\sin^2(\pi Rh)dh/h=\tfrac12\log R+O_b(1)$, by scaling, $2\sin^2 u=1-\cos(2u)$, and integration by parts on $[1,X]$. In particular,

$$
 \liminf_{R\to\infty}\frac{V(R)}{\log R}<\frac{2}{\pi^2}
 \quad\Longrightarrow\quad
 \liminf_{h\downarrow0}\frac{S(h)}h<2.
$$

If the lower slope were at least two, apply the lower estimate for each $c<2$ and let $c\uparrow2$. For $m$ interval components one gets $V(R)=(m/\pi^2)\log R+O_E(1)$, since $S(h)=mh$ near zero and $0\le S\le1$. The coefficient $2/\pi^2$ is sharp.

**Application to actual zeros.** Take all positive ordinates repeated with multiplicity. Set $L_T=\log T/(2\pi)$, draw a uniform center $t\in[0,T]$, and unfold as $Y_T=\sum_i\delta_{L_T(\gamma_i-t)}$. For fixed $R>0$, the count of $(0,R]$ is $\Delta_U N(t)$ with $U=R/L_T$. Its mean tends to $R$, by integrating the difference of the two counts and applying Riemann–von Mangoldt at the boundary. In Goldston–Lee–Schettler–Suriajaya, equations 5.2 and 5.6 hold uniformly for $0<U\le1$. They give an absolute $C$ such that

$$
 \limsup_{T\to\infty}{\mathbb E}(Y_T((0,R])-R)^2
 \le \pi^{-2}\log(2+R)+C\sqrt{\log(2+R)} .
$$

First take height to infinity at each fixed $R$, then take $R\to\infty$. The dyadic center convention $t\in[T,2T]$ gives the same leading coefficient by subtracting the two height integrals at this same physical width. A global truncation at $T$ changes fixed-window moments by $o_R(1)$, using the boundary region of length $O_R(1/\log T)$ and the classical $O(\log T)$ local count there. [Goldston, Lee, Schettler and Suriajaya, §5](https://arxiv.org/html/2503.15449v4#S5)

Suppose along some heights the full translated law converges locally in distribution to a continuous convolution DPP. In the complete physical unfolding its intensity is automatically one. The local first moments tend to the window length, and the fixed-window second-moment bounds make those counts uniformly integrable. A stationary locally finite limit with finite mean has no atoms at fixed endpoints, so this mean passes to the limit. Truncating the squared count and using convergence, then taking the truncation to infinity, transfers the displayed upper bound to the variance of this same limit. Thus its logarithmic coefficient is at most $1/\pi^2$, and the limit is the sine process. This implication uses an unconditional external zeta moment theorem. The sharp zeta moment estimate is not itself a Lean result of this change.

To conclude **ordinary positive-gap PCC** one needs control of the whole family. Local tightness follows from the local first-moment bounds. It suffices that every subsequential limit of the complete physical process admit the convolution two-point representation. Fujii's higher moments give uniform integrability of fixed-window pair counts. For centers in $[0,T]$, sum the fixed-window bound on dyadic height intervals. The physical width $R/L_T$ is at most the width at the lower height of each dyadic interval, so monotonicity preserves the bound. In the sine limit the second factorial measure gives zero mass to coincident points or to the fixed gap $q$. Testing ordered pairs with first point in a unit window and displacement in $(0,q]$ therefore gives $\int_0^q(1-\operatorname{sinc}^2(\pi x))\,dx$. Averaging the center counts each interior anchor with weight $1/(T L_T)$. Boundary anchors give $o_q(1)$ by the same boundary estimate. This is the repository's multiplicity convention. Rational widths and monotonicity give compact-uniform convergence on positive widths. One subsequential kernel identification yields only the corresponding subsequential conclusion. [Arias de Reyna and Rodgers, Theorem 34 and Corollary 35](https://arxiv.org/abs/2311.13441)

## Which kernel limit would suffice?

For a process-level proof it suffices to identify the law **after averaging the translation center**. For each subsequence with a local limit, exhibit one fixed Hermitian convolution operator $K=\mathcal F^{-1}M_f\mathcal F$ on $L^2(\mathbb R,dx)$, $0\le f\le1,\int f=1$, such that for every nonnegative compactly supported continuous $g$,

$$
 \lim\mathbb E\,e^{-\int g\,dY_T}
 =\det\!\left(I-M_{\sqrt{1-e^{-g}}}\,K\,M_{\sqrt{1-e^{-g}}}\right)
$$

along that subsequence. A version originating with the retained configurations also needs a comparison with $Y_T$. For an actual family of deterministic Lebesgue-reference DPP operators for the averaged laws, local trace-norm convergence suffices. Weak operator convergence together with convergence of traces on bounded compressions is a standard way to obtain it for positive locally trace-class contractions. Atomic reference measures on moving zero sites require an identification with the common space and a proof that the resulting point laws approximate the original statistics. [Soshnikov, Theorem 5](https://www.math.ucdavis.edu/~soshniko/stati/umn.pdf)

For a direct low-frequency route, use the centered finite-window periodogram of the **same** limit $Y$. Exactly,

$$
 R^{-1}\mathbb E\left|\int_{[0,R]} e^{-2\pi ihx}(Y(dx)-dx)\right|^2
 =1-\int (1-|u|/R)_+e^{-2\pi ihu}|K(u)|^2\,du
 \longrightarrow S(h).
$$

The last limit follows by dominated convergence, since $f\in L^2$. For the arithmetic family one needs convergence of the corresponding centered second moments at each fixed window and frequency, followed by expanding the window. One may also identify the regular spectral distribution on an open punctured neighborhood and use continuity. One sequence $h_j\downarrow0$ with upper slopes bounded by some $c<2$ suffices. Subtraction of the forward intensity atom and transfer of all-occurrence statistics matter. The Fujii variance route supplies this slope bound indirectly for the full process.

## Audit of the prime-frequency projection and Landau inputs

The source baseline is [175b3a42](https://github.com/Cnoack3/RiemannResearch/commit/175b3a4260d267688663d697a3fdcd6ab15d6166). The horizontal reconstruction result is [21dc7c15](https://github.com/Cnoack3/RiemannResearch/commit/21dc7c15c809937e70042c75f4e8ed9f509cc813).

| Operation | Established identity or estimate | What it supplies for this proof |
|---|---|---|
| Prime-feature exhaustion on zero labels | For occurrences $i,j$, $P_{ij}=\mathbf1_{\gamma_i=\gamma_j}/m_{\gamma_i}$. Fixed finite marginals eventually agree with this limit. [Prime DPP](Probability/ZeroOrdinatePrimeDPP.lean) | One representative per ordinate fibre. The occupied quotient heights are deterministic. Moving-height local convergence is an additional limit. A finite-rank feature projection of rank $r$ on an $N$-site window deletes at least $N-r$ labels in expectation. |
| Forget the labels | The pushforward is a DPP on the distinct-ordinate quotient with counting reference measure. In the exhaustive case its quotient kernel is the identity. [Fibre DPP](Probability/ZeroOrdinateFiberDPP.lean) · [Quotient DPP](Probability/ZeroOrdinateQuotientDPP.lean) | The convolution representation on Lebesgue space remains open. |
| Randomize the physical center | A shift of $s$ unfolded units shifts the uniform center interval by $s/L_T$, changing bounded-test expectations by at most $2\lVert F\rVert_\infty\lvert s\rvert/(T L_T)$. | Local limits are stationary. Averaging determinants over the center gives a mixture whose higher correlations require their own identification. In the shifted lattice example differences remain in $a\mathbb Z$, so its nonzero second factorial measure is singular on the union of the lines $y-x\in a\mathbb Z$. A continuous Lebesgue DPP has an absolutely continuous second factorial measure. [Microscopic note](RIEMANN_MICROSCOPIC_SELBERG_TRACE_20261125.md) · [Lagarias and Rodgers](https://arxiv.org/abs/1907.03391) |
| Restore occurrence multiplicities | Fibre multiplicity marks reproduce complete occurrence statistics pathwise. Without marks the cutoff vacancy is $N-\#\{\text{distinct ordinates}\}$ plus a nonnegative feature residual, zero at exhaustion. [Window statistics](Analysis/ZeroDPPWindowVariance.lean) · [Quotient vacancy](Probability/ZeroOrdinateQuotientDPP.lean) | The marked identity returns the original arithmetic statistic. The auxiliary residue/Mellin sine limit is a different model and its identification with this family is open. Unmarked pair transfer needs an estimate for deletion. [Square-tail criterion](Analysis/MicroscopicSquareTailCriteria.lean) |
| Reconstruct horizontal weights | Uniformly for $\lvert u_b\rvert\le(4/3)\log T$, with the prescribed Taylor orders, the discrepancy between the count-normalized actual cosine-pair sum and reconstructed squared amplitude is at most $C\sum_b\lvert c_b\rvert/T$ for finite weighted tests. Both count all ordered pairs with ties. [Weighted reconstruction](Analysis/RationalLandauInghamTangent.lean) | An error $o(1)$ follows if $\sum\lvert c_b\rvert=o(T)$. The value of the corrected amplitude, localization to the physical window, and the subtraction of the forward atom require further estimates. |
| Evaluate Landau/form-factor main terms | For $u=\log(n/m)>0$ the rational Landau band uses $\log n+3u/2\le\theta\log T$, $\theta<1$, hence $u/\log T\le2\theta/5$. At fixed $\alpha>0$, the repository's Cauchy-weighted all-occurrence form-factor limit $\ell$ is equivalent to the signed arithmetic correction tending to $\ell-\alpha$. [Landau](Analysis/RationalLandauMovingBand.lean) · [Signed correction](Analysis/MontgomeryOrdinateResidual.lean) | The triangular value $\ell=\alpha$ would require vanishing of the third-term/prime-off-diagonal correction minus the horizontal correction. Dense frequencies and the wider horizontal error estimate provide neither this signed cancellation nor identification with the regular structure factor of the same local limit. |

**Deletion and conditional fluctuations.** Write $X_T\subset Y_T$ for an unmarked retained configuration. For a fixed bounded interval $I$, if $X_T$ converges locally to an intensity-one process in the original unfolding, its limiting mean is $|I|$. The full counts satisfy $\mathbb E Y_T(I)\to|I|$. Truncating $X_T(I)$ and using convergence gives $|I|\le\liminf\mathbb E X_T(I)$. Consequently $\mathbb E(Y_T(I)-X_T(I))\to0$, so the two configurations agree on $I$ with probability tending to one. With the full fourth local moments, the expected loss of any bounded local pair test tends to zero by Cauchy–Schwarz. Establishing unit intensity in the physical normalization is essential. Rescaling a thinned configuration to give it unit intensity does not establish this comparison.

There is a further obstruction to proving this by convergence conditional on the center. Fix $0<|I|<1$ and let $F=\mathbf1_{\{N(I)>0\}}$. At a fixed center $t$, $Y_T$ is deterministic. With $\delta_T=\mathbb E(Y_T(I)-X_T(I))$,

$$
 \mathbb E_t\operatorname{Var}(F(X_T)\mid t)
 \le\mathbb E_{t,\omega}|F(X_T)-F(Y_T)|^2\le\delta_T .
$$

If $\delta_T\to0$, the average conditional variance vanishes. For an intensity-one limit $0<\mathbb P(N(I)>0)\le|I|<1$, so its occupancy observable has strictly positive variance. Per-center convergence in probability of the first two conditional moments to the same limiting moments is therefore impossible in this regime. Fluctuations of the translation center survive in the averaged law. For the exhaustive projection on distinct heights the conditional occupancy is already deterministic.

The repository's direct PCC endpoint remains the signed estimate $H_T(q)-P_T(q)-B_T(q)\to0$ for every positive rational $q$. Along the representation route the outstanding arithmetic obligation is to prove convolution two-point structure for **every** physical subsequential limit, or an averaged Fredholm representation for full process identification. The identities audited here do not discharge it. [PCC obligation and exact conventions](PCC_REMAINING_PROOF.md)

## Lean statements and the zeta-specific obligation

| Subject | Reusable declaration |
|---|---|
| Strict lower slope below two implies an a.e. interval and the full Fourier phase and pair density | [spectral_rigidity_of_liminf_lt_two](Probability/DPPContinuousSpectralRigidity.lean) |
| Cofinal logarithmic bounds for the normalized spectral window integral imply the interval and pair formula | [sine_pair_of_log_window_bound](Analysis/DPPNumberVarianceRigidity.lean), with the integrability of each displayed spectral window as an explicit hypothesis |
| Sharp logarithmic lower estimate and extraction of small frequencies | [small_steps_of_log_windowEnergy](Analysis/DPPNumberVarianceRigidity.lean) |
| Projection spectrum, exact squared translation defect and binary translation formula | [DPPSpectralMultiplier](Probability/DPPSpectralMultiplier.lean) |
| Differentiation of right averages, ordered oscillation and interval extraction | [DPPAveragedVariation](Probability/DPPAveragedVariation.lean) · [DPPBinaryInterval](Probability/DPPBinaryInterval.lean) |
| Unit-interval Fourier transform, phase and triangular autocorrelation | [DPPIntervalSpectrum](Probability/DPPIntervalSpectrum.lean) |
| Independent proof at slope at most one via subadditivity and the total mass of the overlap | [DPPTranslationRigidity](Probability/DPPTranslationRigidity.lean) |
| Loss of conditional variance under vanishing local deletions | [DPPDeletionVariance](Probability/DPPDeletionVariance.lean) |

The spectral theorems operate on Lebesgue multipliers and the corresponding integrals. The determinantal law interpretation follows from the finite correlation determinants and the Fourier representation above. The external zeta moment theorem, its passage to subsequential point laws and the unresolved convolution representation for actual zeros have distinct roles. The repository's weaker large-window hypothesis is named ShortWindowSecondMomentUpper. [Positive-gap density](Analysis/MontgomeryPositiveGapDensity.lean)
