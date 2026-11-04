# Prime products and the derivative-energy obstruction

Research continuation, 4 November 2026. This note summarizes the main proofs and the disposition of all twelve items in *Orthonormal Prime Blocks for Squarefree Residue Approximation*. The companion PDF/TeX contains the full arguments and bibliography. **RH is not proved.**

## Setting and published criterion

Put $q=1/\zeta(2)$, $Q(n)=q/n^2$, $g_d(n)=(n\bmod d)/d$, and let $V$ be the closed squarefree residue span in $L^2(Q)$. [Bagchi (2006), Remark 8](https://www.isibang.ac.in/~statmath/eprints/2005/isibc200535.pdf) gives RH iff $1\in V$, using the comparable Pareto and inverse-square weights. This does not make the squarefree dictionary total in the ambient Hilbert space.

Anchor sequences at zero. Then $\Delta f(n)=f(n)-f(n-1)$ is bounded and injective, $\Delta1=\delta_1$, and $\Delta g_d=1/d-\mathbf1_{d\mid n}$.

## The exact tensor optimizer and its legal primitive

For a nonempty finite prime set $S$, set

$$m=|S|,\quad M=2^m,\quad L=\prod_{p\in S}p,\quad a=\prod_{p\in S}(1-p^{-2}),\quad b=\prod_{p\in S}\frac p{p+1}.$$

Under $Q$, the bits $B_p=\mathbf1_{p\mid n}$ are independent Bernoulli$(p^{-2})$; see the absolutely convergent [Euler product](https://dlmf.nist.gov/25.2.E11). Put $W_S=\operatorname{span}\{g_d:1<d\mid L\}$ and

$$h_S=b\prod_{p\in S}(1+pB_p),\qquad C_S=\prod_{p\in S}(1-B_p).$$

The local likelihood moments multiply to $\mathbb E_Qh_S=1$, $\langle h_S,B_d\rangle_Q=1/d$, and $\|h_S\|_Q^2=Mb$. There are $M-1$ independent derivative atoms orthogonal to $h_S$, so their span is precisely the hyperplane perpendicular to $h_S$ in the Boolean cylinder space. Conditional expectation of $\delta_1$ on the Boolean cells is $(q/a)C_S$. Removing its normal component yields

$$D_S=P_{\Delta W_S}\delta_1=\frac q a C_S-\frac qM h_S,$$

$$r_S^2=\|\delta_1-D_S\|_Q^2=q-\frac{q^2}{a}+\frac{q^2b}{M}.$$

Every $F\in W_S$ satisfies the exact remainder

$$\|\Delta F-\delta_1\|_Q^2=r_S^2+\|\Delta F-D_S\|_Q^2.$$

The unique anchored primitive is the explicit finite legal vector

$$F_S=q\sum_{1<d\mid L}\left(\frac{bd}{M}-\frac{\mu(d)}a\right)g_d.$$

The signed subset expansion, actual divisor-atom bridge, finite legality, physical derivative, exact full error, and minimization are kernel-checked in the finite derivative modules and `QPrimeDerivativePrimitive.lean`. No arithmetic premise beyond distinct prime factors is needed.

Along the first primes, $a\to q$ and $b/M\le2^{-m}$, hence $D_S\to\delta_1$. Point evaluation and anchored finite summation give $F_S(n)\to1$ for each fixed positive integer. These limiting arguments use Euler's product and have mathematical-proof scope in the report.

## Fully formalized arithmetic no-go

The identities $\sum_{d\mid L}\mu(d)=0$, $\sum_{d\mid L}\mu(d)/d=ab$, $b\sum_{d\mid L}d=L$, and the residue period mean give

$$\sum_{n=1}^L F_S(n)=\frac{qL^2}{2M}.$$

Weighted Cauchy on the first period, retaining part of the actual complete norm, gives

$$\|F_S\|_Q^2\ge q\frac{(\sum_{n=1}^L F_S(n))^2}{\sum_{n=1}^L n^2}\ge\frac{q^3L}{4M^2}.$$

For the first $m\ge2$ primes, $L/4^m\ge(3/8)(5/4)^{m-2}$. Consequently the complete norms squared tend to infinity and no uniform energy budget exists. **All of these arithmetic steps are kernel-checked**, culminating in `QPrimeDerivativeEnergyNoGo.ordinalPrimitive_norm_sq_tendsto_atTop` and `ordinalPrimitive_no_uniform_energy_budget`. There is no remaining period-mean, prefix-energy, or asymptotic hypothesis in those theorems.

This obstructs the explicit unregularized derivative minimizers, not arbitrary legal approximants or regularized constructions. A further mathematical consequence, not separately formalized, is

$$\|F_S-1\|_Q^2\ge\frac{q^3L}{4M^2}-\frac{q^2}{M}+\frac qL\longrightarrow\infty.$$

## Other checked results

- Every radical-compatible function of one odd-prime valuation is constant. A nonzero legal such factor therefore implies RH; its existence remains Open.
- The parity exception is exact: $f=\varphi(1)1+2(\varphi(0)-\varphi(1))g_2$, with legality iff legality of $\varphi(1)1$. A nonzero even value is required for the conditional RH reduction.
- The actual projection of $g_p$ onto its own valuation subspace is illegal at every odd prime. Coordinate conditioning does not preserve legality.
- Actual monotone cofinal packet errors obey the exact product formula; closure is equivalent to nonsummable relative packet gains. A nonsummable benchmark with summable nonnegative deficit suffices, but its arithmetic estimate remains Open.
- Positive gains alone are insufficient: $r_n=1/(n+2)^2$ and $E_n=(n+2)/(2(n+1))\ge1/2$ give a checked abstract counterexample. This is not a counterexample to the actual arithmetic gains.

The actual legal trials

$$T_6=g_2+g_3+\tfrac23g_6,\qquad T_{30}=g_2+g_3+\tfrac45g_5-\tfrac15g_6+\tfrac15g_{15}+\tfrac15g_{30}$$

satisfy the fully checked complete-norm bounds

$$\|1-T_6\|_Q^2<1/16,\qquad\|1-T_{30}\|_Q^2<27/1000<1/32.$$

The proof retains two complete periods and every remaining progression tail. Summability, $\sum_{k\ge0}(a+(k+1)L)^{-2}\le1/(La)$, exact periodic regrouping, and $29/18<\zeta(2)<5/3$ are all formalized. The report separately proves the old period-six optimizer lower bound $E_6>3/64$, giving mathematical relative-gain certificates greater than $3/4$ and $53/125$. The optimizer lower bound/gain interpretation is not asserted as a new Lean theorem.

## Remaining decisive estimate

The report identifies $\overline{\Delta V}$ with the radical-measurable subspace: a fixed Boolean cylinder has distance squared from $\Delta W_S$ equal to a fixed tilted-mean numerator divided by $\prod_{p\in S}2p/(p+1)$. This denominator tends to infinity, so the distance tends to zero. Cylinder density supplies the closure statement. This does not permit pulling closure through the unbounded primitive map.

For $J_\lambda(F)=\|\Delta F-\delta_1\|_Q^2+\lambda\|F\|_Q^2$, derivative Gram eigenvalues $s_j>0$ and target coordinates $\beta_j$ give

$$\frac{J_{N,\lambda}^{\min}}\lambda=\frac{r_N^2}\lambda+\sum_j\frac{\beta_j^2}{s_j(s_j+\lambda)}.$$

The first term is now explicit for primorial spaces. A cofinal coupled choice $\lambda_j\to0$ keeping both terms bounded remains Open. The global liminf budget condition is equivalent to $1\in V$ by weak compactness and injectivity of $\Delta$; the detailed proof is in the report. [Albani–Elbau–de Hoop–Scherzer (2016)](https://doi.org/10.1080/01630563.2016.1144070) supplies relevant regularization theory, but its data-in-range assumption is itself the RH-sensitive existence premise here and is not used circularly.

Standard Schur and projection algebra uses [Boyd–Vandenberghe, Appendix A.5.5](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf), retaining the complete norm remainder. The auxiliary Bernoulli$(1/p)$ infinite law is singular with respect to the Bernoulli$(1/p^2)$ law by [Borel–Cantelli](https://math.duke.edu/~rtd/PTE/PTE5_011119.pdf); finite likelihoods do not provide a global bounded density.

## Disposition of all twelve items

| Item | Outcome |
|---|---|
| 1: projection-to-RH chain | Actual arithmetic interface audited; infinite gain provider Open. |
| 2: finite exceptions | Strengthened to summable deficits; arithmetic premise Open. |
| 3: dimensions | Divisor split and innovation dimension proved mathematically. |
| 4: Schur/approximate solves | Full remainders and certified directional bounds; no uniform arithmetic estimate inferred. |
| 5: complete certificates | Actual legal trial errors <1/16 and <27/1000 fully checked. |
| 6: tensor legality | Odd-prime rigidity, parity exception, and conditioning obstruction checked. |
| 7: residualized means | Useful directional consumers; no cofinal arithmetic provider or counterexample established. |
| 8: packet gains | Actual packet criterion checked; positivity-only shortcut refuted abstractly. |
| 9: derivative spectrum | Exact tensor optimizer, legal primitive, and actual energy divergence checked. |
| 10: source conditions | Range-assumption circularity excluded; regularized energy budget Open. |
| 11: closed legality | Derivative closure identified mathematically; full primitive-space equality Open. |
| 12: persistence | Five successful code checkpoints, final catalog, proofs, and diagnostics recorded. |

The exact publication and axiom evidence is in `../THEOREM_CATALOG_PRIME_BLOCK_CONTINUATION_20261104.md`. All five code checkpoints passed aggregate plus affected-module builds and were pushed. Representative axiom reports contained only `propext`, `Classical.choice`, and `Quot.sound`. Wolfram and exact Python computations are diagnostics, not proof substitutes. No nonsummable actual-gain estimate or bounded regularized primitive budget has been established.
