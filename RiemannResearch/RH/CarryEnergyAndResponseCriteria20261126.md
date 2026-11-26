# Fifteen carry, energy, and projection results

There are three distinct Hilbert-space constructions here. Raw CRT carries generate the full legal residue space, corrected carries generate the mixed packet space, and the moving short-head estimates use the squarefree residue dictionary. Statements about a residual or a budget below always refer to the indicated dictionary. All physical sites are positive unless a zero evaluation functional is explicitly introduced.

The full-conductor and squarefree constant-membership implications used here are the corresponding checked physical criteria. The classical integer-dilation Nyman–Beurling criterion is due to Báez-Duarte. [Integer-dilation criterion](https://arxiv.org/abs/math/0202141) · [Squarefree converse](ParetoSquarefreeDampingConverse.lean)

| Items | Result |
| --- | --- |
| 1–3 | Two-carry approximation, mixed-span inversion, and bounded Gram reconstruction |
| 4–5 | Exact relative projection gains and loss-corrected dyadic excess |
| 6–7 | Endpoint Mertens energy and corrected semiprime blocks |
| 8, 12, 14 | Signed logarithmic heads and simultaneous block errors |
| 9, 11 | Uniform moving-head energy, including varying weight indices |
| 10, 13 | Congruence anchors and signed harmonic Schur tests |
| 15 | Strong reconstruction and polarized digamma coefficients |

## Raw carries, corrected carries and reconstruction

Work on physical sites \(n\ge1\), with \(P_n=1/[n(n+1)]\) and \(Q_n=1/[\zeta(2)n^2]\). Write \(g_d(n)=\{n/d\}\), and let \(C_d=\sum_{p\mid d}c_{d,p}g_{p^{v_p(d)}}-g_d\) denote the unprojected canonical CRT carry for a mixed conductor \(d\) (at least two distinct prime divisors). A bar over a span denotes norm closure.

**1. Raw carries.** Fix a prime power \(a\) and take \(b=2^k\to\infty\). Choose a prime \(t>\max(a,b^2)\) congruent to \(1\bmod ab\). With \(w_c(t)=1-1/c+1/(ct)\), the CRT inverse coefficients give \(C_{ct}=g_c+t w_c(t)g_t-g_{ct}\) for \(c=a,b\). Therefore the two-carry approximation \(x=w_b(t)C_{at}-w_a(t)C_{bt}\) satisfies
\[
 x-g_a=(w_b(t)-1)g_a-w_a(t)g_b-w_b(t)g_{at}+w_a(t)g_{bt}.
\]
Both coefficients in \(x\) have absolute value at most one. In either physical norm \(\|g_d\|\le c_0/\sqrt d\), with \(c_0=\sqrt{2/\zeta(2)}\) for \(Q\) and \(c_0=\sqrt2\) for \(P\). For example, use \(\{n/d\}=n/d\) for \(n<d\) and \(\{n/d\}\le1\) thereafter, or transfer the established \(Q\) bound. Thus
\[
 \|x-g_a\|\le \|g_a\|/b+\|g_b\|+\|g_{at}\|+\|g_{bt}\|
 \le c_0/\sqrt b+O_a(1/b).
\]
This rate is in the freely chosen balancing parameter \(b\). Every prime-power atom is a norm limit of two raw carries with absolute coefficient mass at most two. For a mixed \(d\), the defining CRT identity now approximates \(g_d\) by at most \(1+2\omega(d)\) raw carries, where \(\omega(d)\) counts distinct prime divisors. The reverse span containment follows directly from the formula for \(C_d\). Consequently the closed raw carry span equals the full closed legal residue span under both measures. Constant membership in that span remains the RH criterion. [Canonical carry closure](CanonicalCarryClosure.lean)

Finite deletions admit an exact description. For a mixed \(d\) let
\[
 \Lambda_d(f)=-\sum_{k\mid d}\mu(d/k)\bigl(f(k)-f(k-1)\bigr),\qquad f(0)=0.
\]
This finite-coordinate functional is continuous in either physical norm. Since \(\Delta g_e(k)=1/e-\mathbf1_{e\mid k}\), divisor inversion gives \(\Lambda_d(g_e)=\mathbf1_{d=e}\) and \(\Lambda_d(C_m)=-\mathbf1_{d=m}\) for mixed \(m\). For any finite set \(S\) of omitted mixed conductors the remaining closed raw span is exactly \(V\cap\bigcap_{d\in S}\ker\Lambda_d\), of codimension \(|S|\) in the full legal span \(V\). Indeed, given \(x\) in that intersection, approximate \(x\) by finite raw sums \(y_j\). Removing the coefficients \(-\Lambda_d(y_j)\) of the omitted rows changes \(y_j\) by a vector tending to zero. The omitted rows give independent complementary classes. In particular every individual mixed raw row is necessary for full density.

**2. Corrected carries.** Let \(K_d\) be the corrected carry, normalized as in the source, and \(J_d\) the mixed packet. Put \(J_d^{\rm mix}=J_d\) for mixed \(d\) and \(0\) otherwise. Then
\[
 K_d=\sum_{e\mid d}J_e^{\rm mix},\qquad
 J_d^{\rm mix}=\sum_{e\mid d}\mu(d/e)K_e .
\]
The first identity follows by cancelling the prime-power part of the CRT packet expansion, the second by Möbius inversion for positive integers. Every finite window closed under taking divisors therefore has identical corrected-carry and mixed-packet spans, including the interval windows through \(N\) (one may adjoin the zero label \(1\)). Taking an increasing exhaustion proves the closure identity. The positivity and uniform comparison of the two physical weights also identify the closures under the physical sequence map. The two finite Pareto projections agree at every depth, with a common limiting mixed projection. Its endpoint energy is a further arithmetic question. [Corrected carry identities](MixedCanonicalCarryCapture.lean)

**3. Prescribed moments and Gram cost.** Fix arbitrary real data \(b_d\), \(d\ge2\), and choose one of the two inner products. On a finite set \(S\) of distinct conductor labels put \(G_S=(\langle g_d,g_e\rangle)_{d,e\in S}\), \(c_S=b_S^\mathsf TG_S^{-1}b_S\), and \(x_S=\sum_{d\in S}(G_S^{-1}b_S)_d g_d\). The atoms are finitely independent. The minimum is taken over all vectors with moments \(\langle g_d,x\rangle=b_d\) on \(S\), and \(c_S=\|x_S\|^2\). For \(S\subset T\), \(P_Sx_T=x_S\) for the projection onto the \(S\)-atom span, whence
\[
 \|x_T-x_S\|^2=c_T-c_S.
\]
For nested, cofinal all-divisor stages, a common bound along even one cofinal subsequence bounds all \(c_S\). The cost increments then make the stage minimizers Cauchy. Their limit \(x\) has every prescribed moment and belongs to the closed legal span. Two such legal solutions differ by a vector orthogonal to that same span, hence coincide. Conversely any representer \(y\) bounds all costs by \(\|y\|^2\). For the unique legal solution the exact error is \(\|x-x_S\|^2=\sup_T c_T-c_S\). Every finite or global cost obeys \((\zeta(2)/2)c_P\le c_Q\le\zeta(2)c_P\) for the same data, by applying the two norm comparisons to the finite synthesis dual quotient. Solvability depends on the target. In particular \(b_d=d^{-1/2}\) yields finite feasible problems at every stage and unbounded costs under both metrics, since any representable data satisfy \(\sqrt d\,b_d\to0\). [Physical reconstruction and obstruction](ConductorReconstructionEnergy.lean) · [Exact norm defect](../Analysis/HilbertConstraintEnergy.lean)

## 4. Complete correction budgets and residual contraction

Let \(V_N\) be the full finite legal residue stage, \(p_N=P^Q_{V_N}1\), \(r_N=1-p_N\), and let \(\sigma\) be nondecreasing. Write \(E_i=\|r_{\sigma(i)}\|_Q^2\). A positive budget \(K_i\) requires, whenever \(E_i>0\), a \(w\in V_{\sigma(i+1)}\) of nonzero pairing satisfying
\[
 E_i\frac{\|w\|_Q^2}{|\langle r_{\sigma(i)},w\rangle_Q|^2}\le K_i .
\]
The largest squared pairing per squared norm in this stage is exactly \(\|p_{\sigma(i+1)}-p_{\sigma(i)}\|_Q^2=E_i-E_{i+1}\) by orthogonal projection. Thus the budget is equivalent to \(E_i/K_i\le E_i-E_{i+1}\), including finite termination. With \([x]_+=\max(x,0)\),
\[
 E_n\le E_0\prod_{i<n}[1-K_i^{-1}]_+
 \le E_0\exp\!\left(-\sum_{i<n}K_i^{-1}\right).
\]
The product keeps a zero factor when a budget forces finite termination. On an uncertified transition nested projections still give \(E_{i+1}\le E_i\). The same proof therefore uses only the certified indices in the product and sum. Divergence on those indices forces \(E_n\to0\) and \(1\in\overline{\bigcup_N V_N}\), hence RH by the full-conductor criterion. If the limiting full residual has squared norm \(\delta>0\), even the partial sums on the certified set satisfy \(\sum 1/K_i\le\log(E_0/\delta)\). Existence of enough actual next-stage witnesses remains open. [Full correction budgets](QFullCorrectionBudgetDescent.lean)

On every nondecreasing cofinal schedule there is also an exact criterion in terms of the optimal observed gains. Every atom in the finite stage vanishes on multiples of \(L=\operatorname{lcm}(2,\ldots,\sigma(i)+1)\), a set with \(Q\)-mass \(L^{-2}\). Thus \(E_i>0\) even at finite periods where a particular transition gains nothing. With \(\lambda_i=(E_i-E_{i+1})/E_i\in[0,1)\), telescoping gives
\[
 \prod_{i<n}(1-\lambda_i)=E_n/E_0.
\]
This product tends to zero exactly when \(\sum_i\lambda_i=\infty\). Indeed \(x\le-\log(1-x)\le2x\) on \([0,1/2]\), and infinitely many terms above \(1/2\) force both sums to diverge. Cofinal projections converge strongly to the full legal projection. RH puts \(1\) in the squarefree legal closure, hence in the full closure, and the full-conductor criterion proves the converse. Therefore
\[
 \mathrm{RH}\quad\Longleftrightarrow\quad\sum_i\lambda_i=\infty
\]
for every such schedule. On a strictly gaining transition the optimal normalized budget is exactly \(1/\lambda_i\). This reformulates the remaining arithmetic question using the actual weighted residuals alone. [Full projections](QFullResidueProjection.lean) · [Squarefree converse](ZetaTwoCRTSquarefreeConverse.lean)

## 5. A sparse-excess dyadic criterion

For this statement let \(D_m=\operatorname{stageEnergy}(\operatorname{denseSchedule},2^m)\), the complete energy of the squarefree optimizer. Choose legal trial coefficients \(t_i\) indexed by the added conductors. Denote the sum of their signed full certificates over \(2^m\le i<2^{m+1}\) by \(S_m\), and the sum of the corresponding nonnegative loss squares by \(L_m\). The exact interval identity is \(D_{m+1}-D_m=S_m-L_m\). For fixed \(B\ge0\), the proposed excess is \(a_m=[S_m-B]_+/(1+D_m)\), taking the positive part after summing the entire block. Set
\[
 x_m=\frac{[S_m-L_m-B]_+}{1+D_m}\le a_m,\qquad Y_m=1+D_m .
\]
Then \(Y_{m+1}\le (1+x_m)Y_m+B\). Iteration, using that each multiplier is at least one, proves
\[
 Y_n\le (Y_0+nB)\prod_{i<n}(1+x_i).
\]
In particular it suffices that
\[
 \liminf_{n\to\infty}\frac1n\sum_{i<n}\log(1+x_i)=0 .
\]
Choose a cofinal sequence attaining the lower limit. Taking logarithms in the product bound, the additive contribution is \(\log(Y_0+nB)=o(n)\). Since \(\log(2^n+2)\sim n\log 2\), the optimizer energy has subpolynomial growth on the resulting cofinal sequence of physical heads. The complete exact-head theorem then gives RH. The same criterion with \(a_i\) is sufficient since \(x_i\le a_i\), and \(a_i\to0\) implies it by Cesàro convergence. The logarithmic average permits sparse large excesses. The loss-corrected quantity itself is independent of the chosen trial coefficients by the exact interval identity. The same iteration allows block-dependent baselines \(B_i\ge0\). Replace \(nB\) by \(\sum_{i<n}B_i\), and require \(\log(Y_0+\sum_{i<n} B_i)/n\to0\) on the same subsequence. In particular every fixed polynomial baseline in the dyadic index is admissible. The arithmetic control of the resulting excess remains open. [Dyadic trial budgets](QCRTDyadicBudget.lean) · [Cofinal optimizer criterion](QCRTOptimizerGrowth.lean)

## 6. Endpoint Mertens energy and the grouped off-diagonal

Put \(M(n)=\sum_{j\le n}\mu(j)\), \(A(n)=\sum_{j\le n}\mu(j)^2\) and \(w_n=n^{-2-2\varepsilon}\). The finite ungrouped energy is \(\sum_{n\le N}w_n M(n)^2\). Its off-diagonal has the two exact finite descriptions
\[
 O_\varepsilon(N)=\sum_{n\le N}w_n\big(M(n)^2-A(n)\big)
 =2\sum_{j\le N}\mu(j)M(j-1)\sum_{n=j}^N w_n .
\]
These follow by expanding the square before interchanging finite sums. For each integer \(a\ge0\) the repository's unconditional Mertens estimate gives \(|M(n)|(6+\log n)^{a+2}\ll_a n\). Using \(|M(n)|\le n\), comparison with \(\sum_{n\ge2}1/(n\log^2 n)\) gives
\[
 \sum_{n\ge1}\frac{M(n)^2(6+\log n)^a}{n^3}<\infty,\qquad
 \sum_{n\ge1}\frac{|M(n)|(6+\log n)^a}{n^2}<\infty.
\]
Consequently the energy converges for every \(\varepsilon\ge1/2\). For **any** \(\varepsilon>0\) at which the energy is finite, the absolute grouped increments of \(O_\varepsilon\) are summable by \(|M(n)^2-A(n)|\le M(n)^2+n\). The series thus has bounded total variation. The literal continuous integral with numerator \(M(\lfloor x\rfloor)^2-A(\lfloor x\rfloor)\) and weight \(x^{-2-2\varepsilon}\,dx\) also converges absolutely, by comparison on each \([n,n+1)\). Its cell weights are \(\int_n^{n+1}x^{-2-2\varepsilon}dx\); the Lean declaration for \(O_\varepsilon\) uses \(w_n\).

At the endpoint the second finite description also passes to an absolutely convergent series of *grouped conductor rows*, since \(\sum_{n\ge j}n^{-3}\ll j^{-2}\) and the absolute first moment is finite. Taking absolute values before summing the individual \(\mu(i)\mu(j)\) contributions gives a different result. The square-divisor union bound gives \(A(n)\ge(2-\zeta(2))n\). Hence \(\sum n^{-3}(A(n)^2-A(n))=\infty\). The grouping is essential at the endpoint.

A stronger endpoint weight follows from Lee and Leong. For \(U_x=(\log x)^{3/5}(\log\log x)^{-1/5}\) and \(\kappa=(5/[3(53.99)^3])^{1/5}\), their Theorem 1.1, equation (11), has exponent \(-\kappa(1-\log(53.99)/\log\log x)^{-1/5}U_x\) and prefactor \(25.85x\log x\). The excess in the exponent is \(\gg U_x/\log\log x\), which dominates every fixed multiple of \(\log\log x\). Therefore even
\[
 \sum_{n\ge3}\frac{M(n)^2}{n^3}\exp(2\kappa U_n)(6+\log n)^a<\infty
\]
for every fixed \(a\), by comparison with \(\sum 1/(n\log^2 n)\). This subpower gain still leaves open every fixed power saving below damping \(1/2\). [Endpoint in Lean](MertensEnergyEndpoint.lean) · [Signed decomposition](MertensEnergyConvergence.lean) · [Lee and Leong, Theorem 1.1](https://arxiv.org/pdf/2208.06141)

## 7. Corrected semiprime blocks at arbitrary starting positions

Let \(r=1-P_V^P1\), \(E=\|r\|_P^2\), and \(q_j=p_jp_{j+1}\) for consecutive primes (starting with \(p_0=2\)). Write \(b_j=\langle r,(x\bmod q_j)/x\rangle_P\). The corrected block is \(B(k,n)=\sum_{j=k}^{k+n-1}b_j\), since restoring both singleton residue terms cancels them from each multiplicative defect. The gap \(1-(x\bmod q_j)/x\) is between zero and one, vanishes below \(q_j\), and the Pareto mass above \(q_j\), including the cut, equals \(1/q_j\). Applying this overlap estimate to a triangular Gram sum (and to the physical vector \(|r|\) for the absolute version) gives
\[
 |nE-B(k,n)|^2
 \le E\sum_{j<n}\frac{2j+1}{q_{k+j}},\qquad
 \sum_{j\ge0}|b_j-E|<\infty .
\]
Indeed \(\sum (2j+1)/q_j<\infty\) by \(p_j\asymp j\log j\). Thus \(S(k)=\sum_{j<k}(b_j-E)\) converges, and
\[
 B(k,n)=nE+S(k+n)-S(k),\qquad
 \sup_{n\ge0}|B(k,n)-nE|\le\sum_{j\ge k}|b_j-E|\longrightarrow0.
\]
In particular \(B(k,n)/n\to E\) uniformly in \(k\) as \(n\to\infty\). More generally this holds along **every** sequence \(n_i\ge1,\ k_i+n_i\to\infty\): for large \(n_i\) use boundedness of \(S\); for the remaining lengths use the tail estimate as \(k_i\to\infty\). For any prescribed such schedule and any nonnegative tolerance \(\eta_i\to0\), RH is equivalent to \(B(k_i,n_i)\le n_i\eta_i\) infinitely often. Under RH all blocks vanish. Otherwise \(E>0\), and their normalized values eventually exceed \(E/2\). In particular, arbitrarily long nonpositive blocks with an arbitrary starting index are equivalent to RH. Conversely one may fix length one and send the starting prime to infinity. [Corrected blocks](SemiprimeBlockRemainders.lean)

## Logarithmic localization in the squarefree dictionary (8, 12, 14)

Work on the positive physical sites with \(Z=\zeta(2)\), \(Q(n)=1/(Zn^2)\) and \(Bf(n)=f(n)/(n+1)\). Let \(P=P_N\) be the native \(Q\)-orthogonal projection onto the complete squarefree stage, \(r_N=(I-P)1\), and \(u_N=PBr_N\). Write \(D_h\) for truncation to \(1,\ldots,h\), \(E_h=I-D_h\), \(L_x=6+\log x\), \(h(x)=\lfloor x/L_x\rfloor\). The signed short-head response at physical site \(n\) is
\[
 s_{N,h}(n)=\left[P D_h\big((B-b_n I)r_N\big)\right](n),\qquad b_n=1/(n+1).
\]
This is the repository's \(\mathrm{response}(N,h,n)\). In its zero-based notation \(\mathrm{logarithmicHeadResponse}(N,i)=s_{N,h(i+1)}(i+1)\).

### The complete omitted tail as one operator

Since \(P r_N=0\), \(B\) commutes with \(E_h\), and \(b_n\) is the output multiplier at \(n\),
\[
 u_N(n)-s_{N,h}(n)=(PBT)(n)-b_n(PT)(n),\qquad T=E_h r_N.
\]
For the entire output on \(n>h\), this equals \([A,B_h]T\), where \(A=E_h P E_h\) and \(B_h=B|_{E_hL^2(Q)}\) act on the tail space. There \(0\le A\le I\) and \(0\le B_h\le aI\) with \(a=(h+2)^{-1}\). Thus
\[
 \|[A,B_h]\|
 \le 2\|A-\tfrac12 I\|\,\|B_h-\tfrac a2 I\|
 \le \frac1{2(h+2)} .
\]
The coefficient \(1/2\) is optimal for arbitrary positive contractions with these spectral intervals, as witnessed by the rank-one projection onto \((1,1)/\sqrt2\) and the diagonal multiplier with eigenvalues \(a,0\). Sharpness on the arithmetic stages remains open.

For one physical site \(n\), evaluation on \(L^2(Q)\) has norm \(\sqrt Z n\). Because \(h(n)<n\) and \(n/(h(n)+2)\le L_n\),
\[
 |u_N(n)-s_{N,h(n)}(n)|\le \tfrac12\sqrt Z\,L_n\,\|E_{h(n)}r_N\|_Q .
\]
The factor after \(L_n\) tends to zero uniformly in \(N\). Indeed \(r_N\) converges strongly, so the family of residuals has compact closure and its tails vanish uniformly. Also \(\|r_N\|_Q\le1\), recovering the stated constant for every stage. A common pointwise polylogarithmic envelope on the short head, reached arbitrarily late for each fixed site, therefore gives a polylogarithmic envelope on \(u=\lim_Nu_N\), which implies RH by the correction-tail theorem. [Sitewise criterion](QSquarefreeShortHeadCriterion.lean)

### A complete block estimate with a common cutoff

Take \(M\ge1\), \(h=h(M)\), block \(I_M=(M,2M]\), and regard \(s=(s_{N,h}(n))_{n\in I_M}\) and \(e=(u_N(n)-s_{N,h}(n))_{n\in I_M}\) as ordinary Euclidean vectors. For every vector \(v\),
\(\sum_{I_M}|v(n)|^2\le4ZM^2\sum_{I_M}Q(n)|v(n)|^2\). Because the block lies above \(h\), the commutator bound gives
\[
 \boxed{\ \|e\|_2^2\le
       Z\frac{M^2}{(h+2)^2}\|E_hr_N\|_Q^2
       \le Z L_M^2\|E_hr_N\|_Q^2 .\ }
\]
The earlier bound was \(4Z M L_M^2\). The argument sums in the physical Hilbert norm before bounding the common input. In particular \(\sup_N\|e\|_2^2=o(L_M^2)\). For any positive \(t\) the exact retained loss is
\[
 \|s+e\|_2^2+t^{-1}\|ts-e\|_2^2
 =(1+t)\|s\|_2^2+(1+t^{-1})\|e\|_2^2.
\]
Using the earlier bound and \(t=2\sqrt{Z/C}\) gives the requested coefficient \((\sqrt C+2\sqrt Z)^2\) with exponent \(2\max(m,1)\). For the stronger estimate, put \(S=\sqrt{CM}L_M^m\) and \(D=\sqrt Z\,M\|E_hr_N\|_Q/(h+2)\). If \(S,D>0\), take \(t=D/S\). Whenever \(\|s\|_2\le S\),
\[
 \|s+e\|_2^2+\frac{S}{D}\left\|\frac DSs-e\right\|_2^2\le(S+D)^2 .
\]
When \(D=0\) the error vanishes, and when \(S=0\) the short response vanishes. Since \(L_M/\sqrt M\to0\), the upper bound is \((C+o(1))M L_M^{2m}\), uniformly in \(N\), for every fixed \(m\ge0\), including \(m=0\). On each dyadic block a cofinally attained short-head bound passes to the limiting full block by coordinate convergence and finiteness of the block. The existing dyadic criterion then implies RH. [Block criterion](QSquarefreeShortHeadBlocks.lean) · [Exact loss](QSquarefreeShortHeadYoung.lean) · [Shared-tail identity](QSquarefreeHeadLeakage.lean)

For an all-stage bound at \(m=0\) with the original coefficient, in fact \(M/(h(M)+2)\le2\sqrt M\). Put \(x=\sqrt M\). Then \(L_M=6+2\log x\le4+2x\), so \(h(M)+2>1+M/L_M\ge 1+x^2/(4+2x)>x/2\). Hence at every stage one can keep coefficient \((\sqrt C+2\sqrt Z)^2\) and use exponent \(2m\) for all \(m\ge0\), retaining the Young loss with \(t=2\sqrt Z/\sqrt C\). For \(m\ge1\), \(\|e\|_2\le\sqrt Z L_M\le \sqrt{ZM} L_M^m\) gives the smaller all-stage coefficient \((\sqrt C+\sqrt Z)^2\), with \(t=\sqrt{Z/C}\).

### Retaining the explicit Mertens profile

A sharper transfer uses the full variable coefficient in Lee and Leong's Theorem 1.1 (11). For large \(x\) write \(t=\log x\), \(U(x)=t^{3/5}/(\log t)^{1/5}\), and
\[
 V(t)=\kappa\,\frac{t^{3/5}}{(\log(t/53.99))^{1/5}},\qquad
 F(x)=\frac{e^{V(t)}}{t(1+U(x))}.
\]
In particular \(V(t)=\kappa(1-\log(53.99)/\log t)^{-1/5}U(x)\). The published upper bound for the absolute ordinary Mertens function divided by \(x\) is \(g(x)=25.85\,t e^{-V(t)}\). Here \(tV'(t)=V(t)(3/5-1/[5\log(t/53.99)])\to\infty\) and \(V'(t)\to0\). Consequently \(g\) is eventually decreasing, \(F\) is eventually increasing, \(d\log F(e^t)/dt\to0\), and \(F(x)=x^{o(1)}\). The derivative of \(\log(1+U(e^t))\) is \(O(1/t)\).

At trial size \(K\) use the uniform Mertens envelope \(\varepsilon=g(K)\). As \(V(\log K)=O(U(K))\), its entropy satisfies
\(\varepsilon(1+\log(1/\varepsilon))=O(1/F(K))\). The actual exact-head trial thus satisfies \(\|f_K\|_Q^2=O(1+K/F(K))\). For each large integer \(X\), Bertrand's theorem provides a prime \(X<p\le2X\). Set \(K=p-1\). The boundary-corrected Möbius trial uses squarefree conductors and the additional conductor \(p\), so \(f_K\) belongs to the squarefree legal space; also \(1-f_K\) vanishes through \(X\). If \(v\) is orthogonal to that space, then \(\langle1,v\rangle_Q=\langle1-f_K,E_Xv\rangle_Q\). Since \(X\le K<2X\) and \(F\) is eventually increasing, Cauchy–Schwarz yields
\[
 |\langle 1,v\rangle_Q|^2\ll (1+X/F(X))\,\|E_Xv\|_Q^2.
\]
Write \(P_\infty\) for the limiting squarefree projection, \(r=1-P_\infty1\), and \(u=P_\infty Br\). Apply the inequality to \(v=(I-P_\infty)Br=Br-u\). If \(r\ne0\), its mean \(\langle1,v\rangle_Q=\langle r,Br\rangle_Q\) is strictly positive. Since \(F(X)=X^{o(1)}\) and \(\|E_XBr\|_Q\le\|r\|_Q/(X+2)\), the triangle inequality gives
\[
 r\ne0\quad\Longrightarrow\quad X\|E_Xu\|_Q^2\gg_r F(X).
\]

It follows that the strictly weaker arithmetic condition
\[
 \lim_{j\to\infty}
 \frac{\liminf_{N\to\infty} \sum_{2^j<n\le2^{j+1}} |s_{N,h(2^j)}(n)|^2}
      {2^j F(2^j)}=0
 \quad\Longrightarrow\quad \mathrm{RH}
\]
suffices. Each fixed block may select its own subsequence. Indeed the joint remainder is \(O(L_M)\) in Euclidean norm, hence \(o(\sqrt{MF(M)})\), and the limiting full block also has energy \(o(MF(M))\). For dyadic \(X\), its entire omitted \(Q\)-tail satisfies \(X\|E_Xu\|_Q^2=o(F(X))\): sum the block bounds at \(2^\ell X\), using \(F(2^\ell X)\le 2^{\ell/2}F(X)\) eventually uniformly in \(\ell\) by the log derivative. This contradicts the displayed lower bound. The sitewise condition \(\liminf_N |s_{N,h(n)}(n)|=o(\sqrt{F(n)})\) as \(n\to\infty\) also suffices by the sitewise remainder and the same block comparison.

In particular the arithmetic mean-square envelope \(O(e^{\kappa U(M)}(\log M)^b)\) works for every fixed \(b\in\mathbb R\). The positive difference \(V(\log M)-\kappa U(M)\gg U(M)/\log\log M\) absorbs \((\log M)^b\) and the two factors in the denominator of \(F\). The profile criterion and the constants on the compressed commutator are paper deductions. [Lee–Leong, equation (11)](https://arxiv.org/pdf/2208.06141) · [Exact-head trial estimate](CanonicalAndReciprocalCertificates20261126.md) · [Squarefree trial membership](QSquarefreeSublinearHeads.lean)

One may also test only the tails of the dyadic response sequence. Set \(A_j=2^{-j}\liminf_N\|s_{N,h(2^j)}\|_{2,I_{2^j}}^2\). The Euclidean inequality \(\|s+e\|_2^2\le2\|s\|_2^2+2\|e\|_2^2\) and finite-block convergence give
\[
 2^j\|E_{2^j}u\|_Q^2
 \le\frac{2}{Z}\sum_{\ell\ge0}2^{-\ell} A_{j+\ell}
   + O\!\left(\frac{(1+j)^2}{2^j}\right).
\]
Thus a zero lower limit, along arbitrarily late \(j\), of
\(F(2^j)^{-1}\sum_{\ell\ge0}2^{-\ell}A_{j+\ell}\) also suffices. Conversely under RH, \(r_N\to0\), hence every fixed-block \(A_j=0\) by boundedness of the projections and the finitely many output evaluations. This gives an equivalence with the dyadic tail condition and permits exceptional blocks through their actual nonnegative contribution.

## Weighted moving heads and the sharp range of varying weight indices (9 and 11)

On the squarefree trial spaces let \(P_N\) be the nested \(Q\)-orthogonal projections, \(P_\infty\) the projection onto their closed union, \(Bf(n)=f(n)/(n+1)\), and \(r=1-P_\infty1\). The actual correction \(u_N=P_NB(1-P_N1)\) converges in \(Q\) to \(u=P_\infty Br\). Here \(Q_n=1/(\zeta(2)n^2)\) for \(n\ge1\). Write
\[
 W_k(n)=\frac{n}{(k+6+\log n)^k},\qquad E_k(H,N)=\sum_{1\le n\le H}W_k(n)Q_n|u_N(n)|^2.
\]
The family \(\{u_N:N\ge0\}\) is relatively compact. Therefore \(D=\sup_N\|u_N\|_Q^2<\infty\) and \(\tau(J)=\sup_N\sum_{n>J}Q_n|u_N(n)|^2\to0\). To see the latter, cover the family by a finite norm net and use that each tail projection has norm at most one and tends strongly to zero. For any nonnegative nondecreasing weight \(W(H)\to\infty\) the normalized head at \(H\ge J\) is bounded by
\[
 D\,W(J)/W(H)+\tau(J).
\]
First let \(H\to\infty\), then \(J\to\infty\). This proves uniformity over every stage, including independently chosen \(N(H)\). It implies both numbered assertions, since each \(W_k\) is nondecreasing and diverges.

There is a sharp extension when \(k=k(H)\) varies. Put \(L=\log H\) and assume \(k(H)/L^2\to\lambda\in[0,\infty]\). With \(c_0=0\), \(c_\infty=1\), and \(c_\lambda=\exp[-1/(2\lambda)]\) for finite positive \(\lambda\), one has
\[
 \sup_N\left|\frac{E_{k(H)}(H,N)}{W_{k(H)}(H)}-c_\lambda\|u_N\|_Q^2\right|\longrightarrow0.
\]
Indeed, for fixed \(n\) and \(H\ge n\),
\[
 \frac{W_k(n)}{W_k(H)}=
 \exp\!\left(-\int_{\log n}^{L}\frac{6+x}{k+6+x}\,dx\right).
\]
If \(k=o(L^2)\), restricting the integral to \([L/2,L]\) bounds it below by \(L^2/[4(k+6+L)]\to\infty\). If \(k/L^2\to\lambda>0\), including \(\lambda=\infty\), then \(L/k\to0\) and the integral is \((1+o(1))L^2/(2k)\). For fixed \(J\), the ratios converge to \(c_\lambda\) uniformly on the first \(J\) sites. Their errors there contribute at most \(D\) times that finite maximum, and all remaining sites contribute at most \(\tau(J)\), since both the truncated normalized weight and \(c_\lambda\) lie in \([0,1]\). This proves the formula. In particular \(k=o((\log H)^2)\) is admissible. At the critical rate every nonzero fixed vector retains a positive fraction of its energy.

The absolute bound has a converse after allowing the head to grow slowly. The established squarefree density theorem gives \(\mathrm{RH}\iff 1\in\overline{\bigcup_NS_N}\iff r=0\). Its forward direction uses the Pareto squarefree damping converse and equivalence of the physical \(P,Q\) norms. If \(r=0\), then \(u_N\to0\). Set \(H_N=\lfloor(\|u_N\|_Q+1/(N+1))^{-1}\rfloor\). This single head tends to infinity and, simultaneously for every \(k\),
\[
 E_k(H_N,N)\le H_N\|u_N\|_Q^2\le\|u_N\|_Q\to0.
\]
Conversely, if one fixed \(k\) admits a common finite bound at arbitrarily late stages of one expanding head, passing to the limit on each finite prefix yields finite total \(W_k\)-energy of \(u\). Thus \(W_k(J)\|\mathbf1_{n>J}u\|_Q^2\) stays bounded, contrary to the established logarithmic tail escape when \(r\ne0\). Equivalently, the absolute energies of every expanding head diverge when RH fails. The normalized limit by itself gives no absolute budget. For a concrete Hilbert-space example take the constant family of vectors \(v(n)=n^{1/4}\). Its complete \(Q\)-energy is \(\zeta(3/2)/\zeta(2)\), and for every fixed \(k\) its unnormalized head energy is asymptotic to \(2\sqrt H/[\zeta(2)(k+6+\log H)^k]\), by partial summation. It diverges even though its normalized ratio is asymptotic to \(2/[\zeta(2)\sqrt H]\).

In particular, for any prescribed strictly positive bounded sequence \(b_H\), RH is equivalent to the following simultaneous test. For every \(H\) there is one \(N\ge H\) for which \(E_k(H,N)\le b_H\) for **every** \(k\). In the forward direction, let \(N\) increase at fixed \(H\) and use \(E_k(H,N)\le H\|u_N\|_Q^2\). Conversely choose one witness \(N_H\ge H\) per head. Then \(u_{N_H}\to u\), and finite-head Fatou at \(k=0\) supplies the absolute bound for the limit.

[Actual head energy and criterion](QSquarefreeMovingHeadEnergy.lean) · [Weight and shift](../Analysis/LogTailWeights.lean) · [Strong convergence](QSquarefreeSmoothedProjection.lean) · [Logarithmic tail escape](QSquarefreeLogResidualTail.lean) · [Squarefree converse](ParetoSquarefreeDampingConverse.lean)

## 10 and 13. The fixed-pair limit and a harmonic Schur criterion

Let \(R_j\) be positive periods nested by divisibility such that each conductor
\(q>1\) divides some \(R_j\), and let \(H_j\to\infty\). Write \(V_j\) for
the full divisor stage, \(U_{j,H}\) for its high-conductor part, and \(r_j\)
for the matched Pareto residual. Use the canonical physical cutoff \(A(H)\)
of the localization theorem. The scalar \(S_j(n,m)\) is its signed head
pairing of \(r_j\) with
\((P^Q_{V_j}-P^Q_{U_{j,H_j}})(e_n-e_m)\), where \(e_n\) represents
evaluation at \(n\). Put \(Z=\zeta(2)\) and let \(d\) be the physical
difference between the full \(Q\) and Pareto projections of \(1\).
For every fixed pair the exact decomposition gives
\[
 S_j(n,m)\longrightarrow Z(d(n)-d(m)).
\]
Indeed the finite displacement converges at both fixed evaluations. The
high-conductor head is bounded by \(Z|n-m|/H_j\) eventually, and the
complete signed tail tends to zero by localization.
[Fixed-pair theorem](QFullShortHeadLocalization.lean)

For a fixed positive modulus \(L\), a common absolute upper bound \(C\)
attained infinitely often at each positive congruent pair therefore implies
\(|d(n)-d(m)|\le C/Z\) on each residue class. Comparison with one finite
representative per class bounds \(d\) everywhere. For claim 13 choose
\(a(n)=L+(n\bmod L)\) and one sign \(\varepsilon=\pm1\). A common upper
bound only for \(\varepsilon S_j(n,a(n))\) gives
\[
 \varepsilon d(n)\le C/Z+\max_{L\le a<2L}\varepsilon d(a).
\]
At \(L=1\) the anchor is 1. A bounded signed side implies
\(\sum_{n\le X}[\varepsilon d(n)]_+/n=O(1+\log X)\), and full signed
harmonic rigidity gives zero full \(Q\) residual. Conversely, zero residual
implies \(d=0\), so each fixed pair eventually satisfies any prescribed
positive absolute bound. Each pair can use its own subsequence.
[One-sided theorem](QFullShortHeadOneSided.lean) · [Harmonic rigidity](QFullCofinalHarmonic.lean)

There is a weaker arithmetic test. In the formula below index \(0\) denotes
the zero evaluation functional, with \(d(0)=0\). For each fixed \(X\) put
\[
 G_j(X)=\min_{\varepsilon=\pm1}\sum_{n=1}^X
              \frac{[\varepsilon S_j(n,0)/Z]_+}{n}.
\]
Then zero full \(Q\) residual is equivalent to the existence of \(B,C\ge0\)
such that for arbitrarily large \(X\), arbitrarily late \(j\) satisfy
\(G_j(X)\le C(\log X)^B\). A single sign is chosen for a whole harmonic
prefix and may change with its head and stage. At fixed \(X\) one can pass
the limit through both finite sums and the minimum. The limit is precisely
the cheaper signed harmonic prefix of \(d\), so the implication from the
arithmetic estimate is the checked cofinal harmonic rigidity theorem. In
the other direction \(d=0\) makes each fixed aggregate tend to zero, and
\(B=0,C=1\) works. This criterion permits large individual site responses.

The same equivalence holds with \(0\) replaced by \(a(n)\), or by any site
selector in a fixed finite anchor set. For either sign the positive part is
1-Lipschitz, so the corresponding limiting harmonic prefixes differ by at
most \(\max_a|d(a)|\sum_{n=1}^X n^{-1}\). This additional \(O(1+\log X)\)
can be absorbed by increasing the common exponent to \(\max(B,1)\).
As a consequence, the pointwise one-sided criterion may even omit a fixed
exceptional set \(E\) with \(\#(E\cap[1,X])=O((\log X)^K)\) on any
unbounded sequence. The missing signed charge is at most
\(\sqrt Z\|d\|_Q\sqrt{\#(E\cap[1,X])}\) by Cauchy–Schwarz, which is
polylogarithmic on that sequence. The requisite bound for the actual
responses remains open.

## 15. Signed digamma synthesis and the covariance of two packets

Let \(\mathcal I\) be the conductors \(q>1\) divisible by at least two distinct primes. Gram–Schmidt in increasing order on \(J_q,\ q\in\mathcal I\), gives a Hilbert basis \((e_q)\) of the closed mixed Pareto space \(M\). Write \(G(a,b)=\langle J_a,J_b\rangle_P\). With \(L=\operatorname{lcm}(a,b)\), the exact contribution of a site \(r\in\{1,\ldots,L\}\) to the Gram entry is \(J_a(r)J_b(r)\) times
\[
 \sum_{h\ge0}P_{r+hL}
 =\frac{\psi((r+1)/L)-\psi(r/L)}{L}.
\]
This follows by taking the difference of the two reciprocal progression sums before summation. The triangular recursion for the signed row at conductor \(a\) is
\[
 d_q(a)=\frac{G(q,a)-\sum_{r<q}d_r(q)d_r(a)}
 {\sqrt{G(q,q)-\sum_{r<q}d_r(q)^2}} .
\]
Every pivot is positive by independence of the mixed packets. Gram–Schmidt gives \(d_q(a)=\langle e_q,J_a\rangle_P=\langle e_q,P_MJ_a\rangle_P\). Fourier reconstruction and polarization now give, for every \(a,b\ge1\),
\[
 \sum_q d_q(a)e_q=P_MJ_a,\qquad
 \sum_q d_q(a)d_q(b)=\langle P_MJ_a,P_MJ_b\rangle_P .
\]
The vector series converges unconditionally in the complete Pareto norm. The scalar covariance series is absolutely summable by Cauchy–Schwarz. For any finite set \(F\) of modes, orthogonality gives the exact squared truncation error \(\sum_{q\notin F}d_q(a)^2\). If \(a,b>1\), the existing screening identity \((I-P_M)J_a=\Lambda(a)u\) therefore gives the explicit signed covariance
\[
 \sum_q d_q(a)d_q(b)=G(a,b)-\Lambda(a)\Lambda(b)\|u\|_P^2.
\]
In particular, since \(\|J_2\|_P^2=\log 2\) and \(\langle u,1\rangle_P=1\), the finite parity energy satisfies
\[
 \log2-(\log2)^2-\sum_{q\in F}d_q(2)^2
 =(\log2)^2\|u-1\|_P^2+\sum_{q\notin F}d_q(2)^2 .
\]
All terms use the unnormalized packet \(J_2\). The first term on the right vanishes exactly under RH. This also quantifies every finite parity deficit without assuming saturation. [Packet rows and covariance](MixedParityDigammaParseval.lean) · [Rank-one covariance](MixedConductorPolarizedParseval.lean) · [Digamma series](https://dlmf.nist.gov/5.7.E6)

## Verification scope

The Lean modules linked above contain the original reductions and the new finite two-carry bound, raw-row separation, cofinal Gram certificate, product bound for residuals and dyadic excess, grouped off-diagonal summability, semiprime tail estimates, shared-tail block bound, simultaneous head budgets, harmonic Schur criterion, and polarized digamma reconstruction. The sharp compression constant, critical growing-weight limit, stretched-envelope comparisons, and finite-deletion codimension calculation are paper arguments in this note. None of the conditional bounds on the actual arithmetic responses is assumed in an unconditional conclusion.
