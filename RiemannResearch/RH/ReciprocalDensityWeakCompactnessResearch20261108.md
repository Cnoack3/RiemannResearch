# Reciprocal density: compactness audit and research checkpoint

8 November 2026. **RH is not proved.** The compactness route is valid once bounded unsmoothed lifts are supplied; injectivity and reciprocal convergence do not supply that bound. This session develops a weaker sufficient condition: a positive power rate of reciprocal approximation together with subpolynomial growth of the complete unsmoothed energy. The explicit Möbius family supplies the reciprocal rate unconditionally. Its required energy estimate remains open.

This note records the mathematical conclusions and their exact formal scope. The targeted Bazel/BuildBuddy receipt is `job_DZ3EHd4ZBxkxlF1IeKQqXz5xONXxA0f_`; axiom-output guard `job_cpPUtovIi9jO5zwaJe-RWooAGFW_8GDx`; the source and axiom audit covers all 25 new modules. Publication is gated separately by the complete-project checkpoint. The theorem catalog below distinguishes checked implications from their open arithmetic hypotheses.

**Sources and notation.** The starting document is `Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf`, especially §§6–10. The published endpoint is [Bhaskar Bagchi, *On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis*, Theorem 1 and Remark 8](https://arxiv.org/pdf/math/0607733). The damped Möbius motivation comes from [Luis Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis*, Theorem 1.1 and §2.2](https://arxiv.org/pdf/math/0202141). Its proof assumes RH when establishing the relevant unsmoothed approximation; those estimates cannot be imported as unconditional providers.

Write $Z=\zeta(2)$, $Q(n)=1/(Zn^2)$, $H_Q=L^2(Q)$, $g_m(n)=\{n/m\}$, and $Rf(n)=f(n)/(n+1)$. In Lean, the reciprocal operator is `QShiftedReciprocal.B`; this is **not** the PDF’s metric multiplier also named $B$. Define

$$
V_{\rm fin}=\operatorname{span}_{\mathbb R}\{g_m:m\ge2\},\qquad
(V_{\rm sf})_{\rm fin}=\operatorname{span}_{\mathbb R}\{g_m:m\ge2,\ m\text{ squarefree}\},
$$

and take their closures in $H_Q$ to obtain $V,V_{\rm sf}$. In the repository these are `QFullResidueProjection.legalSpan`, its `closure`, `ZetaTwoProbability.qSquarefreeCRTSpan`, and the latter’s `topologicalClosure`. The endpoint is $1\in V\iff V=H_Q\iff\mathrm{RH}$, and $1\in V_{\rm sf}\iff\mathrm{RH}$. Squarefree target membership does not assert squarefree totality. None of the new modules asserts $V_{\rm sf}=H_Q$.

**The precise compactness gap.** The PDF’s weak compactness statement is **Theorem 8.1**; **§8.2** is Route B, concerning graph convergence and complete tails. Theorem 8.1 is correct: for a closed legal subspace $S$, if $v_j\in S$, $Rv_j\to R1$, and a cofinal subsequence has uniformly bounded $H_Q$ norms, weak compactness produces $v\in S$, weak continuity gives $Rv=R1$, and injectivity gives $v=1$. Under the Hilbert-space dual identification, weak-* compactness provides the same argument on a bounded ball. It does not put an unbounded family into such a ball. The formal general theorem retains completeness and separability of the source submodule, the uniform source bound, and image convergence explicitly.

The PDF’s counterexample isolates the missing hypothesis. For $W=1^\perp$, $q_N=Q(n\ge N)$, and $w_N=1-1_{\{n\ge N\}}/q_N$, one has $w_N\in W$, $Rw_N\to R1$, and pointwise convergence $w_N(n)\to1$, while $\|w_N\|_Q^2=q_N^{-1}-1\to\infty$ and $1\notin W$. This refutes the abstract inference; it does not identify $W$ with the arithmetic legal space.

A second explicit construction uses only a finite correction to the same actual target and operator. For $N\ge1$, set

$$
a_N(n)=\frac{Zn^2}{N}\,1_{\{1\le n\le N\}},
\qquad v_N=1-a_N,\qquad S=1^\perp.
$$

Then $\langle a_N,1\rangle_Q=N/N=1$, so $v_N\in S$, whereas $1\notin S$. Directly,

$$
\|R(v_N-1)\|_Q^2
=\frac{Z}{N^2}\sum_{n=1}^N\frac{n^2}{(n+1)^2}
\le\frac ZN\longrightarrow0,
$$

$$
\|v_N\|_Q^2=\|a_N\|_Q^2-1
=\frac{Z(N+1)(2N+1)}{6N}-1
\sim\frac Z3N.
$$

Thus even the same probability law, reciprocal operator, target, and a closed complete source space do not permit the unbounded lifting inference. The corresponding Lean theorem, `QReciprocalMeanZeroCounterexample.actual_reciprocal_lifting_counterexample`, proves closedness, mean-zero membership, reciprocal convergence, and target nonmembership. The displayed exact norm formula is a paper calculation; the formal counterexample needs only the checked reciprocal bound. Neither counterexample identifies its mean-zero hyperplane with the arithmetic legal space.

The inverse has domain $\operatorname{Ran}R=\{u:((n+1)u(n))\in H_Q\}$, and is closed and unbounded. The image $RS$ need not be complete in the inherited $Q$ norm. Its graph norm already contains $\|R^{-1}u\|_Q$, so applying closed graph with that norm supplies no missing source estimate. The Route B theorem instead explicitly assumes either `CauchySeq F` for the preimages, or

$$
\forall\delta>0\ \exists N\ \forall j,\quad
\|(I-H_N)v_j\|_Q\le\delta.
$$

Together with reciprocal convergence this proves strong convergence to $1$. Fixed heads alone are insufficient. Independently, the existing conductor estimates give

$$
\frac{\|Rg_d\|_Q}{\|g_d\|_Q}\le\frac{\sqrt Z}{\sqrt{d-1}},\qquad d\ge2.
$$

Thus no uniform inverse bound can hold even on prime atoms. The new noncoercivity module makes that consequence explicit; the underlying decay obstruction was already present in the project.

**The complete first-order reciprocal family.** Let

$$
v_{\varepsilon,N}=-\sum_{m\le N}\mu(m)m^{-\varepsilon}g_m,
\quad \varepsilon>0,
$$

where $g_1=0$. These are literal finite squarefree-legal vectors. The reciprocal atom series is absolutely summable for every positive damping. Its actual Hilbert-space sum $A_\varepsilon$ satisfies

$$
\|A_\varepsilon-R1\|_Q\le C_1\varepsilon,
\qquad
\|Rv_{\varepsilon,N}-R1\|_Q
\le C_1\varepsilon+\frac{N^{-\varepsilon}}{\varepsilon},
\quad C_1=\|qLogEnvelope\|_Q.
$$

These estimates cover every physical coordinate and the full infinite $Q$ tail. They do not assert convergence of the unsmoothed series in $H_Q$. The explicit module instantiates the paper’s diagonal:

$$
\varepsilon_j=\frac1{j+2},\quad N_j=(j+2)^{2(j+2)},\quad
U_j=v_{\varepsilon_j,N_j},\quad
\|R(1-U_j)\|_Q\le\frac{C_1+1}{j+2}.
$$

The cutoff-tail identity is proved exactly: $N_j^{-\varepsilon_j}/\varepsilon_j=1/(j+2)$. Thus the final specialized RH theorem has only the complete unsmoothed energy premise remaining.

**The weaker sufficient energy condition derived in this session.** For $\beta=\Re s>1/2$, the complete Mellin head–tail estimate is

$$
|\mathcal M_Qf(s)|^2\le
\frac{2Z}{2\beta-1}\left((H+1)^2\|Rf\|_Q^2
+H^{1-2\beta}\|f\|_Q^2\right),\qquad H\ge1.
$$

At a zeta zero in the right half of the critical strip, every finite legal vector has zero Mellin transform, whereas $\mathcal M_Q1(s)=1/s\ne0$. Applying the estimate to $f=1-U_j$ gives the verified conditional criterion

$$
\|R(1-U_j)\|_Q=O(j^{-1}),\qquad
\forall a>0,\quad j^{-a}\|U_j\|_Q^2\longrightarrow0
\quad\Longrightarrow\quad\mathrm{RH}.
$$

The proof takes a quadratic subsequence and a slower growing physical head, so it accepts $O(1/j)$ reciprocal error. It does not silently require $o(1/j)$. A further theorem allows any fixed positive power $O(j^{-r})$, $r>0$. The term “new” here describes this session’s derivation and formalization; no claim of priority over the literature is made.

For the explicit family, the growth condition concerns the **approximation index $j$**. A bound merely subpolynomial in the enormous conductor cutoff $N_j$ is insufficient: even $\|U_j\|_Q^2=j^c$ is $N_j^{o(1)}$, while it fails the required condition for $a<c$. The actual open provider is exactly the hypothesis of `riemannHypothesis_of_explicit_subpower_energy`. No reverse implication for this particular cutoff schedule is claimed.

**Second-order refinement.** The coefficient expansion isolates the von Mangoldt function, and the full reciprocal family has the Hilbert expansion

$$
A_\varepsilon=R1+\varepsilon h+E_\varepsilon,
\quad h(n)=\frac{\psi(n)-n}{n+1},
\quad\|E_\varepsilon\|_Q\le C_2\varepsilon^2,
\quad C_2=\|qLogSquareEnvelope\|_Q.
$$

The Richardson combination $2A_{\varepsilon/2}-A_\varepsilon$ therefore has complete reciprocal error at most $3C_2\varepsilon^2/2$. Both $h$ and the logarithmic remainder envelope are actual $H_Q$ vectors. This is a refinement of the smoothed approximation. The Hilbert difference quotient also converges to $h$ as damping tends to zero from above. No assertion is made that the unsmoothed discrepancy $\psi(n)-n$ belongs to $H_Q$.

The finite family is completely explicit. With $n=j+2$, set

$$
W_j=2v_{1/n,n^{3n}}-v_{2/n,n^{3n}}.
$$

Both damping tails are retained, giving

$$
\|R(W_j-1)\|_Q\le\frac{6C_2+3}{(j+2)^2}.
$$

Every $W_j$ belongs to the finite squarefree legal span. Its complete unsmoothed energy remains an open provider in `riemannHypothesis_of_richardson_subpower_energy`.

**Finite dual certificates and regularization.** For $r\perp S$, $v\in S$, $e=\|R(1-v)\|_Q$, $M=\|v\|_Q$, and $b_N=\|R^{-1}H_Nr\|_Q$, $t_N=\|(I-H_N)r\|_Q$, the verified exact identity yields

$$
|\langle1,H_Nr\rangle|\le e b_N+M t_N,
\qquad
\alpha|\langle1,H_Nr\rangle|^2
\le(e^2+\alpha M^2)(\alpha b_N^2+t_N^2).
$$

The actual orthogonal projection residual is an allowed detector. The Tikhonov module preserves the signed normal-equation defect, proves the exact objective remainder, and gives an inexact-solution objective certificate. A normal-equation solution is minimal for nonnegative regularization and unique as a physical vector for positive regularization. These results do not manufacture minimizers or bounds uniform in the regularization parameter. A finite computation must control the full Gram energy $c^{\mathsf T}K_Qc$, including every signed cross term and the infinite physical tail.

**Sharper quantitative detector.** The additional exact finite Mellin sum and signed head-tail energy identity give, for $1/2<\beta=\Re s\le1$,

$$
|\mathcal M_Qf(s)|^2\le
8Z H^{3-2\beta}\|Rf\|_Q^2+
\frac{2Z}{2\beta-1}H^{1-2\beta}\|(I-P_H)f\|_Q^2.
$$

Here $P_H$ denotes the physical head projection through $H$. The actual full tail is retained. `zeta_ne_zero_of_sharp_reciprocal_budget` turns a sufficiently small finite two-energy budget into an exact zero exclusion. This improves the head exponent in the earlier elementary estimate; it does not establish that an arithmetic family meets the budget.

**Near-linear regularized cost.** Define

$$
J_\alpha(v)=\|R(1-v)\|_Q^2+\alpha\|v\|_Q^2,
\qquad \alpha_j=(j+1)^{-4}.
$$

For an actual finite legal family $U_j$, the checked theorem
`QReciprocalRegularizedCriterion.riemannHypothesis_of_near_linear_regularized_cost`
proves RH under

$$
\forall\eta>0\ \exists C_\eta\ge0\ \forall j,\quad
J_{\alpha_j}(U_j)\le C_\eta\alpha_j^{1-\eta}.
$$

This allows every positive exponent loss relative to the PDF's $O(\alpha)$ criterion. The complete cost estimate is Open, and no minimizing-family existence theorem is being substituted for that estimate.

**External finite-energy certificate.** At physical parameter $n=2$, a standard-library-only integer calculation produces outward rational bounds for every omitted physical tail. At the common conductor cutoff $64$, first-order energy lies in $[0.340573609486,0.340628987117]$ and Richardson energy lies in $[0.651789069817,0.651947371464]$. Reciprocal squared error falls from approximately $0.02794$ to $0.00536$. All strict comparisons use exact rational endpoints and were reproduced in a separate run. These are external integer calculations, not kernel-checked numeric values. The generic complete-energy interval theorem is formalized in `QFiniteEnergyIntervals`. The separately recorded $n=3$ floating diagnostics have no rounding certificate. See [the detailed certificate](RichardsonEnergyCertificate20261108.md).

The finite-stage energy increase is not evidence of divergence: both certified energies remain below the constant target's energy $1$. Conversely, finitely many small energies do not prove an asymptotic bound.

**Verification and theorem ledger.** See [the reciprocal-density theorem catalog](../THEOREM_CATALOG_RECIPROCAL_DENSITY_20261108.md) for every new module and declaration, the targeted verification receipt, and the exact Open providers. The original bounded-lift and Mellin core also passed the earlier Lake-era snippet job `job_LQJg6ja9RszQNuRjkzLH-pVGaH60edre`. The current combined audit uses Bazel/BuildBuddy. Standard foundational axioms do not discharge local mathematical hypotheses. A final project publication claim requires a successful checkpoint, not merely either snippet.

**Canonical next action.** Establish or quantitatively investigate the complete unsmoothed energy budget for the explicit finite family, or for a demonstrably better finite legal family. The target is $j^{-a}\|U_j\|_Q^2\to0$ for every $a>0$, with reciprocal convergence already available. Preserve the signed Gram form and certify the complete tail. If this family grows too rapidly, use the finite dual certificates to quantify that obstruction and move to constrained Gram/Tikhonov minimization with an explicit Galerkin error budget. Improving reciprocal rates alone does not establish this missing estimate, and the present work does not prove RH.
