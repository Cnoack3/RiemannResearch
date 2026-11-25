# What happens to the prime and carry splitting under completion?

Write \(g_d(n)=(n\bmod d)/d\) for the normalized residue atom of conductor \(d>1\). Let \(C_{\mathrm{alg}}\) be the finite real span of the **canonical CRT floor carries** \(\kappa_d\), one for each conductor having at least two distinct prime factors. Let \(P_{\mathrm{alg}}\) be the finite span of the atoms at prime powers, including all positive powers. Let \(V\) be the closed span of all the \(g_d\) in the Pareto Hilbert space.

The same arithmetic family satisfies two exact identities.
\[
 A_{\mathrm{alg}}=P_{\mathrm{alg}}\oplus C_{\mathrm{alg}},
 \qquad \overline{C_{\mathrm{alg}}}^{\,P}=V.
\]
The corresponding closure statement holds under the \(Q\) norm. Every prime-power atom is a norm limit of linear combinations of **just two** canonical carries. This explains both the finite splitting and the loss of the prime coordinate on completion. For RH the resulting target is \(\mathbf 1\in\overline{C_{\mathrm{alg}}}^{\,P}\). The approximation theorem below recovers all the atoms. The additional target is the ambient constant.

## Finite stages and the category of presentations

Regard the positive periods as a category \(\mathcal D\) with one arrow \(L\to M\) when \(L\mid M\). It is filtered because the least common multiple is a common refinement. At \(L\), the atom labels are the divisors \(d>1\) of \(L\). Each finite set of labels occurs in such a stage. For \(L=1\) the coefficient space is zero.

Fix the ambient sequence space \(H_0=\mathbb R^{\mathbb N}\). A finite presentation is a finite-dimensional coefficient space \(E\) with a linear synthesis map \(S:E\to H_0\). A morphism from \((E,S)\) to \((F,R)\) is a linear map \(f:E\to F\) with \(Rf=S\). This is the finite-domain part of the slice category of real vector spaces over \(H_0\). Into an injective presentation, a morphism is unique when it exists. For two injective presentations it exists precisely when the source image lies in the target image. Its formula is \(R^{-1}S\), with the inverse taken on the image.

At each stage use the coefficient space \(E_L=X_L\oplus Y_L\) for prime-power and mixed labels. Let \(A_L\) synthesize all atom columns. Let \(U_L:Y_L\to X_L\) insert the prime-power coefficients in the CRT rows. The carry column for a mixed label \(d\) is its prime row minus \(g_d\). The change of coefficient columns is
\[
 T_L(x,y)=(x+U_Ly,-y),\qquad T_L^2=I,\qquad S_L^{\mathrm{carry}}=A_LT_L.
\]
Independence of the atom columns and invertibility of \(T_L\) give unique prime/carry coordinates. Hence there is a split exact sequence
\[
 0\longrightarrow C_L\longrightarrow A_L^{\rm img}
 \mathrel{\mathop{\longrightarrow}^{\pi_L}} P_L\longrightarrow 0,
 \qquad \pi_L(p+c)=p.
\]
The inclusion of \(P_L\) is a section. If \(L=\prod p^{v_p}\), the prime-power summand has dimension \(\sum v_p\), the whole stage has dimension \(\prod(v_p+1)-1\), and the difference is the number of mixed carry columns. Disjointness here means unique coordinates. The two summands can have a nonzero inner product.

[Finite presentations and morphisms](CategoryTheory/AtomCarryPresentation.lean#L34) · [Prime powers and mixed labels](RH/FiniteAtomCarryCRT.lean#L27) · [Finite directness](RH/FiniteAtomCarryCRT.lean#L192)

## Refinement, naturality, and the algebraic colimit

For \(L\mid M\), let \(e_{LM}\) extend a coefficient vector by zeros on new labels. Each old CRT row has precisely its old coefficients at period \(M\). Consequently
\[
 e_{LM}T_L=T_Me_{LM},\qquad A_Me_{LM}=A_L.
\]
In the sequence-space model the bottom map on synthesized vectors is inclusion. On residue tables it is pullback along the reduction \(\mathbb Z/M\to\mathbb Z/L\). In particular a datum at period \(L\) is repeated with period \(L\) on the larger table. Coefficients and tables therefore have different refinement maps. The Lean functors for the two presentations are related by a natural isomorphism with components \(T_L\).

Passing to finite-support unions gives \(A_{\rm alg}=P_{\rm alg}\oplus C_{\rm alg}\). Any alleged relation or comparison of two finite words is tested at their common period. Equivalently, filtered colimits of these split rows in vector spaces give the split row for the union. This computes the **algebraic** colimit.

Arbitrary signed reciprocal certificates admit another presentation. Take the free space on atom and certificate symbols and impose one relation identifying each certificate with its signed atom expression. These relations generate the entire kernel of synthesis. A linear map out of the quotient is exactly an assignment to the symbols respecting every such relation. Canonical mixed carries give the independent family in the splitting above. Allowing all certificate symbols gives a presentation with relations.

[Naturality square](RH/FiniteAtomCarryRefinement.lean#L142) · [Natural isomorphism](RH/FiniteAtomCarryFunctor.lean#L74) · [Universal quotient](RH/UniversalAtomCarryPresentation.lean#L155)

There is a third limit in the arithmetic background. Reduction maps form an inverse system of rings, whose running-LCM limit is the profinite completion \(\widehat{\mathbb Z}\simeq\prod_p\mathbb Z_p\). Each finite atom or carry is a continuous periodic function on this limit. At its zero point every such function is zero. Hence a finite carry word is always at uniform distance at least 1 from the constant, and the same holds for the uniform closure. The RH approximation uses the Pareto \(L^2\) topology. At a physical stage \(L\) the common-zero class of positive multiples of \(L\) has positive but decreasing mass, computed below. The profinite ring limit and the bounded-energy Hilbert limit solve different universal problems.

[Ring-valued limit cone](RH/ConductorTowerLimit.lean#L92) · [Topological identification of the LCM tower](RH/ConductorTowerCompletions.lean#L234)

## A finite transform with its two metrics

The full conductor transform has one row and one column for **each** divisor, including 1. Its input \(W_g\) is a table indexed by gcd classes \(g\mid L\). Write \(c_q(g)\) for the Ramanujan sum and \(\varphi\) for Euler's totient. The forward and inverse maps are
\[
 (F_LW)_q=\sum_{g\mid L}c_q(g)W_g,\qquad
 W_g=\frac{\varphi(L/g)}{L}\sum_{q\mid L}\frac{c_q(g)(F_LW)_q}{\varphi(q)}.
\]
With \((D_{\rm in})_{gg}=L/\varphi(L/g)\) and \((D_{\rm out})_{qq}=1/\varphi(q)\), polarized Plancherel says \(F_L^{\mathsf T}D_{\rm out}F_L=D_{\rm in}\). Hence \(F_L^{-1}=D_{\rm in}^{-1}F_L^{\mathsf T}D_{\rm out}\). This is a genuine isometry between two weighted finite objects. The atom/carry involution acts on a different coefficient space, with \(\tau(L)-1\) labels, where \(\tau(L)\) counts the divisors. For a physical Gram matrix \(G\) its metric changes to \(T_L^{\mathsf T}GT_L\), and the moment column changes to \(T_L^{\mathsf T}b\). The minimum reconstruction cost is invariant when both are transported.

One can see the difference between these metrics at period 6. The actual carry is \(\kappa_6=g_2+2g_3-g_6\), with values \((0,1,1,0,0,1)\) on residues 0 through 5. Under the uniform measure, \(\langle g_2,\kappa_6\rangle=1/6\). The primitive Ramanujan modes at 2 and 3 are orthogonal there, while their integrated packets have inner product \(1/2\). A period transform alone does not supply the Gram matrix in the physical probability measures.

There is also a natural refinement law for the **full** transforms. For \(L\mid M\), send a gcd class \(h\mid M\) to \(g=\gcd(h,L)\). On class masses let \(D_{ML}\) sum the masses over each fiber. Let \(R_{ML}\) restrict transformed coordinates to \(q\mid L\). Since \(c_q(h)\) depends only on \(\gcd(q,h)\), and \(q\mid L\), the following square commutes:
\[
 F_LD_{ML}=R_{ML}F_M .
\]
The uniform mass of class \(g\) at period \(L\) is \(\mu_{L,g}=\varphi(L/g)/L\). Uniform measure pushes forward under residue reduction, so these masses are compatible. In the input norm \(\sum_g|W_g|^2/\mu_{L,g}\), the adjoint lift of a coarse mass \(W_g\) assigns the fine class \(h\) mass \(\mu_{M,h}W_g/\mu_{L,g}\). The lift is isometric and its pushforward is the identity. On transformed coordinates the adjoint of restriction is extension by zero. Thus the transforms give a natural unitary equivalence of the two systems, both for the projections and for their adjoint inclusions.

The bounded inverse limit of the transform side is consequently
\[
 \left\{z=(z_q)_{q\ge1}:\ \sum_{q\ge1}\frac{|z_q|^2}{\varphi(q)}<\infty\right\}.
\]
Indeed every finite set of conductors divides a common period, so the supremum of the squared stage norms is the displayed sum. The algebraic inverse limit permits every sequence. This identifies exactly which infinite completion the finite transform controls. The physical Pareto Gram matrices below use the distribution of positive integers in each residue class and have their own reconstruction costs.

[Weighted transform and inverse](RH/FullConductorRamanujanTransform.lean#L231) · [Physical Gram congruences](RH/PhysicalCarryGram.lean#L187) · [Period-six packet calculation](RH/FiniteCarryRamanujanDictionary.lean#L211)

## Recovering a prime power with two canonical carries

Use the Pareto weights \(P(n)=1/[n(n+1)]\) or \(Q(n)=1/[\zeta(2)n^2]\) for \(n\ge1\). In either space \(g_d\to0\) strongly. One can use \(\|g_d\|\le K/\sqrt d\), where \(K=\sqrt2\) in \(P\) and \(K=\sqrt{2/\zeta(2)}\) in \(Q\).

Fix a prime power \(a>1\), put \(b=a^k\) with \(k\ge2\), and choose a prime \(s\nmid a\). Put \(t=s^{\varphi(b)}\). Then \(t\) is a prime power, \(t\equiv1\bmod b\), and \(t>b\). For \(h=a,b\) the conductor \(ht\) has two coprime prime-power factors. The least inverse of \(t\) modulo \(h\) is 1. The least inverse of \(h\) modulo \(t\) is
\[
 \alpha_h(t)=\frac{(h-1)t+1}{h}.
\]
Indeed this is an integer strictly between 0 and \(t\), and \(h\alpha_h(t)\equiv1\bmod t\). The two canonical carry identities are therefore
\[
 \kappa_{at}=g_a+\alpha_a(t)g_t-g_{at},\qquad
 \kappa_{bt}=g_b+\alpha_b(t)g_t-g_{bt}.
\]
Set \(\lambda=\alpha_a(t)/\alpha_b(t)\in(0,1]\). Cancellation of the common \(g_t\) column gives the exact physical identity
\[
 g_a-(\kappa_{at}-\lambda\kappa_{bt})
    =\lambda g_b+g_{at}-\lambda g_{bt}.
\]
The right side has norm at most \(K(b^{-1/2}+(at)^{-1/2}+(bt)^{-1/2})\). It tends to zero as \(k\to\infty\). The two synthesis coefficients have absolute sum at most 2. This bound is in the parameter \(b\). The required mixed conductors \(at,bt\) can be much larger.

Every prime-power atom is consequently in the closure of the canonical carries. For an arbitrary mixed \(d\), the original CRT identity writes \(g_d\) as a finite prime-power row minus \(\kappa_d\). This puts every \(g_d\) in the same closure. Conversely each \(\kappa_d\) is an atom combination. **The closed canonical-carry span equals the full closed atom span under both probabilities.** The proof of the prime-power step only uses two-factor conductors. The last step uses the own carry of each remaining mixed conductor.

[Canonical inverse convention](NumberTheory/PrimePowerCRTDecomposition.lean#L71) · [Canonical synthesis](RH/FiniteAtomCarryCRT.lean#L153) · [Atom norm bound](RH/QConductorCoefficientMass.lean#L68)

## The quotient that disappears on completion

Put \(\mathcal P=\overline{P_{\rm alg}}\). Algebraically \(A_{\rm alg}/C_{\rm alg}\simeq P_{\rm alg}\). With the quotient seminorm inherited from the physical space, every coset has norm zero, since its representative can be approximated by carries. The Hausdorff cokernel of the dense inclusion into \(V\) is zero. In particular, a continuous observation on \(V\) that annihilates all canonical carries vanishes on \(V\).

The algebraic prime-coordinate projection \(\pi(p+c)=p\) has a stronger defect than unboundedness. For any \(v\in V\) and \(p\in\mathcal P\), choose \(p_j\to p\) from the prime span and \(c_j\to v-p\) from the carry span. Then \(p_j+c_j\to v\) and \(\pi(p_j+c_j)\to p\). Thus
\[
 \overline{\operatorname{graph}(\pi)}=V\times\mathcal P .
\]
In particular \(\pi\) is **not closable**. The separate Hilbert completions give the split exact row
\[
 0\longrightarrow\mathcal P
 \xrightarrow{p\mapsto(p,-p)}\mathcal P\oplus_2 V
 \xrightarrow{(p,c)\mapsto p+c}V\longrightarrow0 .
\]
Its bounded section is \(v\mapsto(0,v)\). The anti-diagonal kernel records the ambiguity created by completing the two coordinates separately. In contrast, completing a paired coefficient space with its **synthesis norm** \(\|(p,c)\|=\|p+c\|\) gives \(V\) directly. The finite natural isomorphism extends isometrically when both presentations are equipped with their own synthesis norms.

There is also a physical orthogonal decomposition. Project the canonical carries onto \(\mathcal P^\perp\) before closing their span. The result is \(V\cap\mathcal P^\perp\), giving \(V=\mathcal P\oplus^\perp(V\cap\mathcal P^\perp)\). The repository's corrected Ramanujan carries give a further, distinct subspace \(M\) of mixed packets. Equality of the **raw** canonical-carry closure with \(V\) does not identify \(M\) with \(V\).

[Physical orthogonal splitting](RH/PhysicalPrimePowerCarryProjection.lean#L114) · [Corrected carry and packet closures](RH/MixedCanonicalCarryCapture.lean#L115)

## Quantifying the loss of the prime coordinate

Take \(t=3^j\), \(j\ge1\), and look at the stage \(L=2t\). Its oblique prime extraction sends
\[
 g_{2t}\longmapsto g_2+\frac{t+1}{2}g_t.
\]
On \(1\le n<t\) the output is at least \(n/2\), so its squared Pareto norm is at least \(\sum_{n=1}^{t-1}n/[4(n+1)]\ge(t-1)/8\). Meanwhile \(\|g_{2t}\|_P^2\le1/t\). It follows that
\[
 \|\pi_{2t}\|_{P\to P}\ge\sqrt{t(t-1)/8}.
\]
The finite inverse exists at every \(2t\), while the norms of these particular coordinate projections grow at least linearly in \(t\). This estimates the component map \(p+c\mapsto p\). The norm of the weighted Ramanujan isometry in its own metrics is 1.

## A complete minimal family with no basis expansion

For each mixed \(m\), the repository constructs a continuous Möbius coordinate \(\ell_m\) with \(\ell_m(g_d)=\delta_{md}\). Every prime-power term in a canonical carry row has zero \(m\)-coordinate. Therefore
\[
 \ell_m(\kappa_d)=-\delta_{md},\qquad
 \ell_m(p)=0\quad(p\in\mathcal P).
\]
Removing \(\kappa_m\) leaves a closed span contained in \(\ker\ell_m\), so no individual carry is redundant for the full closed span. More precisely, for any finite set \(F\) of mixed labels,
\[
 \overline{\operatorname{span}}\{\kappa_d:d\notin F,\ d\ \mathrm{mixed}\}
       =V\cap\bigcap_{m\in F}\ker\ell_m .
\]
For the reverse containment approximate the target by finite carry words and subtract the terms with labels in \(F\). Each removed coefficient tends to zero by continuity. The resulting finite-codimension quotient is \(\mathbb R^F\), with coordinates \((-\ell_m)_{m\in F}\). Thus every nonzero prime-power atom lies in every finite deletion closure, even though deleting any carry removes a direction from \(V\).

The family is complete and minimal. Its biorthogonal coordinates vanish simultaneously on the nonzero space \(\mathcal P\). Consequently **no ordering makes the carries a Schauder basis of \(V\)**. A convergent expansion of a prime atom would have every fixed coefficient zero. The two-carry approximants avoid this obstruction because their labels move.

There is also an unconditional obstruction for the constant. Suppose a single series \(\sum_d a_d\kappa_d\), using each mixed label once, converges in Pareto norm to \(\mathbf1\). Applying \(\ell_m(\mathbf1)=-\mu(m)\) forces \(a_m=\mu(m)\). Along \(m=2p\) for odd primes \(p\), this coefficient is 1 and \(\kappa_{2p}(n)=\lceil n/2\rceil\) on \(1\le n<p\). The preceding head bound gives \(\|\kappa_{2p}\|_P^2\ge(p-1)/8\). The terms fail the necessary condition of tending to zero. Hence this particular series interpretation of reconstruction is impossible, including under RH. The closure criterion allows successive finite words to change their coefficients.

These coordinates also delimit the two-carry proof. Two-factor carries recover every prime-power atom, but \(\ell_{30}\) annihilates **every** two-factor carry and \(\ell_{30}(g_{30})=1\). Recovering the whole \(V\) uses mixed conductors of higher support as well.

[Continuous biorthogonal coordinates](RH/MobiusCoefficientStabilization.lean#L34) · [Coordinates of the unit](RH/SquarefreeMobiusProjection.lean#L88) · [Finite deletion theorem](Analysis/ContinuousBiorthogonalDeletion.lean#L147)

## Reconstruction as a bounded inverse limit

For any real Hilbert family \(u_i\), let \(H_F=\operatorname{span}\{u_i:i\in F\}\) at a finite set \(F\). Synthesis \(S_Fc=\sum c_i u_i\) has adjoint \(S_F^*x=(\langle u_i,x\rangle)_{i\in F}\) and Gram operator \(G_F=S_F^*S_F\). Prescribe observations \(b_F\). The finite minimum-norm representer and its squared cost are
\[
 x_F=S_FG_F^\dagger b_F,\qquad E_F=b_F^{\mathsf T}G_F^\dagger b_F
\]
when \(b_F\in\operatorname{ran}G_F\). For inconsistent data the exact constraint cost is \(+\infty\). For distinct physical atoms, finite independence is proved in **both** \(P\) and \(Q\), so every finite assignment is feasible and \(G_F^\dagger=G_F^{-1}\).

When \(F\subset J\) and the data agree on the overlap, \(P_{H_F}x_J=x_F\). The difference is orthogonal to \(H_F\), which gives the exact identities
\[
 \|x_J-x_F\|^2=E_J-E_F,\qquad
 \|x_\infty-x_F\|^2=E_\infty-E_F,\qquad E_\infty=\sup_F E_F.
\]
The second identity assumes finite \(E_\infty\). The first then makes the minimizing net Cauchy. Its limit gives the unique representer in \(H_\infty=\overline{\bigcup H_F}\). Every ambient solution lies in \(x_\infty+H_\infty^\perp\). Conversely a representer \(y\) bounds every \(E_F\) by \(\|y\|^2\). The divisors of \(\operatorname{lcm}(1,\ldots,N)\) are cofinal, so those stages give the same supremum and strong limit.

In the category of real Hilbert spaces and linear contractions, \(H_\infty\) is the colimit of the isometric inclusions. A compatible family of contractions out of the stages defines a contraction on the union, hence uniquely on its closure. Taking adjoints gives the limit of the reverse orthogonal projections. Its points are the compatible families \((z_F)\) with \(\sup_F\|z_F\|<\infty\), and their norm is that supremum. An arbitrary compatible family belongs to the algebraic inverse limit and may have infinite energy. For example, \(b_d=1/\sqrt d\) is feasible at every conductor stage and has infinite supremum under both physical norms. Every representable target obeys \(\sqrt d\,b_d\to0\).

[Finite pseudoinverse and cofinal reconstruction](RH/ConductorReconstructionEnergy.lean#L67) · [Energy increments and exact error](Analysis/HilbertConstraintEnergy.lean#L267) · [Critical-decay counterexample](RH/ConductorReconstructionEnergy.lean#L207) · [The category of Hilbert spaces and contractions](https://doi.org/10.1112/blms.13010)

## Reconstructing arbitrary atom data from carry observations

For prescribed atom data \(b_d\), form the carry data \(c_d=\sum_h U_{h,d}b_h-b_d\) at mixed conductors. The sum is over the maximal prime-power factors of \(d\). The following two conditions characterize bounded physical representability of the **original** data.

1. The supremum of the exact finite minimum energies for the carry observations \(c_d\) is finite.
2. For each prime power \(a\), the sequences \(b=a^k,t=s^{\varphi(b)}\) and \(\lambda\) in the two-carry proof give
   \[
   b_a=\lim_{k\to\infty}\big(c_{at}-\lambda c_{bt}\big).
   \]
   Here the unsubscripted \(b=a^k\) is the auxiliary conductor, and \(b_a\) denotes the prescribed datum. One fixed choice of \(s\nmid a\) per \(a\) suffices.

Indeed, the first condition gives the unique carry representer \(x\in V\). Strong two-carry approximation identifies the displayed limit with \(\langle x,g_a\rangle\), so the second condition matches the missing prime-power data. The CRT expression then matches every mixed datum. Conversely every bounded representer satisfies both conditions. For represented data the squared global optimum can therefore be computed from carry constraints alone.

For an example of the compatibility issue, assign observation 1 to \(g_2\), zero to every other prime-power atom, and zero to every canonical carry. Extend linearly using the algebraic direct sum. All finite restrictions are feasible. The carry cost is identically zero, but the prime observation at 2 fails the limit condition. Equivalently, applying this functional to \(g_2-\kappa_{2t}+\lambda\kappa_{bt}\) gives 1 on vectors whose norm tends to zero.

[Least squared dual bound](Analysis/HilbertConstraintEnergy.lean#L295) · [Transport between physical norms](RH/ConductorReconstructionEnergy.lean#L148)

## Three target-specific tests for RH

**The actual constant.** In the Pareto metric the target column for \(\mathbf1\) is \(b_d^\star=\log(d)/d\). Let \(C_F=(b_F^\star)^{\mathsf T}G_F^{-1}b_F^\star\). The constant itself represents these observations. Thus \(C_F=\|P_{H_F}\mathbf1\|^2\le1\) and the stage minimizers converge to \(P_V\mathbf1\) unconditionally. For \(d_0=\mathbf1-P_V\mathbf1\),
\[
 1-\sup_F C_F=\|d_0\|^2,\qquad
 \mathrm{RH}\ \Longleftrightarrow\ \sup_F C_F=1.
\]
Because the canonical carries are dense in \(V\), the same saturation test can be run with carry Gram matrices. Their actual target entries are \(\sum_h U_{h,d}\log(h)/h-\log(d)/d\). Algebraic evaluation of any finite entry and attainment of the limiting value 1 are separate statements.

For example, take the single actual carry at conductor 6. Its table has values only 0 and 1, so \(\|\kappa_6\|^2=\langle\mathbf1,\kappa_6\rangle\). The orthogonal projection onto this one column is precisely \(\kappa_6\), and the first cost and squared miss are exact:
\[
 C_{\{6\}}=\frac{\log 2}{3}+\frac{\log 3}{2},\qquad
 \|\mathbf1-\kappa_6\|^2=1-\frac{\log 2}{3}-\frac{\log 3}{2}.
\]

There is an exact recurrence for enlarging a finite family. Write \(u=\kappa_m\) for a new carry, \(q_F=u-P_{H_F}u\), and \(C_F=\|P_{H_F}\mathbf1\|^2\). Independence gives \(q_F\ne0\). With \(v=(\langle\kappa_d,u\rangle)_{d\in F}\) and \(B_F=(\langle\mathbf1,\kappa_d\rangle)_{d\in F}\), projecting the unit onto the one extra line gives
\[
 C_{F\cup\{m\}}-C_F
 =\frac{|\langle\mathbf1,q_F\rangle|^2}{\|q_F\|^2}
 =\frac{(B_m-v^{\mathsf T}G_F^{-1}B_F)^2}
        {\|u\|^2-v^{\mathsf T}G_F^{-1}v}.
\]
Along any enumeration of all mixed conductors, these nonnegative increments telescope to \(1-\|\mathbf1-P_V\mathbf1\|^2\), starting with \(C_\varnothing=0\). This gives a Parseval series in the mutually orthogonal residuals \(q_F/\|q_F\|\). It also explains how a convergent reconstruction can coexist with the obstruction to a series in the original carries. Every increment uses only finite entries, evaluated below.

**One additional row.** On an atom stage require \(\langle x,g_i\rangle=0\) for all its labels and \(\langle x,\mathbf1\rangle=1\). Every atom at the stage vanishes at \(n=L\), a coordinate of positive Pareto mass, so \(\mathbf1\notin H_F\). Put \(e_F=\mathbf1-P_{H_F}\mathbf1\). The unique minimum vector is \(e_F/\|e_F\|^2\) and its squared cost is \(Z_F=(1-C_F)^{-1}\), by Cauchy–Schwarz. Equivalently, the Schur complement of \(G_F\) in the augmented Gram matrix is \(1-C_F\). Hence the augmented problem has a compatible bounded-energy solution precisely when \(d_0\ne0\), with minimal solution \(d_0/\|d_0\|^2\). For this explicit target, RH is equivalent to \(Z_F\to\infty\). For general finite sets choose any common multiple as \(L\).

**Computing the actual finite entries.** For \(d,e\mid L\), the atoms and carries repeat modulo \(L\), but the infinite Pareto norm gives different masses to the residue classes. Number them \(1,\ldots,L\), with \(L\) representing 0. From \(P(n)=1/n-1/(n+1)\) one gets
\[
 w_{L,s}=\sum_{j\ge0}P(jL+s)
 =\frac{\psi((s+1)/L)-\psi(s/L)}{L},
 \qquad (G_F^\kappa)_{de}=\sum_{s=1}^{L}w_{L,s}\,\kappa_d(s)\kappa_e(s),
\]
where \(\psi\) is the digamma function. The second formula and \(B_d=\sum_s w_{L,s}\kappa_d(s)\) are exact. The class \(s=L\) contributes zero to every carry and one to the target. Thus the squared miss at any finite stage is at least \(w_{L,L}>0\). Exact rational CRT coordinates and exact physical Gram entries involve different arithmetic.

**The physical-head boundary.** An independent checked construction has an orthonormal basis of physical-head directions in the mixed-packet space \(M\). In its coordinates the algebraic product-difference cokernel is \(\mathbb R^{\mathbb N}/\ell^2\). The boundary of the unit is the class of a specific sequence \(\sigma_j\), called \(\mathrm{signedCarry}\) in Lean. The repository proves
\[
 \mathrm{RH}
 \ \Longleftrightarrow\ \sum_j|\sigma_j|^2<\infty
 \ \Longleftrightarrow\
 \|P_M J_2\|_P^2=\log2-(\log2)^2.
\]
Here the finite Gram matrices of the orthonormal directions are identities. The unconditional statement \(N^{-1}\sum_{j<N}|\sigma_j|^2\to0\) still allows the unnormalized sums to diverge. The \(\sigma_j\) are signed coordinates of a boundary in \(M\); \(\kappa_d\) are floor functions in the residue dictionary.

[Actual logarithmic moment](RH/NaturalMobiusSourceLimits.lean#L26) · [Ambient projection and residual](RH/MobiusCoefficientStabilization.lean#L65) · [Physical-head Parseval isometry](RH/PhysicalHeadLayerIsometry.lean#L82) · [Boundary, square summability and parity saturation](RH/PhysicalHeadBoundaryCoordinates.lean#L154)

## Sources and proof scope

The linked declarations give the finite presentation, natural change of coordinates, Plancherel identity, physical Gram congruence, cofinal minimum-energy theorem and signed physical-head criterion. [CanonicalCarryClosure.lean](RH/CanonicalCarryClosure.lean) proves equality of the raw-carry and full atom closures under both physical measures, the selector graph formula, the RH membership criterion and the quantitative lower bound for prime-coordinate amplification at twice an odd prime. [CanonicalCarryGram.lean](RH/CanonicalCarryGram.lean) proves the signed logarithmic moment formula, the exact limiting Moore–Penrose cost, the strong limit of finite minimizers and the RH saturation criterion. The explicit Euler-power witnesses, numerical lower bound for the oblique norm along powers of three, fixed-series obstruction, augmented Gram calculation and observations on separated completion have their proofs in this note. A uniform finite-energy criterion supplies an RH result only after its target is identified as above.

[Hilbert-space minimum norm solutions](https://www.damtp.cam.ac.uk/research/cia/files/teaching/Inverse_Problems_2019/LectureNotes2019.pdf) · [Báez-Duarte's natural approximation criterion](https://arxiv.org/abs/math/0202141)
