# The physical parity object and its categorical reconstruction

The input consists of the positive-integer physical sites, the closed legal residue space \(V\), its closed mixed-conductor packet space \(M\), the physical Pareto mean, and the conductor and head maps. The construction starts from the screened parity section \(u\). It keeps the ambient constant \(\mathbf1\) as a separate target. Their difference is the obstruction carried by the centered snake. The results below specify the metric, the domain of each quotient, the kind of convergence and the quantifiers in the arithmetic criteria.

### Lean entry points

[Public categorical imports](All.lean) · [Historical chronological replay](HistoricalRebuild.lean) · [Physical parity interface](PhysicalParityObject.lean)

The theorem \(\texttt{physical_conditions_tfae}(n)\) gives 25 equivalent propositions at every fixed stage \(n\). They include the original thirteen categorical mean tests, the RH proposition itself, and eleven further tests. The theorem \(\texttt{mean_rows_homology_zero}(S)\) computes the middle homology of the legal and ambient rows and of both rows after quotient by any \(S\le M\). The theorem \(\texttt{rawGram_iff_correctedCarryCapture}\) connects two different carry dictionaries at their precise RH thresholds. The import and replay files give access to the full statements, including conditions on indices, coprimality, multiplicities, and seminormed denominators.

### The comparison diagram

For the centered comparison the diagram reads
\[
\begin{array}{ccccccccc}
0&\longrightarrow&M&\longrightarrow&V&\xrightarrow{\epsilon_V}&\mathbb R&\longrightarrow&0\\
&&\downarrow\iota&&\downarrow c|_V&&\downarrow 0\\
0&\longrightarrow&Z&\longrightarrow&H&\xrightarrow{\epsilon_H}&\mathbb R&\longrightarrow&0
\end{array}
\qquad c(x)=x-\epsilon_H(x)\mathbf1,\quad Z=\ker\epsilon_H.
\]
For the inclusion comparison the middle and right vertical maps are \(V\hookrightarrow H\) and \(\mathrm{id}_{\mathbb R}\). The legal and ambient sections are \(a\mapsto au\) and \(a\mapsto a\mathbf1\). The source of the centered connecting morphism is \(\mathbb R\), while the source of the inclusion connecting morphism is zero. The square-zero algebra structures, quotient norms and derived cokernels are recorded below.

## The legal and ambient mean rows

Let \(H=L^2(P)\), \(V\subset H\) be the closed legal residue space, \(M\subset V\) the closed mixed-packet subspace, \(\mathbf1=\mathbf1_H\), \(\epsilon x=\langle x,\mathbf1\rangle_P\), and \(Z=\ker\epsilon=\mathbf1^\perp\). The screened unit is \(u=(I-P_M)J_2/\log 2\), with \(u\in V\cap M^\perp\) and \(\epsilon u=1\). Define \(b=u-\mathbf1\), \(\mathbf1_V=P_V\mathbf1=u/\|u\|_P^2\), \(r=\mathbf1-\mathbf1_V\), and \(E=\|r\|_P^2=1-\|u\|_P^{-2}\). The defects \(b\) and \(r\) have different geometric meanings.

The two split short exact sequences in real topological modules are
\[
 0\longrightarrow M\xrightarrow{i} V\xrightarrow{\epsilon} \mathbb R\longrightarrow0,
 \qquad
 0\longrightarrow Z\xrightarrow{j} H\xrightarrow{\epsilon} \mathbb R\longrightarrow0.
\]
The legal section and retraction are \(s_V(a)=au\) and \(p_V(v)=v-\epsilon(v)u=P_Mv\). The ambient ones are \(s_H(a)=a\mathbf1\) and \(c(x)=x-\epsilon(x)\mathbf1=P_Zx\). In either row, the retraction composed with its inclusion and the mean composed with its section are identities. The inclusion–retraction and section–mean projectors sum to the identity. Thus \(V=M\oplus_P^\perp\mathbb Ru\) and \(H=Z\oplus_P^\perp\mathbb R\mathbf1\). The legal inclusion is a categorical kernel, the legal mean is its cokernel, and the resulting biproduct and quotient carry their topological structures. For any continuous linear \(f:X\to\mathbb R\), every continuous legal lift has the unique form \(s_V f+i m\), \(m:X\to M\). In particular the legal sections have the form \(a\mapsto a(u+m)\), with squared norm \(\|u\|_P^2+\|m\|_P^2\). Ambient sections have the form \(a\mapsto a(\mathbf1+z)\), \(z\in Z\), with squared norm \(1+\|z\|_P^2\).

Lean declarations include `legalMeanSplitting`, `legalMean_shortExact`, `legalMixedIsKernel`, `legalMeanIsCokernel`, `legalMixedBiprodIso`, `legalMixedQuotientIso`, `legalMean_unique_mixed_lift`, `ambientMeanSplitting`, `ambientMean_shortExact`, and `ambientMeanSection_graph`. [Legal row](../RH/MixedConductorSplitExact.lean) · [Ambient row](../RH/CenteredMeanSnake.lean) · [Sections](../RH/CenteredMeanAmbientGeometry.lean)

### Two commutative diagrams on those same rows

| Row comparison, with the legal row above the ambient row | Left vertical \(M\to Z\) | Middle vertical \(V\to H\) | Right vertical \(\mathbb R\to\mathbb R\) | Connecting morphism |
| --- | --- | --- | --- | --- |
| Inclusion | inclusion | inclusion | identity | source \(\ker(\mathrm{id})=0\), hence zero |
| Centering | inclusion | \(c|_V\) | zero | \(\partial(a)=a[b]_M\in Z/M\) |

Both left squares commute because \(c(m)=m\). The right squares follow respectively from preservation of the mean and \(\epsilon c=0\). For the centered diagram, lift \(a\) to \(au\), apply \(c\), then take the class modulo the image of the left vertical. Every other lift differs by a member of \(M\), hence gives the same class. This is Mathlib's actual snake connecting map. The difference of the chosen sections before passing to the quotient is \(a\mapsto a(u-\mathbf1)\). Its physical mean is zero for every \(a\). Vanishing of its class means that it lies in \(M\); since \(b\in M^\perp\), this is equivalent at \(a=1\) to \(b=0\). For each \(z\in Z\) representing \(\partial(1)\),
\[
 \|z\|_P^2=\|b\|_P^2+\|z-b\|_P^2,\qquad
 \|\partial\|^2=\|b\|_P^2=\|u\|_P^2-1=\frac{E}{1-E}.
\]
The unit boundary is injective as a map from the whole scalar line when \(\mathbf1\notin V\); its image then has dimension one. The inclusion snake's successive cokernel arrow is the equivalence \(Z/M\to H/V\).
[Both snake maps, their lifts and norms](../RH/CenteredMeanSnake.lean) · [Inclusion cokernels](../RH/CenteredMeanQuotients.lean)

### The entire centered kernel–cokernel sequence and its homology

Let \(K=V\cap\mathbb R\mathbf1\). The six-arrow sequence in real modules is
\[
0\longrightarrow K\xrightarrow{\kappa}V/M\xrightarrow{\bar\partial}Z/M
 \xrightarrow{\alpha}H/c(V)\xrightarrow{\bar\epsilon}\mathbb R\longrightarrow0.
\]
Its four displayed maps are \(\kappa(x)=[x]_M\), \(\bar\partial([v]_M)=[c(v)]_M=\epsilon(v)[b]_M\), \(\alpha([z]_M)=[z]_{c(V)}\), and \(\bar\epsilon([h]_{c(V)})=\epsilon(h)\). The algebra quotient identifies \(V/M\) with the scalar kernel of the zero right vertical. Explicitly \(\ker(c|_V)=K\), \(c(V)=M\oplus^\perp\mathbb Rb\), \(\ker\bar\partial=\kappa(K)\), \(\ker\alpha=\mathbb R[b]=\operatorname{im}\bar\partial\), and \(\ker\bar\epsilon=\alpha(Z/M)\). The first map is injective and the last mean is split surjective by \(a\mapsto[a\mathbf1]_{c(V)}\). Each middle homology \(\ker(d_{i+1})/\operatorname{im}(d_i)\) is zero. Both original short rows also have zero middle homology. This is unconditional exactness even when \(\bar\partial\) has nonzero image. The target \(Z/M\) is a cokernel of a vertical arrow and need not vanish by exactness alone. [All six arrows and exactness](../RH/CenteredMeanLongExact.lean) · [Closed centered range and continuous last section](../RH/CenteredMeanAmbientGeometry.lean)

In \(V\), both \((\mathbb R\mathbf1_V)^{\perp_V}\) and \((\mathbb Ru)^{\perp_V}\) equal \(M\). Their quotient by \(M\) is zero. In \(H\), \(M=V\cap Z\) and inclusion induces the continuous linear equivalence
\[
 T:Z/M\longrightarrow H/V,\quad T[z]_M=[z]_V,\qquad
 T^{-1}[x]_V=[x-\epsilon(x)u]_M,\qquad T\partial(a)=-a[\mathbf1]_V.
\]
The quotient norms obey \(\|T\partial(1)\|^2=E\), whereas \(\|\partial(1)\|^2=E/(1-E)\). More explicitly put \(W=Z\cap V^\perp\). The minimal Hilbert representatives of the three quotient terms have spaces \(\mathbb Rb\oplus^\perp W\), \(\mathbb Rr\oplus^\perp W\), and \(\mathbb R\mathbf1\oplus^\perp W\), for \(Z/M\), \(H/V\), and \(H/c(V)\) respectively. On these models \(T(tb+w)=-tr+w\) and \(\alpha(tb+w)=w\). [Internal and ambient quotients](../RH/CenteredMeanQuotients.lean) · [Transport on orthogonal representatives](../RH/CenteredMeanAmbientGeometry.lean)

### Stage quotients, two-sided ideals and changing the section

On the legal space write \(v=m+au\). The screened algebra product is \((m,a)(n,b')=(an+b'm,ab')\). Equivalently \(v\star_u w=\epsilon(v)w+\epsilon(w)v-\epsilon(v)\epsilon(w)u\). Its mean is an algebra homomorphism, \(M\) is its maximal square-zero two-sided ideal, and \(V/M\simeq_{\mathbb R\text{-alg}}\mathbb R\) is also a homeomorphism. Every linear subspace \(S\subset M\) is a two-sided ideal for this product. Any mean-one unit \(e\) defines the analogous \(\star_e\); changing \(e\) to \(f\) sends \(v\mapsto v+\epsilon(v)(f-e)\), fixes \(M\), and preserves the scalar quotient. The ambient square-zero algebra has unit \(\mathbf1\) and ideal \(Z\). The defect of the inclusion on any legal product equals \(\epsilon(v)\epsilon(w)(\mathbf1-u)\). It vanishes for each pair with a mean-zero factor. For two pure prime powers their nonzero von Mangoldt means make product agreement equivalent to RH. The indicated products are constructed from the mean and the section. [Square-zero algebra and algebra quotient](../RH/MixedConductorSquareZero.lean) · [Product defect and conductor criterion](../RH/CenteredMeanRHCriteria.lean)

For every subspace \(S\le M\), the two descended short rows have terms \((M/S,V/S,\mathbb R)\) and \((Z/S,H/S,\mathbb R)\). They split and the centered verticals induce the same square diagram. Its snake target \(T_S=(Z/S)/(M/S)\) is isometrically identified with \(Z/M\); even an algebraic nonclosed denominator is allowed here with its quotient seminorm. Under the cancellation isometry \(\partial_S(a)\mapsto\partial(a)\) and \(\|\partial_S(a)\|=|a|\|b\|_P\). For \(S\le S'\), representative-preserving quotient maps commute with the two row splittings and connecting maps. The resulting upper and lower short-complex functors, natural diagram transformation and connecting transformation restrict to the prime-support tower. The stage centered long sequences are exact, with their kernel and cokernel terms identified with the original ones. A zero class at *any one stage* detects the entire obstruction. [Stage functors, naturality, six-arrow exactness and quotient isometries](../RH/CenteredMeanStageSnake.lean)

### Equivalent RH conditions supplied by the mean object

The following conditions are equivalent for this particular legal residue space. Its dilation density theorem supplies the step from \(\mathbf1\in V\) to \(V=H\).
\[
\begin{aligned}
\mathrm{RH}
&\iff \mathbf1\in V \iff V=H \iff M=Z \iff Z/M=0 \iff H/V=0\\
&\iff u=\mathbf1 \iff \|u\|_P\le1 \iff \|u\|_P^2=1
 \iff r=0 \iff E=0\\
&\iff \partial(1)=0 \iff \partial=0 \iff \partial_S(1)=0
 \iff V=M\oplus_P^\perp\mathbb R\mathbf1 .
\end{aligned}
\]
For every fixed \(S\le M\) the list also includes injectivity of the next stage cokernel arrow and existence of a unique mean-one element of the middle vertical kernel. Further equivalent tests are existence of a contractive legal mean section, the constant-one factorization bound for the legal mean, arbitrarily small complete parity quotient classes, attainment of the normalized parity capture \(\sqrt{1/\log2-1}\), convergence of the repository's head determinants at scalar one to zero, and agreement of legal and ambient products for packets 2 and 3. The centered boundary is an epimorphism exactly under RH. On the RH branch its target is zero. On the other branch normalized continuous Mellin characters for distinct right zeros agree on its image but separate points of its cokernel. The same RH statement is equivalent to squarefree constant membership and the complete natural approximation criterion with free coefficients. `stageUnit_zero_iff_RH` supplies the converse without an external hypothesis in its type. [Thirteen categorical tests](../RH/CenteredMeanRHCriteria.lean) · [Squarefree converse and epic boundary](../RH/CenteredMeanSquarefreeConverse.lean) · [Stage lifting and norm equivalences](../RH/CenteredMeanUnitNorm.lean) · [Cokernel Mellin characters](../RH/CenteredMeanMellinCharacters.lean)

## Coprime Fekete slopes and the legal bilinear form

For a real arithmetic function \(f\) and a positive base \(a\), put
\[
 F_a(f)=\inf_{k\ge1} f(a^k)/k .
\]
Fekete's lemma identifies this infimum with the limit when the exponent sequence \(k\mapsto f(a^k)\) is subadditive and its normalized values are bounded below. For positive coprime \(a,b\), suppose \(f(mn)=f(m)+f(n)\) on positive coprime pairs and those two hypotheses hold at each of \(a,b\). Then
\[
 F_{ab}(f)=F_a(f)+F_b(f),\qquad F_{a^j}(f)=jF_a(f)\quad(j\ge1).
\]
The product formula uses coprimality of \(a^k,b^k\) and adds their normalized limits. The power formula follows by restricting the exponent to multiples of \(j\). Coprime additivity together with \(M^{-1}\sum_{i=0}^{M-1}|f(M+i+1)-f(M+i)|\to0\) gives logarithmic rigidity on positive integers, and hence \(F_a(f)=f(a)\). [Fekete power laws](../NumberTheory/FeketePowerSlope.lean) · [Dyadic rigidity](../NumberTheory/DyadicAdditiveRigidity.lean)

In the Pareto space let \(C(x)=\langle x,\mathbf1_H\rangle_P\), \(S=I-P_M^P\), \(u=SJ_2/\log2\), and \(R(h)=\langle u,h\rangle_P\) on \(M^{\perp_P}\). For \(h\in M^{\perp_P}\), the raw residue \(r_n(x)=x\bmod n\) gives \(f_h(n)=\langle r_n,h\rangle_P=R(h)\log n\) for \(n\ge1\). Orthogonality to the mixed packets supplies coprime additivity, and the physical residue variation supplies the rigidity hypothesis. Thus every \(a>1\) computes the same signed coefficient, with \(R(h)=F_a(f_h)/\log a\). On \(M^{\perp_P}\times V\),
\[
 \beta(h,v)=\langle h,v\rangle_P=R(h)C(v),\qquad
 R(\mathbf1_H)=1,\quad C(u)=1,\quad R(u)=\|u\|_P^2.
\]
This continuous outer product has range the line spanned by \(C|_V\), left radical \(V^{\perp_P}\), and right radical \(M\). It induces a nondegenerate bilinear pairing \((M^{\perp_P}/V^{\perp_P})\times(V/M)\to\mathbb R\). The ambient Hilbert form in coordinates \(H=M^{\perp_P}\oplus^{\perp_P}M\) is the sum of the two diagonal inner products. The cross-pairing on \(M^{\perp_P}\times M\) is zero. Consequently \(Sv=C(v)u\) on \(V\), \(P_V^P\mathbf1_H=u/\|u\|_P^2\), and \(SJ_n=\Lambda(n)u\) for \(n>1\). Every positive prime power satisfies \(SJ_{p^k}=(\log p)u\), also when first powers are omitted. [Rank-one rigidity](../RH/MixedConductorRankOne.lean) · [Bilinearity, radicals and screening](../RH/MixedConductorBilinear.lean)

On \(H\) the centered screening \(D_0x=Sx-C(x)\mathbf1_H\) is the orthogonal projection onto \(M^{\perp_P}\cap\mathbf1_H^{\perp_P}\). Its positive Gram form is
\[
 \langle D_0x,D_0y\rangle_P=\langle Sx,Sy\rangle_P-C(x)C(y).
\]
On \(V\times V\) this equals \(\|u-\mathbf1_H\|_P^2 C(v)C(w)\). Testing \(v=w=u\) shows that the restricted form vanishes exactly under RH. Equivalently \(\beta(h,v)=C(h)C(v)\) for all \(h\in M^{\perp_P},v\in V\). Both predicates are equivalent to \(u=\mathbf1_H\). The checked forward implication from RH to legal membership uses the squarefree damping converse. [Defect and mean-product tests](../RH/MixedConductorBilinear.lean) · [Checked approximation converse](../RH/CenteredMeanSquarefreeConverse.lean)

## From the Pareto rank-one splitting to the native \(Q\) carry

### Fekete rates of the mean-bearing packets

Throughout this chapter \(r_k(n)=n\bmod k\), \(g_k=r_k/k\), \(J_d=\sum_{k\mid d}\mu(d/k)r_k\), \(\epsilon(v)=\langle v,\mathbf1\rangle_P\), \(\lambda=\log2\), and \(Z_2=\zeta(2)\). The legal space \(V\) is the closed span of the \(r_k\), and \(M\) is the closed span of packets with at least two distinct prime factors. Each physical site has positive mass in both metrics. We use the same symbols for vectors with the same physical coordinates.

Take \(h\in M^{\perp_P}\) and let \(f_h(k)=\langle r_k,h\rangle_P\). Since \(r_k=\sum_{d\mid k}J_d\), every mixed divisor contribution vanishes against \(h\). Thus \(f_h(ab)=f_h(a)+f_h(b)\) for coprime \(a,b\). The conductor variation theorem also gives
\[
 \lim_{N\to\infty}\frac1N\sum_{j=N}^{2N-1}|f_h(j+1)-f_h(j)|=0 .
\]
Together these facts imply \(f_h(k)=c_h\log k\) by dyadic additive rigidity. For \(a>1\), the coprime Fekete power rate is consequently exact,
\[
 \inf_{\ell\ge1}\frac{f_h(a^\ell)}{\ell}=
 \lim_{\ell\to\infty}\frac{f_h(a^\ell)}{\ell}=c_h\log a,\qquad
 c_h=\langle u,h\rangle_P,\qquad
 u=\frac{(I-P_M^P)J_2}{\lambda}.
\]
Here \(J_2=r_2\). Fekete's subadditivity hypotheses hold because the exponent sequence is linear. The dyadic theorem is the separate ingredient identifying a *single* slope across different primes. Möbius inversion gives \(\langle J_d,h\rangle_P=c_h\Lambda(d)\). At \(h=\mathbf1\) the scalar is one, hence the mean-bearing packets are the prime powers and \(\epsilon(J_{p^j})=\log p\). Testing against every \(h\in M^{\perp_P}\) and extending from the packet span yields
\[
 (I-P_M^P)v=\epsilon(v)u,\qquad
 V=M\oplus^{\perp_P}\mathbb Ru,\qquad \epsilon(u)=1 .
\]
In particular \((I-P_M^P)J_{p^j}=(\log p)u\) for every prime power, and \(M=V\cap\ker\epsilon\). [Coprime Fekete slopes](../NumberTheory/FeketePowerSlope.lean) · [Dyadic rigidity](../NumberTheory/DyadicAdditiveRigidity.lean) · [Screening of every legal vector](../RH/MixedConductorRankOne.lean)

### Two normal equations for the same physical dictionary

Write \(P_n=1/(n(n+1))\), \(Q_n=1/(Z_2 n^2)\), \(R_n=1/(n+1)\) and \(W_n=P_n/Q_n=Z_2(1-R_n)\). When used as a vector, \(W\) means \(W\mathbf1\). The same physical mean satisfies
\[
 \epsilon(v)=\langle v,W\rangle_Q,\qquad
 \langle v,w\rangle_P=\langle v,Ww\rangle_Q.
\]
Let \(\Pi=P_M^Q\). The Pareto fit \(p=P_M^Px\) is characterized by \(p\in M\) and \(\Pi W(x-p)=0\). It can be calculated entirely in \(Q\):
\[
 p=\sum_{j\ge0}(\Pi R)^j\Pi(I-R)x,\qquad \|\Pi R\|_{Q\to Q}\le\tfrac12 .
\]
In particular, if \(p=P_M^P J_2\), the original endpoint asks whether \(\langle p,Wp\rangle_Q=\lambda-\lambda^2\); equivalently \(\langle u,Wu\rangle_Q=1\).

Define the native mean-one representative \(u_Q=(I-\Pi)u=(I-\Pi)J_2/\lambda\). For \(v\in V\), apply \(I-\Pi\) to \(v-\epsilon(v)u\in M\). This proves
\[
 V=M\oplus^{\perp_Q}\mathbb Ru_Q,\qquad
 V\cap M^{\perp_Q}=\mathbb Ru_Q,\qquad
 M=V\cap W^{\perp_Q},\qquad
 V^{\perp_Q}=M^{\perp_Q}\cap u^{\perp_Q}.
\]
The transported Pareto orthogonality reads \(\langle m,Wu\rangle_Q=0\) for \(m\in M\). Equivalently \(V=(W V^{\perp_P})^{\perp_Q}\). The square-root-density isometry \(v\mapsto\sqrt W\,v\) gives \(\sqrt W\,V=(\sqrt W\,M)\oplus^{\perp_Q}\mathbb R(\sqrt W\,u)\) when transforming the entire space and the dictionary.

The two native and Pareto representatives genuinely differ on the physical sites. If \(h\) is perpendicular to \(M\) in both metrics, it is \(P\)-perpendicular to \(M\) and to \(W^{-1}M\). The closed span of \(M+W^{-1}M\) is the full physical Hilbert space by mixed reciprocal density, so \(h=0\). Since \(\epsilon(u)=1\), the mixed vector \(t=\Pi u=u-u_Q\) is nonzero. The exact comparison on every legal vector is
\[
 P_M^Q v-P_M^Pv=\epsilon(v)t,\qquad
 \|t\|_Q^2=\|u\|_Q^2-\|u_Q\|_Q^2>0,\qquad
 t=\sum_{j\ge0}(\Pi R)^j\Pi R u_Q.
\]
The last formula follows from \(\Pi(I-R)(u_Q+t)=0\). Thus reconstruction of the Pareto projection on *all* of \(V\) requires only the native \(Q\) projection and a single mixed correction. [Native normal line and strict metric difference](PhysicalParityObject.lean) · [Physical metric reconstruction](../RH/QPhysicalQuotientMetric.lean) · [Mixed reciprocal density](../RH/MixedReciprocalDensity.lean)

### CRT synthesis with carry line \(\mathbb Ru\)

Define the retained carry of a legal vector by \(\operatorname{Carry}_P(v)=\epsilon(v)u\). Its mixed coordinate is \(v-\epsilon(v)u\). The corresponding native \(Q\) coordinates are \((v-\epsilon(v)u_Q,\epsilon(v)u_Q)\). Changing the representative takes \((m,a)\) in the Pareto coordinates to \((m+at,a)\) in the native coordinates, with \(t=u-u_Q\). It fixes the scalar quotient \(V/M\) and holds for every legal vector. In particular, keeping the physical carry line \(\mathbb Ru\) gives the exact native cost and cross term
\[
 \|m+au\|_Q^2=\|m+at\|_Q^2+a^2\|u_Q\|_Q^2,\qquad \langle m,u\rangle_Q=\langle m,t\rangle_Q .
\]

For a mixed conductor \(d\), put \(q_p=p^{v_p(d)}\) and let \(c_{d,p}\) be the canonical inverse of \(d/q_p\) modulo \(q_p\). The actual raw floor carry \(C_d=\sum_{p\mid d}c_{d,p}g_{q_p}-g_d\) therefore has explicit scalar
\[
 a_d=\epsilon(C_d)
     =\sum_{p\mid d}c_{d,p}\frac{\log q_p}{q_p}-\frac{\log d}{d}
     =\sum_{p\mid d}(\log q_p)\left(\frac{c_{d,p}}{q_p}-\frac1d\right)>0 .
\]
Indeed the least positive CRT inverse is at least one and \(q_p<d\). Thus every individual mixed-conductor raw carry already generates the one-dimensional quotient. Its retained component is \(a_d u\) in Pareto and \(a_d u_Q\) in native \(Q\), with mixed remainder in both cases. The full raw carries have closed span \(V\). The packet-corrected carries \(K_d=\sum_{e\mid d,\ e\ {\rm mixed}}J_e\) have zero scalar and closed span \(M\). The atom–carry involution \((x,y)\mapsto(x+U_Ly,-y)\) preserves the scalar of the physical synthesis. Applying the two linear split maps to the synthesis preserves its mixed vector and retained carry for each chosen metric.

At period six the inverses are \(1,2\), so \(C_6=g_2+2g_3-g_6\) gives \(a_6=(\log2)/3+(\log3)/2\). Consequently its quotient coordinate is \(a_6\), whereas the corrected \(K_6=J_6=r_6-r_2-r_3\) has quotient coordinate zero. [Canonical floor carries](../RH/FiniteAtomCarryCRT.lean) · [Raw closure](../RH/CanonicalCarryClosure.lean) · [Corrected carries and Möbius inversion](../RH/MixedCanonicalCarryCapture.lean)

### An explicit native \(Q\) endpoint for the uncentered parity packet

Let \(w_V=P_V^Q W\). For \(v\in V\), \(\langle v,w_V\rangle_Q=\epsilon(v)\). This functional is nonzero because \(\epsilon(u)=1\). Its unique minimum-norm mean-one vector is \(w_V/\|w_V\|_Q^2\), giving the exact formula
\[
 u_Q=\frac{P_V^QW}{\|P_V^QW\|_Q^2},\qquad
 \|W\|_Q^2=Z_2\sum_{n\ge1}\frac1{(n+1)^2}=Z_2(Z_2-1).
\]
In this discrete space \(W\in V\) is equivalent to \(\mathbf1\in V\). To see the reverse implication as well, let \(T_k v(n)=v(\lfloor n/k\rfloor)\) with \(v(0)=0\). The legal space is invariant under \(T_k\). For a physical generator this follows directly from \(T_k r_d=(r_{kd}-r_k)/k\). Also \(\|T_kv\|_P^2=\|v\|_P^2/k\), by telescoping the site weights over \(kj\le n<k(j+1)\). Define
\[
 L=\sum_{k\ge1}P_k T_k=\tfrac12(I+B),\qquad
 B=2\sum_{k\ge2}P_k T_k,\qquad
 \|B\|_{P\to P}\le 2\sum_{k\ge2}\frac{P_k}{\sqrt{k}}\le\frac1{\sqrt2}<1.
\]
The operator series converge in norm. Both \(L\) and \(L^{-1}=2\sum_{j\ge0}(-B)^j\) preserve closed \(V\). Sitewise \(L\mathbf1(n)=\sum_{k\le n}P_k=n/(n+1)=W_n/Z_2\). This proves the equivalence. The next conclusions are mathematical consequences of the displayed dilation argument and the repository's legal-membership criterion:
\[
\begin{aligned}
\mathrm{RH}
&\iff W\in V
 \iff \|u_Q\|_Q^2=\frac{1}{Z_2(Z_2-1)}
 \iff u_Q(n)=\frac{n}{(n+1)(Z_2-1)}\quad(\forall n\ge1)\\
&\iff
 \|P_M^Q J_2\|_Q^2=\frac{3}{4}-\frac{(\log2)^2}{Z_2(Z_2-1)} .
\end{aligned}
\]
The corresponding perpendicular-space criterion is \(\mathrm{RH}\iff V=M\oplus^{\perp_Q}\mathbb R W\), since \(W\in M^{\perp_Q}\) holds at every stage of the argument. For the norm criterion use Pythagoras on \(W=w_V+(W-w_V)\). For the explicit profile, equality of the vectors implies \(W\in V\) because \(u_Q\in V\). For the last equality use \(P_M^Q J_2=J_2-\lambda u_Q\) and \(Q(n\text{ odd})=3/4\). This endpoint uses the *native* projection of the *unnormalized* \(J_2\). The known Pareto projection of the same packet has the distinct endpoint \(\log2-(\log2)^2\). [Legal-membership converse](../RH/CenteredMeanSquarefreeConverse.lean) · [Exact dilation law](../RH/ThresholdHilbertDilation.lean) · [Native parity energies](../RH/PrimeSupportMeasureChange.lean)

The proof also works directly in native \(Q\). On each block,
\(\sum_{n=kj}^{k(j+1)-1}n^{-2}\le 1/(kj^2)\), so \(\|T_k\|_{Q\to Q}\le k^{-1/2}\). In particular, writing \(\rho=2\sum_{k\ge2}P_k/\sqrt{k}<1\), the same inverse gives a quantitative comparison of distances to \(V\):
\[
 \frac{Z_2}2(1-\rho)\operatorname{dist}_Q(\mathbf1,V)
 \le\operatorname{dist}_Q(W,V)
 \le\frac{Z_2}2(1+\rho)\operatorname{dist}_Q(\mathbf1,V).
\]
Indeed \(L\) induces an invertible operator on \(H_Q/V\), with inverse norm at most \(2/(1-\rho)\).

The exact native deficit has an especially simple form. Put \(A_0=Z_2(Z_2-1)\) and \(d=\operatorname{dist}_Q(W,V)\). Since \(A_0-d^2=\|P_V^QW\|_Q^2>0\),
\[
 \left(\frac{3}{4}-\frac{\lambda^2}{A_0}\right)-\|P_M^Q J_2\|_Q^2
 =\frac{\lambda^2 d^2}{A_0(A_0-d^2)} .
\]
Thus an upper bound on the native parity deficit is an upper bound on the defect of the native mean representer in the physical legal space.

## Universal lifting and the physical norm of a section

For the inclusion \(i:M\to V\), the mean \(C:V\to\mathbb R\), the section \(s(a)=au\) and the retraction \(p(v)=v-s(Cv)=P_M^Pv\), the split identities are
\[
 C s=1_{\mathbb R},\quad p i=1_M,\quad C i=0,\quad p s=0,\quad i p+s C=1_V.
\]
For any real topological module \(X\), continuous linear \(f:X\to\mathbb R\), and continuous linear lift \(g:X\to V\) of \(f\), there is a unique \(m:X\to M\) with \(g=i\,m+s\,f\), namely \(m=p\,g\). Conversely each continuous linear \(m\) gives such a lift. On a point of a fiber this gives the exact excess \(\|v\|_P^2=|C(v)|^2\|u\|_P^2+\|p(v)\|_P^2\). [Unique mixed lift](../RH/MixedConductorSplitExact.lean) · [Physical norm of the fiber](../RH/MixedConductorMetricLifting.lean)

In particular \(\|s\|=\|u\|_P\) is the attained minimum over all continuous linear right inverses of the physical mean. Every such \(t\) satisfies
\[
 \|t\|^2=\|u\|_P^2+\|t(1)-u\|_P^2,\qquad
 C(\overline B_V(0,1))=[-1/\|u\|_P,1/\|u\|_P].
\]
The quotient norm of the scalar \(a\) in \(V/M\) is \(|a|\|u\|_P\). The rescaled quotient \(\|u\|_P C\) always has the isometric section \(a\mapsto au/\|u\|_P\). For the original physical mean, existence of a right inverse of norm at most \(B\) is equivalent to \(\|u\|_P\le B\). At budget one it is equivalent to \(u=\mathbf1_H\), to the unit ball lifting the scalar one, to \(\mathrm{dist}_P(\mathbf1_H,V)=0\), and to RH. A verified finite period gives \(\|u\|_P^2<1000/961\). The older equivalence with an explicit natural-approximation premise composes with the unconditional theorem \(\mathrm{RH}\iff\) natural approximation in the newer module. [Metric sections and budgets](../RH/MixedConductorMetricLifting.lean) · [Converse supplying the premise](../RH/CenteredMeanSquarefreeConverse.lean)

For any finite set of distinct right zeros \(\rho\), the Mellin bound on every physical right inverse is \(1\le\|t\|^2\prod_\rho |1-\rho|^2/|\rho|^2\). It includes the individual lower bound \((2\Re\rho-1)\le |1-\rho|^2(\|t\|^2-1)\). Thus each finite product exceeds \(961/1000\), and RH is equivalent to every such product being at least one. This result concerns distinct finite zeros and their Gram constraints. The multiplicity-counted infinite product uses the continuous projection theorem in the separate capacity argument. [Finite Mellin obstruction and unit-budget equivalence](../RH/MixedConductorMetricLifting.lean)

## Signed residual Fekete tests

Put \(r=\mathbf1_H-P_V^P\mathbf1_H\), \(Z=\zeta(2)\), and \(g_j=Z\langle r,(dQ/dP)J_{p_jp_{j+1}}\rangle_P\). For \(U_n=\sup_k\sum_{j=k}^{k+n-1}g_j\), subadditivity and the uniform block error identify \(\inf_{n\ge1}U_n/n=-\|r\|_P^2\). Thus RH is equivalent to arbitrarily large lengths admitting a nonnegative signed block at some starting prime. With \(b(a)=\langle r,(x\bmod a)/x\rangle_P\), distinct primes obey \(Z\langle r,(dQ/dP)J_{pq}\rangle_P=b(pq)-b(p)-b(q)\). For each fixed \(a>1\), \(b(a^k)\to\|r\|_P^2\) and \(b(a^{2k})-2b(a^k)\to-\|r\|_P^2\). Hence RH is equivalent to \(2b(a^k)\le b(a^{2k})\) at arbitrarily large exponents of that one base. Restoring the two singleton terms gives corrected semiprime blocks, with the companion nonpositive-sign criterion and its vanishing-tolerance strengthening. [Signed Fekete and fixed-base doubling](../RH/SemiprimeFekete.lean) · [Corrected semiprime blocks](../RH/SemiprimeBlockRemainders.lean)

## CRT matching, conductor limits, and carry presentations

### What is being glued

For a finite family of equivalence relations \(R_i\) on \(X\), put \(x(R_i\circ R_j)y\) when there exists \(z\) with \(xR_i zR_jy\). Pairwise realizable data have a simultaneous solution on every nonempty finite family exactly when, for all finite nonempty \(F\) and all \(j\notin F\),
\[
 \bigcap_{i\in F}(R_i\circ R_j)
 =\left(\bigcap_{i\in F}R_i\right)\circ R_j .
\]
Solutions form one class of \(\bigcap_iR_i\). Thus the quotient of \(X\) by the common kernel identifies with the matching tuples for the finite family. Replacing binary composition by the relation join requires permutability. In a regular category the intermediate witnesses are generalized points over regular-epimorphic covers. Under local gluing, the comparison from \(X\) to the matching quotient is a regular epimorphism with kernel pair the intersection of the coordinate kernel pairs. A diagonal common kernel makes it an isomorphism. With overlaps representing binary realizability, the matching object is the equalizer of the two maps from the product of the coordinate quotients to the product of the overlaps. A functor preserving the relevant pullbacks and regular epimorphisms transports the local witnesses. The declarations are \(\texttt{hasFiniteCRT_iff_crtGluing}\), \(\texttt{finite_crt_iff_gluing_of_regular}\), \(\texttt{quotient_matching_kernel}\), \(\texttt{exists_overlap_equalizer_quotient}\), and \(\texttt{localSolution_map_internal}\). [Finite CRT](FiniteFamilyCRT.lean) · [Local gluing](LocalFamilyCRT.lean) · [Regular images](RegularCategoryCRT.lean) · [Matching quotient](QuotientMatchingCRT.lean) · [Overlap equalizer](OverlapEqualizerCRT.lean) · [Functoriality](FunctorCRT.lean)

For finite prime support \(S\), the residue ring at \(\prod_{p\in S}p\) is the categorical product of the residue fields. Divisor reduction restricts prime coordinates, and \(\texttt{primeFanIsLimit}\) proves the universal property. Along a nested conductor tower the compatible residues form the limit cone in commutative rings. A cofinal running-LCM tower has vertex \(\widehat{\mathbb Z}\cong\prod_p\mathbb Z_p\), whereas the primorial tower has vertex \(\prod_p\mathbb F_p\). Compatible coordinate ring maps lift uniquely, and continuous coordinates give a continuous lift. For general discrete coordinates, the product-topological closure of the image consists of all data realizable on every finite coordinate set and is homeomorphic to the inverse limit of the finite images. Physical Hilbert reconstruction additionally uses the energy criterion below. [Squarefree product](SquarefreeResidueCRT.lean) · [Limit cones](../RH/ConductorTowerLimit.lean) · [Profinite lifting](../NumberTheory/ProfiniteCRTUniversal.lean) · [Coordinate completion](../Analysis/FiniteCoordinateCompletion.lean)

### Coordinates kept and exchanged

Write \(g_d(n)=\{n/d\}\). At positive period \(L\), partition the nontrivial divisors \(d\mid L\) into prime powers \(I_L\) and mixed conductors \(D_L\) with at least two distinct prime divisors. For \(d\in D_L\) take \(m_{d,p}=p^{v_p(d)}\) and the canonical CRT inverse coefficients \(c_{d,p}\). The raw floor carry satisfies
\[
 C_d=\sum_{p\mid d}c_{d,p}g_{m_{d,p}}-g_d .
\]
Let \(U_L\) be the matrix with column \(d\) equal to this prime-power coefficient vector. For synthesis maps \(S_{\rm atom}\) and \(S_{\rm carry}\), the exact coefficient change is
\[
 \Gamma_L(x,y)=(x+U_Ly,-y),\qquad
 \Gamma_L^2=I,\qquad S_{\rm carry}=S_{\rm atom}\Gamma_L .
\]
It fixes \((x,0)\), sends a pure mixed column \((0,e_d)\) to \((U_Le_d,-e_d)\), and synthesizes the same function in either presentation. The two finite algebraic direct sums share the prime-power summand and exchange the mixed-atom complement for the raw-carry complement. If \(L\mid L'\), zero extension of both coefficient arrays intertwines the two involutions. Synthesis of the corresponding residue-class functions commutes with pullback by reduction. The nontrivial integrated-packet coefficients at a larger period are the old coefficients extended by zero. In particular the raw carry's mixed packet coefficient is \(-1/d\) at each mixed divisor of \(d\), and zero at new conductors. The natural isomorphism \(\texttt{atomCarryRefinementIso}\) acts over physical synthesis. [Category of presentations](AtomCarryPresentation.lean) · [Concrete stages](../RH/FiniteAtomCarryCRT.lean) · [Refinement](../RH/FiniteAtomCarryRefinement.lean) · [Natural isomorphism](../RH/FiniteAtomCarryFunctor.lean) · [Packet coefficients](../RH/CRTCarryRamanujanCoordinates.lean)

At each finite period, quotienting the stage residue span \(V_L\) by its prime-power subspace \(P_L\) gives the split sequence
\[
 0\longrightarrow P_L\longrightarrow V_L
 \longrightarrow V_L/P_L\longrightarrow0 .
\]
For the quotient class represented by \(\sum_d y_dg_d\), the two sections are \(\sum_d y_d g_d\) and \(-\sum_d y_d C_d\). The latter minus the former equals \(-\sum_d y_d\sum_{p\mid d}c_{d,p}g_{m_{d,p}}\in P_L\). This exhibits the changed complement and the sign on the quotient while fixing the represented physical vector under the full coefficient involution. The stagewise algebraic selector onto \(P_L\) is distinct from the closed mixed orthogonal retraction \(P_M|_V\).

### Algebraic presentation, physical closure, and the two carry dictionaries

The universal certificate consists of inputs \(d_i>1\), integral coefficients \(a_i\), an output \(d>1\), and an integer charge \(\ell\), with \(\sum_i a_i/d_i=1/d+\ell\). Its carry is \(\sum_i a_i g_{d_i}-g_d\). In the free space of finitely supported atom and certificate symbols, let \(\mathcal R\) be spanned by the certificate symbol minus that atom expression. Elimination has the atom inclusion as a section. Independence of the residue atoms gives
\[
 0\longrightarrow\mathcal R\longrightarrow
 {\rm Word}\xrightarrow{\ {\rm synthesis}\ }
 {\rm span}_{\rm alg}\{g_d:d>1\}\longrightarrow0 .
\]
Thus \(\mathcal R\) is the entire kernel and \({\rm Word}/\mathcal R\) is the algebraic residue span. Equivalently all nontrivial integrated-packet coordinates of the eliminated word vanish at a common period. Two adjacent certificates of charges zero and one recover \(d g_d\) by their difference, so the span of *all certified carries* already equals the algebraic residue span. [Universal quotient](../RH/UniversalAtomCarryPresentation.lean) · [Ramanujan detection](../RH/UniversalCarryRamanujanSynthesis.lean) · [Adjacent certificates](../RH/AllCertifiedCarrySpan.lean)

For the *raw canonical mixed carries*, \(\overline{\operatorname{span}}\{C_d\}=V\) in both physical metrics. Each prime-power \(g_a\) is approximable using two raw mixed carries whose total absolute coefficient is at most two. The finite prime selector, which fixes \(g_2\) and kills all raw carries, consequently admits no continuous extension in either metric. Its graph closure is \(V\times\overline{\operatorname{span}}\{g_{p^k}\}\). In the other direction, every raw mixed row is indispensable. Its finite-head Möbius functional sends \(C_e\) to \(-\mathbf1_{e=d}\). Deleting \(s\) distinct rows leaves codimension \(s\) in \(V\). [Raw carry closure, graph and row separation](../RH/CanonicalCarryClosure.lean) · [Finite-deletion proof](../RH/CarryEnergyAndResponseCriteria20261126.md)

The *corrected* carry \(K_d\) subtracts the raw carry from its prime-power packet part and multiplies by \(d\). With \(J_e^{\rm mix}=J_e\) at mixed conductors and zero otherwise,
\[
 K_d=\sum_{e\mid d}J_e^{\rm mix},\qquad
 J_d^{\rm mix}=\sum_{e\mid d}\mu(d/e)K_e .
\]
Therefore these two families have identical spans in every divisor-closed finite window and identical closed span \(M\). This gives the common Pareto mixed projection of \(J_2\). Writing \(u=(I-P_M)J_2/\log2\), its normalized parity identity is
\[
 \|P_M(J_2/\log2)\|_P^2+\|u-\mathbf1\|_P^2=(\log2)^{-1}-1.
\]
RH is equivalent to each of the following: the physical constant belongs to the closed raw carry span, the constant is approximable arbitrarily well by finite certified carry words, the Pareto raw-unit Gram cost has supremum one, and the corrected-carry projections of \(J_2\) have energies tending to \(\log2-(\log2)^2\). [Corrected finite spans](../RH/MixedCanonicalCarryCapture.lean) · [Parity equivalences](../RH/MixedParityCarry.lean) · [Raw-unit Gram criterion](../RH/CanonicalCarryGram.lean)

At a physical head of length \(N\), arbitrary real data admit a corrected mixed lift with conductors at most \(2(N+1)^2\). Thus a normalized parity seed admits a correction giving the exact unit head. For any legal mean-one seed \(g\), the existence of finite mixed corrections on depths \(N_j\to\infty\) with unit head and \(\log\|g+m_j\|_P/\log(N_j+1)\to0\) is equivalent to RH. This last criterion allows the finite conductor windows to depend on the depth and the correction. More generally, for prescribed atom moments \(b\), finite Gram costs \(c_F=b_F^\mathsf TG_F^{-1}b_F\) satisfy \(\|x_G-x_F\|^2=c_G-c_F\) for \(F\subseteq G\). A uniform bound along one cofinal subsequence gives the unique representer in the closed atom span with exact error \(\sup_G c_G-c_F\). This applies separately in \(P,Q\). [Finite interpolation](../RH/PhysicalHeadFiniteMinimum.lean) · [Section growth](../RH/PhysicalHeadSectionLog.lean) · [Gram reconstruction](../RH/ConductorReconstructionEnergy.lean)

For a normalized squarefree carry path the finite telescoping sum of signed prime contributions, weighted actual floor carries, and the remaining parent vector equals the initial parent vector. Under \(D_0\ge2\) and the path bound \(p_k\le2D_k\), both series of norms converge and the remaining parent tends to zero in \(Q\) and Pareto. With prime radices and initial weight one the sum of carries projected onto the \(Q\)-orthogonal complement of the prime-atom closure vanishes exactly when the root conductor is prime. [Infinite carry paths](../RH/QInfiniteSquarefreeCarry.lean)

The actual CRT collocation lift \(F_L\) is a separate vector. For \(L\mid L'\), its increment synthesizes the old block and the screened innovation block. After subtracting the predicted energy and the signed linear response the remaining squared error is nonnegative and bounded by the squared collocation radius. Sublogarithmic positive variation of the actual LCM-stage energy on one sampled cofinal schedule suffices for RH. The metric discrepancy \(Z\|F_L\|_Q^2-\|F_L\|_P^2\) has a positive lower limit on even periods, with \(Z=\zeta(2)\). Vanishing discrepancy for uniformly bounded signed cofinal averages applies to centered Möbius residuals. [Nested lifts and metric distinctions](../RH/CanonicalAndReciprocalCertificates20261126.md) · [Complete budgets and moving responses](../RH/CarryEnergyAndResponseCriteria20261126.md)

## Physical quotient descent, exact lifts and the layer isometry

Use physical sites \(1,2,\ldots\), with layers starting at zero. Let \(M\) be the closed mixed space, \(H=L^2(P)\). Put \(K_N=\{m\in M:m(1)=\cdots=m(N)=0\}\), \(K_0=M\), and \(E_n(x)=x(n+1)\). The closed kernels decrease to zero. Represent \(E_n|_{K_n}\) by \(r_n=P_{K_n}(P_{n+1}^{-1}\mathbf1_{\{n+1\}})\). Each \(r_n\ne0\). The direction \(d_n=r_n/\|r_n\|^2\) has \(E_n(d_n)=1\), and \(e_n=r_n/\|r_n\|\) has norm one. One has \(K_n=\mathbb Re_n\oplus^\perp K_{n+1}\). The \(e_n\) form a Hilbert basis of \(M\), giving the surjective isometry \(m\mapsto(\langle e_n,m\rangle_P)_n\) onto \(\ell^2\). Its inverse is norm-convergent signed synthesis and \(\|m\|_P^2=\sum_n|\langle e_n,m\rangle_P|^2\). [Head tower](../RH/ParetoAffineHeadTower.lean) · [Physical layer isometry](../RH/PhysicalHeadLayerIsometry.lean)

For \(N\le L\), restriction \(M/K_L\to M/K_N\) sends \([x]_{K_L}\) to \([x]_{K_N}\). Identify each quotient isometrically with the span of \(e_0,\ldots,e_{N-1}\) by its orthogonal representative. Restriction truncates those coordinates. Consequently any compatible family has a unique sequence of increments \(c_i\). It lifts to an element of \(M\) exactly when \(\sup_N\sum_{i<N}|c_i|^2<\infty\). Its lift is then \(\sum_i c_i e_i\), the strong limit of its minimum-norm representatives. The algebraic inverse limit allows arbitrary sequences of increments. The bounded-energy criterion for Hilbert realization follows directly from the checked isometry.

For \(p=P_M^P J_2\), set \(a_n=\langle e_n,p\rangle_P\) and \(p_N=\sum_{n<N}a_ne_n\). Every representative \(x\in M\) with the same first \(N\) sites has
\[
 \|x\|_P^2=\|p_N\|_P^2+\|x-p_N\|_P^2,\qquad
 \|p-p_N\|_P^2=\|p\|_P^2-\sum_{n<N}a_n^2.
\]
The \(p_N\) represent a compatible family and converge strongly to \(p\). In the mixed conductor Gram–Schmidt basis \(b_q\), let \(d_q(a)\) be its signed digamma row on \(J_a\). Then
\[
 a_n=\sum_q\langle e_n,b_q\rangle_P d_q(2),\qquad
 P_MJ_a=\sum_q d_q(a)b_q,\qquad
 \langle P_MJ_a,P_MJ_b\rangle_P=\sum_q d_q(a)d_q(b).
\]
The scalar sums converge absolutely by Cauchy–Schwarz. The vector sums converge in Pareto norm. At common period \(L\), site \(s=1,\ldots,L\) has weight \((\psi((s+1)/L)-\psi(s/L))/L\); finite weighted packet Grams give the signed triangular rows with strictly positive pivots. For every finite mode set \(F\), Parseval gives the exact normalized boundary contribution and unnormalized projection tail
\[
 \log 2-(\log 2)^2-\sum_{q\in F}d_q(2)^2
 =(\log 2)^2\|u-\mathbf1\|_P^2+\sum_{q\notin F}d_q(2)^2.
\]
The omitted row energy tends to zero, and full saturation is equivalent to RH. [Restrictions, minimum lifts and strong limit](../RH/MixedParityQuotientDescent.lean) · [Signed rows and covariance](../RH/MixedParityDigammaParseval.lean) · [Section energy and tail variance](../RH/ScreenedSectionDescent.lean)

## Affine sections, stage algebras and their relative snake

Let \(\varepsilon(v)=\langle v,\mathbf1\rangle_P\), \(L_N=\{v\in V:v(j)=\varepsilon(v),\,1\le j\le N\}\), and \(h_N\) the minimum-norm point in the mean-one fiber. The split exact row is
\[
 0\longrightarrow K_N\longrightarrow L_N\xrightarrow{\varepsilon}\mathbb R\longrightarrow0,\qquad s_N(a)=a h_N .
\]
Starting at \(h_0=u\), put \(g_n=(1-h_n(n+1))^2/\|r_n\|_P^2\). Then \(h_{n+1}=h_n+(1-h_n(n+1))d_n\) and \(\|h_L\|_P^2-\|h_N\|_P^2=\sum_{N\le i<L}g_i\). Every feasible mean-one lift at \(N\) is \(h_N+k\) with \(k\in K_N\) and has squared excess \(\|k\|_P^2\). The equivalences \(\sum_i g_i<\infty\iff \sup_N\|h_N\|_P^2<\infty\iff u=\mathbf1\iff\mathrm{RH}\) hold even if the budget bound is assumed only along one cofinal subsequence. Off RH the partial costs tend to infinity, although \(\|h_N-\mathbf1\|_P^2/N\to0\) unconditionally. [Sections and kernels](../RH/PhysicalHeadSnakeSections.lean) · [Exact affine costs](../RH/ParetoAffineHeadTower.lean)

As an augmented commutative real algebra \(L_N\cong\mathbb R\ltimes K_N\) with unit \(h_N\). Its product is \(x*_Ny=\varepsilon(x)y+\varepsilon(y)x-\varepsilon(x)\varepsilon(y)h_N\). The augmentation ideal \(K_N\) is two-sided and square-zero in this multiplication. For \(N\le L\), set \(D_{NL}=h_L-h_N\in K_N\cap K_L^\perp\). The ordinary inclusion \(i:L_L\hookrightarrow L_N\) has multiplicative defect
\[
 ix*_Niy-i(x*_L y)=\varepsilon(x)\varepsilon(y)D_{NL}.
\]
The unital algebra embedding \(x\mapsto ix-\varepsilon(x)D_{NL}\) fixes the kernel inclusion and transports the deeper section to the shallower one. These embeddings compose by the displacement cocycle. Comparing the two split mean rows with vertical arrows given by kernel inclusion, centering in the shallower stage, and zero on the scalar gives the relative snake \(a\mapsto a[D_{NL}]\in K_N/K_L\). Its unit image has squared norm \(\sum_{N\le i<L}g_i\). All adjacent ordinary inclusions are multiplicative exactly under RH. The square-zero structure specifies an algebra on these Hilbert subspaces. [Stage algebra](../RH/PhysicalHeadStageAlgebra.lean) · [Algebra transport and RH](../RH/PhysicalHeadStageAlgebraComparison.lean) · [Relative snake and exact energy](../RH/PhysicalHeadAlgebraSnake.lean)

## Prime-support quotients, algebraic colimits and Hausdorff separation

Let \(S_k\subset M\) be the closed span of mixed packets whose conductors have at most \(k\) distinct prime factors. One has \(S_1=0\), \(S_k\subsetneq S_{k+1}\) for \(k\ge1\), and \(\overline{\bigcup_k S_k}=M\). Write \(A_k=S_{k+1}\cap S_k^\perp\). The row \(0\to S_k\to S_{k+1}\to A_k\to0\) splits orthogonally, each \(A_k\) for \(k\ge1\) is infinite dimensional, and \(M=\widehat{\bigoplus}_k A_k\). With \(z=J_2/\log2\), \(m=P_Mz\), and \(b=u-\mathbf1\),
\[
 \|[z-\mathbf1]_{H/S_n}\|_{\rm quot}^2
 =\|b\|_P^2+\|m-P_{S_n}m\|_P^2,\qquad
 \|[z-\mathbf1]_{H/S_n}\|_{\rm quot}^2+\sum_{k<n}\|P_{A_k}m\|_P^2=(\log2)^{-1}-1 .
\]
The residuals \(z-P_{S_n}m\to u\) strongly. The limiting norm of the centered quotient classes \([z-\mathbf1]_{H/S_n}\) is zero exactly under RH. Equivalently, for any fixed \(0<c<1\), arbitrarily late support depths \(n\) admit \(l\ge n\) with the quotient squared norm at \(l\) at most \(c\) times its value at \(n\). The same endpoint is equivalent to \(\exists C\,\forall K\,\exists N\ge K:\operatorname{Var}_P(u(X)\mid X>N)\le C\). [Support layers and Parseval](../RH/MixedConductorPrimeSupport.lean) · [Quotient norms](../RH/PrimeSupportParityQuotient.lean) · [Support contraction](../RH/PrimeSupportParityDescent.lean) · [Tail variance](../RH/ScreenedSectionDescent.lean)

With the split square-zero algebra on \(V\), the \(S_n\) become square-zero ideals \(I_n\subset M\). A quotient acts on \(M\) on both sides through its scalar mean. For \(n\le l\) the surjection \(V/I_n\to V/I_l\) has kernel \(I_l/I_n\). A mixed packet of conductor \(q\) is killed at the first support depth \(\omega(q)\). Put \(I_{\rm alg}=\bigcup_n I_n\). The ordinary algebra colimit is \(V/I_{\rm alg}\), with \(I_{\rm alg}\subsetneq M\) and \(\overline{I_{\rm alg}}=M\). Its comparison to the separated scalar quotient is the exact sequence
\[
 0\to M/I_{\rm alg}\to V/I_{\rm alg}\longrightarrow V/M\cong\mathbb R\to0 .
\]
The nonzero kernel is exactly the closure of zero in the algebraic quotient topology. The stage boundaries factor through the comparison and the scalar boundary. Strict containment of the comparison kernel in the algebraic-boundary kernel is equivalent to vanishing of the boundary and hence RH. On the ambient side \(H/S_n\to H/S_l\); the colimit in Hausdorff topological real modules is \(H/M\). The orientations follow from the denominators: \(K_N\) decreases while \(S_n\) increases. [Algebra transitions and actions](../RH/PrimeSupportAlgebraDescent.lean) · [Algebraic colimit and separation](../RH/AlgebraicSupportColimit.lean) · [Hausdorff universal property](../RH/HausdorffSupportColimit.lean)

The CRT conductor tower has a further inverse limit in commutative rings. An increasing cofinal LCM schedule yields \(\widehat{\mathbb Z}\cong\prod_p\mathbb Z_p\) with bicontinuous CRT coordinates. The primorial tower yields \(\prod_p\mathbb F_p\). The comparison is coordinatewise reduction modulo \(p\), is surjective, and has nonzero kernel. In particular it loses higher prime-power digits. These ring limits classify compatible residues, while the Hilbert-head criterion additionally controls complete energy. [Conductor limits](../RH/ConductorTowerLimit.lean) · [Profinite and primorial completions](../RH/ConductorTowerCompletions.lean)

## The countable product snake and two descriptions of its cokernel

Take the algebraic products of the rows \(0\to K_N\to L_N\to\mathbb R\to0\). On both towers of subspaces use the vertical map \((\Delta x)_N=i_{N,N+1}x_{N+1}-x_N\); on \(\mathbb R^{\mathbb N}\) use the usual successive difference. The scalar kernel consists of constant sequences and the scalar difference is onto. Write \(C_K=\operatorname{coker}\Delta_K\), \(C_L=\operatorname{coker}\Delta_L\), taking the algebraic ranges. The intersection of the \(K_N\) is zero and the intersection of the \(L_N\) is \(V\cap\mathbb R\mathbf1\). The product snake gives
\[
 0\longrightarrow V\cap\mathbb R\mathbf1
 \xrightarrow{\varepsilon}\mathbb R
 \xrightarrow{\delta_\Pi}C_K
 \longrightarrow C_L\longrightarrow 0,\qquad
 \delta_\Pi(a)=a\,[(h_{N+1}-h_N)_N].
\]
Thus the first derived-limit stage cokernel is \(C_L\cong C_K/\mathbb R\delta_\Pi(1)\). The class is zero precisely when the mean-one stage sections can be chosen coherently under ordinary inclusion, equivalently when \(\mathbf1\in V\) and hence RH. The ambient snake embeds into this product snake by an injective map \(Z/M\to C_K\), where \(Z=\mathbf1^\perp\), carrying \(\partial(a)\) to \(\delta_\Pi(a)\). [Product snake and exact cokernel](../RH/PhysicalHeadProductSnake.lean) · [Infinite boundary criteria](../RH/PhysicalHeadInfiniteBoundary.lean) · [Physical readout and injection](../RH/PhysicalHeadSequenceCokernel.lean)

Physical readout identifies \(C_K\cong\mathbb R^{\mathbb N}/\operatorname{readout}(M)\); the connecting element is represented by the physical sequence of \(u-\mathbf1\). Orthogonal layer coordinates identify \(C_K\cong\mathbb R^{\mathbb N}/\ell^2\) and send \(\delta_\Pi(1)\) to the signed carry sequence
\[
 c_n=(1-h_n(n+1))\|d_n\|_P,\qquad c_n^2=g_n=\|\delta_{n,n+1}(1)\|^2.
\]
Both descriptions are algebraic quotient isomorphisms. The criterion is \(\mathrm{RH}\iff(c_n)\in\ell^2\iff\delta_\Pi(1)=0\iff\partial(1)=0\). The Cesàro mean of \(c_n^2\) tends to zero unconditionally. The formal constant layer sequence \((1,1,\ldots)\) survives even in \(C_L\): \((1-tc_n)\notin\ell^2\) for every real \(t\). This is a concrete independent cokernel class. [Boundary coordinates and Parseval](../RH/PhysicalHeadBoundaryCoordinates.lean)

The legal-space Parseval isometry for prime support simultaneously records the scalar component and every mixed layer. For \(v\in V\), with \(m=P_Mv=v-\varepsilon(v)u\),
\[
 v=\varepsilon(v)u+\sum_k P_{A_k}m,\qquad
 \|v\|_P^2=|\varepsilon(v)|^2\|u\|_P^2+\sum_k\|P_{A_k}m\|_P^2.
\]
At each layer every bounded section of \(S_{k+1}\to A_k\) is \(z\mapsto z+Bz\) for a unique bounded \(B:A_k\to S_k\); its squared lift cost is \(\|z\|^2+\|Bz\|^2\). The orthogonal section is the unique isometric section. [Global Parseval isometry](../RH/MixedConductorGlobalParseval.lean) · [Support snakes and all layer sections](../RH/MixedConductorSupportSnake.lean)

A further physical criterion permits growing norms. If \(\kappa_N=\|h_N\|_P\), RH is equivalent to \(\forall\eta>0\,\exists C_\eta\,\exists^\mathrm{cof}N:\kappa_N^2\le C_\eta(N+1)^\eta\). For any fixed legal mean-one seed \(v\), RH is also equivalent to the existence of a schedule \(N_j\to\infty\) and finite mixed corrections \(w_j\), with \(v+w_j\) matching the unit head through \(N_j\) and \(\log\|v+w_j\|_P/\log(N_j+1)\to0\). The explicit quadratic conductor window through \(2(N+1)^2\) achieves arbitrary finite head interpolation. Its unique optimal corrected parity lift has exact Pythagorean excess against every other feasible corrected carry in the window. [Subpower criteria](../RH/PhysicalHeadSectionGrowth.lean) · [Cofinal logarithmic sections](../RH/PhysicalHeadSectionLog.lean) · [Quadratic realization](../RH/PhysicalHeadFiniteMinimum.lean) · [Finite parity optimum](../RH/PhysicalHeadParityMinimum.lean)

## Pareto and \(Q\) realizations of the categorical object

### Two functorial transports and the mean section

At a positive physical site \(n\), put \(P_n=1/[n(n+1)]\), \(Q_n=1/(Zn^2)\), \(Z=\zeta(2)\) locally in this metric section, and introduce three different multipliers
\[
 D_n=1/n,\qquad R_n=1/(n+1),\qquad
 \Gamma_n=Q_n/P_n=(1+D_n)/Z,\qquad \Gamma_n^{-1}=Z(1-R_n).
\]
The site-preserving equivalence \(I:H_Q\to H_P\) sends the physical sequence \(f\) to the same sequence. It preserves the algebraic residue dictionary, constants, carry relations, closures, heads, compatible quotient maps, strong convergence and uniform boundedness. For any real \(x,y\in H_Q\),
\[
 \langle Ix,Iy\rangle_P=Z\langle x,(1-R)y\rangle_Q,\qquad
 \langle x,y\rangle_Q=\langle Ix,\Gamma Iy\rangle_P.
\]
Thus the transported Pareto mean on \(H_Q\) is \(x\mapsto Z\langle x,(1-R)1\rangle_Q\). Its kernel is \(I^{-1}(\ker\varepsilon_P)\), and its mean-one section is \(t\mapsto tI^{-1}u\). In particular, the transported mixed space has zero **Pareto** mean. For any closed \(S\subset H_P\), \(I^{-1}(S^{\perp_P})=\{\Gamma y:y\in(I^{-1}S)^{\perp_Q}\}\), with the right-hand side meaning the image under \(\Gamma\) of the native \(Q\)-orthogonal complement. Consequently the split sequences transport as sequences of bounded linear maps, even when their native metric representatives differ. The square-root-density isometry \(A:H_Q\to H_P\), \(Af(n)=\sqrt{\Gamma_n}\,f(n)\), sends the target \(1\) to \(\sqrt\Gamma\) and sends a denominator \(T\) to \(AT\). It satisfies \(P^P_{AT}A=AP^Q_T\) and preserves quotient norms, distances, defects, orthogonality and Parseval exactly. A \(Q\) computation for a given Pareto target \(v\) under this isometry uses \(A^{-1}v\) and \(A^{-1}S\). [Physical equivalence](../RH/QParetoEquivalence.lean) · [Density identities](../RH/QDensityMetricInverse.lean) · [Isometric conjugacy](../RH/QParetoIsometricTransport.lean) · [Full transported residual](../RH/QFullIsometricTransport.lean)

### Quotient energy, normal equation and Neumann reconstruction

Let \(S\subset H_P\), \(T=I^{-1}S\), with their orthogonal projections available (in particular for closed Hilbert denominators). The map \([v]_S\mapsto[I^{-1}v]_T\) is a bounded linear equivalence. These maps commute with denominator inclusions and induce the natural isomorphism of support quotient diagrams, \(\texttt{physicalSupportTowerIso}\). With \(q=P^Q_Tx\), \(p=P^P_S(Ix)\), and \(w=x-q\), the complete formula is
\[
 \|[Ix]_S\|_P^2+\|p-Iq\|_P^2
 =Z\bigl(\|[x]_T\|_Q^2-\langle w,Rw\rangle_Q\bigr),\qquad
 \tfrac Z2\|[x]_T\|_Q^2\le\|[Ix]_S\|_P^2\le Z\|[x]_T\|_Q^2.
\]
The equality follows by decomposing \(Iw=(Ix-p)+(p-Iq)\) orthogonally in \(P\). Both comparisons follow by minimizing the physical norm inequalities over the same coset. Rescreening a residual in the other metric recovers that metric's own residual in either direction (\(\texttt{physical_layer_roundtrip}\)). The physical Pareto fit \(z=I^{-1}p\) instead satisfies \(P_T^Q(1-R)(x-z)=0\). Therefore, with \(F=P_T^QR\),
\[
 \|F\|\le\tfrac12,\qquad z=\sum_{j\ge0}F^j\,P_T^Q(1-R)x.
\]
After \(m\) terms the tail is bounded by \(2^{1-m}\|P_T^Q(1-R)x\|_Q\), uniformly over all such denominators. Finite moment Gram matrices inherit the positive form comparison. Inverting on an independent dictionary reverses the inequalities: for the same moment vector, \((Z/2)c_P\le c_Q\le Zc_P\). [Physical quotient energy and Neumann series](../RH/QPhysicalQuotientMetric.lean) · [Naturality and support towers](../RH/PrimeSupportMeasureChange.lean) · [Inverse Gram defects](../RH/QParetoInverseMetricDefect.lean) · [Conductor reconstruction](../RH/ConductorReconstructionEnergy.lean)

A centered Neumann iteration gives a sharper uniform rate as a mathematical consequence of the same normal equation. Put \(G=1-R\) and \(\Pi=P_T^Q\). Start from \(z_0=0\) and iterate
\[
 z_{m+1}=z_m+\tfrac43\,\Pi G(x-z_m).
\]
Every iterate lies in \(T\), and the actual Pareto fit \(z\) satisfies \(\Pi G(x-z)=0\). Thus \(z-z_{m+1}=\Pi(1-\tfrac43G)(z-z_m)\). Since \(G_n=n/(n+1)\in[1/2,1)\), the multiplier \(1-\tfrac43G\) has norm \(1/3\). It follows that
\[
 \|z-z_m\|_Q\le 3^{-m}\|z\|_Q .
\]
This is optimal among scalar step sizes uniformly over all closed denominators. For \(T=H_Q\) the exact norm of \(1-\tau G\) is \(\max(|1-\tau/2|,|1-\tau|)\), using site one and the limit of the high sites. Its minimum occurs at \(\tau=4/3\). The repository formalizes the original \(1/2\) Neumann estimate. This \(1/3\) estimate follows from the displayed physical multiplier proof.

### Native support layers, descended parity and minimum head lifts

Write \(T_n=I^{-1}\operatorname{ambientSupport}(n)\), \(T_\infty=I^{-1}M\), and \(L_n=T_{n+1}\cap T_n^{\perp_Q}\). The stages start at zero and their union is dense in \(T_\infty\). Then \(P^Q_{L_n}=P^Q_{T_{n+1}}-P^Q_{T_n}\), and for every \(x\in H_Q\),
\[
 \sum_{k<n}\|P^Q_{L_k}x\|_Q^2+\|[x]_{T_n}\|_Q^2=\|x\|_Q^2,\qquad
 \sum_{k\ge0}\|P^Q_{L_k}x\|_Q^2=\|x\|_Q^2-\|[x]_{T_\infty}\|_Q^2.
\]
The vector series sums to \(P^Q_{T_\infty}x\). If \(g=J_2/\log2\), native \(Q\) Neumann computations for the Pareto support-stage fits give \(I^{-1}g-I^{-1}P^P_{S_n}g\to I^{-1}u\). With \(h=I^{-1}(g-1)=\mathbf1_{\rm odd}/\log2-1\), the descended terminal class is \([I^{-1}(u-1)]_{T_\infty}\). The total native energy of the input packet, \(\|h\|_Q^2\), is \(E_{\rm odd}=\tfrac34((\log2)^{-1}-1)^2+\tfrac14\). Precisely,
\[
 \mathrm{RH}\iff[h]_{T_\infty}=0
 \iff\lim_n\|[h]_{T_n}\|_Q^2=0
 \iff\sum_k\|P^Q_{L_k}h\|_Q^2=E_{\rm odd}.
\]
For unitary-transformed stages and target, the limiting squared quotient norm is exactly the squared Pareto centered-boundary norm. [Support reconstruction, native saturation and weighted Parseval](../RH/PrimeSupportMeasureChange.lean)

There is also a quantitative comparison between the two saturation deficits. Define \(D_Q=E_{\rm odd}-\sum_k\|P^Q_{L_k}h\|_Q^2\) and \(D_P=\log2-(\log2)^2-\|P_M^P J_2\|_P^2\). The quotient comparison at \(M\), the terminal native Parseval identity and the Pareto splitting give
\[
 (\log2)^2\,\tfrac{\zeta(2)}2 D_Q
 \ \le\ D_P\ \le\
 (\log2)^2\zeta(2)\,D_Q .
\]
Indeed \(D_Q=\|[h]_{T_\infty}\|_Q^2\), and \(D_P=(\log2)^2\|[Ih]_M\|_P^2\) because \(u-\mathbf1\) is the minimal Pareto representative. This transfers bounds on the size of the unresolved endpoint as well as its vanishing.

Let \(K_N\) be the Pareto physical head-stage kernel and \(\widehat K_N=I^{-1}K_N\). For the **unnormalized** packet set \(y=I^{-1}P^P_MJ_2\). The transported signed digamma prefixes and native \(Q\) minimum-norm lifts represent \([y]_{\widehat K_N}\) at every \(N\). The classes commute with head restriction, their common representative at infinite depth is unique, and each of the two sequences converges strongly to \(y\). The native minimum is \(y_N=P^Q_{\widehat K_N^{\perp_Q}}y\), giving \(\|y\|_Q^2=\|y_N\|_Q^2+\|y-y_N\|_Q^2\). For the canonical unit patches \(a_N\), form \(\chi_{N,K}=[I^{-1}(a_K-a_N)]_{\widehat K_K}\), \(N\le K\). The relative snake energies satisfy \((Z/2)\|\chi_{N,K}\|_Q^2\le\|\partial_{N,K}(1)\|_P^2\le Z\|\chi_{N,K}\|_Q^2\). The exact energy with both metric correction terms is \(\texttt{qRelative_energy_balance}\). Consequently
\[
 \mathrm{RH}\iff \partial_{\rm product}(1)=0
 \iff \sum_N\|\chi_{N,N+1}\|_Q^2<\infty
 \iff \sum_k\|P^Q_{L_k}h\|_Q^2=E_{\rm odd}.
\]
This summability statement concerns the **differences between successive unit patches**. [Physical head representatives, energy and infinite snake](../RH/PhysicalHeadQuotientMeasureChange.lean)

### Density images, signed tests and complete metric discrepancies

The checked reciprocal-density theorem gives \(\overline{D(I^{-1}M)}=H_Q\) and therefore \(\overline{I^{-1}M+\Gamma I^{-1}M}=H_Q\), with the same physical conclusion in Pareto space. For any closed \(S\supset M\) the projection of \(\Gamma M\) onto \(S^{\perp_P}\) is dense there. For the full legal space, \(\Gamma|_V\) is the sum of its compression to \(V\) and its complementary component. This latter operator is compact because \(D_n\to0\); its range has dense closure in \(V^\perp\). The assertions that \(V=H\), \(1\in V\), \(\Gamma M\subset V\), that all \(\Gamma J_q\) with mixed conductor lie in \(V\), and that \(V\cup\Gamma V=H\) as a **set union** are equivalent to RH. Each tests an additional invariance or membership beyond unconditional density of the linear sum. [Mixed reciprocal density](../RH/MixedReciprocalDensity.lean) · [Density-image graph](../RH/QDensityOperatorDecomposition.lean) · [Full closure](../RH/QDensityClosureTransfer.lean) · [Union and mixed tests](../RH/MixedPacketDensityTests.lean)

For \(x\in M^{\perp_P}\), vanishing of \(\langle x,\Gamma J_q\rangle_P\) for every mixed conductor forces \(x=0\). Taking \(x=u-1\) gives another RH equivalence. For \(r_P=1-P_V^P1\) and any consecutive two-prime packet \(J_{p_jp_{j+1}}\),
\[
 -Z\langle r_P,\Gamma J_{p_jp_{j+1}}\rangle_P\to\|r_P\|_P^2.
\]
RH is equivalent to cofinal nonnegative pairings, to strong convergence of \(P_{V^{\perp_P}}\Gamma J_{p_jp_{j+1}}\) to zero, and on any prescribed subsequence \(j_i\to\infty\) to cofinal pairings at least \(-\epsilon_i/Z\) for any nonnegative \(\epsilon_i\to0\). For the full physical dictionary \(d=P_V^Q1-P_V^P1\), \(r_Q=1-P_V^Q1\), the corresponding repair identity is \(\|d\|_P^2/Z=\langle Rd-f_N,(1-H_N)r_Q\rangle_Q\), for any legal \(f_N\) matching \(Rd\) on the first \(N\) sites. RH is equivalent to cofinally nonnegative signed repair-tail pairings \(\langle f_N,(1-H_N)r_Q\rangle_Q\). [Signed mixed-packet tests](../RH/MixedPacketDensityTests.lean) · [Full displacement](../RH/QFullDisplacement.lean) · [Exact-head repair theorem](../RH/QFullReciprocalRepairCriterion.lean)

The physical discrepancy equals \(Z\|f\|_Q^2-\|If\|_P^2=\sum_{n\ge1}|f(n)|^2/[n^2(n+1)]\). It tends to zero on cofinal signed blocks of centered Möbius residuals with bounded absolute coefficient mass. For the corresponding full Möbius candidates with total coefficient tending to \(c\), it tends to \(c^2(Z-1)\). Uncentered even-period CRT collocation lifts have strictly positive lower limiting discrepancy, including along the LCM tower. The first two transfers are Lean declarations; the explicit CRT lower bound is proved in the cited research note. The complete correction, budget, Schur, signed-block, and growing-head consequences for the corresponding dictionaries are collected with their quantifiers in the two companion proofs. [Signed Gram comparisons](../RH/QCanonicalCofinalGram.lean) · [CRT discrepancy](../RH/QCanonicalCofinalGramResearch20261015.md) · [Canonical and reciprocal certificates](../RH/CanonicalAndReciprocalCertificates20261126.md) · [Fifteen carry and energy criteria](../RH/CarryEnergyAndResponseCriteria20261126.md)

## Coverage of the original categorical development

Import `RiemannResearch.CategoryTheory.All` to use the original declaration names. The replay takes that interface as its sole project import. It resolves each recorded name in its owning module and namespace and rechecks its stored type and body. The chronological groups through `91f07fd` contain 3,000 declaration entries from 168 modules. The physical quotient descent at `e684cf2` brings this to 3,024 entries from 169 modules. The continuation records 153 further entries from seven source revisions and three theorems on the physical parity object, bringing the initial physical replay to 3,180 entries. The native carry extension adds eleven declarations, giving 3,191 entries. These counts include definitions and structure projections as well as theorems. [Public imports](All.lean) · [Chronological replay with owners and names](HistoricalRebuild.lean)

| Construction | Consequence retained in the public interface | Lean source |
|---|---|---|
| Finite weighted quotient | Fiber averaging is surjective. Repetition of the conditional average is orthogonal projection. The discarded coordinate map has image equal to the averaging kernel, with its rank computed exactly. | [Weighted Hilbert quotient](../LinearAlgebra/WeightedQuotientHilbert.lean) · [Defect rank](../LinearAlgebra/WeightedQuotientDefectRank.lean) |
| Abstract and profinite CRT | In a regular category the finite matching object is a quotient under the gluing condition. Compatible profinite coordinates have a unique continuous lift, natural under precomposition. Finite solvability alone can fail to produce an integer satisfying all congruences. | [Regular-category CRT](RegularCategoryCRT.lean) · [Universal lift](../NumberTheory/ProfiniteCRTUniversal.lean) · [Integer obstruction](../NumberTheory/InfiniteCRTObstruction.lean) |
| Matching and energy gluing | The compact matching space is homeomorphic to the quotient by the common kernel. In a Hilbert space, finite systems of weakly closed constraints on one closed ball admit a global solution when all finite intersections on that ball are nonempty. In the conductor system, the stage Gram costs characterize existence of a global representer. | [Matching quotient](../Analysis/CompactMatchingQuotient.lean) · [Weak compactness](../Analysis/WeakCompactConstraints.lean) · [Conductor Gram costs](../RH/ConductorReconstructionEnergy.lean) |
| Finite arithmetic and moving Gram tests | The first-site computation proves strict slack at stage three and strict failure at stage four for its stated budget. The two-stage projected parity Gram has a nonnegative defect tending to zero and a cofinal solve criterion. The late-solve inequalities retain their cost, drift and zero hypotheses. | [Certified site inequalities](../RH/SiteGramStrictStages.lean) · [Two-stage Gram](../RH/DyadicParityTwoStageGram.lean) · [Burnol stage bounds](../RH/CenteredMeanBurnolStageBarrier.lean) |
| Mixed dilation, quotient characters and RH | A ternary digit vector separates packet ten from the dilated packet-six orbit. Mellin evaluations at right-side zeros give boundary retractions and independent normalized characters. The boundary is epic exactly under RH. The normalized legal tail-mean capacity has a limit, and its endpoint value one is equivalent to RH. | [Ternary obstruction](../RH/TernaryMixedOrbitObstruction.lean) · [Mellin descent](../RH/CenteredMeanMellinDescent.lean) · [Boundary characters](../RH/CenteredMeanMellinCharacters.lean) · [Tail-mean capacity](../RH/LegalTailMeanCapacityDilation.lean) |
| Squarefree and two-seed converses | RH is equivalent to the squarefree closure condition, to the natural approximation condition, and to the stated two-seed closure and density conditions. | [Squarefree converse](../RH/CenteredMeanSquarefreeConverse.lean) · [Two-seed converse](../RH/CenteredMeanTwoSeedConverse.lean) |

## Arithmetic consequences and their hypotheses

The finite-dimensional identities determine exactly which arithmetic estimate suffices for a limiting conclusion. In this table a cofinal bound at a fixed site or block allows the chosen stages to depend on that site or block. Where a common constant is required, it cannot depend on the site or block.

| Object | Conclusion and required quantifiers |
| --- | --- |
| Conditional Pareto tail variance | Write \(C_Nu\) for the vector equal to \(u\) on sites \(1,\ldots,N\) and equal to its conditional mean on the tail. The tail mass is \(1/(N+1)\), hence \(\operatorname{Var}_P(u\mid n>N)=(N+1)\|u-C_Nu\|_P^2\). One common finite bound at arbitrarily large \(N\) is equivalent to \(\|u\|_P^2=1\), to signed digamma saturation, and to RH. |
| Exact physical heads | In the finite mixed window with conductors at most \(2(N+1)^2\), the seed \(J_2/\log2\) admits the prescribed unit head. The minimum complete Pareto cost is attained uniquely as a physical section. Every feasible section has squared excess equal to the squared norm of its difference from that minimizer. A cofinal bounded family of legal unit-head, mean-one sections converges weakly to \(\mathbf1\) and implies RH. Arbitrarily large feasible norms are compatible with exact finite interpolation. |
| Raw and corrected carry spaces | The raw dictionary spans \(V\) after closure, the corrected dictionary spans \(M\) after closure. The supremum of the raw unit Gram costs is \(1\) exactly when the corrected projection energies converge to \(\log2-(\log2)^2\). For any prescribed consistent Gram data the bounded-cost criterion supplies a unique representing element in the closed span, with strong convergence of the minimizers. |
| Nested actual cutoffs | The old directions and screened innovations synthesize the exact difference of the canonical lifts. A predictor bounds the actual energy increment through a signed pairing, its energy and its collocation radius. Sublogarithmic total positive variation of the log of one plus canonical energy is sufficient for RH. Complete predictor radii still enter the estimate. |
| Complete signed budgets | With a valid positive correction budget at each transition, the residual energy obeys the finite product estimate and its exponential bound. Divergence of the reciprocal budget sum exhausts the residual. Vanishing normalized signed dyadic excess for a legal coefficient family above one fixed nonnegative baseline suffices for RH. |
| Localized physical responses | The actual logarithmic-head remainder is at most \(\sqrt{\zeta(2)}(6+\log(n+1))\). A cofinal sitewise bound \(C(6+\log(n+1))^m\) with common \(C,m\) suffices. On \(M_0=2^j\), the cofinal bound \(C M_0(6+\log M_0)^{2m}\) for the squared block sum suffices, with stage subsequences allowed to depend on \(j\). At a common stage the short-head transfer has coefficient \((\sqrt C+2\sqrt{\zeta(2)})^2\) and exponent \(2\max(m,1)\), with its explicit nonnegative loss retained. |
| Native \(Q\) responses | For a nested cofinal all-divisor schedule and a growing head, a common absolute Schur bound attained cofinally for each congruent positive pair is equivalent to zero full \(Q\) residual. One may equivalently fix a positive modulus and one sign and test each site against its residue-class anchor. At modulus one the anchor is site \(1\). The unnormalized common bound is an arithmetic input. |
| Weighted heads | For each fixed polylogarithmic weight the actual weighted head energy divided by its tail profile tends to zero uniformly in stage. An absolute bound along cofinal growing heads yields the separate RH criterion. The checked simultaneous head-budget criterion records the precise order of quantifiers. |
| Reciprocal repair and forcing | For a legal exact reciprocal-head repair, convergence to zero of the product of the complete repair-error norm and the omitted residual-tail norm implies RH. The latter factor tends to zero. The finite primorial correction, iterative endpoint and posterior bounds may be intersected by taking their minimum. At \(\alpha=H^{-2}\) the quantitative minimum bound in its stated range is \(12/(\zeta(2)H^2)+(C/H)e^{-c\sqrt{\log H}}\) for \(c\) below the contour endpoint. The cofinal criterion calls for a bound \(O(\alpha)\). |
| Residual sign tests | RH is equivalent to nonnegative residual pairing with the specified consecutive fresh two-prime density probes at arbitrarily late positions. The corrected semiprime block test allows arbitrarily large lengths \(n\) and a starting position \(k=k(n)\) at which the block is nonpositive. The signed Fekete estimates give the corresponding exclusion when the residual is nonzero. |
| Change of metric and damping | The signed metric discrepancy for cofinal averages of canonical lifts tends to zero under a uniform sum-of-absolute-coefficients bound. A uniform energy bound is a separate input. The full weighted Mertens energy and signed off-diagonal integral are finite at damping \(1/2\), and the energy remains finite at larger damping. Finiteness at arbitrarily small positive damping is the stronger RH-route condition. |

[Screened variance and patches](../RH/ScreenedSectionDescent.lean) · [Physical weak limits](../RH/PhysicalHeadWeakLimit.lean) · [Canonical and reciprocal certificates, eight results](../RH/CanonicalAndReciprocalCertificates20261126.md) · [Carry, energy and response criteria, fifteen results](../RH/CarryEnergyAndResponseCriteria20261126.md)

### Analytic equivalents reached from the categorical interface

The repository also proves a seven-way equivalence. Together with RH it contains six tests. The finite Mellin product is at least one for every injectively listed finite family of right zeros \((\Re s>1/2,\ s\ne1)\). The residue pairing at conductor \(2\) detects every Cauchy–Mellin generator with \(0<\delta<1/2\) and arbitrary real frequency. The full horizontal second energy equals zero. Uniform Selberg density holds at an unbounded set of slopes. The rational Taylor disks satisfy the radius-\(1/2\) criterion. The cofinal sharp polynomial upper criterion holds. Any one of these propositions is equivalent to any condition in the physical parity theorem by composition through RH. A limit of a normalized finite-height energy has different quantifiers from vanishing of the full horizontal second energy. [Analytic equivalence and exact definitions](../RH/CenteredMeanRHCriteria.lean)

### Rescaled legal tail capacity and the continuous zero product

For \(m=K+1\) let \(S_K^{\rm leg}=\{v\in V:v(1)=\cdots=v(K)=0\}\) and \(t_K(n)=\mathbf1_{\{n>K\}}\). Write \(C_K=m\|P_{S_K^{\rm leg}}t_K\|_P^2\), \(C_*=\sup_K C_K\). A paper-level identification recovers the analytic multiplicities by passing to all rescaled head kernels. The kernel-checked finite distinct-zero estimates and the capacity limit are given separately in the repository. [Finite distinct-zero obstruction](../RH/LegalTailMeanCapacityZeroProduct.lean) · [Dilation and capacity limit](../RH/LegalTailMeanCapacityDilation.lean)

Extend a sequence to a step function on \(y\ge1\), constant on each \([n,n+1)\). Integration against \(dy/y^2\) gives its Pareto norm squared. Finite legal residue sums have the form \(f(y)=\sum_{k\ge1}a_k\{y/k\}\) with \(\sum_k a_k/k=0\). Indeed the step representative of \(n\mapsto\{n/k\}\) is \(\{y/k\}-k^{-1}\{y\}\). Equivalently set the bookkeeping coefficient \(a_1=-\sum_{k\ge2}a_k/k\). This representation also vanishes on \(0\le y<1\). For a zero head, \(f\) vanishes on \(0\le y<m\). Its jump at integer \(j\) is \(-\sum_{k\mid j}a_k\). Induction on \(1\le j<m\) therefore kills every \(a_j\) with \(j<m\). [Physical residue dictionary](../RH/MobiusCoefficientStabilization.lean)

Finite legal sums with zero head are dense in \(S_K^{\rm leg}\). In fact, choose a finite legal lift of each basis vector of the image of the finite head restriction on the finite sums. The resulting right inverse is continuous on this finite-dimensional image. Subtracting its value on the head of a finite approximant restores a zero head at a norm cost tending to zero. After \(y=mx\) the closure of the scaled zero-head sums in \(L^2([1,\infty),dx/x^2)\) is therefore exactly
\[
 W_m=\overline{\operatorname{span}}\{F_{m/k}: k\ge m\},\qquad
 F_\theta(x)=\{\theta x\}-\theta\{x\}.
\]
For the forward inclusion use the coefficient relation to subtract the \(\{x\}\) term. For the reverse inclusion the two-term legal sum \(\{y/k\}-(m/k)\{y/m\}\) has zero head. The norm-preserving scaling is \(f\mapsto m^{-1/2}f(mx)\), and it sends \(t_K\) to \(m^{-1/2}\mathbf1\). This proves \(C_K=\|P_{W_m}\mathbf1\|^2\).

If \(m\mid m'\), then \(W_m\subset W_{m'}\). Every rational \(0<\theta<1\) occurs as \(m/k\) at a factorial stage. As \(\theta_j\to\theta\), the corresponding fractional parts converge for almost every \(x\) and are bounded, so \(F_{\theta_j}\to F_\theta\) in the finite measure \(dx/x^2\). After \(t=1/x\), the closed factorial union is precisely Burnol's continuous Nyman space. The real and complex projection norms agree because the dictionary and target are real and taking real parts contracts the approximation error. Orthogonal projection convergence and his Theorem 1.2 now give
\[
 C_*=\prod_{\Re\rho>1/2}
       \left|\frac{1-\rho}{\rho}\right|^{2m_\rho},
 \qquad \mathrm{RH}\iff C_*=1 ,
\]
where the product runs over distinct right zeros and \(m_\rho\) is analytic multiplicity. Both signs of the ordinate are included. The square is forced by the definition of capacity as squared norm. [Burnol, Theorem 1.2](https://arxiv.org/pdf/math/9910055)

The verified height \(T=3\cdot10^{12}\) gives a stronger bound than \(4(1+\log T)/T\). Indeed \(1-|1-1/\rho|^2=(2\Re\rho-1)/|\rho|^2\le|\Im\rho|^{-2}\). Bound the product defect by the sum of the individual defects with multiplicity. Conjugation doubles the positive-height right zeros. Reflection \(\rho\mapsto1-\bar\rho\) matches each such occurrence with a distinct left occurrence at the same height. All these heights exceed \(T\). Hence \(1-C_*\le\int_{(T,\infty)}t^{-2}\,dN(t)\), where \(N(t)\) counts **all** positive-ordinate zeros up to and including \(t\). In the explicit zero-count formula write \(N(t)=\tfrac{t}{2\pi}\log(t/(2\pi e))+R(t)\). The published bound implies \(|R(t)|\le\log t\) throughout \(t\ge T\). Integration by parts, including the term \(-R(T)/T^2\) at the lower endpoint, yields
\[
 0\le 1-C_*\le
 \frac{\log(T/(2\pi))+1}{2\pi T}
 +\frac{2\log T+1/2}{T^2}
 <1.480\cdot10^{-12}.
\]
Here the error bound uses \(2\int_T^\infty t^{-3}\log t\,dt=(\log T+1/2)/T^2\). The estimate bounds the gap above the verified height. [Platt and Trudgian, verified zeros](https://arxiv.org/abs/2004.09765) · [Hasanalizade, Shen and Wong, Corollary 1.2](https://arxiv.org/abs/2107.06506)

### The remaining endpoint

With \(\lambda=\log2\) and \(p=P_M^P J_2\), Parseval and the orthogonal split give
\[
\lambda-\lambda^2-\|p\|_P^2
=\lambda^2(\|u\|_P^2-1)
=\lambda^2\|u-\mathbf1\|_P^2
=\lambda^2\|\partial(1)\|^2.
\]
The four expressions are the same nonnegative obstruction. The finite quotient representatives, signed digamma rows and native-\(Q\) reconstructions converge under the hypotheses proved above. An unconditional proof that the displayed quantity vanishes would prove RH.
