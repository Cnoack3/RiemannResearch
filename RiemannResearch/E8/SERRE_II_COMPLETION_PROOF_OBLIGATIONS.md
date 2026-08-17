# Split E8 Serre II: completion proof and Lean obligations

## Status

This document gives a complete account of what remains along the manuscript's
toral/subsystem-sieve route. It is **not** a completed proof of split-E8
Serre II. The exact terminal reduction is now checked by Lean, but one
genuinely new theorem remains: simultaneous E8-gauge compatibility for the
admissible toral cocycles attached to the 31 certified perfect Weyl lifts.

No primary source located through 10 August 2026 proves this assertion over
every characteristic-zero field of cohomological dimension at most two.
Nguyen still states the general result as Serre's conjecture
([arXiv:2603.08061](https://arxiv.org/abs/2603.08061)). Gille, Izquierdo, and
Lucchini Arteche prove Serre II for the special class of complete discretely
valued fields of dimension two
([arXiv:2501.01403](https://arxiv.org/abs/2501.01403)).

The Lean endpoint is
RiemannResearch.AlgebraicGeometry.SerreII.serreII_of_nonE8_and_certifiedSurvivorCommonGauges.
Its commonGauge argument is deliberately visible; it is the missing theorem,
not an implementation detail.

## 1. Source correction: the full-Weyl packet

Totaro's Section 8 table gives the following rows:

| Subsystem | Table row | Index |
|---|---:|---:|
| D8 | H4 | 135 |
| A2 x E6 | H10 | 1120 |
| (A2)^4 | H14 | 11200 |
| (A4)^2 | H15 | 12096 |

Thus the degree packet in PDF Theorem 5.16 is

\[
D_8,\qquad (A_2)^4,\qquad (A_4)^2
\]

with degrees \(135,11200,12096\). The prior Lean relabeling of degree 11200 as
A2E6 was incorrect and has been reversed. The relevant primary source is
Burt Totaro, "Splitting fields for E8-torsors," Duke Math. J. 121 (2004),
Section 8, printed page 21
([author PDF](https://math.ucla.edu/~totaro/papers/public_html/e8.pdf);
[DOI](https://doi.org/10.1215/S0012-7094-04-12132-3)).

Wolfram Language independently returned

\[
\gcd(135,11200,12096)=1,
\qquad
-1417\cdot135+16\cdot11200+12096=1,
\]

and the common orbit total

\[
5160960\cdot135
=62208\cdot11200
=57600\cdot12096
=696729600.
\]

Lean, rather than Wolfram, kernel-checks these identities in
E8.SubgroupSieve.

## 2. The one genuinely new theorem

Put

\[
W=W(E_8),\qquad W^+=\ker(\det),\qquad
Q=W^+/\{\pm1\}\simeq\Omega_8^+(2).
\]

Let \(P\le Q\) be one of the 31 certified perfect subsystem-free projective
classes and let \(\widetilde P\le W^+\) be its full central lift. For every
selected root-subsystem stabilizer \(S\le Q\) and double-coset representative
\(g\), set

\[
H_{S,g}=P\cap gSg^{-1},\qquad
\widetilde H_{S,g}
=\widetilde P\cap\pi^{-1}(H_{S,g}).
\]

The missing assertion must be restricted to the admissible E8 locus.

### Common-gauge theorem CG(P)

Let \(F\) be characteristic zero with \(\operatorname{cd}(F)\le2\). Suppose:

1. \(E/F\) is finite Galois with group \(\widetilde P\);
2. \(T\subset E_{8,F}\) is a maximal torus split by \(E\), with the certified
   \(\widetilde P\)-action on the E8 root lattice;
3. \(z\in Z^1(\widetilde P,T(E))\) represents a toral presentation of the
   E8-class under consideration;
4. for every \((S,g)\), an element \(u_{S,g}\in E_8(E)\) gauges the restriction
   of \(z\) on \(\widetilde H_{S,g}\).

Then

\[
\bigcap_{S,g}
  E_8(E^{\widetilde H_{S,g}})\,u_{S,g}\ne\varnothing.
\tag{CG(P)}
\]

Equivalently, there is one \(u\in E_8(E)\) that gauges \(z\) on every
\(\widetilde H_{S,g}\). Since those subgroups generate \(\widetilde P\), the
same \(u\) gauges \(z\) globally.

The admissibility clauses are essential. The A11 countermodel in the project
shows that separate local gauges on generating subgroups do not imply a common
gauge for an arbitrary coefficient group and arbitrary nonabelian cocycle.

### Finite packet and the residual torus step (14 August 2026)

The exact GAP/TomLib/SLA calculation in
Certificates/O8_PLUS_2_SURVIVOR_PACKET_ORBITS_CERTIFICATE.md now recovers all
64 integral E8-lattice generators and reduced reflection words. It also proves
two distinct finite facts for every one of the 31 rows:

1. the stabilizers in the 135-point D8 action generate the projective
   survivor, hence their full inverse images generate its central lift;
2. after restricting the corrected D8, (A2)^4, (A4)^2 packet, the combined
   local-subgroup indices have gcd one.

Lean's h1_eq_zero_of_gcd_one_restrictions and
isCoboundary_of_subgroup_filtration_gcd_one_h1 therefore close the residual
additive H1 step: if one simultaneous field-valued gauge puts the cocycle in
a single Galois-stable Borel, the torus quotient class is killed by
restriction--corestriction and Bezout; the unipotent radical is then the
terminal filtration step.

This does not construct the simultaneous Borel reduction. A finite Weyl cell
has a field-valued torus lifting defect, so E8.2 must additionally supply
universal Laurent/Chevalley correction formulas, a principal-open cover with
sections, or a torsor under a group with universally trivial H1. Pure Weyl
reachability and mod-2 Tits defects do not suffice.

## 3. Finite completion theorem

**Theorem.** If CG(P) holds for all 31 certified perfect subsystem-free
projective classes, and the published toral-lifting and restriction-kernel
inputs are available with their stated scope, then split-E8 Serre II holds
over every characteristic-zero field of cohomological dimension at most two.

**Proof.**

1. Use toral lifting to represent the given class \(\xi\in H^1(k,E_8)\) by a
   class in \(H^1(k,T)\) for a maximal torus \(T\).

2. Pass to the extension \(k^+/k\) of degree at most two cut out by the
   determinant of the Weyl action. Gille's cyclic degree-two kernel theorem
   reflects neutrality from \(k^+\) to \(k\).

3. Let \(J\le Q\) be the projective monodromy over \(k^+\). If \(J\) preserves
   a proper root subsystem, descend the corresponding semisimple subgroup.
   Gille's non-almost-abelian criterion then neutralizes the E8 class.

4. Otherwise \(J\) is among the 303 subsystem-free certificate rows. The
   committed GAP/TomLib certificate divides these into 150 solvable rows and
   153 nonsolvable rows.

5. For a solvable row, descend neutrality through a composition series using
   the cyclic degree \(2,3,5\) restriction-kernel theorem.

6. For a nonsolvable row, let \(P=J^{(\infty)}\). The certificate compresses
   the 153 rows to 31 perfect-core rows and records the corresponding full
   nonsplit lifts. The quotient \(J/P\) is handled by the same solvable
   descent. It remains to neutralize the restricted class for
   \(\widetilde P\).

7. Every subsystem-orbit field separately neutralizes that restriction by
   the proper-subsystem theorem, so all local gauges in CG(P) exist.

8. The orbit degrees have gcd one. Hence their projective stabilizers generate
   \(P\), and their full inverse images generate \(\widetilde P\). This is the
   corrected content of Theorem 6.30.

9. Apply CG(P). The common gauge is global, so the class over the perfect-core
   fixed field is neutral.

10. Reflect neutrality through the solvable quotient and then through
    \(k^+/k\). Therefore \(\xi=1\).

This proof uses neither Conjecture 6.33 nor a nonexistent additive
corestriction on nonabelian \(H^1(-,E_8)\).

## 4. Binary 2.A5 case

For each of the four smallest perfect rows, the projective core is \(A_5\) and
the actual lift is \(2.A_5\). Let \(\widetilde H\) and \(\widetilde K\) be the
index-five and index-six subgroups used in the manuscript, and write

\[
L_5=E^{\widetilde H},\qquad
L_6=E^{\widetilde K}.
\]

Separate solvable descent gives gauges \(g_5,g_6\). Their transition is

\[
\delta=g_5g_6^{-1}.
\]

Lean proves the exact abstract equivalence

\[
\xi_F=1
\quad\Longleftrightarrow\quad
\delta\in E_8(L_5)E_8(L_6)
\]

once the concrete field-valued presentation is supplied. Therefore the
indispensable binary theorem is:

\[
\boxed{\text{Every admissible binary-icosahedral transition factors as }
       \delta\in E_8(L_5)E_8(L_6).}
\tag{BICF}
\]

The remaining binary proof obligations are:

1. identify each of the four TomLib rows with its actual \(A_5\le Q\), full
   \(2.A_5\) lift, and degree-five \((D_4)^2\) and degree-six \((A_4)^2\)
   subsystem orbits;
2. compute the \(D_4^2\) diagram action orbit by orbit;
3. handle inner diagram-action orbits with the classical nontrialitarian
   theorem;
4. for an actual \(C_3\) diagram image, pass to its orbit-specific cyclic
   cubic extension and prove only the required toral-source restriction-kernel
   centrality;
5. combine the corrected triality information with the oriented transporter
   constraint to prove BICF.

The Lean interface `BinaryD4OrbitProvider` now mirrors obligations 1--4
without circular pointwise choices: one fixed central geometry must serve all
four binary rows, while each realization carries a certified degree-five
orbit and an explicit inner/cyclic-cubic branch. The finite histogram proves
only existence of the orbit index. It does not construct the geometry, torsor
reduction, diagram action, zero-obstruction lift, or cubic correction, and it
does not imply BICF.

Printed Proposition 6.17 is false in its uniform form: at least one certified
degree-five orbit has a nonidentity order-three stabilizer acting inside the
inner \(W(D_4)\times W(D_4)\) image. Research Target 8.2 must therefore be
orbitwise. Even a corrected Target 8.2 does not finish the proof; BICF remains
the required factorization theorem.

The false ambient statement
\(E_8(M)=E_8(L_5)E_8(L_6)\) must not be used. Only admissible toral
transitions are candidates for factorization.

## 5. Full-Weyl case

The three source-correct subsystem fields have degrees

\[
135,\qquad11200,\qquad12096
\]

for \(D_8,(A_2)^4,(A_4)^2\), respectively. Their signed cycle has degree one
and kills additive transfer-compatible invariants. It does not produce a
rational point or a common gauge.

A sharp full-Weyl common-gauge target uses the 135 conjugate D8 stabilizers.
Let \(H_i\) be their full inverse images, \(u_i\) the local gauges, and \(i_0\)
an anchor. The missing assertion is

\[
\boxed{
\exists c_0\in E_8(E)\ \forall i,\quad
u_i u_{i_0}^{-1}c_0\in E_8(E)^{H_i}.
}
\tag{FWCG}
\]

The Lean theorem
NonabelianCocycle.isCoboundary_iff_exists_anchoredFixedGaugeCorrection proves
that FWCG is equivalent to global coboundary status. It does not construct
\(c_0\). The theorem
NonabelianCocycle.exists_anchoredFixedGaugeCorrection_iff_iInter_fixedPointRightCoset_nonempty
now proves the literal equivalence between FWCG and nonemptiness of
\(\bigcap_i E_8(E)^{H_i}u_i\), while
NonabelianCocycle.isCoboundary_iff_iInter_fixedPointRightCoset_nonempty
identifies both with global coboundary status. Neither theorem proves that
these equivalent conditions hold.

One may instead prove CG(P) using the complete subsystem-orbit family. Neither
the three degree computations, Sylow neutralizations, nor generation of
\(\Omega_8^+(2)\) proves FWCG.

## 6. The other 26 perfect rows

After the four binary rows and the one full-Weyl row, 26 perfect rows remain.
For each one, a rigorous completion package must contain:

1. a concrete subgroup embedding \(P\le Q\) and its full lift
   \(\widetilde P\le W^+\);
2. a kernel-checked match from the committed numerical row to that E8 action;
3. the selected subsystem intersections and fixed fields;
4. descent of the appropriate proper semisimple subsystem groups;
5. local neutrality and explicit local gauges;
6. the admissible toral transporter incidence;
7. CG(P).

Items 1--6 are certificate-to-geometry and cited-theorem formalization. Item 7
is new E8-specific mathematics. A smaller generating cover may simplify a
row, but the complete eight-subsystem family is already sufficient for the
generation step.

## 7. Lean infrastructure required for a literal final theorem

A literal theorem with only field hypotheses still requires:

1. an intrinsic characteristic-zero, perfect, cohomological-dimension-at-most-
   two field predicate;
2. a concrete split E8 Chevalley Hopf algebra and group scheme;
3. its maximal tori, root subgroups, subsystem groups, normalizers, and Weyl
   identification;
4. effective fpqc torsor descent and comparison with the project's global
   Cech \(H^1\);
5. finite-Galois representatives and neutral-class reflection;
6. formal toral lifting;
7. formal versions of Gille's cyclic and proper-subsystem theorems;
8. the certificate-to-E8-geometry bridge for all 31 rows;
9. an admissible-toral-cocycle predicate preventing CG(P) from being applied
   to arbitrary coefficient groups;
10. CG(P) for all 31 cases.

The new Lean structure E8SurvivorReductionData exposes items 1--8 through its
induction, classify, and reduction fields. The terminal theorem takes
commonGauge separately, exposing items 9--10 rather than hiding them in a
structure or axiom.

The wonderful compactification, Chow motives, EVIII, and Conjecture 6.33 are
not needed for this minimal toral-sieve route.

## 8. Noncircularity gates

Any claimed proof must pass all of these checks.

1. Separate local gauges give \(\forall i\,\exists u_i\); the missing statement
   is \(\exists u\,\forall i\). These quantifiers cannot be exchanged.

2. Corrected Theorem 6.30 proves generation and

   \[
   \xi=1\iff\bigcap_iE_8(L_i)u_i\ne\varnothing.
   \]

   It does not prove that intersection nonempty.

3. The diagonal instance of Conjecture 6.33 is exactly the desired neutrality
   rewritten. Lean proves this as diagonalKernelNorm_iff_neutral.

4. Proposition 6.35 makes the universal E8 form of Conjecture 6.33 equivalent
   to split-E8 Serre II. It is not an independent lemma.

5. Neutrality of the E8 image of a torus class does not imply that the torus
   class itself is zero.

6. Gcd-one degrees imply generation, index one, and additive annihilation.
   They do not imply a rational point or a common gauge.

7. A discrete cocycle theorem does not become a theorem about fpqc E8 torsors
   without the comparison and scalar-extension bridge.

8. The final Lean theorem must contain no premise equivalent to all E8 classes
   being neutral. The present commonGauge premise is intentionally still
   present because it has not been proved.

## 9. Primary references and their scope

- V. Chernousov, "The kernel of the Rost invariant, Serre's Conjecture II and
  the Hasse principle for quasi-split groups," Math. Ann. 326 (2003),
  [DOI](https://doi.org/10.1007/s00208-003-0417-x). The manuscript cites
  Theorem 3.1 for toral lifting.

- P. Gille, "Cohomologie galoisienne des groupes quasi-deployes sur des corps
  de dimension cohomologique at most 2," Compos. Math. 125 (2001),
  [DOI](https://doi.org/10.1023/A:1002473132282). Theorem 11 is the cyclic
  degree \(2,3,5\) restriction-kernel input.

- P. Gille, "Groupes algebriques semi-simples en dimension cohomologique at
  most 2," LNM 2238 (2019),
  [DOI](https://doi.org/10.1007/978-3-030-17272-5), with the
  [26 May 2026 errata](https://math.univ-lyon1.fr/~gille/prenotes/errata.pdf).
  Corollaries 9.3.6 and 9.3.7 supply the proper-subsystem and diagonalizable-
  subgroup inputs with their stated hypotheses.

- E. Bayer-Fluckiger and R. Parimala, "Galois cohomology of the classical
  groups over fields of cohomological dimension at most 2," Invent. Math. 122
  (1995), [DOI](https://doi.org/10.1007/BF01231443). Its type-D result excludes
  triality and therefore cannot replace the orbitwise binary analysis.

- B. Totaro, "Splitting fields for E8-torsors," Duke Math. J. 121 (2004),
  [author PDF](https://math.ucla.edu/~totaro/papers/public_html/e8.pdf).
  Section 8 supplies the Weyl/subsystem table, not common-gauge compatibility.

- P. Gille and T.-Y. Lee, "Oriented embedding functors of tori as homogeneous
  spaces," [arXiv:2307.16475](https://arxiv.org/abs/2307.16475). This is
  relevant to formalizing oriented transporter geometry; it does not prove
  CG(P).

- D. Izquierdo and G. Lucchini Arteche, "Transfer principles for Galois
  cohomology and Serre's conjecture II,"
  [arXiv:2308.00903](https://arxiv.org/abs/2308.00903). It proves transfer and
  characteristic-reduction results, not the missing E8 theorem.

- N. Q. Thang, "Corestriction Principle in non-abelian Galois cohomology,"
  [arXiv:math/9801157](https://arxiv.org/abs/math/9801157). The kernel theorem
  used there is for local or global characteristic-zero fields, not arbitrary
  fields of cohomological dimension at most two.

- M. Borovoi, Z. Reichstein, and P. Gille, "The power operation in the Galois
  cohomology of a reductive group over a number field,"
  [arXiv:2403.07659](https://arxiv.org/abs/2403.07659). The paper explicitly
  rules out such a functorial operation over arbitrary fields.

## 10. Verification gate

A completed proof should be accepted only after:

- no sorry, admit, project-local axiom, unsafe, or external execution hook;
- the final theorem has only the intended intrinsic field/group hypotheses;
- minimal-hypothesis analysis finds no neutrality-equivalent premise;
- the kernel axiom report contains only standard Lean foundations;
- all 31 certificate-to-geometry maps are checked;
- all imported published results are formalized with their actual hypotheses;
- the full project and reverse dependents compile.

At present, Lean verifies the finite arithmetic, 31-row count, abstract
subsystem induction, common-gauge equivalences, binary double-coset criterion,
corrected Theorem 6.30, and the terminal conditional assembly. It does not
verify BICF, FWCG, or CG(P). Those are the remaining mathematical closure
theorems.
