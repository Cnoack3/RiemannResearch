# A11 Burnside-gluing certificate

This certificate reproduces the finite computation used in PDF Proposition
6.26, before the field-theoretic realization in Corollary 6.28.

## Scope and result

The script constructs an explicit permutation copy of
`SL(2,5) ≃ 2.A5` (GAP `IdGroup [120,5]`) and its unique conjugacy
classes of subgroups of orders 12, 20, and 24.  Write `U12` for the
order-12 subgroup, `K = U20 ≃ 2.D10`, and
`H = U24 ≃ 2.A4`.

In the transitive-orbit bases ordered by subgroup order, it computes the
restriction matrices from the additive Burnside group of `G` to those
of `H` and `K`.  Both matrices kill

```text
[0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 1],
```

where the columns are ordered by stabilizer orders

```text
[1, 2, 3, 4, 5, 6, 8, 10, 12, 20, 24, 120].
```

Thus the checked vector is exactly

```text
[G/U12] + [G/G] - [G/U20] - [G/U24].
```

The combined restriction matrix has rational rank 10.  The script then
constructs the two 11-point actions

```text
X = G/U12 ⊔ G/G,          Y = G/U20 ⊔ G/U24.
```

Their global orbit-degree packets are `[10,1]` and `[6,5]`, so they
are not isomorphic as `G`-sets.  The restrictions to `H` and `K`
have simultaneous conjugators in `S11`.  For each restriction the
centralizer of the source image contains an odd permutation; multiplying
when necessary produces the explicit even conjugators printed below.
Both action images have order 60, lie in `A11`, their joint image is all
of `A11`, and no global simultaneous conjugator exists.

## Lean boundary

The accompanying Lean module checks the two integer kernel equations, the
complete printed zero-based permutations, permutation validity and parity,
the odd-centralizer correction equations, and both even simultaneous
conjugacies.  Generic Lean theorems then turn any pair of homomorphisms
with these local conjugacies and no global conjugacy into a nonneutral
difference class whose two restrictions are neutral.

The following identifications remain external certificate inputs:

- GAP's explicit permutation group is the intended `2.A5`;
- its order-24 and order-20 subgroup classes are the manuscript's
  `2.A4` and `2.D10` gauge groups;
- the printed permutation lists are the coset actions described above;
- the global orbit packets and GAP's failed conjugator search establish
  nonisomorphism of those externally identified actions.

Lean does not reconstruct the full GAP group enumeration or prove the
field-theoretic realization in Corollary 6.28.  In particular, Riemann
existence, `cd(C(t,y)) = 2`, descent to a finite étale group scheme, and
the comparison with field-valued nonabelian H¹ remain outside the current
formalization.  This is a coefficient-free countermodel, not an E8
counterexample.

## Mathematica availability

The requested Mathematica route was unavailable in the execution image.
`wolframscript`, `WolframKernel`, `math`, and `Mathematica` were
absent from `PATH`; there was no Wolfram version or license to invoke.
The finite computation therefore uses the available reproducible GAP
installation.

## Provenance

- GAP version: 4.16.0
- GAP tarball SHA-256:
  `aaa296b32a5d7bf25fd80f241d23ec1f58b74e991ae730fafe40e54eb3af6e7e`
- TomLib version: 1.2.11
- TomLib `gap/tmstdrd.tom` SHA-256:
  `f65f486646348fb98f36ecaf48615e08ca21e79e004087918bb78c7e51603963`
- CTblLib version: 1.3.11
- CTblLib `data/ctbalter.tbl` SHA-256:
  `b59b10aa51ebcc13eeb3cb054388781e2fb539bab3ac1a73d8c93ea2c97d800f`
- Script SHA-256:
  `baaf47becc395ae0a104679de172db96043be3b0769960f7c9c90f9c76975d2a`
- Raw-output SHA-256:
  `db00da2e15d9df2f62ef059026e884cbda11f81375f432ac22f7960564322edf`

The random sources are reset at the top of the script.  Two independent
fresh invocations produced byte-for-byte identical output.

Run command:

```sh
./gap-4.16.0/gap -q -x 4096 -T -r -A \
  --packagedirs "$PWD/release-packages" a11_burnside_gluing.g
```

## Script

```gap
if LoadPackage("tomlib") <> true then
    Error("TomLib failed to load");
fi;
if LoadPackage("ctbllib") <> true then
    Error("CTblLib failed to load");
fi;

Reset(GlobalMersenneTwister, 1);
Reset(GlobalRandomSource, 1);

tom := TableOfMarks("2.A5");
ct := CharacterTable("2.A5");
expectedOrders := [1, 2, 3, 4, 5, 6, 8, 10, 12, 20, 24, 120];
Assert(0, OrdersTom(tom) = expectedOrders);
Assert(0, Size(ct) = 120);

G := Image(IsomorphismPermGroup(SL(2, 5)));
Assert(0, Size(G) = 120);
Assert(0, IdGroup(G) = [120, 5]);
Assert(0, IsPerfectGroup(G));

classesG := ConjugacyClassesSubgroups(G);
Assert(0, List(classesG, c -> Size(Representative(c))) = expectedOrders);

RepresentativeOfOrder := function(m)
    local candidates;
    candidates := Filtered(classesG,
        c -> Size(Representative(c)) = m);
    Assert(0, Length(candidates) = 1);
    return Representative(candidates[1]);
end;

U12 := RepresentativeOfOrder(12);
U20 := RepresentativeOfOrder(20);
U24 := RepresentativeOfOrder(24);
H := U24;
K := U20;

RestrictionVector := function(L, classesL, U)
    local result, orbit, stabilizer, position;
    result := List(classesL, x -> 0);
    for orbit in Orbits(L, RightCosets(G, U), OnRight) do
        stabilizer := Stabilizer(L, orbit[1], OnRight);
        position := PositionProperty(classesL,
            c -> IsConjugate(L, Representative(c), stabilizer));
        Assert(0, position <> fail);
        result[position] := result[position] + 1;
    od;
    return result;
end;

RestrictionMatrix := function(L)
    local classesL, columns;
    classesL := ConjugacyClassesSubgroups(L);
    columns := List(classesG,
        c -> RestrictionVector(L, classesL, Representative(c)));
    return rec(
        orders := List(classesL, c -> Size(Representative(c))),
        matrix := TransposedMat(columns)
    );
end;

restrictionH := RestrictionMatrix(H);
restrictionK := RestrictionMatrix(K);
combinedRestriction := Concatenation(
    restrictionH.matrix, restrictionK.matrix);
burnsideKernelVector := [0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 1];

Assert(0, restrictionH.orders = [1, 2, 3, 4, 6, 8, 24]);
Assert(0, restrictionK.orders = [1, 2, 4, 5, 10, 20]);
Assert(0, RankMat(combinedRestriction) = 10);
Assert(0, restrictionH.matrix * burnsideKernelVector =
    List(restrictionH.orders, x -> 0));
Assert(0, restrictionK.matrix * burnsideKernelVector =
    List(restrictionK.orders, x -> 0));

action12 := ActionHomomorphism(G, RightCosets(G, U12), OnRight);
action20 := ActionHomomorphism(G, RightCosets(G, U20), OnRight);
action24 := ActionHomomorphism(G, RightCosets(G, U24), OnRight);

DisjointPermutation := function(p, q, firstDegree, secondDegree)
    return PermList(Concatenation(
        List([1 .. firstDegree], i -> i ^ p),
        List([1 .. secondDegree], i -> firstDegree + i ^ q)
    ));
end;

S11 := SymmetricGroup(11);
A11 := AlternatingGroup(11);
generatorsG := GeneratorsOfGroup(G);
rhoX := GroupHomomorphismByImages(G, S11, generatorsG,
    List(generatorsG, g -> Image(action12, g)));
rhoY := GroupHomomorphismByImages(G, S11, generatorsG,
    List(generatorsG, g -> DisjointPermutation(
        Image(action20, g), Image(action24, g), 6, 5)));

Assert(0, IsGroupHomomorphism(rhoX));
Assert(0, IsGroupHomomorphism(rhoY));
Assert(0, List(Orbits(Image(rhoX), [1 .. 11]), Length) = [10, 1]);
Assert(0, List(Orbits(Image(rhoY), [1 .. 11]), Length) = [6, 5]);
Assert(0, Size(Image(rhoX)) = 60);
Assert(0, Size(Image(rhoY)) = 60);
Assert(0, IsSubgroup(A11, Image(rhoX)));
Assert(0, IsSubgroup(A11, Image(rhoY)));
jointImage := Group(Concatenation(
    GeneratorsOfGroup(Image(rhoX)), GeneratorsOfGroup(Image(rhoY))));
Assert(0, jointImage = A11);

EvenLocalConjugatorData := function(L)
    local source, target, initial, centralizer, oddCentralizer,
          evenConjugator;
    source := List(GeneratorsOfGroup(L), g -> Image(rhoX, g));
    target := List(GeneratorsOfGroup(L), g -> Image(rhoY, g));
    initial := RepresentativeAction(S11, source, target, OnTuples);
    Assert(0, initial <> fail);
    centralizer := Centralizer(S11, Image(rhoX, L));
    oddCentralizer := First(Elements(centralizer), c -> SignPerm(c) = -1);
    Assert(0, oddCentralizer <> fail);
    if SignPerm(initial) = -1 then
        evenConjugator := oddCentralizer * initial;
    else
        evenConjugator := initial;
    fi;
    Assert(0, SignPerm(evenConjugator) = 1);
    Assert(0, List(source, p -> p ^ evenConjugator) = target);
    return rec(
        source := source,
        target := target,
        initial := initial,
        oddCentralizer := oddCentralizer,
        evenConjugator := evenConjugator
    );
end;

localH := EvenLocalConjugatorData(H);
localK := EvenLocalConjugatorData(K);
Assert(0, RepresentativeAction(S11,
    List(generatorsG, g -> Image(rhoX, g)),
    List(generatorsG, g -> Image(rhoY, g)), OnTuples) = fail);

ZeroBasedImages := p -> List([1 .. 11], i -> i ^ p - 1);
ZeroBasedList := list -> List(list, ZeroBasedImages);

Print("GAP_VERSION=", GAPInfo.Version, "\n");
Print("TOMLIB_VERSION=", GAPInfo.PackagesLoaded.tomlib[2], "\n");
Print("CTBLLIB_VERSION=", GAPInfo.PackagesLoaded.ctbllib[2], "\n");
Print("TOM_IDENTIFIER=", Identifier(tom), "\n");
Print("CHARACTER_TABLE_IDENTIFIER=", Identifier(ct), "\n");
Print("G_ID=", IdGroup(G), "|PERFECT=", IsPerfectGroup(G), "\n");
Print("G_SUBGROUP_ORDERS=", expectedOrders, "\n");
Print("H_SUBGROUP_ORDERS=", restrictionH.orders, "\n");
Print("H_RESTRICTION_MATRIX=", restrictionH.matrix, "\n");
Print("K_SUBGROUP_ORDERS=", restrictionK.orders, "\n");
Print("K_RESTRICTION_MATRIX=", restrictionK.matrix, "\n");
Print("COMBINED_RESTRICTION_RANK=", RankMat(combinedRestriction), "\n");
Print("BURNSIDE_KERNEL_VECTOR=", burnsideKernelVector, "\n");
Print("H_KERNEL_IMAGE=", restrictionH.matrix * burnsideKernelVector, "\n");
Print("K_KERNEL_IMAGE=", restrictionK.matrix * burnsideKernelVector, "\n");
Print("X_ORBIT_DEGREES=", List(Orbits(Image(rhoX), [1 .. 11]), Length),
    "|Y_ORBIT_DEGREES=", List(Orbits(Image(rhoY), [1 .. 11]), Length), "\n");
Print("X_IMAGE_ORDER=", Size(Image(rhoX)),
    "|Y_IMAGE_ORDER=", Size(Image(rhoY)),
    "|JOINT_IMAGE_ORDER=", Size(jointImage), "\n");
Print("RHO_X_GENERATORS=", ZeroBasedList(
    List(generatorsG, g -> Image(rhoX, g))), "\n");
Print("RHO_Y_GENERATORS=", ZeroBasedList(
    List(generatorsG, g -> Image(rhoY, g))), "\n");
Print("H_X_GENERATORS=", ZeroBasedList(localH.source), "\n");
Print("H_Y_GENERATORS=", ZeroBasedList(localH.target), "\n");
Print("H_INITIAL_CONJUGATOR=", ZeroBasedImages(localH.initial),
    "|INVERSE=", ZeroBasedImages(localH.initial ^ -1),
    "|SIGN=", SignPerm(localH.initial), "\n");
Print("H_ODD_CENTRALIZER=", ZeroBasedImages(localH.oddCentralizer),
    "|INVERSE=", ZeroBasedImages(localH.oddCentralizer ^ -1),
    "|SIGN=", SignPerm(localH.oddCentralizer), "\n");
Print("H_EVEN_CONJUGATOR=", ZeroBasedImages(localH.evenConjugator),
    "|INVERSE=", ZeroBasedImages(localH.evenConjugator ^ -1), "\n");
Print("K_X_GENERATORS=", ZeroBasedList(localK.source), "\n");
Print("K_Y_GENERATORS=", ZeroBasedList(localK.target), "\n");
Print("K_INITIAL_CONJUGATOR=", ZeroBasedImages(localK.initial),
    "|INVERSE=", ZeroBasedImages(localK.initial ^ -1),
    "|SIGN=", SignPerm(localK.initial), "\n");
Print("K_ODD_CENTRALIZER=", ZeroBasedImages(localK.oddCentralizer),
    "|INVERSE=", ZeroBasedImages(localK.oddCentralizer ^ -1),
    "|SIGN=", SignPerm(localK.oddCentralizer), "\n");
Print("K_EVEN_CONJUGATOR=", ZeroBasedImages(localK.evenConjugator),
    "|INVERSE=", ZeroBasedImages(localK.evenConjugator ^ -1), "\n");
Print("GLOBAL_CONJUGATOR=fail\n");
Print("CERTIFICATE_OK=true\n");
QUIT;
```

## Raw output

```text
GAP_VERSION=4.16.0
TOMLIB_VERSION=1.2.11
CTBLLIB_VERSION=1.3.11
TOM_IDENTIFIER=2.A5
CHARACTER_TABLE_IDENTIFIER=2.A5
G_ID=[ 120, 5 ]|PERFECT=true
G_SUBGROUP_ORDERS=[ 1, 2, 3, 4, 5, 6, 8, 10, 12, 20, 24, 120 ]
H_SUBGROUP_ORDERS=[ 1, 2, 3, 4, 6, 8, 24 ]
H_RESTRICTION_MATRIX=[ [ 5, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 5, 0, 2, 0, 1, 1, 1, 0, 0, 0, 0 ], [ 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0 ], [ 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0 ], [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1 ] ]
K_SUBGROUP_ORDERS=[ 1, 2, 4, 5, 10, 20 ]
K_RESTRICTION_MATRIX=[ [ 6, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 6, 0, 2, 0, 2, 0, 1, 0, 0, 0, 0 ], [ 0, 0, 0, 2, 0, 0, 3, 0, 2, 1, 1, 0 ], [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1 ] ]
COMBINED_RESTRICTION_RANK=10
BURNSIDE_KERNEL_VECTOR=[ 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 1 ]
H_KERNEL_IMAGE=[ 0, 0, 0, 0, 0, 0, 0 ]
K_KERNEL_IMAGE=[ 0, 0, 0, 0, 0, 0 ]
X_ORBIT_DEGREES=[ 10, 1 ]|Y_ORBIT_DEGREES=[ 6, 5 ]
X_IMAGE_ORDER=60|Y_IMAGE_ORDER=60|JOINT_IMAGE_ORDER=19958400
RHO_X_GENERATORS=[ [ 2, 1, 0, 4, 3, 5, 7, 6, 9, 8, 10 ], [ 5, 2, 7, 0, 6, 3, 9, 1, 8, 4, 10 ] ]
RHO_Y_GENERATORS=[ [ 4, 5, 2, 3, 0, 1, 7, 6, 9, 8, 10 ], [ 1, 5, 4, 2, 3, 0, 8, 7, 10, 9, 6 ] ]
H_X_GENERATORS=[ [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ], [ 9, 1, 7, 5, 3, 4, 0, 8, 2, 6, 10 ], [ 1, 6, 4, 8, 5, 2, 0, 3, 7, 9, 10 ] ]
H_Y_GENERATORS=[ [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ], [ 3, 2, 5, 4, 0, 1, 6, 7, 10, 8, 9 ], [ 2, 5, 3, 0, 1, 4, 6, 10, 8, 7, 9 ] ]
H_INITIAL_CONJUGATOR=[ 9, 7, 2, 4, 3, 0, 10, 5, 1, 8, 6 ]|INVERSE=[ 5, 8, 2, 4, 3, 7, 10, 1, 9, 0, 6 ]|SIGN=-1
H_ODD_CENTRALIZER=[ 0, 1, 3, 2, 8, 7, 6, 5, 4, 9, 10 ]|INVERSE=[ 0, 1, 3, 2, 8, 7, 6, 5, 4, 9, 10 ]|SIGN=-1
H_EVEN_CONJUGATOR=[ 9, 7, 4, 2, 1, 5, 10, 0, 3, 8, 6 ]|INVERSE=[ 7, 4, 3, 8, 2, 5, 10, 1, 9, 0, 6 ]
K_X_GENERATORS=[ [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ], [ 3, 4, 2, 0, 1, 8, 6, 9, 5, 7, 10 ], [ 9, 4, 7, 0, 8, 1, 5, 3, 6, 2, 10 ] ]
K_Y_GENERATORS=[ [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ], [ 0, 2, 1, 3, 5, 4, 10, 8, 7, 9, 6 ], [ 0, 2, 4, 5, 3, 1, 8, 10, 7, 6, 9 ] ]
K_INITIAL_CONJUGATOR=[ 7, 1, 9, 8, 2, 5, 3, 6, 4, 10, 0 ]|INVERSE=[ 10, 1, 4, 6, 8, 5, 7, 0, 3, 2, 9 ]|SIGN=1
K_ODD_CENTRALIZER=[ 4, 3, 6, 1, 0, 7, 2, 5, 9, 8, 10 ]|INVERSE=[ 4, 3, 6, 1, 0, 7, 2, 5, 9, 8, 10 ]|SIGN=-1
K_EVEN_CONJUGATOR=[ 7, 1, 9, 8, 2, 5, 3, 6, 4, 10, 0 ]|INVERSE=[ 10, 1, 4, 6, 8, 5, 7, 0, 3, 2, 9 ]
GLOBAL_CONJUGATOR=fail
CERTIFICATE_OK=true
```
