# O8+(2) Weyl-cover and marker certificate

This file restores the joint computation behind the assertions that all 31
surviving perfect cores have nonsplit central Weyl lifts and are marker-free.

## Trust boundary

Lean checks the consistency of the 31 embedded rows: cardinalities, doubled
orders, equality of lift and derived orders, and zero fixed dimensions. The
GAP/SLA computation constructs the Weyl cover and mod-two module and associates
those rows with TomLib classes. The central-extension and all-moduli arguments
below explain why the finite tests imply nonsplitting and marker-freeness. The
generic deductions are formalized in `GroupTheory/CentralExtension.lean` and
`GroupTheory/ModTwoFixedReduction.lean`. GAP still supplies the concrete
perfect lifts, their nontrivial central kernels and negation actions, and their
mod-two fixed-space calculations.

## Shared-identification requirement

Triality permutes both the TomLib subgroup classes and the three nonzero
double-cover classes of $O_8^+(2)$. Separate randomized isomorphisms can
therefore produce a false mismatch. The script below constructs one
TomLib-to-$W(E_8)^+/\{\pm 1\}$ identification and uses it for both the
central-cover and $E_8/2E_8$ tests. It searches the three triality
configurations and asserts that exactly one aligned configuration has all 31
properties. The configuration number is intentionally not treated as
canonical.

## Finite criteria

For a perfect subgroup $K \leq Q$, let $E$ be its full inverse image in the
central double cover. The commutator subgroup of $E$ surjects onto $K$.
Because the central kernel has order two, either $|E'|=|K|$, giving a
complement and a split extension, or $E'=E$, giving a nonsplit extension.
Thus the certificate tests the single equality $|E'|=|E|=2|K|$.

Every full inverse image contains the central element $-1$. Invariants in
$L/nL$ vanish automatically for odd $n$. For powers of two, reduction
modulo two and induction show that vanishing of $(L/2L)^E$ implies vanishing
for every $2^a$, and the Chinese remainder theorem handles general $n$.
Thus the certificate needs only the dimension of the mod-two fixed space.

The result is 31/31 nonsplit lifts and 31/31 zero-dimensional mod-two fixed
spaces. The smallest projective core has order 60, while its actual nonsplit
lift has order 120.

## Reproduction

```sh
./gap-4.16.0/gap -q -x 4096 -T -r -A \
  --packagedirs "$PWD/release-packages" o8p2_cover_marker_certificate.g
```

A fresh rerun exits successfully and ends with:

```text
ALIGNED_31_NONSPLIT=true
ALIGNED_31_E8_MOD2_FIXED_FREE=true
CERTIFICATE_OK=true
```

| Artifact | SHA-256 |
|---|---|
| Joint GAP script | `1bede8edc10972ee8d779404f00dfcddc17230eb425e88acabf2b28ab0880b3c` |
| Joint raw output | `83a6be3185cc381a5092c4cd16d014e352708e53386894763d0c34b5c0b78ec4` |
| Joint JSON | `c6442f59682e40041a0a6c1017704489a5dd5e459210bd701ae11909f988645a` |
| Type-validation script | `fe7be1be1922551de01c5efe10295a3c344c3e93626e429e7ff47a5566576761` |
| Type-validation output | `5d22768a2a50f332d79f6cb079563fa53feb7ac4f85b51f055e7bb00967e6005` |

The joint JSON also records GAP 4.16.0, TomLib 1.2.11 at commit
`c460dc4f6bbfbf805b0f0f2dd1d0841bbd4e9c2c`, SLA 1.6.2, and the exact
source-data hashes.

## Joint GAP script

```gap
#############################################################################
##
##  Joint certificate for the Weyl double cover of Omega_8^+(2).
##
##  IMPORTANT: the cover and the E8/2 action must use the same identification
##  with TomLib.  The three possible identifications are permuted by triality.
##  Here TomLib's subgroup straight-line programs are evaluated on one pair of
##  standard generators of the quotient, so no second isomorphism is involved.
##
#############################################################################

if LoadPackage("tomlib") <> true then
    Error("TomLib failed to load");
fi;
if LoadPackage("sla") <> true then
    Error("SLA failed to load");
fi;

SizeScreen([1000, 1000]);
LogTo("o8p2_cover_marker_certificate.raw.txt");

tom := TableOfMarks("O8+(2)");
orders := OrdersTom(tom);
subs := SubsTom(tom);
derivedTom := DerivedSubgroupsTomUnique(tom);
slps := StraightLineProgramsTom(tom);
maximal := MaximalSubgroupsTom(tom)[1];

configurations := [
    rec(
        seven := [11170, 11165, 11164, 11156, 11074, 11155, 11077],
        a1e8 := 11152
    ),
    rec(
        seven := [11169, 11166, 11163, 11158, 11076, 11155, 11077],
        a1e8 := 11153
    ),
    rec(
        seven := [11168, 11167, 11162, 11157, 11075, 11155, 11077],
        a1e8 := 11154
    )
];

PerfectCoreClass := function(class)
    while derivedTom[class] <> class do
        class := derivedTom[class];
    od;
    return class;
end;

SurvivorsForConfiguration := function(cfg)
    local forbidden, class;
    forbidden := [];
    for class in Concatenation(cfg.seven, [cfg.a1e8]) do
        UniteSet(forbidden, subs[class]);
    od;
    return Difference([1 .. Length(subs)], forbidden);
end;

CoreClassesForConfiguration := function(cfg)
    return Difference(
        Set(List(SurvivorsForConfiguration(cfg), PerfectCoreClass)), [1]);
end;

EvaluateTomGenerators := function(class, generators)
    local program;
    program := slps[class];
    if IsStraightLineProgram(program) then
        return ResultOfStraightLineProgram(program, generators);
    fi;
    return List(program,
        entry -> ResultOfStraightLineProgram(entry, generators));
end;

MatrixModTwo := function(matrix)
    local one;
    one := One(GF(2));
    return List(matrix, row ->
        List(row, entry -> (Int(entry) mod 2) * one));
end;

FixedDimensionModTwo := function(generators, actionHom)
    local matrices, identity, constraints;
    matrices := List(generators, generator ->
        MatrixModTwo(PreImagesRepresentative(actionHom, generator)));
    identity := IdentityMat(8, GF(2));
    constraints := List([1 .. 8], row ->
        Concatenation(List(matrices,
            matrix -> matrix[row] - identity[row])));
    return 8 - RankMat(constraints);
end;

Print("GAP_VERSION=", GAPInfo.Version, "\n");
Print("TOMLIB_VERSION=", GAPInfo.PackagesLoaded.tomlib[2], "\n");
Print("TOMLIB_DIR=", GAPInfo.PackagesLoaded.tomlib[1], "\n");
Print("SLA_VERSION=", GAPInfo.PackagesLoaded.sla[2], "\n");
Print("TOMLIB_GIT_COMMIT=c460dc4f6bbfbf805b0f0f2dd1d0841bbd4e9c2c\n");
Print("TOMLIB_TMO8P2_SHA256=eaa82cedb5b805047de0f859f7b17e3dc6c09f7878d4d97e604fa69054c905ed\n");
Print("GAP_TARBALL_SHA256=aaa296b32a5d7bf25fd80f241d23ec1f58b74e991ae730fafe40e54eb3af6e7e\n");
Print("TABLE=", Identifier(tom), "\n");
Print("SUBGROUP_CLASSES=", Length(subs), "\n");

#############################################################################
## Construct W(E8)^+, its centre, and the quotient in one representation.
#############################################################################

lieAlgebra := SimpleLieAlgebra("E", 8, Rationals);
rootSystem := RootSystem(lieAlgebra);
cartanMatrix := CartanMatrix(rootSystem);
weylMatrixGroup := WeylGroup(rootSystem);
roots := Orbit(weylMatrixGroup, cartanMatrix[1], OnRight);
actionHom := ActionHomomorphism(weylMatrixGroup, roots, OnRight);
weylGroup := Image(actionHom);
evenWeylGroup := DerivedSubgroup(weylGroup);
centralKernel := Centre(evenWeylGroup);
centralInvolution := First(Elements(centralKernel),
    element -> element <> One(evenWeylGroup));
quotientMap := NaturalHomomorphismByNormalSubgroup(
    evenWeylGroup, centralKernel);
orthogonalGroup := Image(quotientMap);

Assert(0, Size(weylGroup) = 696729600);
Assert(0, Size(evenWeylGroup) = 348364800);
Assert(0, IsPerfectGroup(evenWeylGroup));
Assert(0, Size(centralKernel) = 2);
Assert(0, Size(orthogonalGroup) = 174182400);
Assert(0, IsPerfectGroup(orthogonalGroup));
Assert(0, PreImagesRepresentative(actionHom, centralInvolution)
    = -IdentityMat(8, Rationals));

standardInfo := StandardGeneratorsInfo(tom)[1];
standardQuotientGenerators := StandardGeneratorsOfGroup(
    standardInfo, orthogonalGroup);
Assert(0, standardQuotientGenerators <> fail);
Assert(0, IsStandardGeneratorsOfGroup(
    standardInfo, orthogonalGroup, standardQuotientGenerators));
standardLiftGenerators := List(standardQuotientGenerators,
    generator -> PreImagesRepresentative(quotientMap, generator));
Assert(0, Size(Group(standardLiftGenerators)) = Size(evenWeylGroup));

Print("WEYL_ORDER=", Size(weylGroup), "\n");
Print("EVEN_WEYL_ORDER=", Size(evenWeylGroup), "\n");
Print("CENTRE_ORDER=", Size(centralKernel), "\n");
Print("QUOTIENT_ORDER=", Size(orthogonalGroup), "\n");
Print("STANDARD_QUOTIENT_GENERATOR_ORDERS=",
    List(standardQuotientGenerators, Order), "\n");
Print("STANDARD_LIFT_GENERATOR_ORDERS=",
    List(standardLiftGenerators, Order), "\n");

#############################################################################
## Independently check the two nonzero orbits in the E8/2 module.
#############################################################################

quotientMatrixGenerators := List(standardLiftGenerators, generator ->
    MatrixModTwo(PreImagesRepresentative(actionHom, generator)));
nonzeroVectors := Difference(
    Tuples(Elements(GF(2)), 8),
    [List([1 .. 8], index -> Zero(GF(2)))]);
nonzeroVectorOrbits := Orbits(
    Group(quotientMatrixGenerators), nonzeroVectors, OnRight);
nonzeroVectorOrbitSizes := SortedList(List(nonzeroVectorOrbits, Length));
Assert(0, nonzeroVectorOrbitSizes = [120, 135]);
Print("E8_MOD2_NONZERO_VECTOR_ORBIT_SIZES=",
    nonzeroVectorOrbitSizes, "\n");

#############################################################################
## Test every perfect core occurring in any triality configuration.
##
## For a perfect projective core K and its full inverse image E, the central
## extension splits iff |E'|=|K|; it is nonsplit iff E'=E, equivalently
## |E'|=2|K|.  The latter is what the `nonsplit` field records.
#############################################################################

allCoreClasses := [];
for cfg in configurations do
    UniteSet(allCoreClasses, CoreClassesForConfiguration(cfg));
od;

results := [];
for class in allCoreClasses do
    liftGenerators := EvaluateTomGenerators(
        class, standardLiftGenerators);
    pullback := Group(Concatenation(
        liftGenerators, [centralInvolution]));
    pullbackOrder := Size(pullback);
    derivedOrder := Size(DerivedSubgroup(pullback));
    fixedDimension := FixedDimensionModTwo(liftGenerators, actionHom);

    Assert(0, Size(Image(quotientMap, pullback)) = orders[class]);
    Assert(0, pullbackOrder = 2 * orders[class]);
    Assert(0, derivedOrder in [orders[class], pullbackOrder]);

    Add(results, rec(
        class := class,
        order := orders[class],
        pullbackOrder := pullbackOrder,
        derivedOrder := derivedOrder,
        nonsplit := derivedOrder = pullbackOrder,
        fixedDimension := fixedDimension
    ));

    Print("CORE|", class,
        "|order=", orders[class],
        "|pullback=", pullbackOrder,
        "|derived=", derivedOrder,
        "|nonsplit=", derivedOrder = pullbackOrder,
        "|fixed_mod2_dim=", fixedDimension, "\n");
od;

ResultForClass := function(class)
    return First(results, result -> result.class = class);
end;

ConfigurationReport := function(number, cfg)
    local coreClasses, cfgResults, nonsplitClasses, markerFreeClasses,
          bothClasses;
    coreClasses := CoreClassesForConfiguration(cfg);
    cfgResults := List(coreClasses, ResultForClass);
    nonsplitClasses := List(Filtered(cfgResults,
        result -> result.nonsplit), result -> result.class);
    markerFreeClasses := List(Filtered(cfgResults,
        result -> result.fixedDimension = 0), result -> result.class);
    bothClasses := Intersection(nonsplitClasses, markerFreeClasses);
    Print("CONFIG|", number,
        "|cores=", coreClasses,
        "|nonsplit_count=", Length(nonsplitClasses),
        "|marker_free_count=", Length(markerFreeClasses),
        "|both_count=", Length(bothClasses), "\n");
    return rec(
        coreClasses := coreClasses,
        nonsplitClasses := nonsplitClasses,
        markerFreeClasses := markerFreeClasses,
        bothClasses := bothClasses
    );
end;

configurationResults := List([1 .. Length(configurations)], number ->
    ConfigurationReport(number, configurations[number]));
alignedConfigurations := Filtered([1 .. Length(configurations)], number ->
    Length(configurationResults[number].bothClasses) = 31);
Assert(0, Length(alignedConfigurations) = 1);
alignedConfiguration := alignedConfigurations[1];

#############################################################################
## Identify the root-aligned index-120 and index-135 point stabilizers.
#############################################################################

index120Candidates := Filtered(maximal, class ->
    orders[class] = Size(orthogonalGroup) / 120);
index135Candidates := Filtered(maximal, class ->
    orders[class] = Size(orthogonalGroup) / 135);
index120MarkerClasses := Filtered(index120Candidates, class ->
    ResultForClass(class).fixedDimension = 1);
index135MarkerClasses := Filtered(index135Candidates, class ->
    ResultForClass(class).fixedDimension = 1);

Assert(0, Length(index120Candidates) = 3);
Assert(0, Length(index135Candidates) = 3);
Assert(0, Length(index120MarkerClasses) = 1);
Assert(0, Length(index135MarkerClasses) = 1);
Assert(0, index120MarkerClasses[1]
    in configurations[alignedConfiguration].seven);
Assert(0, index135MarkerClasses[1]
    in configurations[alignedConfiguration].seven);
Assert(0, not ResultForClass(index120MarkerClasses[1]).nonsplit);

Print("ALIGNED_CONFIGURATION=", alignedConfiguration, "\n");
Print("INDEX_120_CANDIDATES=", index120Candidates, "\n");
Print("ROOT_ORBIT_STABILIZER_CLASS=", index120MarkerClasses[1], "\n");
Print("ROOT_ORBIT_STABILIZER_PULLBACK_STATUS=split\n");
Print("INDEX_135_CANDIDATES=", index135Candidates, "\n");
Print("SINGULAR_ORBIT_STABILIZER_CLASS=", index135MarkerClasses[1], "\n");
Print("ALIGNED_31_CLASSES=",
    configurationResults[alignedConfiguration].bothClasses, "\n");
Print("ALIGNED_31_NONSPLIT=true\n");
Print("ALIGNED_31_E8_MOD2_FIXED_FREE=true\n");
Print("CERTIFICATE_OK=true\n");

LogTo();
QUIT;
```

## Joint raw output

```text
GAP_VERSION=4.16.0
TOMLIB_VERSION=1.2.11
TOMLIB_DIR=/workspace/scratch/fde9de896a87/gap_reconstruct/release-packages/tomlib/
SLA_VERSION=1.6.2
TOMLIB_GIT_COMMIT=c460dc4f6bbfbf805b0f0f2dd1d0841bbd4e9c2c
TOMLIB_TMO8P2_SHA256=eaa82cedb5b805047de0f859f7b17e3dc6c09f7878d4d97e604fa69054c905ed
GAP_TARBALL_SHA256=aaa296b32a5d7bf25fd80f241d23ec1f58b74e991ae730fafe40e54eb3af6e7e
TABLE=O8+(2)
SUBGROUP_CLASSES=11171
WEYL_ORDER=696729600
EVEN_WEYL_ORDER=348364800
CENTRE_ORDER=2
QUOTIENT_ORDER=174182400
STANDARD_QUOTIENT_GENERATOR_ORDERS=[ 2, 5 ]
STANDARD_LIFT_GENERATOR_ORDERS=[ 2, 5 ]
E8_MOD2_NONZERO_VECTOR_ORBIT_SIZES=[ 120, 135 ]
CORE|4012|order=60|pullback=120|derived=60|nonsplit=false|fixed_mod2_dim=4
CORE|4013|order=60|pullback=120|derived=120|nonsplit=true|fixed_mod2_dim=0
CORE|4014|order=60|pullback=120|derived=120|nonsplit=true|fixed_mod2_dim=0
CORE|4015|order=60|pullback=120|derived=120|nonsplit=true|fixed_mod2_dim=0
CORE|4016|order=60|pullback=120|derived=60|nonsplit=false|fixed_mod2_dim=3
CORE|4017|order=60|pullback=120|derived=120|nonsplit=true|fixed_mod2_dim=0
CORE|9329|order=360|pullback=720|derived=720|nonsplit=true|fixed_mod2_dim=0
CORE|9330|order=360|pullback=720|derived=360|nonsplit=false|fixed_mod2_dim=3
CORE|9331|order=360|pullback=720|derived=720|nonsplit=true|fixed_mod2_dim=0
CORE|10378|order=960|pullback=1920|derived=1920|nonsplit=true|fixed_mod2_dim=0
CORE|10379|order=960|pullback=1920|derived=960|nonsplit=false|fixed_mod2_dim=3
CORE|10380|order=960|pullback=1920|derived=1920|nonsplit=true|fixed_mod2_dim=0
CORE|10743|order=1920|pullback=3840|derived=1920|nonsplit=false|fixed_mod2_dim=2
CORE|10744|order=1920|pullback=3840|derived=3840|nonsplit=true|fixed_mod2_dim=0
CORE|10745|order=1920|pullback=3840|derived=3840|nonsplit=true|fixed_mod2_dim=0
CORE|10843|order=2520|pullback=5040|derived=5040|nonsplit=true|fixed_mod2_dim=0
CORE|10844|order=2520|pullback=5040|derived=2520|nonsplit=false|fixed_mod2_dim=2
CORE|10845|order=2520|pullback=5040|derived=5040|nonsplit=true|fixed_mod2_dim=0
CORE|10913|order=3600|pullback=7200|derived=7200|nonsplit=true|fixed_mod2_dim=0
CORE|10914|order=3600|pullback=7200|derived=7200|nonsplit=true|fixed_mod2_dim=0
CORE|10915|order=3600|pullback=7200|derived=3600|nonsplit=false|fixed_mod2_dim=0
CORE|11062|order=11520|pullback=23040|derived=11520|nonsplit=false|fixed_mod2_dim=2
CORE|11063|order=11520|pullback=23040|derived=23040|nonsplit=true|fixed_mod2_dim=0
CORE|11064|order=11520|pullback=23040|derived=23040|nonsplit=true|fixed_mod2_dim=0
CORE|11102|order=20160|pullback=40320|derived=40320|nonsplit=true|fixed_mod2_dim=0
CORE|11103|order=20160|pullback=40320|derived=20160|nonsplit=false|fixed_mod2_dim=2
CORE|11104|order=20160|pullback=40320|derived=40320|nonsplit=true|fixed_mod2_dim=0
CORE|11105|order=20160|pullback=40320|derived=20160|nonsplit=false|fixed_mod2_dim=1
CORE|11106|order=20160|pullback=40320|derived=40320|nonsplit=true|fixed_mod2_dim=0
CORE|11107|order=20160|pullback=40320|derived=40320|nonsplit=true|fixed_mod2_dim=0
CORE|11120|order=25920|pullback=51840|derived=25920|nonsplit=false|fixed_mod2_dim=2
CORE|11121|order=25920|pullback=51840|derived=51840|nonsplit=true|fixed_mod2_dim=0
CORE|11122|order=25920|pullback=51840|derived=51840|nonsplit=true|fixed_mod2_dim=0
CORE|11159|order=161280|pullback=322560|derived=322560|nonsplit=true|fixed_mod2_dim=0
CORE|11160|order=161280|pullback=322560|derived=161280|nonsplit=false|fixed_mod2_dim=1
CORE|11161|order=161280|pullback=322560|derived=322560|nonsplit=true|fixed_mod2_dim=0
CORE|11162|order=181440|pullback=362880|derived=362880|nonsplit=true|fixed_mod2_dim=0
CORE|11163|order=181440|pullback=362880|derived=181440|nonsplit=false|fixed_mod2_dim=0
CORE|11164|order=181440|pullback=362880|derived=362880|nonsplit=true|fixed_mod2_dim=0
CORE|11165|order=1290240|pullback=2580480|derived=2580480|nonsplit=true|fixed_mod2_dim=0
CORE|11166|order=1290240|pullback=2580480|derived=2580480|nonsplit=true|fixed_mod2_dim=1
CORE|11167|order=1290240|pullback=2580480|derived=2580480|nonsplit=true|fixed_mod2_dim=0
CORE|11168|order=1451520|pullback=2903040|derived=2903040|nonsplit=true|fixed_mod2_dim=0
CORE|11169|order=1451520|pullback=2903040|derived=1451520|nonsplit=false|fixed_mod2_dim=1
CORE|11170|order=1451520|pullback=2903040|derived=2903040|nonsplit=true|fixed_mod2_dim=0
CORE|11171|order=174182400|pullback=348364800|derived=348364800|nonsplit=true|fixed_mod2_dim=0
CONFIG|1|cores=[ 4012, 4013, 4015, 4016, 9329, 9330, 10379, 10380, 10743, 10744, 10843, 10844, 10914, 10915, 11062, 11063, 11102, 11103, 11104, 11105, 11120, 11121, 11160, 11161, 11162, 11163, 11166, 11167, 11168, 11169, 11171 ]|nonsplit_count=17|marker_free_count=18|both_count=16
CONFIG|2|cores=[ 4013, 4014, 4015, 4017, 9329, 9331, 10378, 10380, 10744, 10745, 10843, 10845, 10913, 10914, 11063, 11064, 11102, 11104, 11106, 11107, 11121, 11122, 11159, 11161, 11162, 11164, 11165, 11167, 11168, 11170, 11171 ]|nonsplit_count=31|marker_free_count=31|both_count=31
CONFIG|3|cores=[ 4012, 4014, 4016, 4017, 9330, 9331, 10378, 10379, 10743, 10745, 10844, 10845, 10913, 10915, 11062, 11064, 11103, 11105, 11106, 11107, 11120, 11122, 11159, 11160, 11163, 11164, 11165, 11166, 11169, 11170, 11171 ]|nonsplit_count=17|marker_free_count=18|both_count=16
ALIGNED_CONFIGURATION=2
INDEX_120_CANDIDATES=[ 11170, 11169, 11168 ]
ROOT_ORBIT_STABILIZER_CLASS=11169
ROOT_ORBIT_STABILIZER_PULLBACK_STATUS=split
INDEX_135_CANDIDATES=[ 11167, 11166, 11165 ]
SINGULAR_ORBIT_STABILIZER_CLASS=11166
ALIGNED_31_CLASSES=[ 4013, 4014, 4015, 4017, 9329, 9331, 10378, 10380, 10744, 10745, 10843, 10845, 10913, 10914, 11063, 11064, 11102, 11104, 11106, 11107, 11121, 11122, 11159, 11161, 11162, 11164, 11165, 11167, 11168, 11170, 11171 ]
ALIGNED_31_NONSPLIT=true
ALIGNED_31_E8_MOD2_FIXED_FREE=true
CERTIFICATE_OK=true
```

## Joint JSON

```json
{
  "schema": "o8p2-weyl-cover-marker-certificate-v1",
  "provenance": {
    "gap_version": "4.16.0",
    "gap_tarball_sha256": "aaa296b32a5d7bf25fd80f241d23ec1f58b74e991ae730fafe40e54eb3af6e7e",
    "tomlib_version": "1.2.11",
    "tomlib_directory": "/workspace/scratch/fde9de896a87/gap_reconstruct/release-packages/tomlib/",
    "tomlib_git_commit": "c460dc4f6bbfbf805b0f0f2dd1d0841bbd4e9c2c",
    "tomlib_tmo8p2_sha256": "eaa82cedb5b805047de0f859f7b17e3dc6c09f7878d4d97e604fa69054c905ed",
    "sla_version": "1.6.2",
    "script_sha256": "1bede8edc10972ee8d779404f00dfcddc17230eb425e88acabf2b28ab0880b3c",
    "raw_output_sha256": "83a6be3185cc381a5092c4cd16d014e352708e53386894763d0c34b5c0b78ec4"
  },
  "run_command": "./gap-4.16.0/gap -q -x 4096 -T -r -A --packagedirs \"$PWD/release-packages\" o8p2_cover_marker_certificate.g",
  "groups": {
    "table": "O8+(2)",
    "subgroup_class_count": 11171,
    "weyl_group_order": 696729600,
    "even_weyl_group_order": 348364800,
    "central_kernel_order": 2,
    "quotient_order": 174182400
  },
  "criterion": {
    "nonsplitting": "For perfect K and its full inverse image E in the central C2-cover, E splits iff |E'|=|K|; E is nonsplit iff E'=E.",
    "marker_freeness": "Because central -I lies in E, (L/nL)^E is zero for every n>1 iff (L/2L)^E is zero."
  },
  "e8_mod2": {
    "nonzero_vector_orbit_sizes": [
      120,
      135
    ],
    "index_120_candidates": [
      11170,
      11169,
      11168
    ],
    "root_orbit_stabilizer_class": 11169,
    "root_orbit_stabilizer_pullback_status": "split",
    "index_135_candidates": [
      11167,
      11166,
      11165
    ],
    "singular_orbit_stabilizer_class": 11166
  },
  "triality_note": "The absolute configuration number can change between runs. Cover and E8/2 tests share one standard-generator identification, and exactly one of the three triality configurations is aligned.",
  "configurations": [
    {
      "configuration": 1,
      "core_class_positions": [
        4012,
        4013,
        4015,
        4016,
        9329,
        9330,
        10379,
        10380,
        10743,
        10744,
        10843,
        10844,
        10914,
        10915,
        11062,
        11063,
        11102,
        11103,
        11104,
        11105,
        11120,
        11121,
        11160,
        11161,
        11162,
        11163,
        11166,
        11167,
        11168,
        11169,
        11171
      ],
      "nonsplit_count": 17,
      "marker_free_count": 18,
      "both_count": 16
    },
    {
      "configuration": 2,
      "core_class_positions": [
        4013,
        4014,
        4015,
        4017,
        9329,
        9331,
        10378,
        10380,
        10744,
        10745,
        10843,
        10845,
        10913,
        10914,
        11063,
        11064,
        11102,
        11104,
        11106,
        11107,
        11121,
        11122,
        11159,
        11161,
        11162,
        11164,
        11165,
        11167,
        11168,
        11170,
        11171
      ],
      "nonsplit_count": 31,
      "marker_free_count": 31,
      "both_count": 31
    },
    {
      "configuration": 3,
      "core_class_positions": [
        4012,
        4014,
        4016,
        4017,
        9330,
        9331,
        10378,
        10379,
        10743,
        10745,
        10844,
        10845,
        10913,
        10915,
        11062,
        11064,
        11103,
        11105,
        11106,
        11107,
        11120,
        11122,
        11159,
        11160,
        11163,
        11164,
        11165,
        11166,
        11169,
        11170,
        11171
      ],
      "nonsplit_count": 17,
      "marker_free_count": 18,
      "both_count": 16
    }
  ],
  "aligned_configuration": 2,
  "aligned_core_results": [
    {
      "class_position": 4013,
      "order": 60,
      "pullback_order": 120,
      "derived_order": 120,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 4014,
      "order": 60,
      "pullback_order": 120,
      "derived_order": 120,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 4015,
      "order": 60,
      "pullback_order": 120,
      "derived_order": 120,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 4017,
      "order": 60,
      "pullback_order": 120,
      "derived_order": 120,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 9329,
      "order": 360,
      "pullback_order": 720,
      "derived_order": 720,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 9331,
      "order": 360,
      "pullback_order": 720,
      "derived_order": 720,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 10378,
      "order": 960,
      "pullback_order": 1920,
      "derived_order": 1920,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 10380,
      "order": 960,
      "pullback_order": 1920,
      "derived_order": 1920,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 10744,
      "order": 1920,
      "pullback_order": 3840,
      "derived_order": 3840,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 10745,
      "order": 1920,
      "pullback_order": 3840,
      "derived_order": 3840,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 10843,
      "order": 2520,
      "pullback_order": 5040,
      "derived_order": 5040,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 10845,
      "order": 2520,
      "pullback_order": 5040,
      "derived_order": 5040,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 10913,
      "order": 3600,
      "pullback_order": 7200,
      "derived_order": 7200,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 10914,
      "order": 3600,
      "pullback_order": 7200,
      "derived_order": 7200,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11063,
      "order": 11520,
      "pullback_order": 23040,
      "derived_order": 23040,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11064,
      "order": 11520,
      "pullback_order": 23040,
      "derived_order": 23040,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11102,
      "order": 20160,
      "pullback_order": 40320,
      "derived_order": 40320,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11104,
      "order": 20160,
      "pullback_order": 40320,
      "derived_order": 40320,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11106,
      "order": 20160,
      "pullback_order": 40320,
      "derived_order": 40320,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11107,
      "order": 20160,
      "pullback_order": 40320,
      "derived_order": 40320,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11121,
      "order": 25920,
      "pullback_order": 51840,
      "derived_order": 51840,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11122,
      "order": 25920,
      "pullback_order": 51840,
      "derived_order": 51840,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11159,
      "order": 161280,
      "pullback_order": 322560,
      "derived_order": 322560,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11161,
      "order": 161280,
      "pullback_order": 322560,
      "derived_order": 322560,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11162,
      "order": 181440,
      "pullback_order": 362880,
      "derived_order": 362880,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11164,
      "order": 181440,
      "pullback_order": 362880,
      "derived_order": 362880,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11165,
      "order": 1290240,
      "pullback_order": 2580480,
      "derived_order": 2580480,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11167,
      "order": 1290240,
      "pullback_order": 2580480,
      "derived_order": 2580480,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11168,
      "order": 1451520,
      "pullback_order": 2903040,
      "derived_order": 2903040,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11170,
      "order": 1451520,
      "pullback_order": 2903040,
      "derived_order": 2903040,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    },
    {
      "class_position": 11171,
      "order": 174182400,
      "pullback_order": 348364800,
      "derived_order": 348364800,
      "nonsplit": true,
      "fixed_mod2_dimension": 0,
      "marker_free": true
    }
  ],
  "all_31_nonsplit": true,
  "all_31_e8_mod2_fixed_free": true,
  "certificate_ok": true
}
```

## Abstract-type validation script

```gap
#############################################################################
## Independent checks behind the abstract labels in the JSON certificate.
#############################################################################

if LoadPackage("tomlib") <> true then
    Error("TomLib failed to load");
fi;

tom := TableOfMarks("O8+(2)");
subs := SubsTom(tom);
orders := OrdersTom(tom);
derived := DerivedSubgroupsTomUnique(tom);
n := Length(subs);

configurations := [
    [ [11170, 11165, 11164, 11156, 11074, 11155, 11077], 11152 ],
    [ [11169, 11166, 11163, 11158, 11076, 11155, 11077], 11153 ],
    [ [11168, 11167, 11162, 11157, 11075, 11155, 11077], 11154 ]
];

PerfectCoreClass := function(class)
    while derived[class] <> class do
        class := derived[class];
    od;
    return class;
end;

allCoreClasses := [];
for cfg in configurations do
    forbidden := [];
    for class in Concatenation(cfg[1], [cfg[2]]) do
        UniteSet(forbidden, subs[class]);
    od;
    survivors := Difference([1 .. n], forbidden);
    UniteSet(allCoreClasses,
             Difference(Set(List(survivors, PerfectCoreClass)), [1]));
od;

perfectLibraryIdentifiers := [
    [60,    [60, 1],    "A5"],
    [360,   [360, 1],   "A6"],
    [960,   [960, 2],   "2^4:A5"],
    [1920,  [1920, 1],  "2^5:A5"],
    [2520,  [2520, 1],  "A7"],
    [3600,  [3600, 1],  "A5xA5"],
    [11520, [11520, 1], "2^5:A6"]
];

simpleIdentifiers := [
    [20160,     "A8"],
    [25920,     "U4(2)"],
    [181440,    "A9"],
    [1451520,   "S6(2)"],
    [174182400, "O8+(2)"]
];

ValidateCoreClasses := function()
    local class, order, group, entry, shortname, radical, quotientName,
          complementOrder, label, complementsInTom;

    for class in allCoreClasses do
        order := orders[class];
        group := RepresentativeTom(tom, class);
        entry := First(perfectLibraryIdentifiers, pair -> pair[1] = order);

        if entry <> fail then
            Assert(0, PerfectIdentification(group) = entry[2]);
            Print(class, "|", order, "|", entry[3],
                  "|PerfectIdentification=", entry[2], "\n");
        else
            entry := First(simpleIdentifiers, pair -> pair[1] = order);
            if entry <> fail then
                shortname :=
                    IsomorphismTypeInfoFiniteSimpleGroup(group).shortname;
                Assert(0, shortname = entry[2]);
                Print(class, "|", order, "|", entry[2],
                      "|SimpleGroupRecognition=", shortname, "\n");
            elif order = 161280 or order = 1290240 then
                radical := SolvableRadical(group);
                Assert(0, Size(radical) = 64);
                Assert(0, IsElementaryAbelian(radical));
                quotientName := IsomorphismTypeInfoFiniteSimpleGroup(
                                    group / radical).shortname;
                if order = 161280 then
                    Assert(0, quotientName = "A7");
                    complementOrder := 2520;
                    label := "2^6:A7";
                else
                    Assert(0, quotientName = "A8");
                    complementOrder := 20160;
                    label := "2^6:A8";
                fi;
                complementsInTom := Filtered(subs[class],
                                      sub -> orders[sub] = complementOrder);
                Assert(0, not IsEmpty(complementsInTom));
                Print(class, "|", order, "|", label,
                      "|radical=2^6|quotient=", quotientName,
                      "|complement_classes=", complementsInTom, "\n");
            else
                Error("unhandled perfect core order ", order);
            fi;
        fi;
    od;

    Assert(0, Length(allCoreClasses) = 46);
    Print("DISTINCT_CORE_CLASSES_ACROSS_TRIALITY=",
          Length(allCoreClasses), "\n");
    Print("CORE_IDENTIFIER_VALIDATION_OK=true\n");
end;

ValidateCoreClasses();
QUIT;
```

## Abstract-type validation raw output

```text
4012|60|A5|PerfectIdentification=[ 60, 1 ]
4013|60|A5|PerfectIdentification=[ 60, 1 ]
4014|60|A5|PerfectIdentification=[ 60, 1 ]
4015|60|A5|PerfectIdentification=[ 60, 1 ]
4016|60|A5|PerfectIdentification=[ 60, 1 ]
4017|60|A5|PerfectIdentification=[ 60, 1 ]
9329|360|A6|PerfectIdentification=[ 360, 1 ]
9330|360|A6|PerfectIdentification=[ 360, 1 ]
9331|360|A6|PerfectIdentification=[ 360, 1 ]
10378|960|2^4:A5|PerfectIdentification=[ 960, 2 ]
10379|960|2^4:A5|PerfectIdentification=[ 960, 2 ]
10380|960|2^4:A5|PerfectIdentification=[ 960, 2 ]
10743|1920|2^5:A5|PerfectIdentification=[ 1920, 1 ]
10744|1920|2^5:A5|PerfectIdentification=[ 1920, 1 ]
10745|1920|2^5:A5|PerfectIdentification=[ 1920, 1 ]
10843|2520|A7|PerfectIdentification=[ 2520, 1 ]
10844|2520|A7|PerfectIdentification=[ 2520, 1 ]
10845|2520|A7|PerfectIdentification=[ 2520, 1 ]
10913|3600|A5xA5|PerfectIdentification=[ 3600, 1 ]
10914|3600|A5xA5|PerfectIdentification=[ 3600, 1 ]
10915|3600|A5xA5|PerfectIdentification=[ 3600, 1 ]
11062|11520|2^5:A6|PerfectIdentification=[ 11520, 1 ]
11063|11520|2^5:A6|PerfectIdentification=[ 11520, 1 ]
11064|11520|2^5:A6|PerfectIdentification=[ 11520, 1 ]
11102|20160|A8|SimpleGroupRecognition=A8
11103|20160|A8|SimpleGroupRecognition=A8
11104|20160|A8|SimpleGroupRecognition=A8
11105|20160|A8|SimpleGroupRecognition=A8
11106|20160|A8|SimpleGroupRecognition=A8
11107|20160|A8|SimpleGroupRecognition=A8
11120|25920|U4(2)|SimpleGroupRecognition=U4(2)
11121|25920|U4(2)|SimpleGroupRecognition=U4(2)
11122|25920|U4(2)|SimpleGroupRecognition=U4(2)
11159|161280|2^6:A7|radical=2^6|quotient=A7|complement_classes=[ 10845 ]
11160|161280|2^6:A7|radical=2^6|quotient=A7|complement_classes=[ 10844 ]
11161|161280|2^6:A7|radical=2^6|quotient=A7|complement_classes=[ 10843 ]
11162|181440|A9|SimpleGroupRecognition=A9
11163|181440|A9|SimpleGroupRecognition=A9
11164|181440|A9|SimpleGroupRecognition=A9
11165|1290240|2^6:A8|radical=2^6|quotient=A8|complement_classes=[ 11106, 11107 ]
11166|1290240|2^6:A8|radical=2^6|quotient=A8|complement_classes=[ 11103, 11105 ]
11167|1290240|2^6:A8|radical=2^6|quotient=A8|complement_classes=[ 11102, 11104 ]
11168|1451520|S6(2)|SimpleGroupRecognition=S6(2)
11169|1451520|S6(2)|SimpleGroupRecognition=S6(2)
11170|1451520|S6(2)|SimpleGroupRecognition=S6(2)
11171|174182400|O8+(2)|SimpleGroupRecognition=O8+(2)
DISTINCT_CORE_CLASSES_ACROSS_TRIALITY=46
CORE_IDENTIFIER_VALIDATION_OK=true
```
