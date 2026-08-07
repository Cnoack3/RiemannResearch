# A5 degree-five triality countercertificate

This certificate audits the outer-triality assertion in Proposition 6.17 of
the 5 August 2026 E8 Serre II memorandum.

## Result

The numerical table-of-marks statement remains correct: rows 4013, 4014,
4015, and 4017 have respectively 5, 5, 1, and 1 degree-five `(D4)^2`
subsystem orbits. The universal triality conclusion is false.

For the exact ATLAS integral representation `2A5G1-Zr8bB0`, the script
below checks:

- `G = <A,B>` has order 120, center of order two, and structure
  `SL(2,5)`; both generators have determinant one and the projective quotient
  is `A5`;
- the natural actions on the 120 E8 root pairs and 135 nonzero singular
  mod-two vectors have spectra `20 + 20 + 20 + 60` and
  `3*5 + 3*10 + 3*30`;
- comparison with the geometrically designated TomLib root-pair and singular
  columns narrows the projective class, among all nine A5 rows, to
  `{4015, 4017}`;
- both candidate rows are among the four rows in Proposition 6.17 and each
  has exactly one degree-five `(D4)^2` orbit;
- the displayed roots form two 24-root `D4` components;
- `H = <w,j,r>` has order 24, projective quotient `A4`, and is exactly the
  stabilizer in `G` of their 48-root union, so the subsystem orbit has degree
  five;
- `H` is contained in the reflection group
  `W(D4) x W(D4)`;
- `r` has order three and lies in that inner reflection group.

The remaining `4015/4017` ambiguity is immaterial to the universal claim:
whichever of the two TomLib classes the integral embedding represents, its
unique degree-five orbit is the explicitly stabilized orbit above, and its
order-three stabilizer action is inner on both D4 components. This contradicts
the PDF's assertion that at least one component is outer trialitarian on every
one of the twelve orbits.

## Trust boundary

GAP performs the exact integer-matrix group enumeration. GAP/TomLib supplies
the table-of-marks orbit spectra and narrows the projective row to
`{4015,4017}`; the certificate does not choose between those two classes.
The pre-existing subsystem certificate supplies the geometric identification
of TomLib columns 11169, 11166, and 11155 with the root-pair, singular-vector,
and `(D4)^2) actions. That column geometry remains an explicit external
certificate input.

Lean independently checks the same integer matrices: the quadratic-form
isometries, the `D4 + D4` Gram matrix, the ATLAS words, the order-three
relation, and explicit factorizations through the reflection-generated inner
image. Lean does not internalize TomLib's complete table of marks.

## Provenance

- GAP: 4.16.0
- TomLib: 1.2.11
- GAP binary SHA-256:
  `61324baef6ca84a4e36849122f44f77f1a56891f72a8206239007fc6faf7bb5e`
- Script SHA-256:
  `492dfbf08a853b35feaa41178c92889ae323e64854fcee86bd168a1185eb5308`
- Raw output SHA-256:
  `f512bb9427ba50a53a25a03e8b607d16de70197998e572ce0b2a17eaab0ce2ec`
- ATLAS matrix source:
  <https://brauer.maths.qmul.ac.uk/Atlas/alt/A5/mag/2A5G1-Zr8bB0.M>

Run command:

```sh
GAP_HISTFILE=/dev/null ./gap-4.16.0/gap -q -x 4096 -T -r -A \
  --packagedirs "$PWD/release-packages" a5_triality_countercertificate.g
```

## Script

```gap
if LoadPackage("tomlib") <> true then
    Error("TomLib failed to load");
fi;

A := [
[0,1,0,0,0,0,0,0],
[-1,0,0,0,0,0,0,0],
[-1,0,0,1,-1,1,-1,-1],
[0,-1,-1,0,-1,-1,1,-1],
[1,0,-1,1,-1,-1,0,-1],
[0,1,-1,-1,1,-1,1,0],
[-1,0,-1,-1,0,-1,1,-1],
[0,-1,1,-1,1,0,1,1]
];
B := [
[0,0,1,0,0,0,0,0],
[0,0,0,1,0,0,0,0],
[0,0,0,0,1,0,0,0],
[0,0,0,0,0,1,0,0],
[1,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0],
[0,0,0,0,0,0,1,0],
[0,0,0,0,0,0,0,1]
];
Q := [
[2,0,0,-1,0,1,0,-1],
[0,2,1,0,-1,0,1,0],
[0,1,2,0,0,-1,0,-1],
[-1,0,0,2,1,0,1,0],
[0,-1,0,1,2,0,0,-1],
[1,0,-1,0,0,2,1,0],
[0,1,0,1,0,1,2,0],
[-1,0,-1,0,-1,0,0,2]
];
w := B*A*B*A*B*B*A*B*A;
j := B*B*A*B;
r := A*A*A*B*A;
G := Group(A,B);
H := Group(w,j,r);
Print("G_SIZE=", Size(G), "\n");
Print("H_SIZE=", Size(H), "\n");
Print("INDEX=", Index(G,H), "\n");
Print("A_ISOMETRY=", A*Q*TransposedMat(A)=Q, "\n");
Print("B_ISOMETRY=", B*Q*TransposedMat(B)=Q, "\n");
Print("A_DETERMINANT=", DeterminantMat(A), "\n");
Print("B_DETERMINANT=", DeterminantMat(B), "\n");
Print("Q_SYMMETRIC=", Q=TransposedMat(Q), "\n");
Print("Q_DETERMINANT=", DeterminantMat(Q), "\n");
Print("Q_LEADING_PRINCIPAL_MINORS=",
      List([1..8], n -> DeterminantMat(Q{[1..n]}{[1..n]})), "\n");
Print("CENTER_G_SIZE=", Size(Centre(G)), "\n");
Print("G_STRUCTURE=", StructureDescription(G), "\n");
Print("H_STRUCTURE=", StructureDescription(H), "\n");
Print("CENTER_H_SIZE=", Size(Centre(H)), "\n");
Print("G_MOD_CENTER_STRUCTURE=", StructureDescription(G/Centre(G)), "\n");
Print("H_MOD_CENTER_STRUCTURE=", StructureDescription(H/Centre(H)), "\n");
Print("R_ORDER=", Order(r), "\n");
Print("H_NORMAL_IN_G=", IsNormal(G,H), "\n");

# Compare the natural E8 root-pair and singular-vector actions with the
# geometrically designated TomLib columns.  These two spectra isolate the
# projective row to the pair 4015/4017; both are manuscript rows with exactly
# one degree-five D4xD4 orbit.
CanonicalRootPair := function(v)
  if v < -v then return v; else return -v; fi;
end;
latticeRoots := Filtered(Cartesian(List([1..8], i -> [-2..2])),
  v -> v * Q * v = 2);
rootPairs := Set(List(latticeRoots, CanonicalRootPair));
Print("E8_ROOT_COUNT=", Length(latticeRoots), "\n");
Print("E8_ROOT_PAIR_COUNT=", Length(rootPairs), "\n");
atlasRootSpectrum := Collected(List(Orbits(G,rootPairs,
  function(v,g) return CanonicalRootPair(v*g); end), Length));
Print("PROJECTIVE_A5_ROOT_PAIR_ORBITS=", atlasRootSpectrum, "\n");

modTwoVectors := Filtered(Cartesian(List([1..8], i -> [0,1])),
  v -> not IsZero(v));
singularVectors := Filtered(modTwoVectors,
  v -> ((v * Q * v) / 2) mod 2 = 0);
ActModTwo := function(v,g) return List(v*g,x->x mod 2); end;
atlasSingularSpectrum := Collected(List(Orbits(G,singularVectors,ActModTwo),Length));
Print("E8_NONZERO_SINGULAR_COUNT=",Length(singularVectors),"\n");
Print("PROJECTIVE_A5_SINGULAR_VECTOR_ORBITS=",atlasSingularSpectrum,"\n");

tom := TableOfMarks("O8+(2)");
orders := OrdersTom(tom);
OrbitSizes := function(h,s)
  local dec,result,k,multiplicity,jj;
  dec := IntersectionsTom(tom,h,s);
  result := [];
  for k in [1..Length(dec)] do
    multiplicity := dec[k];
    for jj in [1..multiplicity] do
      Add(result,orders[h]/orders[k]);
    od;
  od;
  Sort(result);
  return result;
end;
a5rows := [4012,4013,4014,4015,4016,4017,4018,4019,4020];
for row in a5rows do
  Print("TOMLIB_A5_ROW=",row,
    "|ROOT_PAIR_ORBITS=",Collected(OrbitSizes(row,11169)),
    "|SINGULAR_VECTOR_ORBITS=",Collected(OrbitSizes(row,11166)),"\n");
od;
matchingRows := Filtered(a5rows,row ->
  Collected(OrbitSizes(row,11169))=atlasRootSpectrum and
  Collected(OrbitSizes(row,11166))=atlasSingularSpectrum);
Assert(0,matchingRows=[4015,4017]);
degreeFiveMultiplicities := List(matchingRows,row ->
  Number(OrbitSizes(row,11155),x->x=5));
Assert(0,degreeFiveMultiplicities=[1,1]);
Print("ATLAS_MATCHING_TOMLIB_ROWS=",matchingRows,"\n");
Print("MATCHING_ROW_D4D4_DEGREE_FIVE_MULTIPLICITIES=",
  degreeFiveMultiplicities,"\n");

roots := [
[-1,-1,0,-1,0,0,1,0],
[0,0,0,1,-1,1,-1,-1],
[0,1,0,0,0,0,-1,0],
[1,0,1,1,0,0,0,1],
[-1,0,0,-1,0,0,1,-1],
[0,0,0,1,0,0,-1,0],
[0,1,0,0,1,1,-1,1],
[1,-1,1,0,0,0,0,1]
];

# Full root sets of the two D4 components, represented by signed row vectors.
SimpleReflection := function(root)
  local col;
  col := Q * TransposedMat([root]);
  return IdentityMat(8) - col * [root];
end;
WA := Group(List(roots{[1..4]}, SimpleReflection));
WB := Group(List(roots{[5..8]}, SimpleReflection));
WAB := Group(Concatenation(GeneratorsOfGroup(WA),GeneratorsOfGroup(WB)));
Print("WA_SIZE=", Size(WA), "\n");
Print("WB_SIZE=", Size(WB), "\n");
Print("WAB_SIZE=", Size(WAB), "\n");
Print("WAB_STRUCTURE=", StructureDescription(WAB), "\n");
Print("WJ_IN_WAB=", w in WAB, "\n");
Print("J_IN_WAB=", j in WAB, "\n");
Print("R_IN_WAB=", r in WAB, "\n");
Print("H_SUBGROUP_WAB=", IsSubgroup(WAB,H), "\n");

# Check the exact D4xD4 root subsystem and its G-stabilizer/orbit.
RootOrbit := function(W, root)
  return Set(Concatenation(Orbit(W,root,OnRight), Orbit(W,-root,OnRight)));
end;
RA := RootOrbit(WA, roots[1]);
RB := RootOrbit(WB, roots[5]);
RAB := Set(Concatenation(RA,RB));
Print("RA_SIZE=", Length(RA), "\n");
Print("RB_SIZE=", Length(RB), "\n");
Print("RAB_SIZE=", Length(RAB), "\n");
Print("H_STABILIZES_RAB=", ForAll(GeneratorsOfGroup(H), x -> Set(List(RAB,y->y*x))=RAB), "\n");
stab := Stabilizer(G,RAB,function(set,g) return Set(List(set,y->y*g)); end);
Print("STAB_SIZE=", Size(stab), "\n");
Print("H_EQ_STAB=", H=stab, "\n");
Print("RAB_ORBIT_SIZE=", Length(Orbit(G,RAB,function(set,g) return Set(List(set,y->y*g)); end)), "\n");
Print("CERTIFICATE_OK=true\n");
QUIT;
```

## Raw output

```text
G_SIZE=120
H_SIZE=24
INDEX=5
A_ISOMETRY=true
B_ISOMETRY=true
A_DETERMINANT=1
B_DETERMINANT=1
Q_SYMMETRIC=true
Q_DETERMINANT=1
Q_LEADING_PRINCIPAL_MINORS=[ 2, 4, 6, 9, 6, 4, 2, 1 ]
CENTER_G_SIZE=2
G_STRUCTURE=SL(2,5)
H_STRUCTURE=SL(2,3)
CENTER_H_SIZE=2
G_MOD_CENTER_STRUCTURE=A5
H_MOD_CENTER_STRUCTURE=A4
R_ORDER=3
H_NORMAL_IN_G=false
E8_ROOT_COUNT=240
E8_ROOT_PAIR_COUNT=120
PROJECTIVE_A5_ROOT_PAIR_ORBITS=[ [ 20, 3 ], [ 60, 1 ] ]
E8_NONZERO_SINGULAR_COUNT=135
PROJECTIVE_A5_SINGULAR_VECTOR_ORBITS=[ [ 5, 3 ], [ 10, 3 ], [ 30, 3 ] ]
TOMLIB_A5_ROW=4012|ROOT_PAIR_ORBITS=[ [ 1, 10 ], [ 5, 10 ], [ 10, 6 ] ]|SINGULAR_VECTOR_ORBITS=[ [ 1, 5 ], [ 5, 6 ], [ 10, 10 ] ]
TOMLIB_A5_ROW=4013|ROOT_PAIR_ORBITS=[ [ 60, 2 ] ]|SINGULAR_VECTOR_ORBITS=[ [ 15, 5 ], [ 60, 1 ] ]
TOMLIB_A5_ROW=4014|ROOT_PAIR_ORBITS=[ [ 60, 2 ] ]|SINGULAR_VECTOR_ORBITS=[ [ 15, 5 ], [ 60, 1 ] ]
TOMLIB_A5_ROW=4015|ROOT_PAIR_ORBITS=[ [ 20, 3 ], [ 60, 1 ] ]|SINGULAR_VECTOR_ORBITS=[ [ 5, 3 ], [ 10, 3 ], [ 30, 3 ] ]
TOMLIB_A5_ROW=4016|ROOT_PAIR_ORBITS=[ [ 1, 4 ], [ 6, 6 ], [ 10, 2 ], [ 15, 4 ] ]|SINGULAR_VECTOR_ORBITS=[ [ 1, 3 ], [ 6, 2 ], [ 10, 6 ], [ 15, 4 ] ]
TOMLIB_A5_ROW=4017|ROOT_PAIR_ORBITS=[ [ 20, 3 ], [ 60, 1 ] ]|SINGULAR_VECTOR_ORBITS=[ [ 5, 3 ], [ 10, 3 ], [ 30, 3 ] ]
TOMLIB_A5_ROW=4018|ROOT_PAIR_ORBITS=[ [ 10, 2 ], [ 20, 2 ], [ 30, 2 ] ]|SINGULAR_VECTOR_ORBITS=[ [ 5, 3 ], [ 10, 1 ], [ 20, 1 ], [ 30, 1 ], [ 60, 1 ] ]
TOMLIB_A5_ROW=4019|ROOT_PAIR_ORBITS=[ [ 1, 2 ], [ 12, 4 ], [ 15, 2 ], [ 20, 2 ] ]|SINGULAR_VECTOR_ORBITS=[ [ 1, 1 ], [ 12, 2 ], [ 15, 2 ], [ 20, 4 ] ]
TOMLIB_A5_ROW=4020|ROOT_PAIR_ORBITS=[ [ 10, 2 ], [ 20, 2 ], [ 30, 2 ] ]|SINGULAR_VECTOR_ORBITS=[ [ 5, 3 ], [ 10, 1 ], [ 20, 1 ], [ 30, 1 ], [ 60, 1 ] ]
ATLAS_MATCHING_TOMLIB_ROWS=[ 4015, 4017 ]
MATCHING_ROW_D4D4_DEGREE_FIVE_MULTIPLICITIES=[ 1, 1 ]
WA_SIZE=192
WB_SIZE=192
WAB_SIZE=36864
WAB_STRUCTURE=((C2 x C2 x C2) : S4) x ((C2 x C2 x C2) : S4)
WJ_IN_WAB=true
J_IN_WAB=true
R_IN_WAB=true
H_SUBGROUP_WAB=true
RA_SIZE=24
RB_SIZE=24
RAB_SIZE=48
H_STABILIZES_RAB=true
STAB_SIZE=24
H_EQ_STAB=true
RAB_ORBIT_SIZE=5
CERTIFICATE_OK=true
```
