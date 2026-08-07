# A5 subsystem-orbit certificate

This certificate reproduces the table-of-marks calculation supplying the
finite orbit input to PDF Proposition 6.16 and the numerical orbit counts in
Proposition 6.17.

## Scope and trust boundary

For the four triality-aligned projective `A5` rows 4013, 4014, 4015, and
4017, the script decomposes the restrictions of the `(D4)^2` and `(A4)^2`
coset actions. It checks that each row has a degree-five `(D4)^2` orbit and a
degree-six `(A4)^2` orbit, and that the degree-five multiplicities are
`[5, 5, 1, 1]`.

The table-of-marks calculation and the identification of TomLib row 11155
with the `(D4)^2` action and row 11076 with the `(A4)^2` action are external
certificate inputs. Lean checks the embedded compressed histograms, their
full action-degree sums, and all reported small-orbit multiplicities. Neither
this certificate nor the accompanying Lean file checks the further assertion
that an order-three quotient acts by outer triality on a `D4` factor.

## Wolfram availability

The requested Mathematica route was unavailable in the execution image.
`wolframscript`, `WolframKernel`, `math`, and `Mathematica` were all absent
from `PATH`, and no Wolfram installation was found under `/usr/local` or
`/opt`. Consequently there was no Wolfram version or license to invoke.

## Provenance

- GAP version: 4.16.0
- GAP tarball SHA-256:
  `aaa296b32a5d7bf25fd80f241d23ec1f58b74e991ae730fafe40e54eb3af6e7e`
- TomLib version: 1.2.11
- TomLib `tmo8p2.tom` SHA-256:
  `eaa82cedb5b805047de0f859f7b17e3dc6c09f7878d4d97e604fa69054c905ed`
- Script SHA-256:
  `df187f8454c857a2501bfe4d36554f6275d70ffe53e823bf1d6fb1d99102e1d9`
- Raw output SHA-256:
  `062fa86af26dd7b6432454a72aa59219ab4638022c24dcacd10efe0a0e506d14`

Run command:

```sh
./gap-4.16.0/gap -q -x 4096 -T -r -A \
  --packagedirs "$PWD/release-packages" a5_subsystem_orbits.g
```

## Script

```gap
if LoadPackage("tomlib") <> true then
    Error("TomLib failed to load");
fi;

tom := TableOfMarks("O8+(2)");
orders := OrdersTom(tom);

# Triality-aligned A5 rows and subsystem columns from configuration 2.
a5rows := [4013, 4014, 4015, 4017];
d4d4 := 11155;
a4a4 := 11076;

OrbitSizes := function(h, s)
    local dec, result, k, multiplicity, j;
    dec := IntersectionsTom(tom, h, s);
    result := [];
    for k in [1 .. Length(dec)] do
        multiplicity := dec[k];
        Assert(0, IsInt(multiplicity));
        Assert(0, multiplicity >= 0);
        for j in [1 .. multiplicity] do
            Add(result, orders[h] / orders[k]);
        od;
    od;
    Sort(result);
    Assert(0, Sum(result) = orders[Length(orders)] / orders[s]);
    return result;
end;

Print("GAP_VERSION=", GAPInfo.Version, "\n");
Print("TOMLIB_VERSION=", GAPInfo.PackagesLoaded.tomlib[2], "\n");
Print("TABLE=", Identifier(tom), "\n");
for s in [11169, 11166, 11163, 11158, 11076, 11155, 11077] do
    Print("COLUMN=", s, "|ORDER=", orders[s], "|INDEX=",
          orders[Length(orders)] / orders[s], "\n");
od;
for h in a5rows do
    d := OrbitSizes(h, d4d4);
    a := OrbitSizes(h, a4a4);
    Assert(0, 5 in d);
    Assert(0, 6 in a);
    Print("A5_ROW=", h, "|D4D4_HIST=", Collected(d),
          "|A4A4_HIST=", Collected(a), "\n");
od;
Assert(0, List(a5rows, h -> Number(OrbitSizes(h, d4d4), x -> x = 5))
          = [5, 5, 1, 1]);
Print("CERTIFICATE_OK=true\n");
QUIT;
```

## Raw output

```text
GAP_VERSION=4.16.0
TOMLIB_VERSION=1.2.11
TABLE=O8+(2)
COLUMN=11169|ORDER=1451520|INDEX=120
COLUMN=11166|ORDER=1290240|INDEX=135
COLUMN=11163|ORDER=181440|INDEX=960
COLUMN=11158|ORDER=155520|INDEX=1120
COLUMN=11076|ORDER=14400|INDEX=12096
COLUMN=11155|ORDER=110592|INDEX=1575
COLUMN=11077|ORDER=15552|INDEX=11200
A5_ROW=4013|D4D4_HIST=[ [ 5, 5 ], [ 10, 15 ], [ 15, 10 ], [ 20, 10 ], [ 30, 15 ], [ 60, 10 ] ]|A4A4_HIST=[ [ 6, 6 ], [ 30, 90 ], [ 60, 156 ] ]
A5_ROW=4014|D4D4_HIST=[ [ 5, 5 ], [ 10, 15 ], [ 15, 10 ], [ 20, 10 ], [ 30, 15 ], [ 60, 10 ] ]|A4A4_HIST=[ [ 6, 6 ], [ 30, 90 ], [ 60, 156 ] ]
A5_ROW=4015|D4D4_HIST=[ [ 5, 1 ], [ 10, 7 ], [ 15, 6 ], [ 30, 31 ], [ 60, 8 ] ]|A4A4_HIST=[ [ 6, 6 ], [ 10, 6 ], [ 20, 6 ], [ 30, 84 ], [ 60, 156 ] ]
A5_ROW=4017|D4D4_HIST=[ [ 5, 1 ], [ 10, 7 ], [ 15, 6 ], [ 30, 31 ], [ 60, 8 ] ]|A4A4_HIST=[ [ 6, 6 ], [ 10, 6 ], [ 20, 6 ], [ 30, 84 ], [ 60, 156 ] ]
CERTIFICATE_OK=true
```
