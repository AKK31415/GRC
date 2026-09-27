restart
needsPackage "HHLResolutions"
--function to compute the resolution of the normalization of a curve
--Build the ring first
normalCurveRing = method()
normalCurveRing(ZZ,ZZ) := (d,e) -> (
    L := splice{d:1,e:e};
    S := ZZ/101[x_0..x_(d-1),y_0..y_(e-1),Degrees=>L];
    dsMatrix := matrix{{x_0..x_(d-2),x_(d-1)^e,y_0..y_(e-2)},{x_1..x_(d-1),y_0..y_(e-1)}};
    I := minors(2,dsMatrix);
    {S/I,S,I,dsMatrix}
)
normalCurve = method()
normalCurve(ZZ,ZZ) := (d,e) -> (
    --Build coordinate ring as a quotient by a determinantal ideal:
    normCurveRing := normalCurveRing(d,e);
    R := normCurveRing_0;
    S := normCurveRing_1;
    I := normCurveRing_2;
    --Resolution of R over S:
    r := res I;
    r.dd_1;
    betti res I;
    X := weightedProjectiveSpace(flatten degrees S);
    a := d-1;
    b := e-1;
    g := map(ZZ^(d-1+e),ZZ^1, transpose matrix{{1..a,e*d-b..e*d}});
    --this is HHL resolution
    HHL := makeHHLResolution(X,g);
    --To minimize the HHL resolution:
    M := HH_0(HHL);
    --This M is the normalization of the Davis-Sobieska
    {R,S,M,res prune M}
)

makeGuessMatrix = method()
makeGuessMatrix(ZZ,ZZ) := (d,e) -> (
    if not e == 2 then error("Not yet implemented for e != 2");
    normCurveRing := normalCurveRing(d,e);
    
)