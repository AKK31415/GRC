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
normalCurveRing(ZZ,ZZ,Ring) := (d,e,kk) -> (
    L := splice{d:1,e:e};
    S := kk[x_0..x_(d-1),y_0..y_(e-1),Degrees=>L];
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

makeDSmatrix = method()
makeDSmatrix(ZZ,ZZ,Ring) := (d,e,kk) -> (
    L := splice{d:1,e:e};
    S := kk[x_0..x_(d-1),y_0..y_(e-1),Degrees=>L];
    matrix{{x_0..x_(d-2),x_(d-1)^e,y_0..y_(e-2)},{x_1..x_(d-1),y_0..y_(e-1)}}
)

makeGuessMatrix = method()
makeGuessMatrix(ZZ,ZZ,Ring) := (d,e,kk) -> (
    if not e == 2 then error("Not yet implemented for e != 2");
    ncr := normalCurveRing(d,e,kk);
    M := ncr_3;
    S := ncr_1;
    use S;
    minorsM := minors(2,M);
    gensMinorsM = gens minorsM;
    row1 := {};
    row2 := {};
    for i to numColumns gensMinorsM - 1 do (
        row1 = append(row1,(gensMinorsM_(0,i)));
        row2 = append(row2,0);
    );
    gensS := gens S;
    for i to numColumns M - 3 do (
        row1 = append(row1,-gensS_(i+1)*gensS_(d-1));
        row2 = append(row2,gensS_i);
    );
    row1 = append(row1,-gensS_d);
    row2 = append(row2,gensS_(d-1));
    row1 = append(row1,-gensS_(d-1)*gensS_(d+1));
    row2 = append(row2,gensS_d);
    matrix{row1,row2}
)


end
-- Development down here
restart
load "moreCurves.m2"
d=3
e=2
M = makeGuessMatrix(d,e,ZZ/101)
prune M