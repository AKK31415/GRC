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

makePureQuadMinorsDS = method()
makePureQuadMinorsDS(Matrix,Ring) := (M',S) -> (
    use S;
    minors(2,M'_{0..(numColumns M' - 3),numColumns M' - 1})
)

makeGuessFullMatrix = method()
makeGuessFullMatrix(ZZ,ZZ,Ring) := (d,e,kk) -> (
    if not e == 2 then error("Not yet implemented for e != 2");
    ncr := normalCurveRing(d,e,kk);
    S := ncr_1;
    M := ncr_3;
    gensS := gens S;
    minorsM := gens minors(2,M);
    (minorsM||map(S^1,S^(numColumns minorsM),0))|(matrix{
        apply(toList(0..numColumns M - 3), i -> -gensS_(i+1)*gensS_(d-1)),
        apply(toList(0..numColumns M - 3), i -> gensS_i)
    })|matrix{{-gensS_d,-gensS_(d-1)*gensS_(d+1)},{gensS_(d-1),gensS_d}}
)

makeGuessMatrix = method()
makeGuessMatrix(ZZ,ZZ,Ring) := (d,e,kk) -> (
    ncr := normalCurveRing(d,e,kk);
    S := ncr_1;
    gensS := gens S;
    M := ncr_3;
    minorsM = gens minors(2,M_(append(toList(0..numColumns M - 3),numColumns M - 1)));
    (minorsM||map(S^1,S^(numColumns minorsM),0))|(matrix{
        apply(toList(0..numColumns M - 3), i -> -gensS_(i+1)*gensS_(d-1)),
        apply(toList(0..numColumns M - 3), i -> gensS_i)
    })|matrix{{-gensS_d,-gensS_(d-1)*gensS_(d+1)},{gensS_(d-1),gensS_d}}
)


end
-- Development down here
restart
load "moreCurves.m2"
d=3
e=2
M = makeGuessFullMatrix(d,e,ZZ/101)
makeGuessMatrix(d,e,ZZ/101)
minimalPresentation M