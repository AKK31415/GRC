restart
needsPackage "HHLResolutions"
--function to compute the resolution of the normalization of a curve
--Build the ring first
normalCurveRing = method()
normalCurveRing(ZZ,ZZ) := (d,e) -> (
    L := splice{e:e,d:1};
    S := ZZ/101[y_0..y_(e-1),x_0..x_(d-1),Degrees=>L,MonomialOrder=>Lex];
    dsMatrix := matrix{{x_0..x_(d-2),x_(d-1)^e,y_0..y_(e-2)},{x_1..x_(d-1),y_0..y_(e-1)}};
    I := minors(2,dsMatrix);
    {S/I,S,I,dsMatrix}
) -- {S/I,S,I,dsMatrix}
normalCurveRing(ZZ,ZZ,Ring) := (d,e,kk) -> (
    L := splice{e:e,d:1};
    S := ZZ/101[y_0..y_(e-1),x_0..x_(d-1),Degrees=>L,MonomialOrder=>Lex];
    dsMatrix := matrix{{x_0..x_(d-2),x_(d-1)^e,y_0..y_(e-2)},{x_1..x_(d-1),y_0..y_(e-1)}};
    I := minors(2,dsMatrix);
    {S/I,S,I,dsMatrix}
) -- {S/I,S,I,dsMatrix}

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
    g := map(ZZ^(d-1+e),ZZ^1, transpose matrix{{e*d-b..e*d,1..a}});
    --this is HHL resolution
    HHL := makeHHLResolution(X,g);
    --To minimize the HHL resolution:
    M := HH_0(HHL);
    --This M is the normalization of the Davis-Sobieska
    {R,S,M,res prune M,HHL}
) -- {R,S,M,res prune M} where M is the HHL_0

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
    gensS1 := gens S;
    gensS := (for i to d-1 list gensS1_(e+i))|(for i to e-1 list gensS1_i);
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

columnOps = method()
columnOps(Matrix,ZZ) := (M,d) -> (
    Mright2 := (mutableMatrix M)_(for i to d-2 list numColumns M - d - 1 + i); -- this is the degree two part
    Mright1 := (mutableMatrix M)_{numColumns M - 1}; -- this is the degree three part
    y0col := (mutableMatrix M)_{numColumns M - 2}; -- this is the y0 part
    Mleft := (mutableMatrix M)_(for i to numColumns M - d - 2 list i);
    apply(for i to numColumns Mleft - 1 list i, c -> (
        if leadTerm Mleft_(0,c) == 0 then (-* do nothing for now *-) else (
            if leadTerm(Mleft_(0,c)) % leadTerm(y0col_(0,0)) == 0 then (
                mult := leadTerm(Mleft_(0,c)) // leadTerm(y0col_(0,0));
                newCol := Mleft_{c} - mult*y0col_{0};
                Mleft_(0,c) = newCol_(0,0);
                Mleft_(1,c) = newCol_(1,0);
                break
            ) else if leadTerm(Mleft_(0,c)) % leadTerm(Mright1_(0,0)) == 0 then (
                mult := leadTerm(Mleft_(0,c)) // leadTerm(Mright1_(0,0));
                newCol := Mleft_{c} - mult*Mright1_{0};
                Mleft_(0,c) = newCol_(0,0);
                Mleft_(1,c) = newCol_(1,0);
                break
            ) else (
                 for j to d-2 do (
                    if leadTerm(Mleft_(0,c)) % leadTerm(Mright2_(0,j)) == 0 then (
                        mult := leadTerm(Mleft_(0,c)) // leadTerm(Mright2_(0,j));
                        newCol := Mleft_{c} - mult*Mright2_{j};
                        Mleft_(0,c) = newCol_(0,0);
                        Mleft_(1,c) = newCol_(1,0);
                        break
                    );
                );
            );
        );
    ));
    newM := matrix(Mleft)|matrix(Mright2)|matrix(y0col)|matrix(Mright1);
    if newM == M then return newM else columnOps(newM,d)
)

minimizeMatrix = method()
minimizeMatrix(Matrix) := M -> (
    tempOut := matrix {{},{}};
    for i to numColumns M - 1 do (
        if M_{i} == 0 then continue else tempOut = tempOut|M_{i};
    );
    tempOut
)


end
-------------------------------------------------------
-- Development down here
-------------------------------------------------------
restart
load "moreCurves.m2"
d=3
e=2
M = makeGuessFullMatrix(d,e,ZZ/101)
M = columnOps(M,d)
M = minimizeMatrix M
leadTerm M_(0,2)
makeGuessMatrix(d,e,ZZ/101)
minimalPresentation M