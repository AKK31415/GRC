restart
needsPackage "HHLResolutions"
--function to compute the resolution of the normalization of a curve
normalcurve = (d,e) -> (
    --Build coordinate ring as a quotient by a determinantal ideal:
    L=splice{d:1,e:e};
    S = ZZ/101[x_0..x_(d-1),y_0..y_(e-1),Degrees=>L];
    M = matrix{{x_0..x_(d-2),x_(d-1)^e,y_0..y_(e-2)},{x_1..x_(d-1),y_0..y_(e-1)}};
    I = minors(2,M);
    R=S/I;
    --Resolution of R over S:
    r = res I;
    r.dd_1;
    betti res I;
    X = weightedProjectiveSpace(flatten degrees S);
    a = d-1;
    b = e-1;
    g = map(ZZ^(d-1+e),ZZ^1, transpose matrix{{1..a,e*d-b..e*d}});
    --this is HHL resolution
    HHL = makeHHLResolution(X,g);
    --To minimize the HHL resolution:
    M = HH_0(HHL);
    --This M is the normalization of the Davis-Sobieska
    minHHL = res prune M)
normalcurve(4,2)
N = oo
N.dd_1