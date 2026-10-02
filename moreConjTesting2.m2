load "conjectureExamples2.m2";
checkNonstandardKoszul = (I,n)->(
    --Build associated graded of R=S/I;
    T := ZZ/101[flatten entries vars ring I];
    J := tangentCone I;
    grI := substitute(J,T);
    grR := T/grI;
    --Resolution of k over associated graded (through step n);
    m := ideal vars grR;
    k := module grR/m;
    r := betti res(k,LengthLimit=>n);
    return (regularity r == 0)
);
for n to 2 do (
    for m to 2 do (
        -- Hard code warning, e=5
        e = 5;
        kk = ZZ/101;
        L = (for i to n+1 list 1)|(for j to m+1 list 2);
        R = weightedVeronese(L,kk,e);
        use R.cache#T;
        print("For (n,m)=");
        print((n,m));
        print(", S^(5) NonstandardKoszul=");
        print(checkNonstandardKoszul(R.cache#K,10));
        print("\n");
    )
)