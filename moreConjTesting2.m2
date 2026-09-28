load "conjectureExamples2.m2";
for i to 3 do (
    for j to 3 do (
        n := i+1;
        e := 2*j+1;
        R := weightedVeronese(n,e,ZZ/101);
        M := tGuessMat(e,R.cache#S,R.cache#mons);
        str := "(n,e)="|toString((n,e));
        str = str||(tex M);
        print(str);
    );
);