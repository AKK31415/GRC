restart

-- Method for making the ring with the appropriate weights
makeP1n2Ring = method()
makeP1n2Ring(ZZ,Ring) := (n,kk) -> (
    kk[x_1..x_n,y, Degrees => append((for i to n-1 list 1),2)]
)

-- Want to figure out what the right generalization is when we replace 2 with k
makeP1nkRing = method()
makeP1nkRing(ZZ,ZZ,Ring) := (n,k,kk) -> (
    kk[x_1..x_n,y, Degrees => append((for i to n-1 list 1),k)]
)

-- Helper method for making all monomials from a list of generators 
-- with degree d

makeMonomials = method()
-- This is at best a ZZ graded code and may work on nonstandard 
-- gradings, but not multigradings
makeMonomials(List,ZZ) := (L,d) -> (
    n := #L;
    -- Condition checking on d to make sure we have nothing nonsensical
    if d == 0 then (
        {1}
    );
    if d < 0 then (
        {}
    );
    -- If d is reasonable and we only have one var, we can only return one thing.
    if n == 1 then (
        x := L#0;
        degx := (degree x)#0;
        if d%degx == 0 then (
            return {x^(d//degx)}
        );
        -- return an empty list if d is not divisible by degx
        return {};
    );
    degxn := (degree L#(n-1))#0;
    flatten for i to d//degxn list (
        tempList := flatten makeMonomials(take(L,n-1),d-i*degxn);
        for j to #tempList - 1 list (tempList#j)*((L#(n-1))^i)
    )
)

pruneMonomials = method()
-- returns the set of monomials from mon2 that 
-- were not combos of stuff from mon1
--
-- I realized after coding this that for the simple PP(1^n,2) case, 
-- you only get new things in degree 2e, and the only new thing 
-- you ever get is y^e. Everything else is already a linear combo, 
-- so we need not compute monomials in degree 2e then prune, at 
-- least for this example. This function might be useful in the 
-- future though, so I won't delete it for now.
pruneMonomials(List,List) := (mon1,mon2) -> (
    -- if mon2 is empty we neeed not prune
    if #mon2 == 0 then return {};
    -- check the first element now, and do the rest later
    tempRest := drop(mon2,1);
    for i to #mon1 - 1 do (
        if (mon2#0) % (mon1#i) == 0 then (
            return pruneMonomials(mon1,tempRest)
        );
    );
    append({mon2#0},pruneMonomials(mon1,tempRest))
)

weighted1n2Veronese = method()
weighted1n2Veronese(ZZ,ZZ,Ring) := (n,e,kk) -> (
    Stemp := makeP1n2Ring(n,kk);
    genSet := gens Stemp;
    -- Since currently deg(y)=2 for our examples, we will have 
    -- everything by degree 2e since we will have the pure power y^e
    monsTemp := flatten append({y^e},makeMonomials(genSet,e));
    --varBlocks := 
    Ttemp := kk[w,z_1..z_(#monsTemp-1), Degrees => append((for i to #monsTemp - 2 list 1),2), MonomialOrder => {Lex => 1, GRevLex => #monsTemp - 2}];
    Ktemp := ker map(Stemp,Ttemp,monsTemp);
    output := Ttemp/Ktemp;
    output.cache#S = Stemp;
    output.cache#mons = monsTemp;
    output.cache#T = Ttemp;
    output.cache#K = Ktemp;
    output
)

makeMatrix = method() -- Method for making the matrix of z's
makeMatrix(ZZ,ZZ) := (n,e) -> (
    if n == 1 then (
        if e%2 == 0 then error "Expected odd degree embedding";
        Rtemp := weighted1n2Veronese(n,e,ZZ/101);
        k := e//2; -- so e=2k+1 
        row1 := for i to k list (
            if i == k then (z_(i+1))^2 else z_(i+1)
        );
        row2 := for i to k list (
            if i == k then w else z_(i+2)
        );
        M := matrix{row1,row2};
        M.cache#R = Rtemp;
        M
    ) else error "Not yet implemented for n>=2"
)

changeBackToXY = method()
changeBackToXY(Ring,Ring,List,Matrix) := (S,T,mons,M) -> (
    e := (degree mons_0)_0;
    n := #(gens S) - 1;
    matrix for i to numRows M - 1 list (
        tempRow := for j to numColumns M - 1 list (
            tempEntry := 0;
            gensT := gens T;
            if j == numColumns M - 1 then (
                if M_(i,j) == w then tempEntry = y^e else (
                    for k from #gensT - (n+1) to #gensT - 1 do (
                        for l from #gensT - (n+1) to #gensT - 1 do (
                            if z_k*z_l == M_(i,j) then tempEntry = mons#(k-1)*mons#(l-1);
                        );
                    );
                );
            ) else (
                for k from 1 to #gensT-1 do (
                    if M_(i,j) == z_k then tempEntry = mons_(k-1);
                );
            );
            tempEntry
        );
        tempRow
    )
)

makeGuessXYmatrix = method()
makeGuessXYmatrix(ZZ,Ring) := (e,S) -> (
    gensS := gens S;
    tempColumn := transpose matrix{makeMonomials(gensS,2)};
    tempRow := matrix{append(makeMonomials(gensS,e-2),y^(e-1))};
    tempColumn * tempRow
)

reverseTriangle = method()
reverseTriangle(ZZ) := n -> (
    if n == 1 then 1 else 1 + reverseTriangle(n-1)
)

turnToZiMatrixFromXY = method()
turnToZiMatrixFromXY(Matrix,Ring,Ring,List) := (M,S,T,mons) -> (
    gensT := gens T;
    gensS := gens S;
    n := #gensS - 1;
    use T;
    d := reverseTriangle(numRows M - 1);
    transpose matrix for j to numColumns M - 1 list (
        if j == numColumns M - 1 then append(for i to numRows M - 2 list (
                tempEntry := 0;
                for k from #gensT - d to #gensT - 1 do (
                    for l from #gensT - d to #gensT - 1 do (
                        if mons_(k) * mons_(l) == M_(i,j) then tempEntry = z_k * z_l;
                    );
                );
                tempEntry
            ),w
        ) else for i to numRows M - 1 list (
            z_(position(mons, m -> m == M_(i,j)))
        )
    )
)

checkIfGroebner = method()
checkIfGroebner(ZZ,ZZ) := (n,e) -> (
    -- f checks if x fails the divisibility test from the minors, i.e. if we need it as a Groebner generator
    f := (x,Mminors) -> (
        for m in Mminors do (
            if not x//m == 0 then (
                return true
            );
        );
        false
    );
    R := weighted1n2Veronese(n,e,ZZ/101);
    ZiMat := turnToZiMatrixFromXY(makeGuessXYmatrix(e,R.cache#S),R.cache#S,R.cache#T,R.cache#mons);
    MminorsTemp := gens minors(2,ZiMat);
    Mminors := for i to numColumns MminorsTemp - 1 list MminorsTemp_(0,i);
    G := gens gb ideal Mminors;
    Glist := for i to numColumns G - 1 list G_(0,i);
    failureList := {};
    for g in Glist do (
        if not f(g,Mminors) then (
            --print("false for g=");
            --print(g);
            --return false
            failureList = append(failureList,g);
        );
    );
    --true
    {failureList,ZiMat,gens R.cache#T,R.cache#mons}
)

failureToBeQuad = method()
failureToBeQuad(List) := gen -> (
    tempOut := {};
    for g in gen do if not degree leadMonomial g == {2} then tempOut = append(tempOut,g);
    tempOut
)

checkIfGroebnerQuad = method()
checkIfGroebnerQuad(ZZ,ZZ) := (n,e) -> (
    R := weighted1n2Veronese(n,e,ZZ/101);
    ZiMat := turnToZiMatrixFromXY(makeGuessXYmatrix(e,R.cache#S),R.cache#S,R.cache#T,R.cache#mons);
    I := minors(2,ZiMat);
    Mminors := gens I;
    Gbasis := gens gb I;
    missingGlist := {};
    f := (m,L) -> (
        for i to numColumns L - 1 do (
            if L_(0,i) == m then return true
        );
        false
    );
    for i to numColumns Gbasis - 1 do (
        if not degree leadMonomial Gbasis_(0,i) == {2} then (
            if not f(Gbasis_(0,i),Mminors) then missingGlist = append(missingGlist,Gbasis_(0,i));
        );
    );
    {(n,e),missingGlist,ZiMat,gens R.cache#T,R.cache#mons}
)




--------------------------------------------------
-- New code to try to make it more flexible ------
--------------------------------------------------
makeLexMonomials = method()
makeLexMonomials(List,ZZ) := (L,d) -> (
    n := #L;
    -- Condition checking on d to make sure we have nothing nonsensical
    if d == 0 then (
        {1}
    );
    if d < 0 then (
        {}
    );
    -- If d is reasonable and we only have one var, we can only return one thing.
    if n == 1 then (
        x := L#0;
        degx := (degree x)#0;
        if d%degx == 0 then (
            return {x^(d//degx)}
        ) else return {};
        -- return an empty list if d is not divisible by degx
    );
    degx1 := (degree L#0)#0;
    flatten for i to d//degx1 list (
        tempList := flatten makeLexMonomials(drop(L,1),i*degx1);
        apply(tempList, m -> ((L#0)^(d-i) * m))
    )
)

weightedVeronese = method()
weightedVeronese(ZZ,ZZ,Ring) := (n,e,kk) -> (
    Stemp := makeP1n2Ring(n,kk);
    genSet := gens Stemp;
    -- Since currently deg(y)=2 for our examples, we will have 
    -- everything by degree 2e since we will have the pure power y^e
    monsTemp := flatten append({y^e},makeLexMonomials(genSet,e));
    --varBlocks := 
    Ttemp := kk[for m in monsTemp list t_m, Degrees => append((for i to #monsTemp - 2 list 1),2), MonomialOrder => {Lex => 1, GRevLex => #monsTemp - 2}];
    Ktemp := ker map(Stemp,Ttemp,monsTemp);
    output := Ttemp/Ktemp;
    output.cache#S = Stemp;
    output.cache#mons = monsTemp;
    output.cache#T = Ttemp;
    output.cache#K = Ktemp;
    output
)

tGuessMat = method()
tGuessMat(ZZ,Ring,List) := (e,S,mons) -> (
    M := makeGuessXYmatrix(e,S);
    transpose matrix(
        for j to numColumns M - 1 list (
            for i to numRows M - 1 list (
                tempOut := 0;
                if j == numColumns M - 1 then (
                    tempOut = t_(mons#0);
                    for m in mons do (
                        for n in mons do (
                            if m * n == M_(i,j) then tempOut = t_m * t_n;
                        );
                    );
                ) else (
                    tempOut = t_(M_(i,j));
                );
                tempOut
            )
        )
    )
)

groebnerCheck = method()
groebnerCheck(ZZ,ZZ,Ring) := (n,e,kk) -> (
    R := weightedVeronese(n,e,kk);
    
)

end
restart
load "conjectureExamples2.m2"
n = 3
e = 3
kk = ZZ/101
R = weightedVeronese(n,e,ZZ/101)
tGuessMat(e,R.cache#S,R.cache#mons)
tempBool = true
gensK = gens R.cache#K
gensGbK = gens gb R.cache#K
tempList = {}
f = (g,L) -> (
    for i to numColumns L - 1 do (
        if L_i == g then return true
    );
    false
)
for i to numColumns gensGbK - 1 do (
    if not f(gensGbK_(0,i),gensK) then tempList = append(tempList,gensGbK_(0,i));
);
#tempList
tempList
apply(tempList, t -> degree leadMonomial t)



end