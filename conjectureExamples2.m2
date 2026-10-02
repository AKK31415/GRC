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

makeP124Ring = method()
makeP124Ring(Ring) := (kk) -> (
    kk[x,y,z, Degrees => {1,2,4}]
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

isAlreadyGenerated = method()
isAlreadyGenerated(List,RingElement) := (L,m) -> ( -- L is gens so far
    isGenerated := false;
    apply(L, l -> (
        if m % l == 0 then (
            if m == l then (isGenerated = true; break) else if isAlreadyGenerated(L,m//l) then (isGenerated = true; break);
        );
    ));
    isGenerated
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
-- Need to fix this method
pruneMonomials(List,List) := (prevMons,mon2) -> (
    -- check the first element now, and do the rest later
    newMon2 := flatten apply(mon2,m -> (
        if isAlreadyGenerated(prevMons,m) then {} else {m}
    ));
    -- if mon2 is empty we neeed not prune
    if #newMon2 == 0 then return prevMons;
    pruneMonomials(prevMons|{newMon2#0},drop(newMon2,1))
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

weighted124Veronese = method()
weighted124Veronese(ZZ,Ring) := (e,kk) -> (
    Stemp := makeP124Ring(kk);
    currentGens := makeMonomials(gens Stemp,e);
    currentDegree := 2*e;
    mOut := {};
    while not mOut == currentGens do (
        mOut = currentGens;
        for i to 3 do (
            currentGens = pruneMonomials(currentGens,makeMonomials(gens Stemp,currentDegree));
            currentDegree += e;
        );
    );
    Ttemp := kk[for m in currentGens list t_m, -*Degrees => (for m in currentGens list (degree m)//e)*-];
    Ktemp := ker map(Stemp,Ttemp,currentGens);
    output := Ttemp/Ktemp;
    output.cache#S = Stemp;
    output.cache#mons = currentGens;
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

factorMomomial = method()
factorMonomial = (monList,m) -> (
    numMons := #monList;
    for i to numMons - 1 do (
        l := monList#(numMons - i - 1);
        if m % l == 0 then (
            if m == l then (return {l});
            tempFactoring := factorMonomial(monList,m//l);
            if not #tempFactoring == 0 then (return append(tempFactoring,l));
        );
    );
    {}
)

make124tMat = method()
make124tMat(ZZ,Ring) := (e,R) -> (
    -- Assuming e = 5 for now
    xyzMat := (transpose matrix{makeMonomials(gens R.cache#S,4)}) * matrix{makeMonomials(gens R.cache#S,e-4)|makeMonomials(gens R.cache#S,2*e-4)|makeMonomials(gens R.cache#S,3*e-4)|makeMonomials(gens R.cache#S,4*e-4)};
    use R.cache#T;
    makeMatT(xyzMat,R)
)

makeMatT = method()
makeMatT(Matrix,Ring) := (M,R) -> (
    use R.cache#T;
    matrix for i to numRows M - 1 list (
        for j to numColumns M - 1 list (
            entry := 1;
            for l in factorMonomial(R.cache#mons,M_(i,j)) do (
                entry *= t_l;
            );
            entry
        )
    )
)

makeMatX1n2 = method()
makeMatX1n2 = (R,e,l) -> ( -- l is lcm maybe
    row := {};
    trimMons := (L1,L2) -> (
        flatten apply(L2, l -> (
            for m in L1 do (
                if l%m == 0 then return {}
            );
            {l}
        ))
    );
    for i to l-1 do (
        row = flatten append(row,trimMons(row,makeMonomials(gens R.cache#S,e*(i+1)-2)));
    );
    (transpose matrix{makeMonomials(gens R.cache#S,2)}) * matrix{row}
)

makeMatX = method()
makeMatX = (R,e,l) -> (
    row := {};
    col := {};
    trimMons := (L1,L2) -> (
        flatten apply(L2, l -> (
            for m in L1 do (
                if l%m == 0 then return {}
            );
            {l}
        ))
    );
    for i to l-1 do (
        row = flatten append(row,trimMons(row,makeMonomials(gens R.cache#S,e*(i+1)-l)));
        col = flatten append(col,trimMons(col,makeMonomials(gens R.cache#S,l+i*e)));
    );
    (transpose matrix{col}) * matrix{row}
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
weightedVeronese(List,Ring,ZZ) := (L,kk,e) -> (
    Stemp := kk[for i to #L-1 list x_i, Degrees => L];
    genSet := gens Stemp;
    -- Since currently deg(y)=2 for our examples, we will have 
    -- everything by degree 2e since we will have the pure power y^e
    monsTemp := {};
    for i to lcm L - 1 do (
        monsTemp = pruneMonomials(monsTemp,makeMonomials(genSet,e*(i+1)));
    );
    --varBlocks := 
    Ttemp := kk[for m in monsTemp list t_m];
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
-- Developing
restart
load "conjectureExamples2.m2"
e = 5
kk = ZZ/101
WV = weighted124Veronese(e,kk)

M = make124tMat(e,WV)
minors(2,M) == WV.cache#K
I = minors(2,M);
J = WV.cache#K;
numColumns gens gb I
numColumns gens gb J
gI = gens gb I
gJ = gens gb J
flatten for i to numColumns gI - 1 list (
    if isMember(gI_(0,i),J) then {} else gI_(0,i)
)
flatten for i to numColumns gJ - 1 list (
    if isMember(gJ_(0,i),I) then {} else gJ_(0,i)
)

netList for i to 3 list (
    for j to 4 list (
        flatten degrees weighted124Veronese(4*j+i,ZZ/101)
    )
)
WV.cache#K
gens oo
numColumns oo

restart
load "conjectureExamples2.m2"
R = ZZ/101[x,y]
f = x^5*y
L = {x^2,x*y}
factorMonomial(L,f)


restart
load "conjectureExamples2.m2"
e = 5;
kk = ZZ/101;
L = {1,2,4};
R = weightedVeronese(L,kk,e);
xMat = makeMatX(R,e,lcm L);
tMat = makeMatT(xMat,R);
I = minors(2,tMat);
J = R.cache#K;
I == J
gI = gens gb I;
gJ = gens gb J;
numColumns gI
numColumns gJ
flatten for i to numColumns gI - 1 list (
    if isMember(gI_(0,i),J) then {} else gI_(0,i)
)
flatten for i to numColumns gJ - 1 list (
    if isMember(gJ_(0,i),I) then {} else gJ_(0,i)
)

restart
load "conjectureExamples2.m2"
e = 5;
kk = ZZ/101;
L = {1,1,2,2}
R = weightedVeronese(L,kk,e);
xMat = makeMatX(R,e,lcm L);
tMat = makeMatT(xMat,R);
I = minors(2,tMat);
J = R.cache#K;
use R.cache#T;
checkNonstandardKoszul(J,10)
I == J
gI = gens gb I;
gJ = gens gb J;
numColumns gI
numColumns gJ
flatten for i to numColumns gI - 1 list (
    if isMember(gI_(0,i),J) then {} else gI_(0,i)
)
flatten for i to numColumns gJ - 1 list (
    if isMember(gJ_(0,i),I) then {} else gJ_(0,i)
)
#oo