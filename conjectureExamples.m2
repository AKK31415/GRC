restart

-- Method for making the ring with the appropriate weights

makeP1n2Ring = method()

makeP1n2Ring(ZZ,Ring) := (n,kk) -> (
    L := for i to n-1 list 1;
    L = append(L,2);
    R := kk[x_1..x_n,y, Degrees => flatten L];
    R
)

-- Want to figure out what the right generalization is when we replace 2 with k
makeP1nkRing = method()

makeP1nkRing(ZZ,ZZ,Ring) := (n,k,kk) -> (
    L := for i to n-1 list 1;
    L = append(L,k);
    R := kk[x_1..x_n,y, Degrees => flatten L];
    R
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
        -- append(makeMonomials(take(L,n-1),d-i*degxn),(L#(n-1))^i)
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
    S = makeP1n2Ring(n,kk);
    genSet := gens S;
    -- Since currently deg(y)=2 for our examples, we will have 
    -- everything by degree 2e since we will have the pure power y^e
    mons = append(makeMonomials(genSet,e),y^e);
    L := for i to #mons-2 list 1;
    L = append(L,2);
    T = kk[z_1..z_(#mons-1),w, Degrees => L];
    K = ker map(S,T,mons);
    T/K
)


makeMatrix = method() -- Method for making the matrix of z's

makeMatrix(ZZ,ZZ) := (n,e) -> (
    if n == 1 then (
        R = weighted1n2Veronese(n,e,ZZ/101);
        if e%2 == 0 then error "Expected odd degree embedding";
        k := e//2; -- so e=2k+1 
        row1 := for i to k list (
            if i == k then (z_(i+1))^2 else z_(i+1)
        );
        row2 := for i to k list (
            if i == k then w else z_(i+2)
        );
        return matrix{row1,row2}
    ) else error "Not yet implemented for n>=2"
)

changeBackToXY = method()

changeBackToXY(Ring,Ring,Ring,Matrix) := (R,S,T,M) -> (
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
                        if mons_(k-1) * mons_(l-1) == M_(i,j) then tempEntry = z_k * z_l;
                    );
                );
                tempEntry
            ),w
        ) else for i to numRows M - 1 list (
            z_(1+position(mons, m -> m == M_(i,j)))
        )
    )
)


end