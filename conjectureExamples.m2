restart

-- Method for making the ring with the appropriate weights

makeP1n2Ring = method()

makeP1n2Ring(ZZ,Ring) := (n,kk) -> (
    L := for i to n-1 list 1;
    L = append(L,2);
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
    R := makeP1n2Ring(n,kk);
    genSet := gens R;
    -- Since currently deg(y)=2 for our examples, we will have 
    -- everything by degree 2e since we will have the pure power y^e
    mons := append(makeMonomials(genSet,e),y^e);
    L := for i to #mons-2 list 1;
    L = append(L,2);
    T := kk[z_1..z_(#mons-1),w, Degrees => L];
    T/(ker map(R,T,mons))
)



{*


R = makeP1n2Ring(3,QQ)
gens R
degrees R
degree y



R = QQ[x,y,z, Degrees => {1,1,2}]

makeMonomials({x,y,z},3)


mon1 = makeMonomials({x,y,z},4)
mon2 = makeMonomials({x,y,z},8)
monOut = pruneMonomials(mon1,mon2)
for i to 6 list (
    mon1 = makeMonomials({x,y,z},2*i+1);
    mon2 = makeMonomials({x,y,z},4*i+2);
    pruneMonomials(mon1,mon2)
)



*}