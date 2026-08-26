restart

-- Method for making the ring with the appropriate weights

makeP1n2Ring = method()

makeP1n2Ring(ZZ,Ring) := (n,kk) -> (
    L := for i to n-1 list 1;
    L = append(L,2);
    R := kk[x_1..x_n,y, Degrees => flatten L];
    R
)



-- Helper method for making all monomials from a list of generators with degree d

makeMonomials = method()

-- This is at best a ZZ graded code and may work on nonstandard gradings, but not multigradings

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

R = QQ[x,y,z, Degrees => {1,1,2}]

makeMonomials({x,y,z},3)



weighted1n2Veronese = method()

weightedVeronese(ZZ,ZZ,Ring) := (n,e,kk) -> (
    R := makeP1n2Ring(n,kk);

)



{*
    R = makeP1n2Ring(3,QQ)
    gens R
    degrees R
    degree y





*}