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

makeMonomials(List,ZZ) := (L,d) -> (
    n := #L;
    -- Condition checking on d to make sure we have nothing nonsensical
    if d == 0 then return list 1
    if d < 0 then return {}
    -- If d is reasonable and we only have one var, we can only return one thing.
    if n == 1 then (
        x := L#0;
        degx := degree x;
        return list x^(d/degx)
    );
    
)



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