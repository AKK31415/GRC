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


end
--------------------------------------------------------------------
-- Helper function to make the matrix
--------------------------------------------------------------------
makeCandidates = method()

makeCandidates(ZZ,List,Variable,Variable,Variable,Ideal) := (m,L,x,y,z,I) -> (
    candidates := {};
    if m > #L then m=#L;
    for i from 1 to m do (
        if isMember(L#i*z-x*y,I) then candidates = append(candidates,L#i);
    );
    if #candidates != 1 then print("There was not only one option");
    candidates
)


makeColCandidates = (m,x_1,L,x_3,I) -> (
    n := #L;
    for i to n-1 list makeCandidates(m,x_1,L#i,x_3,I)
)


makeLeftHalf = (m,R,L) -> (
    #R := sizeR;
    for j to sizeR - 1 list (
        makeColCandidates(m,R#j,L,w,I)
    )
)















end -- Development and testing down here
restart
load "conjectureExamples.m2"


R = weighted1n2Veronese(1,3,ZZ/101)
R = weighted1n2Veronese(1,5,ZZ/101)
for i to 5 list weighted1n2Veronese(1,2*(i+3)+1,ZZ/101)
R = weighted1n2Veronese(2,3,ZZ/101)
I = ideal R
gens I
f = z_1*z_6^2-z_3*z_5^2
g = z_2*z_6^2-z_4*z_5^2
-- The new relations from the 2x2 minors of the matrix are not actually new


R = weighted1n2Veronese(2,5,ZZ/101)
I = ideal R
gens I
M = matrix{{z_1,z_2,z_3,z_4,z_7,z_8,z_11^2},{z_2,z_3,z_4,z_5,z_8,z_9,z_11*z_12},{z_3,z_4,z_5,z_6,z_9,z_10,z_12^2},{z_7,z_8,z_9,z_10,z_11,z_12,w}}
J = minors(2,M)
J


R = weighted1n2Veronese(2,7,ZZ/101)
K
use T
I = ideal R
gens I

S = ZZ/101[x_1..x_20,y]


row1 = {};
row2 = {};
row3 = {};
row4 = (
    tempList := for i from 9 to 20 list z_i;
    append(tempList,w)
);
for i from 1 to 6 do (
    row1 = append(row1,z_i);
    row2 = append(row2,z_(i+1));
    row3 = append(row3,z_(i+2));
);
for i from 9 to 12 do (
    row1 = append(row1,z_i);
    row2 = append(row2,z_(i+1));
    row3 = append(row3,z_(i+2));
);
for i from 15 to 16 do (
    row1 = append(row1,z_i);
    row2 = append(row2,z_(i+1));
    row3 = append(row3,z_(i+2));
);
row1 = append(row1,z_19^2);
row2 = append(row2,z_19*z_20);
row3 = append(row3,z_20^2);
M = matrix{row1,row2,row3,row4}
J = minors(2,M)


restart
load "conjectureExamples.m2"
R = weighted1n2Veronese(2,9,ZZ/101)
gens R
use T
row1 = {}
row2 = {}
row3 = {}
row4 = (
    tempList := for i to 19 list z_(11+i);
    append(tempList,w)
)
for i to 3 do (
    for j to 8-2*i-1 do (
        k := (
            if i == 0 then 1 else if i == 1 then 11 else if i == 2 then 19 else 25
        );
        row1 = append(row1,z_(k+j));
        row2 = append(row2,z_(k+j+1));
        row3 = append(row3,z_(k+j+2));
    )
)
row1 = append(row1,z_29^2)
row2 = append(row2,z_29*z_30)
row3 = append(row3,z_30^2)
M = matrix{row1,row2,row3,row4}
J = minors(2,M)
K == J

restart
load "conjectureExamples.m2"
R = weighted1n2Veronese(3,3,ZZ/101)
I = ideal R
use T
M = matrix{{z_1,z_2,z_5,z_11^2},{z_2,z_3,z_6,z_11*z_12},{z_3,z_4,z_7,z_12^2},{z_5,z_6,z_8,z_11*z_13},{z_6,z_7,z_9,z_12*z_13},{z_8,z_9,z_10,z_13^2},{z_11,z_12,z_13,w}}
J = minors(2,M)
K == J

restart
load "conjectureExamples.m2"
R = weighted1n2Veronese(4,3,ZZ/101)
I = ideal R
use T
M = matrix{{z_1,z_2,z_5,z_11,z_21^2},
            {z_2,z_3,z_6,z_12,z_21*z_22},
            {z_3,z_4,z_7,z_13,z_22^2},
            {z_5,z_6,z_8,z_14,z_21*z_23},
            {z_6,z_7,z_9,z_15,z_22*z_23},
            {z_8,z_9,z_10,z_16,z_23^2},
            {z_11,z_12,z_14,z_17,z_21*z_24},
            {z_12,z_13,z_15,z_18,z_22*z_24},
            {z_14,z_15,z_16,z_19,z_23*z_24},
            {z_17,z_18,z_19,z_20,z_24^2},
            {z_21,z_22,z_23,z_24,w}}
J = minors(2,M)
K == J









-----------------------------------------------------------------
-- Testing S^(5) with S = k[x_1,x_2,x_3,y, Degrees => {1,1,1,2}]
-----------------------------------------------------------------


restart
load "conjectureExamples.m2"
R = weighted1n2Veronese(3,5,ZZ/101)
I = ideal R
use T
for i from 12 to 22 list (
    if isMember(z_i*w-z_31*z_33*z_34,I) then i
)
for i from 27 to 30 list (
    tempList := {};
    for j from 8 to 25 do (
        if isMember(z_j*w-z_i*z_32^2,I) then tempList = append(tempList,(i,j))
    );
    tempList
)
for i from 4 to 30 list (
    tempList = {};
    if isMember(z_20*z_32-z_i*z_31,I) then tempList = append(tempList,i);
    tempList
)

row1 = {};
row2 = {};
row3 = {};
row4 = {};
row5 = {};
row6 = {};
row7 = {};
for i from 1 to 4 do (
    row1 = append(row1,z_i);
    row2 = append(row2,z_(i+1));
    row3 = append(row3,z_(i+2));
)
for i from 7 to 9 do (
    row1 = append(row1,z_i);
    row2 = append(row2,z_(i+1));
    row3 = append(row3,z_(i+2));
)
for i from 12 to 13 do (
    row1 = append(row1,z_i);
    row2 = append(row2,z_(i+1));
    row3 = append(row3,z_(i+2));
)
for i from 16 to 16 do (
    row1 = append(row1,z_i);
    row2 = append(row2,z_(i+1));
    row3 = append(row3,z_(i+2));
)
for i from 22 to 23 do (
    row1 = append(row1,z_i);
    row2 = append(row2,z_(i+1));
    row3 = append(row3,z_(i+2));
)
for i from 26 to 26 do (
    row1 = append(row1,z_i);
    row2 = append(row2,z_(i+1));
    row3 = append(row3,z_(i+2));
)
row1 = append(row1,z_32^2);
row2 = append(row2,z_32*z_33);
row3 = append(row3,z_33^2);
for i from 7 to 10 do (
    row4 = append(row4,z_i);
    row5 = append(row5,z_(i+1));
)
for i from 12 to 14 do (
    row4 = append(row4,z_i);
    row5 = append(row5,z_(i+1));
)
for i from 16 to 17 do (
    row4 = append(row4,z_i);
    row5 = append(row5,z_(i+1));
)
for i from 19 to 19 do (
    row4 = append(row4,z_i);
    row5 = append(row5,z_(i+1));
)
for i from 26 to 27 do (
    row4 = append(row4,z_i);
    row5 = append(row5,z_(i+1));
)
for i from 29 to 29 do (
    row4 = append(row4,z_i);
    row5 = append(row5,z_(i+1));
)
row4 = append(row4,z_32*z_34);
row5 = append(row5,z_33*z_34);
for i from 12 to 21 do (
    row6 = append(row6,z_i);
)
for i from 29 to 31 do (
    row6 = append(row6,z_i);
)
row6 = append(row6,z_34^2);
for i from 22 to 34 do (
    row7 = append(row7,z_i);
)
row7 = append(row7,w);

M = matrix{row1,row2,row3,row4,row5,row6,row7}

J = minors(2,M)
K == J

netList for i from 1 to 6 list (
    tempList := {};
    for j from 1 to 31 do (
        if isMember(z_(15+i)*z_34-z_31*z_j,I) then tempList = append(tempList,(i,j));
    );
    tempList
)





makeId = n -> (
    rows := for i to n-1 list (
        for j to n-1 list (
            if i == j then 1 else 0
        )
    );
    matrix rows
)




J = minors(2,M)

for i from 1 to 3 list (
    R = weighted1n2Veronese(2,2*i+1,ZZ/101);
    I = ideal R;
    gens I
)







--------------------------------------------------------------
-- Trying to write code to help automate making the matrix
--------------------------------------------------------------













tangentCone ideal R



makeNxNid = n -> (
    tempRows := {};
    for i to n-1
)


S = ZZ/101[x_1..x_6,y]
f = map(R,S,)






factorial = n -> (
    if n == 1 then return 1 else return n*factorial(n-1)
)

choose = (n,k) -> (
    factorial(n)/(factorial(k)*factorial(n-k))
)

choose(4,3)
choose(5,3)
choose(6,3)
choose(7,3)
choose(8,3)
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

restart
R = ZZ[n]
ker matrix{{1,-n,1,0},{0,1,0,1}}


V = weighted1n2Veronese(1,1,QQ)
gens V
degree z_1
degree w
tangentCone ideal(z_1,w)


