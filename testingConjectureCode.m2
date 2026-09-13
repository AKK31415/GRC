restart
load "conjectureExamples.m2"

R = weighted1n2Veronese(5,3,ZZ/101)
gens R
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
use S
N = matrix for i to (numRows M) - 1 list (
    for j from (numColumns M) - 1 list (
        tempOut := z_1;
        if j == (numColumns M)-1 then (
            if i == (numRows M)-1 then (
                tempOut = y^e;
            ) else (
                
            )
        ) else (
            tempIndex := 0;
            for k to #(gens T) - 1 do (
                if (gens T)#k == M_(i,j) then tempIndex = k;
            );
            mons#tempIndex
        )
    )
)


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


