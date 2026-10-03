S = QQ[x_0,x_1,x_2,x_3, Degrees => {1,1,2,3}]
pointIdeal = (a,b,c)->(
    radical ideal(b*x_0-a*x_1, c*x_0^2 - a^2*x_2,  c*x_0*x_1 - a*b*x_2, c*x_1^2 - b^2*x_2,
        x_0^3 - a^3*x_3, x_1^3 -b^3*x_3, x_2^3 - c^3*x_3^2)
    )
I =  pointIdeal(1,2,3)
isPrime I
codim I

J = intersect apply(11, i -> pointIdeal(random(10),random(10),random(10)));
betti res J


testIsSparse = N ->(
    tally apply(10,j->(
            J = intersect apply(N, i -> pointIdeal(random(10),random(10),random(10)));
            betti res J
            ))
    )
testIsSparse(2)
testIsSparse(3)
testIsSparse(4)
testIsSparse(5)
testIsSparse(6)
testIsSparse(7)
testIsSparse(8)
testIsSparse(9)
netList for n from 2 to 9 list (
    {n,testIsSparse(n)}
)