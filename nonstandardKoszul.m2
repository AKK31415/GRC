restart

--Given an ideal I in a nonstandard graded polynomial ring, checks whether resolution of k over gr(S/I) is linear for first n steps
checkNonstandardKoszul = (I,n)->(
    --Build associated graded of R=S/I;
    T =  ZZ/101[flatten entries vars ring I];
    J = tangentCone I;
    grI = substitute(J,T);
    grR = T/grI;
    --Resolution of k over associated graded (through step n);
    m = ideal vars grR;
    k = module grR/m;
    r = betti res(k,LengthLimit=>n);
    return (regularity r == 0)
)

--Here's an example which is nonstandard Koszul:
S = ZZ/101[x,y,z,Degrees=>{1,2,3}]
I = ideal(y^3-z^2)
checkNonstandardKoszul(I,10)

--And one that isn't:
I = ideal(y^3-x^6)
checkNonstandardKoszul(I,10)