newPackage(
    "QuasiPolynomials",
    AuxiliaryFiles => true,
    PackageImports => {"OldChainComplexes"},
    Version => "1.0", 
    Date => "August 31, 2026",
    Keywords => {"Hilbert"},
    Authors => {
        {Name => "Andrew Karsten", 
         Email => "akk0071@auburn.edu"},
        {Name => "Ben Betts",
         Email => "fraughn@unm.edu",
         HomePage => ""},
        {Name => "Isadora Bailey",
         Email => "",
         HomePage => ""}
    },
    Headline => "Methods for computing quasi-polynomials"
)

export {
    
    -- types
    "QuasiPolynomial",

    -- methods
    "quasiPolynomial",

    --symbols
    "constituents", --Stanley's term for the polynomials in the list
    "period"

    
}

--private ring for constituents to live in
T := QQ[getSymbol "t"];
t := T_0;


------------------------------------------------
-- Typing for Quasi polys
----------------------------------------------

QuasiPolynomial = new Type of HashTable

quasiPolynomial = method(TypicalValue => QuasiPolynomial)
--constructor from a list of polys. consituent i tells the coefficients (i mod period)
--automatically reduce to the actual period if overdetermined

quasiPolynomial List := L -> (
    if #L ==0 then error "nonempty list expected for quasiPolynomial";

    L' := apply(L, p -> sub(p, T));
    n := #L';

    --reduce to minimal period by finding smallest divisor e of n
    --such that the list repeats every e entries
    minPer := n;
    for e from 1 to n do (
        if n % e !=0 then continue;
        if all(n, i -> L'#i == L'#(i % e)) then (
            minPer = e;
            break;
            );
        );

    new QuasiPolynomial from {
        symbol constituents => take(L', minPer),
        symbol period => minPer,
        --This cache symbol is standard and useful for if we eventually have a
        --quasiPolynomial method that is expensive and we want to call it multiple
        --times for the same instance of the object. 
        symbol cache => new CacheTable
    }
)

--casting: a polynomial or scalar is a quasipoly with period 1

quasiPolynomial RingElement := f -> quasiPolynomial {f}
quasiPolynomial ZZ := n -> quasiPolynomial {n*1_T}
quasiPolynomial QQ := q -> quasiPolynomial {q*1_T}


--printing: we might fiddle with this a bit for what looks best.
--for now its simply 1 line for each poly in the quasipoly
net QuasiPolynomial := Q -> (
    if Q.period == 1 then net Q.constituents#0
    else stack apply(Q.period, i -> (toString i | ": ") | net Q.constituents#i)
)

toString QuasiPolynomial := Q -> toString apply(Q.constituents, toString)

--evaluate the quasipoly Q(n) picks the right constituent to evaluate at n
QuasiPolynomial ZZ := (Q,n) -> (
    ev := map(QQ, T, {promote(n,QQ)});
    ev Q.constituents#(n % Q.period)
)

--degree of quasi polynomial is the max degree of its constituents
--I think they should be the same but this is safer
degree QuasiPolynomial := Q -> max apply(Q.constituents, p -> first degree p)


-------------------------------------------
--arithmetic with quasi polys
------------------------------------

--equality of quasi polys is same period, same constituents
QuasiPolynomial == QuasiPolynomial := (Q, R) -> (
    Q.period == R.period and Q.constituents == R.constituents
)

--addition of quasi polys
QuasiPolynomial + QuasiPolynomial := (Q,R) -> (
    p := lcm(Q.period, R.period);
    quasiPolynomial apply(p, i -> 
        Q.constituents#(i % Q.period) + R.constituents#(i % R.period))
)

--negative quasi poly
- QuasiPolynomial := Q -> quasiPolynomial apply(Q.constituents, p -> -p)

--subtraction of quasi poly
QuasiPolynomial - QuasiPolynomial := (Q,R) -> Q + (-R)

--multiplication of quasi polys
QuasiPolynomial * QuasiPolynomial := (Q,R) -> (
    p := lcm(Q.period, R.period); --new period
    quasiPolynomial apply(p, i -> 
        Q.constituents#(i % Q.period) * R.constituents#(i % R.period))
)


--scaling properties
ZZ * QuasiPolynomial := (c,Q) -> quasiPolynomial apply(Q.constituents, p -> c*p)
QQ * QuasiPolynomial := (c,Q) -> quasiPolynomial apply(Q.constituents, p -> c*p)
--right is same as left scalar multiplication
QuasiPolynomial * ZZ := (Q,c) -> c * Q
QuasiPolynomial * QQ := (Q, c) -> c*Q

------------------------------------
-- Hilbert quasi polys
-----------------------------------
--quasiPolynomial(S): input: S = nonstandard ZZ-graded poly ring
--output: Quasi Polynomial
quasiPolynomial PolynomialRing := S -> (
    --if this has been computed for the instance previously, return it
    if S.?cache and S.cache#?QuasiPolynomial then return S.cache#QuasiPolynomial;
    if degreeLength S !=1 then error "quasiPolynomial expects singly ZZ-graded ring";
    if any(flatten degrees S, d-> d<=0) then error "quasiPolynomial expects generators of positive degree only";
    alpha := lcm flatten degrees S;
    n := numgens S;
    Q := quasiPolynomial for i from 0 to alpha-1 list (
        pts := apply(n+2, j -> (j+1)*alpha + i);
        mat := sub(matrix apply(n+2, k -> apply(n+2, j -> pts_k^j)), QQ);
        vals := sub(transpose matrix {apply(n+2, k -> hilbertFunction((k+1)*alpha+i, S))}, QQ);
        coeffs := solve(mat,vals);
        sum(n+2, j -> coeffs_(j,0) *t^j)
        );

    if not S.?cache then S.cache = new CacheTable;
    S.cache#QuasiPolynomial = Q
)

--quasiPolyFree(M,S) takes free module over nonstandard ZZ-graded ring
--outputs quasipolynomial

quasiPolyFree := (M,S) -> (
    degs := flatten degrees M;
    m := numgens M;
    alpha := lcm flatten degrees S;
    qp := quasiPolynomial S;
    if m == 0 then return quasiPolynomial {0_T};
    quasiPolynomial for i from 0 to alpha - 1 list (
        L := for k from 0 to m-1 list (
            j := (i - degs_k) % alpha;
            shift := map(T, T, {t - degs_k});
            shift qp.constituents#j
        );
        sum L
    )
)

--quasiPolynomial(M) input module over nonstandard ZZ-graded poly ring
-- output quasiPolynomial 

quasiPolynomial Module := M -> (
    S := ring M;
    if not isPolynomialRing S then error "quasiPolynomial expects module over polynomial ring";
    if not isHomogeneous M then error "quasiPolynomial expects homogeneous module";
    F := res M;
    L := for i from 0 to length F list (
        (-1)^i * quasiPolyFree(F_i, S)
    );
    q := L_0;
    for j from 1 to length F do (
        q = q + L_j
    );
    q
)

--for ideal I give quasi Polynomial of S/I
quasiPolynomial Ideal := I -> quasiPolynomial comodule I

beginDocumentation()
load "./QuasiPolynomials/docs.m2"
