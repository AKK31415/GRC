newPackage(
    "QuasiPolynomials",
    AuxiliaryFiles => true,
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

--Type definition
QuasiPolynomial = new Type of HashTable

quasiPolynomial = method(TypicalValue => QuasiPolynomial)
--constructor from a list of polys. consituent i tells the coefficients (i mod period)
--automatically reduce to the actual period if overdetermined

quasiPolynomial List := L -> (
    if #L ==0 then error "nonempty list expected for quasiPolynomial";

    L' := apply(L, p -> sub(p, T));
    n := $L';

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
quasiPolynomial QQ :- q -> quasiPolynomial {q*1_T}


--printing: we might fiddle with this a bit for what looks best.
--for now its simply 1 line for each poly in the quasipoly
net QuasiPolynomial := Q -> (
    if Q.period == 1 then net Q.constituents#0
    else stack apply(Q.period, i -> (toString i | ": ") | net Q.constituents#i)
)


--quasiPolyRing(S): takes in a nonstandard ZZ-graded polynomial ring and outputs the quasi-Hilbert polynomial
  --Input: S = nonstandard ZZ-graded polynomial ring
  --Output: quasipolynomial
quasiPolyRing = (S) -> (
    alpha= lcm(flatten degrees S);
    n = numgens S;
    for i from 0 to alpha when i < alpha list (
	pts = apply(n+2, j->((j+1)*alpha+i));
	mat = sub(matrix(apply(n+2, k->apply(n+2, j->pts_k^j))), QQ);
	vals=transpose(matrix{apply(n+2, k->hilbertFunction((k+1)*alpha+i,S))});
	coeffs = sub(inverse(mat)*vals, T);
	quasipoly = 0;
	for j from 0 to n+1 do(
	    quasipoly = quasipoly + coeffs_(j,0)*t^j
	    );
	quasipoly
	)
    )


--quasiPolyFree(M,S): takes in a free module over a nonstandard ZZ-graded polynomial ring and outputs the quasi Hilbert polynomial
    --Input: M a free module, S a nonstandard ZZ-graded polynomial ring
    --Output: quasipolynomial
quasiPolyFree = (M, S) -> (
    degs = flatten degrees M;
    m = numgens M;
    alpha= lcm(flatten degrees S);
    qp = quasiPolyRing(S);
    for i from 0 to alpha when i < alpha list(
	L = for k from 0 to m-1 list (
	    j=i-degs_k % alpha;
	    qpList = toList qp_j;
	    shift = map(T,T,{t-degs_k});
	    shift((1/alpha)*qpList_0)
	    );
	sum L
	)
    )

--quasiPolynomial(M,S): takes in a module over a nonstandard ZZ-graded polynomial ring and outputs the quasi Hilbert polynomial
    --Input: M a graded module, S a nonstandard ZZ-graded polynomial ring (note that if you input an ideal of S this will give the Hilbert series for S/I not for I as a subobject)
    --Output: quasipolynomial
quasiPolynomial = (M, S) -> (
    F = res M;
    L = for i from 0 to length F list(
	(-1)^i*quasiPolyFree(F_i,S)	  
	);
    q = L_0;
    for  j from 1 to length F do(
	q = q+L_j
	);
    q
    )



beginDocumentation()
load "./QuasiPolynomials/docs.m2"