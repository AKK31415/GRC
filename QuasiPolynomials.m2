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
         Email => "",
         HomePage => ""},
        {Name => "Isadora Bailey",
         Email => "",
         HomePage => ""}
    },
    Headline => "Methods for computing quasi-polynomials"
)

export {
    -*
    -- types
    -- Leaving these as examples right now
    "YoungDiagram",
    "YoungTableau",
    "SkewDiagram",
    -- methods
    "youngDiagram",
    "youngTableau",
    -- symbols
    -- "Weak"
    *-
}

-*
QuasiPoly = new Type of List;
makeQuasiPoly = method(TypicalValue => QuasiPoly);
makeQuasiPoly(ZZ, ZZ) := QuasiPoly => (deg, idx) -> (
    new CGVertex from {symbol degree => deg, symbol index => idx, symbol weight => null, symbol label => null}
);

makeVerCGtex(ZZ, ZZ, Thing) := CGVertex => (deg, idx, wt) -> (
    new CGVertex from {symbol degree => deg, symbol index => idx, symbol weight => wt, symbol label => null}
);
*-


T=QQ[t]
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