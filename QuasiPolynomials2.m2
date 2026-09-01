restart
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


--quasiPolyFree(M): takes in a free module over a nonstandard ZZ-graded polynomial ring and outputs the quasi Hilbert polynomial
    --Input: M a free module
    --Output: quasipolynomial
quasiPolyFree = (M) -> (
    degs = flatten degrees M;
    m = numgens M;
    s=ring M;
    alpha= lcm(flatten degrees s);
    qp = quasiPolyRing(s);
    for i from 0 to alpha when i < alpha list(
	L = for k from 0 to m-1 list (
	    j=i-degs_k % alpha;
	    shift = map(T,T,{t-degs_k});
	    shift(qp_j)
	    );
	sum L
	)
    )

--quasiPolynomial(M): takes in a module over a nonstandard ZZ-graded polynomial ring and outputs the quasi Hilbert polynomial
    --Input: M a graded module  (note that if you input an ideal of S this will give the Hilbert series for S/I not for I as a subobject)
    --Output: quasipolynomial
quasiPolynomial = (M) -> (
    F = res M;
    L = for i from 0 to length F list(
	(-1)^i*quasiPolyFree(F_i)	  
	);
    q = L_0;
    for  j from 1 to length F do(
	q = q+L_j
	);
    q
    )
end--

restart 
needs "QuasiPolynomials2.m2"
--Example
T=QQ[t]
R=QQ[x,y, Degrees=>{1,2}]
I = ideal(x)
quasiPolyRing(R)
quasiPolynomial(I)

