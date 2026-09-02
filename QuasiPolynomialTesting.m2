restart 
needs "QuasiPolynomials2.m2"
T=QQ[t]
--Notes:
  --In M2's Hilbert Polynomial code they include ways to calculcate projective Hilbert Polynomials, what are these?
  --Code cannot handle degree zero variables (or negative degree variables), should add error message if this is used as input (I don't know how to do this)
  --As a biproduct of the fact that res I computes the resolution of S/I when working with an ideal, might be worth adding some sort of error message for this too
--Example #1 - standard graded setting, twisted cubic
R=QQ[x,y,z,w]
I = (x*z-y^2, w*y-z^2, x*w-y*z)
M = module R/I
hilbertPolynomial(M, Projective=> false)
quasiPolynomial(M)
--These agree and their output in 3t+1

--Example #2
R=QQ[x,y, Degrees=>{1,2}]
M1 = ideal(x,y)
quasiPolynomial(M1)
--Yields {0,0}
M2= ideal(x)
quasiPolynomial(M2)
--Yields {1,0}
M3=ideal(x^6)
quasiPolynomial(M3)
--Yields {3,3}
M4=ideal(y)
quasiPolynomial(M4)
--Yields {1,1}

--Example #3
R=QQ[x,y,Degrees=>{0,1}]
quasiPolynomial(R^{0})
--Gives empty list, need to do something to make this not an issue (like add an error or something)

