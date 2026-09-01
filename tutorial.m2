needsPackage "QuasiPolynomials"

-- construct by hand from a list of polynomials in QQ[t]
R = QQ[t]
Q = quasiPolynomial {t, t+1}       -- period 2
Q.period
Q.constituents

-- period is reduced automatically
quasiPolynomial {t, t, t, t}       -- comes back with period 1

-- casts: polynomials and scalars are period-1 quasipolynomials
quasiPolynomial (t^2+1)
quasiPolynomial 5
quasiPolynomial (3/2)

-- evaluation: picks the constituent for n mod period, plugs in n
Q(4)                               -- uses constituent 0: gives 4
Q(7)                               -- uses constituent 1: gives 8

-- degree
degree Q

-- arithmetic
Q + Q
Q * Q
2*Q
Q - Q == quasiPolynomial 0         -- true
Q == quasiPolynomial {t, t+1}      -- true

-- Hilbert quasipolynomial of a nonstandard graded polynomial ring
S = QQ[x,y,z, Degrees => {1,2,3}]
QS = quasiPolynomial S             -- period 6
QS(10) == hilbertFunction(10, S)   -- true

-- standard grading gives an honest polynomial (period 1)
quasiPolynomial(QQ[a,b,c])

-- modules and ideals
quasiPolynomial S^{-1,-2}          -- twisted free module
I = ideal(x^2, y)
quasiPolynomial I                  -- quasipolynomial of S/I
quasiPolynomial comodule I == quasiPolynomial I   -- true
