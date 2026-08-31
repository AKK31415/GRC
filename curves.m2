restart
d=2
e=2

--Build coordinate ring as a quotient by a determinantal ideal:
L=splice{d:1,e:e}
S = ZZ/101[x_0..x_(d-1),y_0..y_(e-1),Degrees=>L]
M = matrix{{x_0..x_(d-2),x_(d-1)^e,y_0..y_(e-2)},{x_1..x_(d-1),y_0..y_(e-1)}}
I = minors(2,M)
R=S/I

--Resolution of R over S:
r = res I
r.dd_1
betti res I

needsPackage "HHLResolutions"
X = weightedProjectiveSpace(flatten degrees S)
--the 1,1,2,2 are the dgrees of the variables in the target
g = map(ZZ^3,ZZ^1,transpose matrix{{1,3,4}})
--HARD CODING WARNING
--the 1,3,4 are the exponents of the variable t
--That is, this was the d=2, e=2 case where the map was
--[s:t] --> [s^2:st:st^3:t^4] and 1,3,4 are exponents of t
--after ignoring the first coordinate

--And this is the HHL resolution.
--Note that it is very different!!!
HHL = makeHHLResolution(X,g)
r
--But it is NOT minimal.  To minimize you can do:
M = HH_0(HHL);
--This M is the normalization of the Davis-Sobieska
minHHL = res prune M;
betti minHHL
minHHL
minHHL.dd_1
R = ring X
degrees R
gens R
