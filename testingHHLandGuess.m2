load "moreCurves.m2";
for d to 6 do (
    Mguess := minimizeMatrix columnOps(makeGuessFullMatrix(d,2,ZZ/101),d);
    Mhhl := (normalCurve(d,2))_3;
    print(Mguess == Mhhl);
    print("\n");
);
end