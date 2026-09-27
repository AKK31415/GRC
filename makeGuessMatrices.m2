load "moreCurves.m2"
makeGuessMatrix = method()
makeGuessMatrix(ZZ,ZZ) := (d,e) -> (
    if not e == 2 then error("Not yet implemented for e != 2");
    normCurve := normalCurve(d,e);
    
)