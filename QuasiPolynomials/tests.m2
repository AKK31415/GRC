TEST ///
    R = QQ[x,y,z,w]
    I = ideal(x*z-y^2, w*y-z^2, x*w-y*z)
    M = module R/I
    assert(quasiPolynomial M == (new QuasiPolynomial from {symbol constituents => {3*t+1}, symbol period => 1, symbol cache => new CacheTable}))
///

TEST ///
    R = QQ[x,y, Degrees => {1,2}]
    M1 = ideal(x,y)
    assert(quasiPolynomial(M1) == new QuasiPolynomial from {symbol constituents => {0}, symbol period => 1, symbol cache => new CacheTable})
    M2 = ideal(x)
    assert(quasiPolynomial(M2) == new QuasiPolynomial from {symbol constituents => {1,0}, symbol period => 2, symbol cache => new CacheTable})
    M3 = ideal(x^6)
    assert(quasiPolynomial(M3) == new QuasiPolynomial from {symbol constituents => {3}, symbol period => 1, symbol cache => new CacheTable})
    M4 = ideal(y)
    assert(quasiPolynomial(M4) == new QuasiPolynomial from {symbol constituents => {1}, symbol period => 1, symbol cache => new CacheTable})
///