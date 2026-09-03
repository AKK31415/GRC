doc ///
    Key
        QuasiPolynomials
    Headline
        a package which computes the quasipolynomials of a hilbert series for a multigraded ring and defines the QuasiPolynomial type.
    Description
        Text
            It is well known that the growth of the dimension of the graded pieces in a nonstandard graded polynomial ring follow a quasipolynomial growth. This package is designed to take a nonstandard graded ring and return it's hilbert quasipolynomial, or an ideal and take the hilbert quasipolynomial of the quotient ring. This package defines the QuasiPolynomial type.
///

doc ///
    Key
        QuasiPolynomial
    Headline
        The QuasiPolynomial data type
    Description
        Text
            QuasiPolynomial is a data type implemented in the QuasiPolynomials package. This data type has keys "constituents" and "period".
        Example
            R = QQ[x,y, Degrees => {1,2}]
            
///