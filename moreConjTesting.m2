load "conjectureExamples.m2";
failures = (
    temp := {};
    for i to 4 do (
        for j to 3 do (
            L := checkIfGroebnerQuad(i+1,2*j+3);
            if not #(L_1) == 0 then temp = append(temp,L);
        );
    );
    temp
);
print("#failures=");
print(#failures);
print("\n");
for f in failures do (
    print("(n,e)=");
    print(f_0);
    print("\nSize of missingGlist=");
    print(#(f_1));
    print("\n");
)



end
load "conjectureExamples.m2";
failures = (
    temp := {};
    for i to 2 do (
        for j to 2 do (
            L := checkIfGroebner(i+1,2*j+3);
            if not #(L_0) == 0 then temp = append(temp,append(L,(i+1,2*j+3)));
        );
    );
    temp
);
for f in failures do (
    print("Failure at (n,e)=");
    print((f_4));
    print("\n");
    print("Missing things below\n");
    print(tex f_0);
    print("\nThe matrix was \n");
    print(tex f_1);
    print("\n");
    print("The corresponding monomials are:\n");
    print(tex f_2);
    print(tex f_3);
    print("\n");
)




end
load "conjectureExamples.m2";
L1 = checkIfGroebner(3,3);
print(#(L1_0));
print("\n");
L2 = checkIfGroebner(3,5);
print(#(L2_0));











end
failures = (
    temp := {};
    for i to 2 do (
        for j to 2 do (
            L := checkIfGroebner(i+1,2*j+3);
            if not #(L_0) == 0 then temp = append(temp,L);
        );
    );
    temp
);
print(#failures)