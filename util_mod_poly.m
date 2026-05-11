function classic_modpoly(ell)
    // This reads in the modular polynomial ell.
    ZZ<X,Y> := PolynomialRing(Integers(), 2);
    ret := AssociativeArray();
    try 
        input := Open(Sprintf("mod_polys/phi_j_%o.txt",ell),"r");
    catch e 
        print("No modular polynomial file found. Using Magma's database instead...");
        return Evaluate(ClassicalModularPolynomial(ell), [X,Y]);
    end try;
    s := Read(input);
    arr := Split(s,"\n");
    for st in arr do
        ij_c := Split(Substring(st,2,#st),"] ");
        c := StringToInteger(ij_c[2]);
        i,j := Explode(<StringToInteger(dat) : dat in Split(ij_c[1],",")>);
        ret[<i,j>] := c; ret[<j,i>] := c;
    end for;
    return &+[ret[dat]*X^(dat[1])*Y^(dat[2]) : dat in Keys(ret)];
end function;

function gam2_modpoly(ell)
    assert IsPrime(ell) and ell gt 3;
    try
        I := Open(Sprintf("mod_polys/phi_gam2_%o.dat",ell),"r"); _,ret := ReadObjectCheck(I); return ret; 
    catch e 
        print(Sprintf("Could not find file mod_polys/phi_gam2_%o.dat...",ell));
    end try;
    R<X,Y> := PolynomialRing(Integers(), 2);
    temp := Evaluate(classic_modpoly(ell), [X^3, Y^3]);
    ret := Factorization(temp)[1][1];

    I := Open(Sprintf("mod_polys/phi_gam2_%o.dat",ell),"w"); WriteObject(I,ret);
    return ret;
end function;

function gam3_modpoly(ell)
    assert IsPrime(ell) and ell gt 3;
    try
        I := Open(Sprintf("mod_polys/phi_gam3_%o.dat",ell),"r"); _,ret := ReadObjectCheck(I); return ret; 
    catch e 
        print(Sprintf("Could not find file mod_polys/phi_gam3_%o.dat...",ell));
    end try;
    R<X,Y> := PolynomialRing(Integers(), 2);
    temp := Evaluate(classic_modpoly(ell), [X^2+1728, Y^2+1728]);
    // Now, recall that by Eichler-Shimura, we will have it reduce mod p to (X-Y^p)(X^p-Y) = 0.
    // We should have that the coefficient of X^pY^p is -1 mod p.
    temptemp := Factorization(temp);
    eps := (MonomialCoefficient(temptemp[1][1], X^ell*Y^ell) + 1) mod ell eq 0 select 0 else 1;
    ret := temptemp[1+eps][1];

    I := Open(Sprintf("mod_polys/phi_gam3_%o.dat",ell),"w"); WriteObject(I,ret);
    return ret;
end function;