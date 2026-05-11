easy_bintree := recformat<
    poly:RngUPolElt,
    children:SeqEnum
>;

function precompute(a, n)
    // Let R_i denote "X-(a+i)". This function computes the binary tree
    // R_0 R_1 ... R_{2^n-1}
    // R_0*R_1 R_2*R_3 ...
    // ...
    // R_0*R_1*...*R_{2^n-1}.
    try
        I := Open(Sprintf("lagranges/tree_%o_%o.dat",2^n,a),"r"); _,ret := ReadObjectCheck(I); return ret; 
    catch e 
        print(Sprintf("Could not find file lagranges/tree_%o_%o.dat...",2^n,a));
    end try;
    ZZ := Integers(); CC := ComplexField();
    M := 2^n; assert ((a-1) mod M) eq 0;
    R<x> := PolynomialRing(Rationals());
    if n eq 0 then ret := rec<easy_bintree|poly:=x-a,children:=[]>;
    else 
        left := precompute(a, n-1); right := precompute(ZZ!(a+M/2), n-1);
        ret := [left, right];
        d := ZZ!(M/2);
        A := AbelianGroup([3*d]); 
        io := AssociativeArray(); for i in [0..3*d-1] do io[i] := i*A.1; end for;
        ioinv := AssociativeArray(); for i in [0..3*d-1] do ioinv[i*A.1] := i; end for;
        f1 := map<A -> CC | x :-> (r le d) select Coefficient(left`poly, r) else 0 where r := ioinv[x]>;
        f2 := map<A -> CC | x :-> (r le d) select Coefficient(right`poly, r) else 0 where r := ioinv[x]>; 
        prod := poly_mult(f1, f2); 
        try prod := R![strict_round(prod(io[i])) : i in [0..2*d]]; catch e Error("Not enough precision!!"); bad := 0; bad2 := 1/bad; end try;
        ret := rec<easy_bintree|poly:=prod,children:=ret>;
    end if;

    I := Open(Sprintf("lagranges/tree_%o_%o.dat",2^n,a),"w"); WriteObject(I,ret);
    return ret;
end function;

function poly_interp_consec(a, betas : bottom := true, polys := [], facts := [])
    // Given a number "a" and an array "betas" of some size 2^n, this function outputs a degree 2^n-1 polynomial F such that F(a+i-1) = betas[i] for i=1,2,...2^n.
    // facts is a list of factorials starting with 0. so facts[i] := (i-1)!.  
    // if bottom then print betas; end if;
    M := #betas; 
    ZZ<X> := PolynomialRing(Integers());
    if M eq 1 then return betas[1]; end if;
    assert IsPrimePower(M); _,p,n := IsPrimePower(M); assert(p eq 2); M2 := Integers()!(M/2);
    if bottom then 
        polys := rec<easy_bintree|poly:=ZZ!0,children:=[precompute(a,n-1),precompute(a+M2,n-1)]>;
        facts := [1]; for i in [1..M+1] do Append(~facts, facts[#facts]*#facts); end for;
    end if;
    
    f1 := poly_interp_consec(a, [(-1)^(M2) * betas[j+1] * facts[M2-j] * (facts[M-j])^(-1) : j in [0..M2-1]] : bottom := false, polys := (polys`children)[1], facts := facts);
    f2 := poly_interp_consec(a+M2, [betas[M2+j+1]*facts[j+1] * (facts[M2+j+1])^(-1) : j in [0..M2-1]] : bottom := false, polys := (polys`children)[2], facts := facts);

    Z1 := (polys`children)[1]`poly; Z2 := (polys`children)[2]`poly;
    return f1*Z2 + f2*Z1;
end function;