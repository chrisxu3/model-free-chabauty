pr := 50;
N := 40;
SetDefaultRealField(RealField(1000));
C := ComplexField();

Attach("XuSeries.m");
j := function(n)
    Z<q> := LaurentSeriesRing(Integers(), n+1);
    return Coefficients(jInvariant(q));
end function;

S := CuspForms(Gamma0(43),2);
f1 := function(n)
    qexp := qExpansion(S.1, n+2);
    q := Parent(qexp).1;
    return Coefficients(qexp/q);
end function;

// f2 := function(n)
//     return Coefficients(qExpansion(S.2,n+1));
// end function;

// r := CreateSeries(f);
// EvaluateDerivativeTau(r,600,Sqrt(-1));
create_M := function(n, a)
    M := ZeroMatrix(C, n+1, n+1);
    for k in [1..n+1] do
        M[k,1] := k*a[k];
    end for;
    for r in [2..n+1] do
        for k in [r..n+1] do 
            M[k,r] := &+[a[i]*M[k-i,r-1] : i in [1..k-r+1]];
        end for;
    end for;
    return M;
end function;

// Given a lower triangular matrix M and a vector b, solves Mx = b for x.
solve := function(M, b)
    N := #b;
    x := [*0 : i in [1..N]*];
    x[1] := b[1]/M[1,1];
    for n in [2..N] do 
        x[n] := (b[n] - (&+[M[n,i]*x[i] : i in [1..n-1]]))/M[n,n];
    end for;
    return x;
end function;

function expand_at_cm_pt(f,x,y,D,N,pr)
    tau := x+y*Sqrt(-D);
    // a := derivatives of j-inv at q_b (1-indexed)
    a := CoeffList(TaylorExpansionTau(CreateSeries(j), tau, pr), 1, N+1);
    // b := derivatives of f(q) (of f(q) dq) at q_b (0-indexed)
    b := CoeffList(TaylorExpansionTau(CreateSeries(f), tau, pr), 0, N);
    // c := coefficients of f w.r.t j-j_b (0-indexed).
    M := create_M(N, a);
    return solve(M, b);
end function;

expand_at_cm_pt(f1,43/2,1/2,43,N,pr);