declare type XuSeries;
declare attributes XuSeries: v, d, prec, coeffs, fun, ZZ, CC;
intrinsic CreateSeries(fun::UserProgram) -> XuSeries
{}
    r := New(XuSeries);
    r`coeffs := [**];
    r`fun := fun;
    _, r`v, r`d := r`fun(20);
    r`ZZ := Integers();
    r`CC := ComplexField();
    r`prec := r`v-1;
    return r;
end intrinsic;

intrinsic Coeff(r::XuSeries, n::RngIntElt) -> RngIntElt
{}
    if n gt r`prec then
        r`prec := Abs(2*n);
        r`coeffs := r`fun(r`prec-r`v+1);
    end if;

    if n-r`v+1 gt 0 and n-r`v+1 lt #r`coeffs + 1 then 
        return r`coeffs[n-r`v+1];
    else
        return 0;
    end if;
end intrinsic;

intrinsic CoeffList(r::XuSeries, n_low::RngIntElt, n_up::RngIntElt) -> SeqEnum
{}
    _ := Coeff(r, n_up);
    return [Coeff(r,a) : a in [n_low-r`v+1..n_up-r`v+1]];
end intrinsic; 

intrinsic Print(r::XuSeries)
{}
    printf "%o", CoeffList(r,r`v,r`v+5);
end intrinsic;

intrinsic EvaluateDerivative(r::XuSeries, k::RngIntElt, q::FldComElt, pr::RngIntElt) -> FldComElt
{}
    ff := map<r`ZZ -> r`CC | n :-> Binomial(n+k,k)*Coeff(r,n+k)*(q^n)>;
    if r`v lt 0 then 
        negterms := (-1)^k * (&+[Binomial(n+k-1,k)*(1/q)^(n+k) : n in [1..-r`v]]);
    else 
        negterms := 0;
    end if;
    ret := negterms;
    done := false;
    i := 0;
    eps := 10.^(-2*pr);
    while not done do
        x := ff(i);
        if Abs(x) lt eps then
            done := true;
        end if;
        ret := ret + x;
        i := i+1;
    end while;
    return ret;
end intrinsic;

intrinsic EvaluateDerivativeTau(r::XuSeries, k::RngIntElt, tau::FldComElt, pr::RngIntElt) -> FldComElt
{}
    return EvaluateDerivative(r, k, Exp(2*Pi(r`CC)*r`CC.1*tau), pr);
end intrinsic;

intrinsic TaylorExpansion(r::XuSeries, q::FldComElt, pr::RngIntElt) -> XuSeries
{}
    fun := function(n) return [EvaluateDerivative(r, k, q, pr) : k in [0..n]], 0, 1; end function;
    ret := CreateSeries(fun);
    return ret;
end intrinsic;

intrinsic TaylorExpansionTau(r::XuSeries, tau::FldComElt, pr::RngIntElt) -> XuSeries
{}
    return TaylorExpansion(r, Exp(2*Pi(r`CC)*r`CC.1*tau), pr);
end intrinsic;