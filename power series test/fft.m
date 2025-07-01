// Input: a = [a0,..., a_{n-1}], where n is assumed to be a power of 2.
// Output: discrete fourier transform applied to a; if rev is true, then do the inverse fourier transform.
function fft(a, rev: top := true)
    CF := ComplexField();
    n := #a;
    if n eq 1 then
        return a;
    end if;
    a_e := [*a[i] : i in [1..n] | i mod 2 eq 1*];
    a_o := [*a[i] : i in [1..n] | i mod 2 eq 0*];
    y_e := fft(a_e, rev: top := false);
    y_o := fft(a_o, rev: top := false);
    if not rev then 
        zeta := Exp(2*Pi(CF)*CF.1/n);
    else 
        zeta := Exp(-2*Pi(CF)*CF.1/n);
    end if;
    om := 1;

    ret := [*0 : i in [1..n]*];
    for k in [1..n/2] do 
        ret[k] := y_e[k] + om * y_o[k];
        ret[Integers()!(k+n/2)] := y_e[k] - om * y_o[k];
        om := om * zeta;
    end for;

    if rev and top then 
        ret := [*ret[i]/n : i in [1..n]*];
    end if;
    return ret;
end function;

function dft(a)
    return fft(a, false);
end function;

function ift(a)
    return fft(a, true);
end function;

// adds trailing zero's to a until the size is M, where M is the smallest power of 2 greater than N.
function pad(a, N)
    M := 2^(Ceiling(Log(2,N)));
    n := #a;
    for i in [n+1..M] do 
        Append(~a, 0);
    end for;
    return a;
end function;