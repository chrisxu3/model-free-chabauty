load "power series test/fft.m";
PREC := 100;
ROOTS := 3000;
SetDefaultRealField(RealField(PREC));
CC := ComplexField();

// COPIED FROM LEWIS COMBES https://github.com/lewismcombes/EtaExpressions/blob/main/data/big_expressions/43.2.a.a.txt
quots:=[
    [ -2, 5, -3, 2, -2, 5, -3, 2 ],
    [ 0, -3, 7, -2, 0, -3, 7, -2 ],
    [ 0, 1, 0, 1, 0, -3, 8, -3 ],
    [ 0, 0, -1, 3, 0, 0, 3, -1 ],
    [ 0, -3, 8, -3, 0, 1, 0, 1 ],
    [ 1, 0, 1, 0, -3, 8, -3, 0 ],
    [ -2, 3, 3, -2, -2, 3, 3, -2 ],
    [ 0, -4, 8, 0, 0, 0, 0, 0 ],
    [ 0, -1, 3, 0, 0, 3, -1, 0 ],
    [ 2, -1, -1, 2, 2, -1, -1, 2 ],
    [ -3, 8, -3, 0, 1, 0, 1, 0 ],
    [ 2, 0, -1, 1, -2, 6, -3, 1 ],
    [ 2, -3, 5, -2, 2, -3, 5, -2 ],
    [ 0, 3, -1, 0, 0, -1, 3, 0 ],
    [ 2, -1, 2, -1, -2, 5, 0, -1 ],
    [ -2, 6, -3, 1, 2, 0, -1, 1 ],
    [ -2, 5, 0, -1, 2, -1, 2, -1 ],
    [ 0, 0, 0, 0, 0, -4, 8, 0 ],
    [ 0, 0, 3, -1, 0, 0, -1, 3 ],
    [ 0, -1, 1, 2, 0, -1, 1, 2 ]
];
coeffs:=[ -3, -5/2, -1, 2, 1, -2, -3/4, 1/2, 1, 3, 2, 7/4, 3/4, 1, -7/8, 7/4, 7/8, 43/2, 2, -10 ];

// CUSP FORM 43.2.a.a
function FFF(z)
    divs := Divisors(43*8);
    assert #quots eq #coeffs;
    return &+[coeffs[k] * &*[DedekindEta(divs[kk]*z)^quots[k][kk]: kk in [1..#divs]] : k in [1..#coeffs]];
end function;

///////////////////////////////////////////////////////////////////////////////
// INTERLUDE: SOME FUNCTIONS RELATED TO J-INVARIANT
///////////////////////////////////////////////////////////////////////////////
function dt_to_brch(z)
    // distance from z to the interval [0,1728]
    x := (Abs(Re(z)) + Abs(Re(z)-1728))/2 - 1728;
    y := Im(z);
    return Sqrt(x^2+y^2);
end function;

function JINV(q)
    return jInvariant(Z(q));
end function;

function JDER(q)
    z := Z(q);
    return -JINV(q)*Eisenstein(6,z)/(Eisenstein(4,z)*q);
end function;

function Q(z)
    return Exp(2*Pi(CC)*CC.1*z);
end function;

function QGEN(M)
    ret := function(z)
        return Q(z/M);
    end function;
    return ret;
end function;

function Z(q) 
    // only well-defined up to addition by an integer
    return Log(q)/(2*Pi(CC)*CC.1);
end function;

function JCOMPINV(y, qM0, M, prec)
    // Newton's method: solve j(q_M) = y for q_M, given y
    // note that j as a function of q_M is different from j as a function of q!!!
    // in particular we have j'(q_M) = j'(q) * dq/dq_M = j'(q) * M*q_M^{M-1}
    qM := qM0; itt := 0;
    while true do
        q := qM^M; dd := (JINV(q) - y)/(JDER(q)*M*qM^(M-1));
        qM := qM - dd;
        if Abs(dd) eq 0 or Floor(-Log(Abs(dd))/Log(10)) ge prec then 
            break;
        end if;
        itt := itt+1;
    end while;
    return qM;
end function;

z0 := (43+Sqrt(-43))/2;
j0Num := CC!Round(jInvariant(z0));

qN0 := Q(z0);

// OK, now let's evaluate the values of qN that give rise to a circle around j0.
R := Floor(dt_to_brch(j0Num) - 1);
qNvalues := [*0 : k in [0..ROOTS-1]*];
for k in [0..ROOTS-1] do 
    if k lt 10 then
        start := qN0;
    else 
        start := qNvalues[k];
    end if;
    qNvalues[k+1] := JCOMPINV(j0Num + R * Q(k/ROOTS), start, 1, PREC-1);
    printf "Got the q-value for k = %o\n", k;
end for;
qvalues := qNvalues;
// OK, now for our final expression in C[[j-j0]] d(j-j0), we are going to compute f(q_N)/(q_N * j'(q_N)) = f(q_N)/(N*q*j'(q)) as q_N ranges in qNvalues.
qNdens := [*0 : k in [1..#qvalues]*];
for k in [1..#qvalues] do
    qNdens[k] := qvalues[k] * JDER(qvalues[k]);
    printf "Got the denominator for k = %o\n", k;
end for;

qNnums := [*0 : x in qNvalues*];
for k in [1..#qNvalues] do 
    qNnums[k] := FFF(Z(qNvalues[k]));
    printf "Evaluated cusp form for k = %o\n", k;
end for;
vals := [*qNnums[k]/qNdens[k] : k in [1..ROOTS]*];
// Now take the inverse Fourier transform to get [a_0, a_1*R, a_2*R^2, ...]
printf "Now taking inverse Fourier transform!\n"; cputi := Cputime();
coeffs := ift(pad(vals, ROOTS));
printf "Successfully obtained IFT in %o seconds\n", Cputime()-cputi;
coeffs := [*coeffs[k]/R^(k-1) : k in [1..#coeffs]*]; // This should be the money......