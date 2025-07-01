load "zywina/GL2GroupTheory.m";
load "zywina/ModularCurves.m";
load "power series test/fft.m";

// precision
PREC := 1000;
ROOTS := 1000;
SetDefaultRealField(RealField(PREC));
CC := ComplexField();

///////////////////////////////////////////////////////////////////////////////
// CUSP FORMS
///////////////////////////////////////////////////////////////////////////////

M := 1024;

f := Newforms(CuspForms(DirichletCharacter("20.1"),2))[1][1];

f1 := Coefficients(qExpansion(f,M));

function naive_twist(f,chi)
    return [f[i]*chi(i) : i in [1..#f]];
end function;

function alpha(f,d)
    ret := [0 : i in [1..#f]];
    for i in [1..Floor(#f/d)] do 
        ret[i*d] := f[i];
    end for;
    return ret;
end function;

function act(f,N)
    K := CyclotomicField(N);
    return [f[i]*K.1^i : i in [1..#f]];
end function;

function GaussSum(chi)
    N := Modulus(chi);
    return &+[CC!chi(u)*Exp(2*Pi(CC)*CC.1*u/N) : u in [1..N]];
end function;

function evaluate(f, z)
    return &+[CC!f[i]*z^i : i in [1..#f]];
end function;


f1_5 := alpha(f1,5);
f2 := naive_twist(f1, DirichletCharacter("5.4"));
f3 := naive_twist(f1, DirichletCharacter("5.2"));
f3_bar := naive_twist(f1, DirichletCharacter("5.3"));


b := 0.9;
lam := -(b^(-2))*evaluate(f3, Exp(-2*Pi(CC)/(b*10))) / evaluate(f3_bar, Exp(-2*Pi(CC)*b/10));
lamlam := lam/GaussSum(DirichletCharacter("5.4")); // lamlam = -(1+2i)/5.

lam := -(b^(-2))*evaluate(f3_bar, Exp(-2*Pi(CC)/(b*10))) / evaluate(f3, Exp(-2*Pi(CC)*b/10));
lamlam := lam/GaussSum(DirichletCharacter("5.4")); // lamlam = -(1-2i)/5.

z4 := Parent(f3[1]).1;
f3tr := [Trace(f3[i]) : i in [1..#f3]];
if3tr := [Trace(z4*f3[i]) : i in [1..#f3]];

K5 := CyclotomicField(10);
z10 := K5.1;
alph := z10^2 - z10^4 - z10^6 + z10^8;
S := Matrix(K5, [[0,-5,0,0,0],[-1/5,0,0,0,0],[0,0,-1,0,0],[0,0,0,-1/5*alph,2/5*alph],[0,0,0,2/5*alph,1/5*alph]]);

M := [f1, f1_5, f2, f3tr, if3tr];
M_ := [Vector([M[i][j]*z10^j : j in [1..#M[i]]]) : i in [1..#M]];
T := Matrix(Solution(Matrix(K5,M),M_));

Mz10 := Matrix(Rationals(),[[0,1,0,0],[0,0,1,0],[0,0,0,1],[-1,1,-1,1]]);
ff := hom<K5->MatrixRing(Rationals(),4)|Mz10>;
M3 := Matrix(Integers(),[[1,0,0,0],[0,0,0,1],[0,-1,0,0],[1,-1,1,-1]]);
M7 := M3^(-1);

Sblock := BlockMatrix(5,5,[ff(a) : a in ElementToSequence(S)]);
Tblock := BlockMatrix(5,5,[ff(a) : a in ElementToSequence(T)]);
M3block := BlockMatrix(5,5,[M3,0,0,0,0,0,M3,0,0,0,0,0,M3,0,0,0,0,0,M3,0,0,0,0,0,M3]);
M7block := M3block^(-1);

// [4,3,7,1] = M3 * ST^(-2)ST^4ST, [6,9,3,4] = M7 * ST^2ST^(-4)S
G1 := M3block * Sblock * Tblock^(-2) * Sblock * Tblock^4 * Sblock * Tblock;
G2 := M7block * Sblock * Tblock^2 * Sblock * Tblock^(-4) * Sblock;

V := Nullspace(G1 - IdentityMatrix(Rationals(), 20)) meet Nullspace(G2 - IdentityMatrix(Rationals(), 20));

v1 := ElementToSequence(V.1); v2 := ElementToSequence(V.2);
v1 := [ v1[1+4*j] + z10*v1[2+4*j] + z10^2*v1[3+4*j] + z10^3*v1[4+4*j] : j in [0..4]];
v2 := [ v2[1+4*j] + z10*v2[2+4*j] + z10^2*v2[3+4*j] + z10^3*v2[4+4*j] : j in [0..4]];



///////////////////////////////////////////////////////////////////////////////
// BASEPOINTS
///////////////////////////////////////////////////////////////////////////////

p := 13;
seen := {**};
basepoints := [**];
for t in [0..Floor(2*Sqrt(p))] do
    K := QuadraticField(t^2-4*p); OK := MaximalOrder(K);
    D := -Discriminant(K);
    f0 := Integers()!Sqrt((4*p-t^2)/D);
    P<x> := PolynomialRing(K);
    pps := [x[1] : x in Factorization(ideal<OK|p>)];
    for f in Divisors(f0) do
        disc := -f^2*D;
        phi := f*(disc mod 2);
        delta := (disc - phi^2)/4;
        // find omega and frobenius that have positive imaginary part
        for r in Roots(x^2-phi*x-delta) do 
            if Im(Evaluate(r[1], InfinitePlaces(K)[1])) gt 0 then 
                om := r[1];
                break;
            end if;
        end for;

        for r in Roots(x^2-t*x+p) do 
            if Im(Evaluate(r[1], InfinitePlaces(K)[1])) gt 0 then 
                fr := r[1];
                break;
            end if;
        end for;
        // find the ideal above p that contains the Frobenius
        for I in pps do 
            if fr in I then 
                pp := I;
                break;
            end if;
        end for;

        P_O := HilbertClassPolynomial(-D*f^2);
        H_O := ext<K | P_O>; OH := MaximalOrder(H_O);
        jinvs := [r[1] : r in Roots(P_O, H_O)];
        // find the j-invariant that agrees with j(om)
        _, ind := Min([Abs(jInvariant(Evaluate(om, InfinitePlaces(K)[1])) - Evaluate(r, InfinitePlaces(H_O)[1])) : r in jinvs]);
        jinv := jinvs[ind];
        ppOH := &+[y*OH : y in Generators(pp)];
        ppOHs := [I[1] : I in Factorization(ppOH)];
        for I in ppOHs do
            _, pi := ResidueClassField(OH, I);
            j_ := pi(jinv);
            if not j_ in seen then
                 Include(~seen,j_);
                 Append(~basepoints,<f,D,om,fr,I,jinv,j_>);
            end if; 
        end for;
    end for;
end for;

N := 10;
GL2 := GL(2,Integers(N));
SL2 := sub<GL2|[[0,1,N-1,0],[1,1,0,1]]>;
G := sub<GL2|[[4,3,7,1],[6,9,3,4]]>;
G0 := G meet SL2;
XG := CreateModularCurveRec(N, [[4,3,7,1],[6,9,3,4]]);

// basepoints with level structure
bpts := [**];
for b in basepoints do 
    om := b[3]; fr := b[4]; K := Parent(om); j_ := b[7];
    A := Transpose(Matrix(Rationals(), [Flat(om/N), Flat(K!(1/N))]));
    B := Transpose(Matrix(Rationals(), [Flat(fr), Flat(fr*K.1)]));
    Fr := GL(2,Integers(N))!(A^(-1)*B*A);

    size_A := (1728 mod p eq j_) select 2 else ((0 mod p eq j_) select 3 else 1);
    A_matrices := [[1,0,0,1],[0,-1,1,0],[1,1,-1,0]];
    A := GL2!A_matrices[size_A];
    a_list := [A^(i-1) : i in [1..size_A]];
    already_seen := {**};
    TT, phi := Transversal(SL2, G0); //phi sends g to its a coset representative of Gg; we are assuming surjective determinant.
    for g in TT do
        if &or[phi(g*a) in already_seen : a in a_list] then 
            continue;
        end if;
        if &or[g*Fr*a*g^(-1) in G : a in a_list] then 
            Append(~bpts, <b[1],b[2],b[3],b[4],b[5],b[6],b[7],g>);
        end if;
        Include(~already_seen, g);
    end for;
end for;

// cuspidal basepoints (there are none)
A := GL2![1,1,0,1];
Fr := GL2![p,0,0,1];
a_list := [A^(i-1) : i in [1..N]];
cusp_bpts := [**];
TT, phi := Transversal(SL2, G0);
for g in XG`cusps do
    if &or[g*Fr*a*g^(-1) in G : a in a_list] then 
        Append(~cusp_bpts, g);
    end if;
end for;
assert #cusp_bpts eq 0;

///////////////////////////////////////////////////////////////////////////////
// INTERLUDE: SOME FUNCTIONS RELATED TO J-INVARIANT
///////////////////////////////////////////////////////////////////////////////
function dt_to_brch(z)
    // distance from z to the interval [0,1728]
    x := Abs(Re(z)) + Abs(Re(z)-1728) - 1728;
    y := Im(z);
    return Sqrt(x^2+y^2);
end function;

// functions that allow fast computation of the derivative of the j-invariant
function AA(q, prec)
    // q := Exp(2*Pi(CC)*CC.1*z);
    C := Ceiling(2 + Sqrt(-2/3 * prec * Log(10)/Log(Abs(q))));
    return 1 + &+[(-1)^n * (q^((3*n^2-n)/2) + q^((3*n^2+n)/2)) : n in [1..C]];
end function;

function AADER(q, prec)
    // q := Exp(2*Pi(CC)*CC.1*z);
    C := 2 + Sqrt(-2/3 * prec * Log(10)/Log(Abs(q)));
    C := Ceiling(C + 2*Max(Log(C),1));
    return &+[(-1)^n * (q^((3*n^2-n)/2-1) * (3*n^2-n)/2 + q^((3*n^2+n)/2-1) * (3*n^2+n)/2) : n in [1..C]];
end function;

function FINV(q, prec)
    // q := Exp(2*Pi(CC)*CC.1*z);
    temp2 := AA(q^2, 2*prec);
    temp1 := AA(q, 2*prec);
    temp := temp2/temp1;
    return q*temp^24;
end function;

function FDER(q, prec)
    // q := Exp(2*Pi(CC)*CC.1*z);
    temp2 := AA(q^2, 2*prec);
    temp1 := AA(q, prec);
    temp := temp2/temp1;
    return temp^24 + 24 * q * temp^23 * (2*q*temp1*AADER(q^2, 2*prec) - temp2*AADER(q, prec))/temp1^2;
end function;

function JINV(q, prec)
    eff := FINV(q, prec);
    return (256*eff+1)^3/eff;
end function;

function JDER(q, prec)
    eff := FINV(q, 2*prec); effder := FDER(q, prec);
    return 2^25 * eff * effder + 3 * 2^16 * effder - effder/eff^2; 
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
        q := qM^M;
        qold := qM;
        qM := qM - (JINV(q, prec) - y)/(JDER(q, prec)*M*qM^(M-1));
        if Abs(qold - qM) lt 10^(-prec) or itt gt Sqrt(prec) then 
            break;
        end if;
        itt := itt+1;
    end while;
    return qM;
end function;

///////////////////////////////////////////////////////////////////////////////
// INTERLUDE: SOME FUNCTIONS RELATED TO OUR CUSP FORMS
///////////////////////////////////////////////////////////////////////////////

function F1(q, prec)
    return q * AA(q^2, prec)^2 * AA(q^10, prec)^2; // this is ETA(2z)^2 * ETA(10z)^2
end function;

function F1_5(q, prec)
    return F1(q^5, prec);
end function;

function F2(q, prec)
    chi := DirichletCharacter("5.4");
    chi := chi^(-1);
    return GaussSum(chi)^(-1) * &+[CC!chi(u) * F1(q * Q(u/5), prec) : u in [0..4]];
end function;

function F3(q, prec)
    chi := DirichletCharacter("5.2");
    chi := chi^(-1);
    return GaussSum(chi)^(-1) * &+[CC!chi(u) * F1(q * Q(u/5), prec) : u in [0..4]];
end function;

function F3BAR(q, prec)
    chi := DirichletCharacter("5.3");
    chi := chi^(-1);
    return GaussSum(chi)^(-1) * &+[CC!chi(u) * F1(q * Q(u/5), prec) : u in [0..4]];
end function;

function F3TR(q, prec)
    return F3(q, prec)+F3BAR(q, prec);
end function;

function IF3TR(q, prec)
    return CC.1*F3(q, prec) - CC.1*F3BAR(q, prec);
end function;

// Based on Theorem 1.1 in Lozano-Robledo https://arxiv.org/abs/1809.02584
function GL2Cartan(D,N)
    // The Cartan subgroup of GL(2,Z/NZ) isomorphic to (O/NO)* where O is the imaginary quadratic order of discriminant D.
    // assert N gt 0;
    if N eq 1 then return sub<GL(2,Integers())|>; end if;
    // require D lt 0 and IsDiscriminant(D): "D must be the discriminant of an imaginary quadartic order";
    R := Integers(N); G := GL(2,R);
    DK := FundamentalDiscriminant(D); _,f := IsSquare(D div DK);
    if D mod 4 eq 0 then
        delta := D mod 4 eq 0 select R!ExactQuotient(D,4) else R!D/4; phi := R!0;
    else
        delta := R!((D-f^2) div 4);  phi := R!f;
    end if;

    P := PrimeDivisors(N);
    m := (N div &*P)^2 * &*[(p-1)*(p-KroneckerSymbol(D,p)):p in P]; // m = cartan size
    gens := [];
    repeat
        a := Random(R); b := Random(R);
        if GCD(a^2+a*b*phi-delta*b^2,N) ne 1 then continue; end if;
        Append(~gens,G![a+b*phi,b,delta*b,a]);
    until #sub<G|gens> eq m;
    H,pi := AbelianGroup(sub<G|gens>); B := AbelianBasis(H);
    H := sub<G|[Inverse(pi)(h):h in B]>;
    assert #H eq m;
    return H;
end function;

cusp_forms := [v1, v2];
BASIS := [F1, F1_5, F2, F3TR, IF3TR];

function eval_cuspform(cuspform, qN, prec)
    assert #cuspform eq #BASIS;
    return &+[CC!cuspform[k]*BASIS[k](qN, prec) : k in [1..#cuspform]];
end function;
ff := hom<SL2 -> GL(5,K5)|S, T>;
QN := QGEN(N);
for b in bpts do
    j0 := b[6];
    if j0 eq 0 or j0 eq 1728 then continue; end if; // TEMPORARY
    j0Num := Evaluate(j0, InfinitePlaces(Parent(j0))[1]);

    om := b[3];
    gamma := b[8]; 
    z0 := Evaluate(om, InfinitePlaces(Parent(om))[1]);
    qN0 := QN(z0);
    
    // OK, now let's evaluate the values of qN that give rise to a circle around j0.
    R := Floor(dt_to_brch(z0) - 1);
    qNvalues := [*0 : k in [0..ROOTS-1]*];
    for k in [0..ROOTS-1] do 
        qNvalues[k+1] := JCOMPINV(j0Num + R * Q(k/ROOTS), qN0, N, PREC-1);
        printf "Got the q-value for k = %o\n", k;
    end for;
    qvalues := [*x^N : x in qNvalues*];
    // OK, now for our final expression in C[[j-j0]] d(j-j0), we are going to compute f(q_N)/(q_N * j'(q_N)) = f(q_N)/(N*q*j'(q)) as q_N ranges in qNvalues.
    qNdens := [*0 : k in [1..#qvalues]*];
    for k in [1..#qvalues] do
        qNdens[k] := qvalues[k] * N * JDER(qvalues[k], PREC);
        printf "Got the denominator for k = %o\n", k;
    end for;
    for cuspform in cusp_forms do 
        printf "Performing slash operator %o on the cusp form given by the vector %o\n", gamma, cuspform;
        slashed := Matrix(K5,[cuspform]) * ff(gamma); slashed := ElementToSequence(slashed[1]); // note that f(gamma z) d(gamma z) = (f|gamma)(z) dz.
        printf "Got %o for the result\n", slashed;
        qNnums := [*0 : x in qNvalues*];
        for k in [1..#qNvalues] do 
            qNnums[k] := eval_cuspform(slashed, qNvalues[k], PREC);
            printf "Evaluated cusp form for k = %o\n", k;
        end for;
        vals := [*qNnums[k]/qNdens[k] : k in [1..ROOTS]*];
        // Now take the inverse Fourier transform to get [a_0, a_1*R, a_2*R^2, ...]
        printf "Now taking inverse Fourier transform!\n"; cputi := Cputime();
        coeffs := ift(pad(vals, ROOTS));
        printf "Successfully obtained IFT in %o seconds\n", Cputime()-cputi;
        coeffs := [*coeffs[k]/R^(k-1) : k in [1..#coeffs]*]; // This should be the money......
        break; // TEMP
    end for;
    break; // TEMP
end for;