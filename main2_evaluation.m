Attach("gl2.m");
assert assigned G; assert assigned N; assert assigned ind; assert assigned genus; assert assigned p; assert assigned GL2; assert assigned SL2; assert assigned ZN; assert assigned io; assert assigned oi; assert assigned P1N; assert assigned secP1; assert assigned CN; assert assigned secCN; assert assigned CNpm; assert assigned secCNpm; assert assigned lift_cusp_CN; assert assigned P1NtoCN; assert assigned CNtoP1N; 

assert assigned io_makdisi; assert assigned Hecke_mat;

// 10^PREC < p^(2^??)
assert assigned PREC;
C_expt := Ceiling(Log(PREC*Log(10)/Log(p))/Log(2));
C := 2^C_expt;

Zp := pAdicRing(p, C);
Qp := FieldOfFractions(Zp);
Qpx<X> := PolynomialRing(Qp);

function roots(P,R)
    ret := [-Eltseq(datt[1])[1] : datt in Factorization(P,R)];
    assert #ret eq Degree(P);
    return ret;
end function;

function E_from_j0(j0,p)
    // Return an elliptic curve in one of three prescribed formats, from j-invariant.
    Fp := GF(p);
    ab := map<ZZ -> car<Fp,Fp>|j :-> <Fp!a, Fp!b> where a,b := Explode(
                (j mod p eq 0) select <0,54*1728^2> 
                else ( ((j-1728) mod p eq 0) select <-27*1728,0> 
                else <-27*j*(j-1728), 54*j*(j-1728)^2> )
            )>;
    a,b := Explode(ab(j0));
    E := EllipticCurve([a,b]);
    return E;
end function;

/////////////////////////////////////////////////////////
// Helper functions to access a basis of E[N] quickly. //
/////////////////////////////////////////////////////////

function find_basis(E)
    // Find a basis of N-torsion for the elliptic curve E/F_p.
    ftn := Factorization(N);
    f := Order(GL2!FrobeniusMatrix(E)); q := p^f; Fq := GF(q);
    Fpx<x> := PolynomialRing(GF(p));
    E_Fq := E(Fq);
    P1 := Identity(E); P2 := Identity(E);
    for dat in ftn do
        ell,e := Explode(dat);
        Psi_elle := Fpx!(DivisionPolynomial(E, ell^e)/DivisionPolynomial(E, ell^(e-1)));
        x_coords := roots(Psi_elle, Fq);
        done := false; 
        while not done do 
            x1 := Random(x_coords); Q1 := Random(Points(E_Fq, x1));
            x2 := Random(x_coords); Q2 := Random(Points(E_Fq, x2));
            zet := WeilPairing(Q1,Q2,ell^e);
            if Order(zet) eq ell^e then
                done := true; P1 := P1+Q1; P2 := P2+Q2; 
            end if;
        end while;
    end for;
    return P1, P2, f, WeilPairing(P1,P2,N);
end function;

function E_and_basis(j0)
    // Given a j-invariant j0, return an elliptic curve E over F_p with that j-invariant, and return a basis of E[N]. Also return f, the number such that the basis is defined over GF(p^f).
    E := E_from_j0(j0,p);
    P1,P2,f,eN := find_basis(E);
    return E,<P1,P2>,f,eN;
end function;

////////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper functions related to endomorphisms of E and their action on a level structure beta of E[N]. //
////////////////////////////////////////////////////////////////////////////////////////////////////////

function endo_matrix(E,P1,P2,endo,f)
    // Given endomorphism endo and basis P1, P2 of E[N], compute the action of endo on P1, P2 as a 2x2 matrix.
    // f is such that P1 and P2 are defined over GF(p^f).
    q := p^f;
    Fq := GF(q);
    zet := WeilPairing(P1,P2,N);
    // prim := PrimitiveRoot(Fq);
    // o := Log(prim,zet);
    // r := (q-1)/N;
    // oo := o/r;

    EFq := E(Fq);
    zet_abcd := [ WeilPairing(EFq!(endo(P1)), P2, N), WeilPairing(P1, EFq!(endo(P1)), N), WeilPairing(EFq!(endo(P2)),P2,N), WeilPairing(P1, EFq!(endo(P2)), N)];
    Z_N := Integers(N);
    
    return GL2![Z_N!(Log(zet, zet_)) : zet_ in zet_abcd];
    // return GL2![Z_N!(Log(Fq.1, zet_)/r) * (Z_N!(oo))^(-1) : zet_ in zet_abcd];
end function;

function frob(E)
    return FrobeniusMap(E);
end function;

function aut_gen(E,f)
    q := p^f;
    Fq := GF(q);
    E := BaseExtend(E, Fq);
    mu_E, io := AutomorphismGroup(E);
    if #mu_E le 2 then return IdentityMap(E); end if;
    return io(Setseq(Generators(mu_E))[1]);
end function;

//////////////////////////////////////////////////////////////////////////////////////////////////////////
// Knockoff functions implementing group law operations on elliptic curves, the way I want to use them. //
//////////////////////////////////////////////////////////////////////////////////////////////////////////

function slope(A,B,P,Q)
    if Type(P) eq Infty or Type(Q) eq Infty then return Infinity(); end if;
    xP := P[1][1]; yP := P[2][1]; xQ := Q[1][1]; yQ := Q[2][1];
    // if xP eq xQ and yP eq yQ then 
    //     return (3*xP^2 + B)/(2*yP);
    // else 
    //     return (yP-yQ)/(xP-xQ);
    // end if;
    return (xP^2 + xP*xQ + xQ^2 + A)/(yP+yQ);
end function;

function add_pts(A,B,P,Q)
    if Type(P) eq Infty then return Q; elif Type(Q) eq Infty then return P; end if;
    xP := P[1][1]; yP := P[2][1]; xQ := Q[1][1]; yQ := Q[2][1];
    lam := slope(A,B,P,Q);
    if Type(lam) eq Infty then return Infinity(); end if;
    xPQ := lam^2 - xP - xQ; yPQ := yP - lam*(xP - xPQ);
    return col_vector([xPQ, -yPQ]), lam;
end function;

function multiply_pt(A,B,u,P)
    if Type(P) eq Infty or u eq 1 then return P; end if;
    ZZ := Integers(); assert u in ZZ;
    xP := P[1][1]; yP := P[2][1];
    if u lt 0 then return multiply_pt(A,B,-u,col_vector([xP,-yP])); 
    elif u eq 0 then return Infinity();
    elif IsOdd(u) then return add_pts(A,B,P,multiply_pt(A,B,u-1,P));
    else PP := multiply_pt(A,B,ZZ!(u/2),P); return add_pts(A,B,PP,PP);
    end if;
end function;

function negate_pt(P)
    if Type(P) eq Infty then return P; end if;
    xP := P[1][1]; yP := P[2][1];
    return col_vector([xP,-yP]);
end function;

function dbl_add(N)
    M := N; ret := [];
    while M ne 1 do
        if (M mod 2) eq 0 then M := ZZ!(M/2); Append(~ret,<M,M>);
        else M -:= 1; Append(~ret,<1,M>);
        end if;  
    end while;
    return Reverse(ret);
end function;

function addn_seq(S)
    // Given a set S of numbers a_1, ..., a_n, find an addition sequence that contains S.
    // This implements algorithm "I\alpha" in Section 4.8 (page 17) of https://ir.cwi.nl/pub/5726/5726D.pdf.
    assert &and[s gt 0 : s in S];
    Include(~S,1);
    an := Max(S);
    if an eq 1 then return []; end if;
    if an eq 2 then return [<1,1>]; end if;
    Exclude(~S,an);
    anm1 := Max(S); // anm1 = a_{n-1}, an = a_n.
    r := Floor(an/anm1); a0 := an - r*anm1;
    if a0 ne 0 then Include(~S,a0); end if;
    ret := [<dat[1]*anm1, dat[2]*anm1> : dat in dbl_add(r)];
    return addn_seq(S) cat ret cat (a0 ne 0 select [<a0,r*anm1>] else []);
end function;

function addn_seq_with_action(N,u)
    // This finds an addition sequence that traverses coset reprsentatives of Z(N)*/<u>.
    // With the condition that the representative "u" must be traversed, for the identity coset.
    uZ := sub<ZN | [oi(u)]>;
    reps, sec := Transversal(ZN, uZ);
    S := {Min({Integers()!io(r+a) : a in uZ}) : r in reps};
    Exclude(~S,1); Include(~S,Integers()!u);
    return addn_seq(S), S;
end function;

function generate_Eis_tables(j0, E, beta, f, C : tw := 1)
    // Given a j-invariant j0 \in Z, given N and p (implicit), given framed elliptic curve (E,\beta) over F_p with j-invariant j_0, and given f (such that q = p^f is what E[N] is defined over), compute the values of Eis_1 and Eis_2 at the torsion points of E_{j0}.
    printf "Generating Eisenstein tables for j = %o mod %o, twisted by %o, up to precision %o.\n", ((1728 mod p eq j0) select 1728 else j0), p, tw, #C;
    P1, P2 := Explode(beta);
    q := p^f;
    // Let us define universal elliptic curves.
    if (1728-j0) mod p eq 0 then A := func<T | -27*tw*(tw*T^2+1728)>; B := func<T | 54*tw^2*T*(tw*T^2+1728)>;
    elif j0 mod p eq 0 then A := func<T | -27*tw*T*(tw*T^3-1728)>; B := func<T | 54*tw*(tw*T^3-1728)^2>;
    else A := func<T | -27*(T+j0)*(T+j0-1728)>; B := func<T | 54*(T+j0)*(T+j0-1728)^2>;
    end if;
    // Now P1 and P2 form a basis for E[N], and everything is defined over F_q, where q = p^f.
    // Let us compute the action of Frobenius on E[N], with respect to the level structure P1,P2.
    sigma_p := endo_matrix(E,P1,P2,frob(E),f);
    printf "The matrix of Frobenius is [%o,%o,%o,%o]...\n", sigma_p[1][1],sigma_p[1][2],sigma_p[2][1],sigma_p[2][2];
    reps, sec, stabs := dbl_coset(K0(N),GL2,sub<GL2|[sigma_p]>); // "reps" parametrizes lines in Z(N)^2, up to Frobenius.
    ZN_pm, pm := quo<ZN | [Inverse(io)(-1)]>;
    // Let us now lift P1 and P2 to characteristic 0.
    // Zp := pAdicRing(p,#C); Qp := FieldOfFractions(Zp);
    Zpf<ze> := UnramifiedExtension(Zp,f : Cyclotomic := true);
    Qpf := FieldOfFractions(Zpf);
    R := quo<Zpf | p^(#C)>;
    fr := FrobeniusAutomorphism(R);
    x1 := Zpf!TeichmuellerLift(P1[1], R); y1 := Zpf!TeichmuellerLift(P1[2], R);
    x2 := Zpf!TeichmuellerLift(P2[1], R); y2 := Zpf!TeichmuellerLift(P2[2], R);
    // We're gonna iterate over values of T, so T = t*p as t ranges from 0 to C-1.
    ret := AssociativeArray();
    // Let's first look at all frob-orbits of lines in Z(N)^2. Precompute the optimal addition sequences and store them.
    optimal_add_seq := AssociativeArray();
    for dat in reps do
        a := dat[2][1]; b := dat[2][2];
        o := ZZ!(f/#stabs[dat]);
        a_lam, b_lam := Explode(Eltseq(Matrix(Integers(N),1,2,[[a,b]]) * sigma_p^o)); // This is what the (minimal power of Frob that fixes my line [a:b]) does to (a,b).
        c,d := Explode(find_inv_pair(a,b)); lam := ZZ!(Integers(N)!((a_lam*d-b_lam*c)/(a*d-b*c)));
        addseq, S := addn_seq_with_action(N,lam);
        optimal_add_seq[dat] := <lam, o, addseq, S>;
        // printf "For rep %o, we have S = %o, addseq = %o, o = %o and lam = %o.\n", Eltseq(dat[2]), S, addseq, o, lam;
    end for;
    // Now we're really gonna loop over values of T.
    POL<X> := PolynomialRing(Qp);
    for t in C do
        printf "(%o/%o) Starting the loop for t = %o...\n", t, C[#C], t;
        // We construct a tamely ramified extension of degree p+1.
        // We also construct the Frobenius automorphism of that guy.
        Kpf<pi> := TotallyRamifiedExtension(Qpf, X^(p+1)-t*p);
        fr_base := FrobeniusAutomorphism(Qpf);
        fr := map<Kpf -> Kpf | dat :-> Kpf![fr_base(rr) : rr in Eltseq(dat)]>;
        // We first find our lifts of P1 and P2. These will be called v1 and v2.
        v1 := col_vector([Kpf!x1,Kpf!y1]); v2 := col_vector([Kpf!x2,Kpf!y2]);
        A_T := A(pi); B_T := B(pi);  
        newton_iterate(A_T,B_T,N,~v1); newton_iterate(A_T,B_T,N,~v2);
        printf "(%o/%o) Found lift of basis elements.\n", t, C[#C];
        // Now we've got to populate CN and CN_pm with Eisenstein series values.
        Eis1 := AssociativeArray(); Eis2 := AssociativeArray(); 
        for dat in reps do
            a := dat[2][1]; b := dat[2][2];
            // OK, so we have P = a*v1 + b*v2. 
            // o is the smallest positive integer such that sigma_p^o fixes <P>, and u is what sigma_p^o scales P by.
            // addseq is the addition sequence we determined, and S is representatives of Z(N)*/<u>.
            // c_tab is the table of c_n's, and P_mult_tabl is the table of multiples of P. The keys are going to be INTEGERS from 1 to N-1.
            P := add_pts(A_T,B_T,multiply_pt(A_T,B_T,ZZ!a,v1),multiply_pt(A_T,B_T,ZZ!b,v2)); 
            u, o, addseq, S := Explode(optimal_add_seq[dat]);
            c_tab := AssociativeArray(); P_mult_tab := AssociativeArray();
            c_tab[1] := 0; P_mult_tab[1] := P;
            // Now we follow the addition sequence to determine everything in S.
            for tup in addseq do 
                m,n := Explode(tup);
                P_mult_tab[m+n], lam_m_n := add_pts(A_T,B_T,P_mult_tab[m], P_mult_tab[n]);
                c_tab[m+n] := c_tab[m] + c_tab[n] + lam_m_n;
            end for;
            // The next step is to determine c_(m*u^Z) and (m*u^Z)P. 
            for m in S do
                m0 := m;
                for k in [1..#stabs[dat]-1] do 
                    new_m0 := ZZ!(m0*u mod N);
                    P_mult_tab[new_m0] := col_vector([(fr^o)(P_mult_tab[m0][1][1]), (fr^o)(P_mult_tab[m0][2][1])]);
                    c_tab[new_m0] := m0*c_tab[u] + (fr^o)(c_tab[m0]);
                    m0 := new_m0;
                end for;    
            end for;
            // The next step is to fill up Eis1 and Eis2.
            for m in S do 
                dat_m_fr_i := secCN(GL2![1,0,0,m] * dat);
                eis1val := -m*c_tab[N-1]/N + c_tab[m];
                eis2val := P_mult_tab[m][1][1];
                for i in [0..f-1] do 
                    neg_dat_m_fr_i := secCN(GL2![-1,0,0,-1]*dat_m_fr_i);
                    // if dat_m_fr_i in Keys(Eis1) then Eis1[dat_m_fr_i] - eis1val; assert Eis1[dat_m_fr_i] eq eis1val; end if; if secCNpm(dat_m_fr_i) in Keys(Eis2) then Eis2[secCNpm(dat_m_fr_i)] - eis2val; assert Eis2[secCNpm(dat_m_fr_i)] eq eis2val; end if;
                    Eis1[dat_m_fr_i] := eis1val;
                    Eis1[neg_dat_m_fr_i] := -eis1val;
                    Eis2[secCNpm(dat_m_fr_i)] := eis2val;
                    dat_m_fr_i := secCN(dat_m_fr_i * sigma_p);
                    eis1val := fr(eis1val);
                    eis2val := fr(eis2val);
                end for;
            end for;
        end for;
        ret[t] := <map<CN -> Kpf | assoc_to_tup(Eis1)>, map<CNpm -> Kpf | assoc_to_tup(Eis2)>>;
    end for;
    return ret, sigma_p;
end function;

function eval_padic(r, eN, Qpf)
    // Given a cyclotomic element r in Q(zeta_N), evaluate r in the p-adic ring RR.
    // Such that zeta_N is the Teichmuller lift of eN.
    C := Precision(Qpf); Zpf := IntegerRing(Qpf); R := quo<Zpf|p^C>;
    // zeta_N is guaranteed to lie in RR because the field of N-torsion points contains the Weil pairing. 
    zet := Zpf!TeichmuellerLift(eN, R);
    arr := Eltseq(r);
    return &+[Qpf!(arr[i])*zet^(i-1) : i in [1..#arr]];
end function;

function eval_mak_G_padic(gam, eis1, eis2, sigma_p, eN, diffl, h)
    // Given Eisenstein tables eis1 : CN -> R and eis2 : CNpm -> R with respect to a level structure beta, compute Mak_G(gam) at the level structure h*beta. Also, sigma_p denotes the Frobenius matrix w.r.t. beta.
    
    // gam*g*h*sigma_p = gam*g'*h, thus g' = g*h*sigma_p*h^{-1}.
    assert h*sigma_p*h^(-1) in G; // This is assured because of the twisting operations we have done.
    Gp := sub<GL2|h*sigma_p*h^(-1)>;
    ret := 0;
    ret2 := rGxys[gam];

    // If -I is not in Gp, then we will transverse G/<pm, Gp>.
    // If -I is in Gp, then we will transverse G/Gp and then divide the end result by 2.
    if GL2![-1,0,0,-1] in Gp then eps := 2^(-1); reps, _ := LeftTransversal(G, Gp);
    else eps := 1; reps, _ := LeftTransversal(G, add_pm(Gp,N)); end if; 
    
    for g in reps do
        a,b,c,d := Explode(Eltseq(gam*g*h));
        ret +:= eis1(lift_cusp_CN(a,b))*eis1(lift_cusp_CN(c,d));
    end for;
    Kpf := Parent(eis1(Random(CN))); Qpf := BaseField(Kpf);
    ret *:= eps;
    // "ret" lies in Kpf. We're going to take the trace down to Kp, which is not actually defined.
    // So we do it the following way...
    ret := Kpf![Trace(rr) : rr in Eltseq(ret)];

    // Lastly, subtract the eis2 terms.
    for g in Keys(ret2) do 
        // in general the rGGxy's won't be defined over Q, only Q(zN), because the Eis2GamG's are only 
        // defined over Q(zN); but the Eis2G's are defined over Q.
        rGGxy := &+[Conjugate(ret2[sec(GL2![io(-d),0,0,1]*g*get_det_elt(d))],ZZ!io(-d)) : d in ZN];
        ret -:= eval_padic(Conjugate(rGGxy, Integers()!Determinant(h)), eN, Qpf) * evaluate_Eis2GamG(g, eis2, h);
        // ret -:= Kpf!(Rationals()!rGGxy) * evaluate_Eis2GamG(g, eis2, h);
    end for;
    ret *:= diffl(Kpf.1);
    return [ZZ!(Eltseq(rr)[1]) : rr in Eltseq(ret)];
end function;

function basepts(E,beta,f)
    // We compute representatives g in G\GL_2(N)/mu_E such that acting by \sigma_p preserves the double coset.
    P1,P2 := Explode(beta);
    // Automorphisms and Frobenius.
    alph := aut_gen(E,f);
    mu := endo_matrix(E,P1,P2,alph,f); muE := sub<GL2|[mu]>;
    sigma_p := endo_matrix(E,P1,P2,frob(E),f);
    // The double coset space G\GL2/A_E.
    reps, sec, stabs := dbl_coset(G,GL2,muE);
    ret := [g : g in reps | sec(g*sigma_p) eq g];
    // Now let us partition "ret" into the elliptic g, and the non-elliptic g.
    ell_pts := [g : g in ret | #stabs[g] eq #muE];
    nonell_pts := [g : g in ret | #stabs[g] ne #muE];
    // ... now for the fun part. Sometimes, in the non-elliptic case, it may happen that 
    // sigma_p does not actually lie inside of g^{-1}Gg, but only sigma_p * a does.
    ret2 := AssociativeArray();
    j := ZZ!jInvariant(E);
    if 1728 mod p eq j then
        // In this case, any level structure g for which sigma_p doesn't actually lie in G
        // will lie in G once we take a quartic twist.
        eps := PrimitiveRoot(p); 
        ret2[1] := [g : g in nonell_pts | g*sigma_p*g^(-1) in G];
        ret2[eps] := [g : g in nonell_pts | not g*sigma_p*g^(-1) in G];
    elif j eq 0 and (p mod 3 eq 1) then 
        // In this case, we will take a cubic twist.
        eps := PrimitiveRoot(p);
        _, alphh := IsIsomorphism(alph);
        z3 := IsomorphismData(alphh)[4]^2; // So alph is given by (x,y) :-> (z3*x, \pm y).
        if (eps^(ZZ!((p-1)/3)) mod p) ne z3 then 
            eps := (eps^2 mod p);
        end if;
        ret2[1] := [g : g in nonell_pts | g*sigma_p*g^(-1) in G];
        ret2[eps] := [g : g in nonell_pts | g*sigma_p*mu*g^(-1) in G and (not g in ret2[1])];
        ret2[(eps^2 mod p)] := [g : g in nonell_pts | g*sigma_p*mu^2*g^(-1) in G and (not g in ret2[1])
                                                        and (not g in ret2[eps])];
    elif j eq 0 and (p mod 3 eq 2) then  
        for i in [1..#nonell_pts] do
            while not nonell_pts[i]*sigma_p*nonell_pts[i]^(-1) in G do
                nonell_pts[i] := nonell_pts[i] * mu; 
            end while;  
        end for;
        ret2[1] := nonell_pts;
    end if;
    for kk in Keys(ret2) do 
        if #ret2[kk] eq 0 then Remove(~ret2, kk); end if;
    end for;
    return ell_pts, ret2;
end function;

function twist_me(E,beta,f,tw)
    // Assume the j-invariant is 0 or 1728.
    // Then this function takes in E : y^2 = x^3 + bx or y^2 = x^3 + b,
    // a level structure beta = <P1,P2> of E[N], and a number tw,
    // and outputs E_new : y^2 = x^3 + b*tw*x or y^2 = x^3 + b*tw,
    // and the level structure given by applying the map
    // (x,y) :-> (tw^(1/2)*x,tw^(3/4)*y) resp. (tw^(1/3)*x, tw^(1/2)*y).
    Fp := Integers(p); Fq := GF(p^f);
    R<X> := PolynomialRing(Fq);
    P1,P2 := Explode(beta);
    if jInvariant(E) eq 0 then
        a6 := aInvariants(E)[5];
        E_new := EllipticCurve([Fq!0,Fq!tw*Fq!a6]);
        aa := Roots(X^6-tw)[1][1];
        P1 := E_new ! [P1[1] * aa^2 , P1[2] * aa^3, 1];
        P2 := E_new ! [P2[1] * aa^2 , P2[2] * aa^3, 1];
    elif jInvariant(E) eq 1728 then
        a4 := aInvariants(E)[4];
        E_new := EllipticCurve([Fq!tw*Fq!a4,Fq!0]);
        aa := Roots(X^4-tw)[1][1];
        P1 := E_new ! [P1[1] * aa^2 , P1[2] * aa^3, 1];
        P2 := E_new ! [P2[1] * aa^2 , P2[2] * aa^3, 1];
    else 
        bad1 := 0; bad2 := 1/bad1;
    end if; 
    return E_new, <P1, P2>, WeilPairing(P1,P2,N);
end function;

supersingular_jinvs := [dat[1] : dat in Roots(SupersingularPolynomial(p))];

function canonical_lift(j0bar)
    return ZZ!j0bar;
    // j0bar := j0bar mod p;
    // assert not (j0bar in supersingular_jinvs);
    // if j0bar mod p eq 0 then return 0;
    // elif j0bar mod p eq 1728 then return 1728;
    // end if;
    // R<X> := PolynomialRing(Zp);
    // return HenselLift(Evaluate(classic_modpoly(p), [X,X]), j0bar, C);
end function;

function find_xi(Pol)
    // Given "modpoly", which is assume to be the modular polynomial for p for either j-j0, \gamma_2 or \gamma_3,
    // find the \xi such that the polynomial modpoly(x,-x) splits up into (x^2-\xi)*(other stuff), and where the unique 
    // roots of positive valuation are in the x^2-\xi factor.
    R := Parent(Pol);
    temp2 := R![Coefficient(Pol,2*i) : i in [0..Floor(Degree(Pol)/2)]];
    ret := Roots(temp2, Zp)[1][1];
    return ret;
end function;

function generate_list(C)
    // Generates a list of C integers, none of which are divisible by p, making sure they're "evenly" distributed mod p.
    q := Floor(C/(p-1)); r := C - q*(p-1);
    return &cat[[(i-1)*p+1..(i-1)*p+(p-1)] : i in [1..q]] cat [q*p+1..q*p+r];
end function;

function interp(interp_list)
    POL<X> := PolynomialRing(Rationals());
    return CRT([POL!dat[2] : dat in interp_list], [X^(p+1) - dat[1]*p : dat in interp_list]);
end function;

j_invs := GL2jInvariants(G, p);
printf "You have chosen the prime %o.\nThe j-invariants are %o.\n", p, j_invs;
printf "The supersingular j-invariants are %o.\n", [dat : dat in j_invs | dat in supersingular_jinvs];
Fp_pt_info := AssociativeArray(); // This is a dictionary assigning j0 in Z to a tuple <(E,beta,f),{h_i},{h_j}>, where E is an elliptic curve with j-invariant j0, beta is a basis <P1,P2> of E[N] defined over GF(p^f), the {h_i} give the points that afford j-j0 as a uniformizer, and the {h_j} give the non-elliptic points if j0 is 0 or 1728 (so {h_j} is empty if j0 is not one of those.) 
for j0 in j_invs do
    // j00 is a lift of j0 to Z.
    if j0 eq 0 then j00 := 0; 
    elif 1728 mod p eq j0 then j00 := 1728;
    else 
        try j00 := canonical_lift(j0); catch e j00 := ZZ!j0; end try;
    end if;
    printf "For j = %o mod %o:\n", j00, p;
    E,beta,f,eN := E_and_basis(j0);
    printf "The %o-torsion field is of degree f = %o over its prime field.\n", N, f;
    ell_pts, nonell_pts := basepts(E,beta,f);
    printf "The elliptic level structures are %o.\nThe non-elliptic level structures are %o.\n", {Eltseq(x) : x in ell_pts}, assoc_to_tup(nonell_pts);
    // Fp_pt_info has keys <j00, kk>, where
    // j00 is the j-invariant, and kk is the number to twist by.
    // The values are <E,beta,f,eN,ell_pts,non_ell_pts,is_supersingular,j00>.
    is_sup := (j0 in supersingular_jinvs);
    for kk in Keys(nonell_pts) do
        if kk eq 1 then 
            Fp_pt_info[<j0,kk>] := <E,beta,f,eN,ell_pts,nonell_pts[kk], is_sup, j00>;
        else 
            E_new, beta2, eN_new := twist_me(E, beta, f, kk); // ell_pts is empty because j-invariant doesn't require twisting.
            Fp_pt_info[<j0,kk>] := <E_new,beta2,f,eN_new,[],nonell_pts[kk], is_sup, j00>;
        end if;
    end for;
    if (not 1 in Keys(nonell_pts)) and #ell_pts gt 0 then 
        // This is just if we didn't encounter kk=1 and we had elliptic points to add.
        Fp_pt_info[<j0,1>] := <E,beta,f,eN,ell_pts,[],is_sup, j00>;
    end if;
end for;


// After this:
// You've got the Eisenstein tables for some j0. T=p,2p,...,Cp.
// Now you want to compute Mak_G(gam) at h, for various gam in T[io_makdisi[i]], and h in ell_pts or nonell_pts.
basept_exps := [**];
for blahblah in Keys(Fp_pt_info) do 
    j0, tw := Explode(blahblah);
    E,beta,f,eN,ell_pts,nonell_pts, is_sup, j00 := Explode(Fp_pt_info[blahblah]);
    pts := ell_pts cat nonell_pts;
    // alphs is [alph_1, ..., alph_C] for some integers alph_i
    // tables is AssociativeArray() indexed by alphs, and each value is <Eis1table, Eis2table, Kp>.
    // sigma_p gives the frobenius matrix,
    // and R gives a ring where all N-torsion points are defined.
    alphs := generate_list(C);
    tables, sigma_p := generate_Eis_tables(j00, E, beta, f, alphs : tw := tw);
    for h in pts do
        Texps_h := [];
        for i in [1..#io_makdisi] do 
            gam := T[io_makdisi[i]];
            // Don't forget to multiply by this!
            if j00 eq 0 then diffl := func<t | -(12*(tw*t^3-1728))^(-1)>;
            elif j00 eq 1728 then diffl := func<t | -(18*(tw*t^2+1728))^(-1)>;
            else diffl := func<t | -(36*(t+j00)*(t+j00-1728))^(-1)>; end if;
            // This will give Mak_G(gam) at h\beta at the points T=p,2p,...,Cp.
            coeffs := Eltseq(interp([<idx, eval_mak_G_padic(gam, tables[idx][1], tables[idx][2], sigma_p, eN, diffl, h)> : idx in Keys(tables)])); 
            C_new := (p+1)*Ceiling(C*(1-p/(p^2-2*p+1))); // This accounts for precision loss from Lagrange interp.
            coeffs := [Qp!(coeffs[i]) : i in [1..C_new]];
            // #coeffs;
            // [Valuation(coeffs[i]) : i in [1..#coeffs]]; bad1 := 0; bad2 := 1/bad1; 
            // If elliptic j=1728, then coefficients will look like 2*u*a_0*T + 2*u^2*a_1*T^3 + .....
            if j00 eq 1728 and h in ell_pts then 
                coeffs := [coeffs[2*idx]*(2*(tw*p)^idx)^(-1) : idx in [1..Floor(C_new/2)]];
            // If elliptic j=0, then coefficients will look like 3*u*a_0*T^2 + 3*u^2*a_1*T^5 + .....
            elif j00 eq 0 and h in ell_pts then 
                coeffs := [coeffs[3*idx]*(3*(tw*p^2)^idx)^(-1) : idx in [1..Floor(C_new/3)]];
            end if;
            Append(~Texps_h, coeffs);
        end for;
        Append(~basept_exps, <j0, j00, h, (h in ell_pts), tw, is_sup, Matrix(Qp, #io_makdisi, #(Texps_h[1]), Texps_h)>);
    end for;
end for;

////////////////////////////////////////////////
// Now I know, that a rainbow, /////////////////
// rises high above my brow. ///////////////////
// On the path that I have taken, //////////////
// and from a bright distance it can be seen. //
// And those who stand nearest to me here, /////
// and think they know me well, ////////////////
// they nevertheless cannot see, ///////////////
// how it shines above me so redeemingly. //////
////////////////////////////////////////////////


//Zp2s := AllExtensions(Zp, 2); Zp3s := AllExtensions(Zp, 3);
// Rt<t> := PolynomialRing(Zp);
// // basept_exps is a list containing a tuple <j00, is_ell_pt, tw, is_sup, t_exp_matrix>
// // where j00 is the j-invariant, tw is how much I twisted by, and the rest are self explanatory.
// // Precompute classical modular polynomials.
// xis := AssociativeArray();
// for dat in basept_exps do 
//     j0, j00, is_ell_pt, _, is_sup, __ := Explode(dat);
//     j_ell_key := <j0, is_ell_pt>;
//     if j_ell_key in Keys(xis) or (not is_sup) 
//         then continue;
//     elif (not is_ell_pt) and (j0 - 1728) eq 0 then 
//         Pol := Evaluate(gam3_modpoly(p), [t,-t]);
//     elif (not is_ell_pt) and j0 eq 0 then 
//         Pol := Evaluate(gam2_modpoly(p), [t,-t]);
//     else 
//         Pol := Evaluate(classic_modpoly(p), [t+j00, -t+j00]);
//     end if;
//     xis[j_ell_key] := find_xi(Pol);
// end for;

// assoc_to_tup(xis);

XQp1 := AssociativeArray();
// basept_exps is a list containing a tuple <j00, is_ell_pt, tw, is_sup, t_exp_matrix>
// where j00 is the j-invariant, tw is how much I twisted by, and the rest are self explanatory.
// Precompute classical modular polynomials.
mpolys := AssociativeArray();
for dat in basept_exps do 
    j0, j00, h, is_ell_pt, tw, _, __ := Explode(dat);
    j_ell_key := <j0, is_ell_pt, tw>;
    if j_ell_key in Keys(mpolys) then 
        continue;
    elif (not is_ell_pt) and (j0 - 1728) eq 0 then 
        Pol := Evaluate(gam3_modpoly(p), [0, X]);
        Pol := &+[Coefficient(Pol,2*i) * tw^i * X^(2*i) : i in [0..Floor(Degree(Pol)/2)]];
    elif (not is_ell_pt) and j0 eq 0 then
        Pol := Evaluate(gam2_modpoly(p), [0, X]); 
        if (p mod 3) eq 1 then 
            Pol := &+[Coefficient(Pol,3*i+2) * tw^i * X^(3*i+2) : i in [0..Floor(Degree(Pol)/3)]];
        end if;
    else 
        Pol := Evaluate(classic_modpoly(p), [j00, j00+X]);
    end if;
    mpolys[j_ell_key] := Pol;
end for;

for dat in basept_exps do
    j0, j00, h, is_elliptic, tw, is_sup, T_exps := Explode(dat);
    C_T := NumberOfColumns(T_exps);
    // This matrix gives you antiderivatives.
    antideriv_mat := ChangeRing(DiagonalMatrix([1/i : i in [1..C_T]]),Qp);
    // This computes the Coleman integrals from j00 to {cusps}.
    power_sums := col_vector(newton_girard_arr(mpolys[<j0, is_elliptic, tw>], C_T));
    // if not is_sup then 
    //     big_coleman_vals := ChangeRing(col_vector([0 : i in [1..Nrows(T_exps)]]),Qp);
    // else 
    //     ssC_T := Floor(C_T/2);
    //     scaling_mat := DiagonalMatrix([(-2*i*p^(2*i-1)*tw^i)^(-1) : i in [1..ssC_T]]);
    //     xi := xis[<j0, is_elliptic>];
    //     big_coleman_vals := ChangeRing(Submatrix(T_exps,[1..Nrows(T_exps)],[2*i : i in [1..ssC_T]]),Qp) * ChangeRing(scaling_mat,Qp) * ChangeRing(col_vector([xi^i : i in [1..ssC_T]]),Qp);
    // end if;
    // tiny_coleman_exps := p * ChangeRing(T_exps,Qp) * antideriv_mat;
    // final_pow_sers := HorizontalJoin(big_coleman_vals, tiny_coleman_exps);
    big_coleman_vals := -ChangeRing((p+1-Hecke_mat(p))^(-1),Qp) * T_exps * antideriv_mat * power_sums;
    tiny_coleman_exps := T_exps * antideriv_mat;
    XQp1[<j00, Eltseq(h), is_elliptic, tw>] := HorizontalJoin(big_coleman_vals, tiny_coleman_exps);
    // We need to compute roots over all of the rings in Exts.
    // Exts := [Zp];
    //if is_elliptic then Exts := [Zp];
    //elif j00 eq 0 then Exts := Zp3s; 
    //else assert j00 eq 1728; Exts := Zp2s; end if;
    // This computes the Coleman integrals from j00 to j.
    // for Zpp in Exts do 
    //     pi := UniformizingElement(Zpp);
    //     Zppt<t> := PolynomialRing(Zpp);
    //     small_coleman_exps := p * ChangeRing(T_exps,Qp) * ChangeRing(antideriv_mat,Qp); // BUGGY, MAKE T_exps A MATRIX!!
    //     // This assembles the above to get power series, and then turns them into the Coleman integrals of the annihilating differentials.
    //     final_pow_sers := HorizontalJoin(big_coleman_values, small_coleman_exps);
    //     // Now you need to find the intersection of the roots of each row in final_pow_sers. I DON'T KNOW HOW TO TAKE INTERSECTIONS OF THINGS WITH VARYING PRECISION!!!!
    //     final_sers := GCD([Zppt!row : row in Rows(final_pow_sers)]);
    //     if is_elliptic then temp_roots := Roots(final_sers, Zp);
    //     elif j00 eq 0 then temp_roots := [r^3 : r in Roots(final_sers, Zp)];
    //     else assert j00 eq 1728; temp_roots := [r^2+1728 : r in Roots(final_sers, Zp)]; end if;
    //     Append(~XQp1_dat, temp_roots);
    // end for;
end for;