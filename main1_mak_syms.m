CC := ComplexField();
ZZ := Integers();
QQ := Rationals();

// CONVENTIONS:
// We will refer to Z(N) as Z/NZ. We will refer to Z(N)* and ZN as (Z/NZ)*.

assert assigned G; assert assigned N; assert assigned ind; assert assigned genus;
QzN<zet> := CyclotomicField(N); // G := real_type_conjugate(G);
printf "The group you have chosen has level %o, index %o inside of GL2(%o) and genus %o.\n", N, ind, N, genus;
printf "The group has generators %o", &cat[[Eltseq(mat)] : mat in elts] where elts := Setseq(Generators(G));

// Some geometry associated to Z(N)^2.
GL2 := GL(2, Integers(N)); SL2 := SL(2, Integers(N));
ZN, io := UnitGroup(Integers(N)); oi := Inverse(io);
P1N, secP1 := RightTransversal(GL2, K0(N));
CN, secCN := RightTransversal(GL2, K1(N));
CNpm, secCNpm := RightTransversal(GL2, add_pm(K1(N),N));

// Now we need to define functions going to and from CN and P1N.
function find_inv_pair(a,b) while true do c := Random([1..N]); d := Random([1..N]); if GCD(ZZ!a*d-ZZ!b*c,N) eq 1 then return <Integers(N)!c,Integers(N)!d>; end if; end while; end function;
function lift_cusp_CN(a,b) c,d := Explode(find_inv_pair(a,b)); return secCN(GL2![c,d,a,b]); end function;
function lift_cusp_CNpm(a,b) c,d := Explode(find_inv_pair(a,b)); return secCNpm(GL2![c,d,a,b]); end function;
P1NtoCN := map<car<P1N,ZN> -> CN | dat :-> secCN(GL2![1,0,0,io(u)] * P) where P,u := Explode(dat)>; memoize(~P1NtoCN);
CNtoP1N := map<CN -> car<P1N,ZN> | [<P1NtoCN(dat),dat> : dat in car<P1N,ZN>]>;

// This gives the Sturm bound for X_G, in terms of q_N.
sturmy := Floor(ind/6) * N;
// This gives the Sturm bound for S_2(N^2, chi) for any chi. Note that everything is in terms of q. 
fakephiN2 := 2*N^2-EulerPhi(N^2); // #P1(Z/nZ) = n + n - phi(n). 
full_sturmy := Floor(fakephiN2/6);

// GamG is intersection of G with SL2.
GamG := GammaSb(G,N);
reps, sec, stabs := dbl_coset(Gamma1(N), SL2, GamG);
T, secG := LeftTransversal(SL2,GamG);

// So get_det_elt(d) gives an element of G of determinant d.
alph, _ := Transversal(G, GamG);
get_det_elt := map<ZN -> alph | [<oi(Determinant(a_d)), a_d>: a_d in alph]>;

// What are the cusp widths, and what are the Galois orbits?
CNG, secCNG, stabsCNG := dbl_coset(GamG, SL2, sub<GL2|[GL2![1,1,0,1]]>);
GalCNG := diamond_ops(N);
orbitsCNG := {{secCNG(get_det_elt(-oi(Determinant(m)))*g*m) : m in GalCNG} : g in CNG}; orbitsCNG := [Setseq(o) : o in orbitsCNG];
cusp_to_orbit := map<CNG -> CNG | &cat[[<o[i],o[1]> : i in [1..#o]] : o in orbitsCNG]>;
// infoCNG is a tuple of <g, w, H>, where g is a representative from each Galois orbit of cusps, w is the width of g, and H is the stabilizer of g in the Galois group.
infoCNG := [<o[1], ZZ!(N/#stabsCNG[o[1]]), sub<ZN | [m : m in ZN | secCNG(get_det_elt(-m)*o[1]*GL2![1,0,0,io(m)]) eq o[1]]> >: o in orbitsCNG];
Sort(~infoCNG, func<f,g|f[2]-g[2]>); // This sorts infoCNG in order of increasing width. (The smaller the width, the more precision you need to get the first term.)

// gInd maps g in GL2 to the index of the coset representative in SL2/GamG that g corresponds to.
rInd := map<T->Integers() | t :-> Index(T, t)>; memoize(~rInd);
gInd := map<SL2->Integers() | g :-> rInd(secG(g))>; 

function get_enhanced_sturm_bd()
    // Let I be the Galois orbits of the cusps. For each i in I, choose a representative cusp x_i, with width w_i, and let Q_i be the size of its Galois orbit. 
    // This function computes a C such that \sum_{i in I} Q_i * (Floor(C*w_i/N) - 1) > 2*g - 2. Additionally, it is required that Floor(C*w_i/N) \geq 1 for all i.
    C := 0;
    while &+[(Floor(C/#stabsCNG[g0])-1) : g0 in CNG] le 2*genus - 2 do 
        C +:= 1;
    end while;
    ret := Max([C] cat [#stabsCNG[g0] : g0 in CNG]); 
    return ret;
end function;

function pivots(M)
    /*
        Input: 
            M, a matrix in row-echelon form. Say that there are n columns, and m non-pivot entries.
            That is, the row vectors of M give the relations between a spanning set of n vectors, and there are m basis vectors.
        Output: 
            io_M: [m] -> [n], the unique injective order-preserving map giving the non-pivot columns. This is represented as a length m sequence with entries in [n].
            F, an n x m matrix representing a map from R^n to R^m (basically, a presentation of the vector space that M encodes).
    */
    R := BaseRing(M);
    n := NumberOfColumns(M); k := NumberOfRows(M);
    idx := 1;
    basis_cols := [];
    table := [**]; // Elements of these are <Bool, num>, where the first entry is True iff the corresponding column is a basis column, 
                    // and the second entry is either (1) the corresponding row, if False, or (2) the corresponding index in basis_cols, if True. 
    for i in [1..n] do
        // We start at index (1,1) and go southeast on M.
        if idx gt k or M[idx,i] eq 0 then 
            // If we are here, then we "overstepped" and are currently on a non-pivot column. We record this data, and go east.
            Append(~basis_cols, i); Append(~table, <true, #basis_cols>); 
        else
            // If we are here, then our entry is currently 1 (so we're at a pivot column). 
            // In this case, we record the row number (this is idx), and then go southeast. 
            assert M[idx,i] ne 0;
            Append(~table, <false, idx>); 
            idx := idx + 1; 
        end if;
    end for;
    m := #basis_cols;
    // We construct a mapping R^n to R^m as follows. It should take row vector e_j to:
    F := ZeroMatrix(R, n, m); 
    for jj in [1..n] do 
        j := n+1-jj;
        // If column j in M corresponds to basis column number x := table[j][2], send e_j to f_x.
        if table[j][1] then F[j,table[j][2]] := 1;
        else
            // Otherwise, column j in M is a pivot column where the action is happening at row x := table[j][2];
            // in that row, read off what is happening for each basis column.
            idx := table[j][2];
            ret :=  -1/M[idx, j] * Vector(Submatrix(M,[idx],[j+1..n]) * Submatrix(F,[j+1..n],[1..m]));
            for i in [1..m] do F[j,i] := ret[i]; end for;
        end if;
    end for;
    return basis_cols, F;
end function;

function make_manin_data()
    /* 
        Let us now compute the Manin relation matrix for the modular symbols associated to the left SL2(N)-module C[SL2(N)/GamG].
        This is BEFORE we add in any relations that come from the q-expansion coefficients. 
    */
    rho := GL2![0,1,-1,-1]; sigma := GL2![0,-1,1,0]; eta := GL2![1,0,0,-1];
    // Please note that if there are any repetitions in a row, then that guy deserved to be 0 in the first place, since we work rationally.
    rel_list := [*SparseMatrix(#T, #T, &cat[[<i, gInd(rho^2*T[i]), 1>, <i, gInd(rho*T[i]), 1>, <i, i, 1>] : i in [1..#T]]), 
                SparseMatrix(#T, #T, &cat[[<i, gInd(sigma*T[i]), 1>, <i, i, 1>] : i in [1..#T]]),
                SparseMatrix(#T, #T, &cat[[<i, gInd(eta*T[i]*get_det_elt(oi(-1))), 1>, <i, i, 1>] : i in [1..#T]]) *]; 
    // Also note that there ARE examples for which the above relations are not all the relations between the cusp forms. Example: 10.60.3.d.1
    manin_mat := ChangeRing(VerticalJoin([rel_list[1], rel_list[2], rel_list[3]]), QQ);
    manin_mat := EchelonForm(Matrix(manin_mat));
    io_manin, F_manin := pivots(manin_mat);
    return io_manin, F_manin, manin_mat;
end function;

/*
    Let us now compute the r(x,y) and r_0 that make the expression :
        G1((1,0)/N)*G1((0,1)/N) + r_0*G_2(0) - \sum_{(x,y) \in Cusps} r(x,y)G_2((x,y)/N)
    into a cusp form.
*/

function recognize(A, w, a_exact : B := 1)
    // This is unused, but I decided to leave it in here anyways.
    /*
        Input: 
            A, a finite abelian group.
            w, a function from A to CC, approximating a tuple of Galois conjugates: that is, w(g+sigma) is approximately sigma(w(g)).
            a_exact, a function from A to K, giving a normal basis of K over QQ. That is, a(g+sigma) = sigma(a(g)).
            B, a positive integer representing a denominator bound.
        Output: 
            v, a function from A to CC, giving the true value of w(0), i.e. w(0) = \sum_{g \in A} v(g)*a(g).
    */
    C := Order(A);
    a := map<A->CC | g :-> CC!(a_exact(g))>;
    w_hat := fft(A,w); a_hat := fft(A,a);
    [<g, w_hat(g), a_hat(g)>: g in A];
    what_over_ahat := map<A->CC| g :-> w_hat(g)/a_hat(g)>;
    v := fft(A,what_over_ahat);
    ret := map<A->ZZ | g :-> Round(B*v(g)/C)>;
    return &+[ret(g)*a_exact(g)/B : g in A];
end function;

function recognize_cycl(w, io : B := 1)
    /*
        Input: 
            N, a positive integer.
            w, a function from Z(N)^* to CC, approximating Galois conjugates of a number alpha in Q(zeta_N).
            io, the inclusion from Z(N)^* to Z(N).
            B, an integer such that alpha*B is an algebraic integer.
        Output:
            The exact value of alpha as a cyclotomic number.
    */
    A := AbelianGroup([N]);
    arr := [IsInvertible(r) select <(ZZ!r)*A.1, (Inverse(io)*w)(r)> else <(ZZ!r)*A.1, 0> : r in Integers(N)];
    ww := map<A -> CC | arr>;
    ww_hat := fft(A,ww);
    ww_hat_exact := map<A -> Rationals() | a :-> strict_round(ww_hat(a)*B)/B>;
    ww_exact := ifft(A, ww_hat_exact : exact := true);
    return ww_exact(A.1);
end function;

function eis_projection()
    /* 
        Output: 
            Let r(x,y) be the unique complex numbers such that
                G1((1,0)/N)*G1((0,1)/N) - \sum_{(x,y) \in Cusps} r(x,y)G_2((x,y)/N) 
            is a cusp form.
            The output is precisely the function r:CNpm->Q(zeta_N).
    */
    B := den(N); // From "util_bernoulli.m"
    
    B1bar_N := map<Integers(N) -> QQ | a :-> (ZZ!a)/N - 1/2>; memoize(~B1bar_N);
    ZN_pm, pm := quo<ZN | [Inverse(io)(-1)]>;

    csc2 := map<ZN_pm -> CC | x :-> Cosec( Pi(CC) * ZZ!((Inverse(pm)*io)(-x)) / N )^2 >; memoize(~csc2);

    intr := AssociativeArray();
    for P in P1N do
        a_pr := P[2][1]; a := P[2][2]; if (a_pr eq 0) or (a eq 0) then continue; end if;
        prod_bern_int := map<ZN_pm -> CC | x :-> 4*B1bar_N(lam*a_pr)*B1bar_N(lam*a) where lam := (Inverse(pm)*io)(x)>; memoize(~prod_bern_int);
        temp := poly_div(prod_bern_int, csc2); temp := map<ZN -> CC | x :-> temp(pm(x))>;
        printf "Attempting to recognize cyclotomic numbers for [%o : %o]...\n", a_pr, a;
        money := recognize_cycl(temp, io : B := B);
        temp_fn := map<ZN_pm -> QzN | x :-> Conjugate(money, u) where u := ZZ!(Inverse(pm)*io)(x)>; memoize(~temp_fn); intr[P] := temp_fn;
    end for;

    edge := AssociativeArray();
    for a in ZN do
        d := io(a);
        prod_bern_edge :=  map<ZN_pm -> CC | x :-> -2*CC.1*B1bar_N(lam*d)*Cot(Pi(CC) * ZZ!(lam^(-1))/N) where lam := (Inverse(pm)*io)(x)>; memoize(~prod_bern_edge);
        edge[a] := poly_div(prod_bern_edge, csc2);
    end for;

    edge_map := map<ZN_pm -> QzN | x :-> recognize_cycl(map<ZN -> CC | a :-> edge[a](x)>, io : B:=B)>; memoize(~edge_map);
    neg_edge_map := map<ZN_pm -> QzN | x :-> -edge_map(x)>; memoize(~neg_edge_map);

    ret := func<P | (P[2][2] eq 0) select edge_map else ( (P[2][1] eq 0) select neg_edge_map else intr[P] )>;
    ret := &cat [[<secCNpm(GL2![1,0,0,(Inverse(pm)*io)(u)] * P), (ret(P))(u)> : u in ZN_pm] : P in P1N];
    ret := map<CNpm -> QzN | ret>;
    return ret;
end function;

eis_proj := eis_projection();
printf "Obtained eis_projection.\n";

function r_G_x_y(gam)
    ret := AssociativeArray();
    for g0 in reps do 
        ret[g0] := &+[eis_proj(secCNpm(g0*g*gam^(-1))) : g in RightTransversal(GamG, add_pm(stabs[g0],N))] * #stabs[g0];
    end for;
    return ret;
end function;

function evaluate_Eis2GamG(g0, table2, h)
    cosets := RightTransversal(GamG, add_pm(stabs[g0],N));
    return &+[table2(secCNpm(g0*g*h)) : g in cosets];
end function;

// function Eis_11_mtx_stdform(gam)
//     // Given gam = [a,b,c,d], find [a0:b0] and [c0:d0] in secP1 such that [a:b] = [a0:b0] and [c:d] = [c0:d0],
//     // and also find lambda such that [a,b,c,d] ~ [a0,b0,lambda*c0,lambda*d0].
//     // Then return <[a0:b0], [c0:d0], lambda>. Or, if [a0:b0] is bigger than [c0:d0] in lexicographic order,
//     // return <[c0:d0], [a0:b0], lambda^(-1)>.
//     a := gam[1][1]; b := gam[1][2]; c := gam[2][1]; d := gam[2][2];
//     c0d0 := secP1(gam); a0b0 := secP1(GL2![c,d,a,b]);
//     a0 := a0b0[2][1]; b0 := a0b0[2][2]; c0 := c0d0[2][1]; d0 := c0d0[2][2];
//     w,x := Explode(find_inv_pair(a0,b0)); y,z := Explode(find_inv_pair(c0,d0));
//     guy1 := (a*x-b*w)/(a0*x-b0*w); guy2 := (c*z-d*y)/(c0*z-d0*y);
//     if (ZZ!c0 gt ZZ!a0) or ((ZZ!c0 eq ZZ!a0) and (ZZ!d0 gt ZZ!b0)) then 
//         return <<a0b0, c0d0>, oi(guy2/guy1)>;
//     else 
//         return <<c0d0, a0b0>, oi(guy1/guy2)>;
//     end if;
// end function;

// function Eis_11(gam, h)
//     // Consider the sum \sum_{g in G_{\pm}} gam*g*h.
//     // We group togther matrices that are just scalings of each other.
//     // Then, for each representative [a,b,c,d], we turn it into <[a0,b0],[c0,d0],u>, where (a0,b0),(c0,d0) in P1N and u in Z(N) such that 
//     // [a,b,c,d] is a scaling of [a0,b0,u*c0,u*d0].
//     GL1 := scalars(N);
//     assert GL1 subset G;
//     PG, _ := Transversal(G, GL1);

//     Eis_11_table := AssociativeArray();
//     for g in PG do 
//         tup, lam := Explode(Eis_11_mtx_stdform(gam*g*h));
//         if tup in Keys(Eis_11_table) then Eis_11_table[tup] cat:= [lam]; else Eis_11_table[tup] := [lam]; end if;
//     end for;
//     return Eis_11_table;
// end function;

///////////////////////////////////////////////////////////////////////////////////////////////
// Some helper functions for computing q-expansions of Eisenstein series of weights 1 and 2. //
///////////////////////////////////////////////////////////////////////////////////////////////

function generalized_sigma(k,x,y,n)
    /*
        \sigma_k^{(x,y)}(n) = \sum_{m|n, n/m \equiv x(N)} \sgn(m)*m^k*zeta^{y*m}.
    */
    S := Divisors(n); S := [d : d in S] cat [-d : d in S];
    arr := [Sign(m) * m^k * zet^(ZZ!y*m) : m in S | (ZZ!(n/m) - ZZ!x) mod N eq 0];
    return ((#arr eq 0) select 0 else &+arr);
end function;

function eis_qexp(k,x,y,C : exact := true)
    /*
        Computes the q-expansion of G_k((x,y)/N) up to and including the q_N^{C-1} term. The formula is given by (2*pi*i)^k times
            c_0 + (-1)^k * \sum_{n geq 1} \sigma_{k-1}^{(x,y)}(n) q_N^n,
        where if k = 1 then 
            c_0 = 1/2 * (zeta^y+1)/(zeta^y-1) if x = 0,
            c_0 = x/N - 1/2                   if x != 0,
        or if k = 2 then 
            c_0 = delta_0(x)*(zeta^y+zeta^{-y)-2)^{-1}.
        We always take x to lie in between 0 and N-1.
    */
    // Only works for weight 1 and 2... for now...
    assert k in [1,2];
    if k eq 1 then c0 := (x eq 0) select 1/2 * (zet^(ZZ!y)+1)/(zet^(ZZ!y)-1) else (ZZ!x)/N - 1/2;
    else c0 := (x eq 0) select (zet^(ZZ!y) + zet^(ZZ!(-y)) - 2)^(-1) else 0;
    end if;
    // Add in the rest of the terms.
    ret := [c0] cat [(-1)^k * generalized_sigma(k-1,x,y,n) : n in [1..C-1]];
    return ret; //return fftify(ret);
end function;

function act(fq, b, d)
    // This acts on fq by [1,b,0,d].
    C := Precision(Parent(fq))-1;
    arr := [Coefficient(fq, i) : i in [0..C]];
    arr_ret := [Conjugate(arr[i+1],Integers()!d)*zet^(Integers()!b*i) : i in [0..C]];
    return Parent(fq)!arr_ret;
end function;

function find_bd(x,y)
    // Given x,y such that gcd(x,y,N) = 1, find b and d such that 
    // b*x + d = y (mod N), where gcd(d,N) = 1.
    done := false;
    while not done do 
        a,c := Explode(find_inv_pair(x,y)); // so c*x - d0 = a*y
        if GCD(a,N) eq 1 then done := true; end if;
    end while;
    d0 := c*x - a*y;
    // Now multiply by a^{-1} to get ca^{-1}*x - d0*a^{-1} = y.
    // so let b = c*a^{-1} and d = -d0*a^{-1}.
    ainv := (Integers(N)!a)^(-1);
    return c * ainv, -d0*ainv;
end function;

function eis_qexp_table(C)
    /*
        This returns map<CN -> QzNqN>, map<CNpm -> QzNqN>, giving the weight 1 and weight 2 Eisenstein series q-expansions up to and including q_N^C.
    */
    ret1 := AssociativeArray(); ret2 := AssociativeArray();
    QzNqN<q> := PowerSeriesRing(QzN, C+1);
    for x in [0..N-1] do 
        o := lift_cusp_CN(x,1);
        ret1[o] := QzNqN!eis_qexp(1,x,1,C+1); ret1[secCN(GL2!(-o))] := -ret1[o];
        ret2[secCNpm(o)] := QzNqN!eis_qexp(2,x,1,C+1);
    end for;
    for o in CNpm do
        if o in Keys(ret2) then continue; end if;
        _,__,x,y := Explode(Eltseq(o));
        o1 := lift_cusp_CN(x,1);
        b,d := find_bd(x,y);
        ret1[o] := act(ret1[o1],b,d); ret1[secCN(GL2!(-o))] := -ret1[o];
        ret2[o] := act(ret2[o1],b,d);
    end for;
    // We are going to speed up the computation slightly by noting the cyclotomic action.
    // Gal := sub<GL2|[GL2![1,0,0,io(a)] : a in Generators(ZN)]>;
    // reps1, sec1, stabs1 := dbl_coset(K1(N),GL2,Gal);
    // tot := #reps1; tal := 1;
    // for dat in reps1 do 
    //     if dat in Keys(ret1) then continue; end if;
    //     // Now we're going to compute Eis(x,dy) for all d in Z(N)*... (Where dat = [*,*,x,y].)
    //     sigmas,_ := RightTransversal(Gal, stabs1[dat]); // This gives us the possible [1,0,0,d] to act by.
    //     for sig in sigmas do
    //         o := secCN(dat*sig); x := o[2][1]; y := o[2][2]; o_pm := secCNpm(o); o_neg := secCN(GL2!(-o));
    //         ret1[o] := QzNqN!eis_qexp(1,x,y,C+1); ret1[o_neg] := -ret1[o];
    //         ret2[o_pm] := QzNqN!eis_qexp(2,x,y,C+1);
    //     end for;
    // end for;
    return map<CN -> QzNqN | assoc_to_tup(ret1)>, map<CNpm -> QzNqN | assoc_to_tup(ret2)>;
end function;

// function generate_Eis_tables_infty(C)
//     // This outputs an array length C. Element index i gives me the Eisenstein table <eis1, eis2> evaluated at q = zeta_C^(i-1).
//     assoc := AssociativeArray(); assoc2 := AssociativeArray();
//     A := AbelianGroup([C]);
//     tot := #CNpm; tal := 1;
//     for dat in CN do
//         if dat in Keys(assoc) then continue; end if;
//         x := dat[2][1]; y := dat[2][2];
//         printf "(%o/%o) Computing values of the Eisenstein series of weights 1 and 2 for the vector (%o, %o)...\n", tal, tot, x, y;
//         qexp1 := eis_qexp(1,x,y,C : exact := false); A := Domain(qexp1);
//         qexp2 := eis_qexp(2,x,y,C : exact := false); AA := Domain(qexp2);
//         assoc[dat] := defftify(fft(A,qexp1)); assoc[secCN(GL2![1,0,0,-1]*dat)] := [-blah : blah in assoc[dat]]; 
//         assoc2[secCNpm(dat)] := defftify(fft(AA,qexp2)); 
//         tal +:= 1;
//     end for;
//     return [< map<CN -> CC | [<dat, assoc[dat][c]> : dat in CN]>,
//             map<CNpm -> CC | [<dat, assoc2[dat][c]> : dat in CNpm]> > : c in [1..C]];
// end function;



procedure mak_G_naive(gam,eis1,eis2,~eis11,rGxys,h,~ret)
    ret1 := Transversal(GamG,sub<GL2|[GL2![-1,0,0,-1]]>);
    ret2 := rGxys[gam];
    ret := 0;
    tot := #ret1; tal := 1; tot_save := 0;
    for g in ret1 do 
        // printf "Evaluating %o/%o for gam = %o and h = %o.\n", tal, tot, Eltseq(gam), Eltseq(h);
        gg := gam*g*h;
        a,b,c,d := Explode(Eltseq(gg));
        if not gg in Keys(eis11) then
            //printf "Did not find [%o,%o,%o,%o] in the cache.\n",a,b,c,d;  
            gg1 := Transpose(secCN(Transpose(gg*GL2![0,1,1,0])))*GL2![0,1,1,0];
            ggdiff := gg1^(-1) * gg;
            bb := ggdiff[1][2]; dd := ggdiff[2][2];
            eis11[gg] := act(eis11[gg1],bb,dd); eis11[GL2!(-gg)] := eis11[gg];
        else 
            //printf "Found [%o,%o,%o,%o] in the cache.\n",a,b,c,d; 
            tot_save +:= 1;
        end if;
        ret +:= eis11[gg];
        tal +:= 1;
    end for;

    for g0 in Keys(ret2) do 
        ret -:= ret2[g0] * evaluate_Eis2GamG(g0, eis2, h);
    end for;
end procedure;

// function generate_DFT_rays(eis1)
//     // Given Eisenstein table eis1 (just weight 1 guys), generate a map DFT_ray : P1N -> <map1, map2>. Suppose (a,b) in P1N. Then it gets mapped to:
//     // map1, the DFT of lam :-> eis1((a*lam,b*lam)). (for lam in Z(N)*)
//     // map2, the DFT of lam :-> eis1((a*lam^(-1),b*lam^(-1)).
//     ret := AssociativeArray();
//     for dat in P1N do
//         map1 := fft(ZN, map<ZN -> CC | lam :-> (P1NtoCN*eis1)(<dat,lam>)>);
//         map2 := fft(ZN, map<ZN -> CC | lam :-> (P1NtoCN*eis1)(<dat,-lam>)>);
//         ret[dat] := <map1, map2>;  
//     end for;
//     return ret;
// end function;  

// function generate_conv_prods(P1, P2, dft_rays)
//     // Given P1 = [*,*,a:b] and P2 = [*,*,c:d], compute a function that sends u in ZN to \sum_{lam in ZNpm} eis1(lam*a,lam*b)*eis1(u*lam*c,u*lam*d).
//     ret := ifft(ZN, ptws_mult(dft_rays[P1][2], dft_rays[P2][1]));
//     ret := map<ZN -> CC | u :-> ret(u)/2>; memoize(~ret);
//     return ret;
// end function;

// procedure eval_mak_G(~retval, gam, dft_rays, ~conv_prods, table2, rGxys, h)
//     // Given the DFT ray map from above, and an Eisenstein table table2: CNpm -> R with respect to a level structure \beta, compute Mak_G(gam) at the level structure h*\beta. 
//     Eis_11_table := Eis_11(gam,h); // So this is a dictionary where the keys are <[*,*,a,b],[*,*,c,d]> in P1N x P1N, and the value is an array [a_i]_i; each a_i says that I should compute sum_{u in ZNpm} u*[a,b,a_i*c,a_i*d].
//     ret2 := rGxys[gam];
//     tot := #Keys(Eis_11_table); tal := 1;
//     // First, let us precompute.
//     for tup in Keys(Eis_11_table) do
//         printf "Evaluating %o/%o for gam = %o and h = %o.\n", tal, tot, Eltseq(gam), Eltseq(h);
//         if tup in Keys(conv_prods) then tal +:= 1; continue; end if;
//         P1,P2 := Explode(tup);
//         conv_prods[tup] := generate_conv_prods(P1,P2,dft_rays);
//         tal +:= 1;
//     end for;
//     retval := &+[&+[conv_prods[k](a) : a in Eis_11_table[k]]: k in Keys(Eis_11_table)];
//     ligma := Determinant(h);
//     for mat in Keys(ret2) do 
//         retval -:= CC!Conjugate(ret2[mat], ZZ!ligma) * evaluate_Eis2GamG(mat, table2, h);
//     end for;
// end procedure;

io_manin, F_manin, manin_mat := make_manin_data();

// rGxys is an associative array going from gam :-> {g0 : r^G_{(x,y),gam}}, where gam = [*,*,x,y] as usual.
rGxys := AssociativeArray(); 
for i in [1..#io_manin] do gam := T[io_manin[i]]; rGxys[gam] := r_G_x_y(gam); end for;
printf "Obtained rGxys.\n";
// den_rGxy := LCM([(#Keys(rGxys[gam]) eq 0) select 1 else LCM([Denominator(rGxys[gam][g0]) : g0 in Keys(rGxys[gam])]) : gam in Keys(rGxys)]);
// We load in everything we need.
C := get_enhanced_sturm_bd(); // That is, we are evaluating from 0 to sturmbd, inclusive.

printf "Your sturm bound for every cusp is %o.\n", C;

eis1, eis2 := eis_qexp_table(C);
printf "Obtained q-expansion table for Eisenstein series.\n";
eis11 := AssociativeArray(); // This will memoize the eis11 q-expansions.
for g in CN do
    // If g lies in [*,*,0,1] \ GL2, then g^T * [0,1,1,0] lies in GL2 / [1,*,0,*].
    gg := Transpose(g)*GL2![0,1,1,0];
    a,b,c,d := Explode(Eltseq(gg));
    eis11[gg] := eis1(lift_cusp_CN(a,b))*eis1(lift_cusp_CN(c,d)); eis11[GL2!(-gg)] := eis11[gg];
end for;
printf "Obtained q-expansion table for products of weight 1 Eisenstein series.\n";
// function temptemptemp(P)
//     a,b,c,d := Explode(Eltseq(P));
//     return eis1(lift_cusp_CN(a,b))*eis1(lift_cusp_CN(c,d)) - &+[Conjugate(eis_proj(dat), ZZ!Determinant(P)) * eis2(secCNpm(dat*P)) : dat in CNpm];
// end function;

// function temptemptemptemp(P)
//     return &+[temptemptemp(P*g) : g in GamG];
// end function;

// procedure blahblahblah()
//     while true do 
//         P := Random(SL2);
//         ret := Matrix(QzN, 1, C+1, [Coefficient(fq,j) : j in [0..C]]) where fq := temptemptemptemp(P);
//         if not assigned MM then MM := ret;
//         else MM := VerticalJoin(MM, ret); end if;
//         Rank(MM);
//     end while;        
// end procedure;

cusp_qexps_prelim := AssociativeArray();
tal := 1; 
for g in CNG do
    temptemp := [];
    for i in [1..#io_manin] do 
        qexp_temp := 0;
        printf "Evaluating (%o/%o) gam = %o, (%o/%o) h = %o.\n", i, #io_manin, Eltseq(T[io_manin[i]]), tal, #CNG, Eltseq(g);
        mak_G_naive(T[io_manin[i]],eis1,eis2,~eis11,rGxys,g,~qexp_temp);
        Append(~temptemp, [Coefficient(qexp_temp, j) : j in [0..C]]);
    end for;
    tal +:= 1;
    cusp_qexps_prelim[g] := Matrix(QzN,#io_manin,C+1,temptemp); 
end for;
QzNqN<q> := Parent(qexp_temp);

cusp_qexps := AssociativeArray();
tal := 1; 
for dat in infoCNG do
    g,w,H := Explode(dat);
    temptemp := [];
    for i in [1..#io_manin] do 
        qexp_temp := 0;
        printf "Evaluating cusp_qexps_real for (%o/%o) gam = %o, (%o/%o) h = %o.\n", i, #io_manin, Eltseq(T[io_manin[i]]), tal, #infoCNG, Eltseq(g);
        for d in ZN do
            gg := get_det_elt(d)*g*GL2![1,0,0,io(-d)];
            gam_d := secCNG(gg);
            for u in [0..N-1] do
                if gam_d * GL2![1,u,0,1] * gg^(-1) in GamG then 
                    uu := u; break;
                end if;
            end for;  
            actor := GL2![1,uu,0,1] * GL2![1,0,0,io(d)];
            delete uu;
            qexp_temp +:= act(QzNqN![cusp_qexps_prelim[gam_d][i][j] : j in [1..C+1]], actor[1][2], actor[2][2]); 
        end for;
        Append(~temptemp, [Coefficient(qexp_temp, j) : j in [0..C]]);
    end for;
    tal +:= 1;
    cusp_qexps[g] := Matrix(QzN,#io_manin,C+1,temptemp); 
end for;
print(assoc_to_tup(cusp_qexps));
// // TEST: Don't do anything here.
// eis_tables := generate_Eis_tables_infty(C);
// dft_ray_tables := [generate_DFT_rays(eis_tables[i][1]) : i in [1..C]];
// conv_prod_tables := [AssociativeArray() : i in [1..C]];
// // For each cusp, we are going to compute the q-expansions of each Mak_G(gam) up to and including precision q_N^C.
// cusp_qexps := AssociativeArray();
// cusp_tal := 1;
// for dat in infoCNG do 
//     g,w,H := Explode(dat); w_co := ZZ!(N/w);
//     repsZNH, secZNH := Transversal(ZN, H);
//     // We are at a cusp. Now let's loop over the gams.
//     qexps_g := [];
//     for i in [1..#io_manin] do 
//         // I am going to evaluate Mak_G(gam) at g*[1,0,0,u]*infty for all u in ZN. I will populate this in "temp".
//         gam := T[io_manin[i]];
//         temp := AssociativeArray();
//         gg_tal := 1;
//         for gg in ZN do // for gg in repsZNH do 
//             retvals := [CC!0 : j in [1..C]]; // This will be populated with values of this evaluation at q_N = roots of unity.
//             for j in [1..C] do
//                 printf "(%o/%o cusps (g = %o), %o/%o gams (gam = %o), %o/%o conjugates (gg = %o)) Doing j = %o out of C = %o...\n", cusp_tal, #infoCNG, Eltseq(g), i, #io_manin, Eltseq(T[io_manin[i]]), gg_tal, #ZN,io(gg),j,C; 
//                 eval_mak_G(~retvals[j], gam, dft_ray_tables[j], ~conv_prod_tables[j], eis_tables[j][2], rGxys, g*GL2![1,0,0,io(gg)]); 
//             end for;
//             // Now let me inverse DFT retvals to get the q-expansion coefficients.
//             blah := fftify(retvals); blah_A := Domain(blah);
//             retvals := defftify(ifft(blah_A, blah));
//             temp[gg] := retvals; //for h in H do temp[gg+h] := retvals; end for;
//             gg_tal +:= 1;
//         end for;
//         // OK, good. Now "temp" maps u in ZN to the q-expansion of Mak_G(gam) at g*[1,0,0,u]*infy. Time to recognize the coefficients as cyclotomic numbers!
//         asdf := [recognize_cycl(map<ZN->CC|u :-> temp[u][j]>,io : B := LCM(2,N)^2 * den_rGxy) : j in [1..C]];
//         Append(~qexps_g, asdf);
//         print(asdf);
//     end for;
//     // So: at cusp g, there will be a matrix of q-expansions, the row of index i having the q-expansion of T[io_manin[i]].
//     cusp_qexps[g] := Matrix(QzN, #io_manin, C, qexps_g);
//     cusp_tal +:= 1;
// end for;

// We are going to compute the Makdisi relations, and we will output the new matrix as io_makdisi, F_makdisi. 
num_mak_rel := #io_manin - genus;
printf "The genus is %o and the number of Manin symbols is %o.\nThe number of extraneous relations is %o.\n", genus, #io_manin, num_mak_rel;
cusp_qexps_keys := Setseq(Keys(cusp_qexps));
joined_qexps_mat := HorizontalJoin([cusp_qexps[g] : g in cusp_qexps_keys]);
joined_qexps_mat_rat := Matrix([ &cat[ Eltseq(joined_qexps_mat[i,j]) : j in [1..NumberOfColumns(joined_qexps_mat)]] : i in [1..NumberOfRows(joined_qexps_mat)]]);
tempM := ChangeRing(Matrix(Basis(Kernel(joined_qexps_mat_rat))),QQ); io_M, F_M := pivots(EchelonForm(tempM));
printf "There are %o basis elements of rank 0.\n", #io_M;
printf "The number of positive analytic rank relations is %o.\n", genus - #io_M;
printf "The relations between the Manin symbols are the rows of the following matrix:\n%o\n", tempM;
if #io_M eq 0 then 
    printf "We don't have anything to work with! Goodbye.\n";
    bad1 := 0; bad2 := 1/bad1;
end if;
for dat in infoCNG do
    g,_,__ := Explode(dat);
    old_mat := cusp_qexps[g];
    cusp_qexps[g] := Submatrix(old_mat,[io_M[i] : i in [1..#io_M]], [1..NumberOfColumns(old_mat)]); 
end for;
io_makdisi := [io_manin[io_M[i]] : i in [1..#io_M]]; F_makdisi := F_manin * F_M;
joined_qexps_mat := HorizontalJoin([cusp_qexps[g] : g in cusp_qexps_keys]);


// We will now describe some helper functions to compute the Hecke action on the basis described by io_makdisi, F_makdisi.
QGL2Q := GroupAlgebra(QQ,GL(2,QQ));
QGL2 := GroupAlgebra(QQ,GL2);
function Mer(n,s)
    s := s mod n;
    if s eq 0 then return n * QGL2Q!GL(2,QQ)![n,0,0,1]; end if;
    return n * QGL2Q!GL(2,QQ)![n,0,s,1] - n/s * Mer(s,n) * QGL2Q!GL(2,QQ)![1,1/s,0,-n/s];
end function;

// function tr_cre(p)
//     retlist := [];
//     Append(~retlist, [1,0,0,p]); //Append(~retlist, [p,0,0,1]); // 
//     for r in [Ceiling(-p/2)..Ceiling(p/2)-1] do 
//         x1 := p; x2 := -r; y1 := 0; y2 := 1; a := -p; b := r;
//         Append(~retlist, [x1,x2,y1,y2]); // Append(~retlist, [y2,-x2,-y1,x1]); // 
//         while b ne 0 do
//             q := (Denominator(a/b) eq 2) select (Sign(a/b)*(Abs(a/b)+1/2)) else Round(a/b);
//             c := a-b*q; a := -b; b := c;
//             x3 := q*x2-x1; x1 := x2; x2 := x3; y3 := q*y2-y1; y1 := y2; y2 := y3;
//             Append(~retlist, [x1,x2,y1,y2]); // Append(~retlist, [y2,-x2,-y1,x1]); // 
//         end while;
//     end for;
//     return &+[QGL2!GL2!g : g in retlist];
// end function;

// function blahblah(p, h, n)
//     // This finds the unique orbit representative o and an integer u such that 
//     // G * [1,0,0,p^{-n}] * h = G * o * [1,u,0,p^{-n}].
//     gg := get_det_elt(n*oi(p)) * GL2![1,0,0,p^(-n)] * h;
//     o := cusp_to_orbit(secCNG(gg));
//     for u in [0..N-1] do
//         if o * GL2![1,u,0,p^(-n)] * h^(-1) * GL2![1,0,0,p^n] in GamG then 
//             uu := u; break;
//         end if;  
//     end for;
//     return o, Integers(N)!uu, Integers(N)!p^(-n);
// end function;

function Hecke(p, gam)
    assert GCD(p,N) eq 1;
    assert IsPrime(p); // This formula only works when p is prime; for prime power p, you'll need to do a bit more work.
    // "raw" gives the formula for the Hecke action, in terms of the group algebras. It is a sum of guys of the form c*g.
    // It is related to constructions of Cremona/Heilbronn/Manin/Merel.
    raw := QGL2!GL2![1,0,0,p] + 1/p * &+[ &+[aa[1] * QGL2!GL2!aa[2] : aa in Eltseq(Mer(p,s))]: s in [0..p-1]]; // print(raw);
    // raw := tr_cre(p);
    ret := Vector(#io_makdisi, [0 : i in [1..#io_makdisi]]);
    gam := QGL2!gam;
    
    for aa in Eltseq(raw*gam) do
        c, g := Explode(aa); 
        g_d := get_det_elt(-oi(Determinant(g)));
        v := F_makdisi[gInd(g*g_d)]; // This is a row vector describing what g in GL2 is in terms of the g_i's that form a basis of our space.
        // printf "raw = %o, c = %o, g = %o, normalized g = %o, v = %o.\n", Eltseq(g*(GL2!gam)^(-1)), c, Eltseq(g), Eltseq(g*g_d), v;
        ret +:= c * v;
    end for;
    return ret;

    // temptemp := [];
    // for h in cusp_qexps_keys do
    //     // We are now going to evaluate the above linear combination at [1,0,0,p^{-1}]*h.
    //     o, b, d := blahblah(p,h,1); // So gam*G*[1,0,0,p^{-1}]*h = gam*G*o*[1,b,0,d]
    //     qexp_temp := &+[ret[i]*act(QzNqN!Eltseq(cusp_qexps[o][i]),b,d) : i in [1..#io_makdisi]];
    //     temptemp cat:= [Coefficient(qexp_temp, j) : j in [0..C]];
    // end for;
    // return Solution(joined_qexps_mat, Vector(temptemp));
end function;

function Hecke_raw(p)
    assert GCD(p,N) eq 1; 
    assert IsPrime(p);
    return QGL2!GL2![1,0,0,p] + 1/p * &+[ &+[aa[1] * QGL2!GL2!aa[2] : aa in Eltseq(Mer(p,s))]: s in [0..p-1]];
end function;

function Hecke_mat(p)
    // This is a square matrix. Column number "i" describes what Tp does to the basis vector Mak_G(gam_i).
    ret := VerticalJoin([Hecke(p,T[io_makdisi[i]]) : i in [1..#io_makdisi]]);
    return Transpose(ret);
end function;

function pseudoinv(M)
    // We have an m x n matrix M of column rank n. (So m is at least n.) This function returns an n x m matrix M' such that M'*M = I_n. 
    m := NumberOfRows(M); n := NumberOfColumns(M);
    assert Rank(M) eq n;
    _, T := EchelonForm(M); // This computes an m x m matrix T such that T*M = EchelonForm(M).
    // Note that the first n rows of EchelonForm(M) give the identity matrix I_n. Thus, in order to extract a pseudoinverse, we simply take the first n rows of T.
    return RowSubmatrix(T,1,n);
end function;

// function eval_mat_poly(f, M)
//     // Given a square matrix M and a polynomial f, evaluate f(M).
//     return &+[Coefficient(f, i)*M^i : i in [0..Degree(f)]];
// end function;

// function ZN_good_generators()
//     // This function returns a list of primes that generate the unit group ZN, such that none of them divide N.
//     H := sub<ZN|[0]>; ret := []; p := 2;
//     while #H lt EulerPhi(N) do
//         if (N mod p) ne 0 and not (oi(p) in H) then ret cat:= [oi(p)]; H := sub<ZN|ret>;  end if;
//         p := NextPrime(p); 
//     end while;
//     return [ZZ!io(a) : a in ret];
// end function;

// // We're now going to decompose our space of Makdisi symbols into irreducible Hecke submodules. 
// ZX<X> := PolynomialRing(ZZ);
// // Let us first decompose by nebentypus.
// decomp := [<IdentityMatrix(QQ,genus),IdentityMatrix(QQ,genus), []>]; // The first two entries are M_inv, M, which give the transformation matrix into each piece (i.e. the columns of M are basis vectors for a piece), and the third entry keeps track of the diamond operators. 
// good_prime_gens := ZN_good_generators();
// expofZN := Exponent(ZN);
// for p in good_prime_gens do 
//     Tp := Hecke_mat(p);
//     Tp2 := Hecke_mat(p^2);
//     new_decomp := [];
//     for dat in decomp do 
//         M_inv, M, blah := Explode(dat);
//         Tpdat := M_inv * Tp * M; Tp2dat := M_inv * Tp2 * M;
//         diamond_p := 1/p * (Tpdat^2 - Tp2dat); blah cat:= [diamond_p];
//         f_p := CharacteristicPolynomial(diamond_p); f_p_factors := Factorization(f_p);
//         if #f_p_factors eq 1 then
//             new_decomp cat:= [<M_inv, M, blah>];
//             continue;
//         end if;
//         for f_pi in f_p_factors do 
//             ker := Transpose(Matrix(Basis(Kernel(Transpose(eval_mat_poly(f_pi[1], diamond_p)))))); // This is the kernel of f_pi on "dat" with respect to the basis of "dat".
//             ker_inv := pseudoinv(ker);
//             new_M_inv := ker_inv*M_inv; new_M := M*ker; // This is the kernel of f_pi with respect to basis of everything.
//             new_blah := [ker_inv * diam_ell * ker : diam_ell in blah]; 
//             new_decomp cat:= [<new_M_inv, new_M, new_blah>];
//         end for;
//     end for;
//     decomp := new_decomp;
// end for;
// // Now let us compute the character chi of each piece of decomp.
// for i in [1..#decomp] do 
//     // Diagonalize the diamond operators, get the character angles, get the character from the angle, and get its conductor.
//     mats := Diagonalization(decomp[i][3]);
//     Qze := Parent(mats[1][1][1]); vinf := InfinitePlaces(Qze)[1];
//     args_raw := [Evaluate(mat[1][1], vinf) : mat in mats];
//     angles := [strict_round(Log(z)/(2*Pi(CC)*CC.1)*expofZN)/expofZN : z in args_raw];
//     chi := DirichletCharacterFromAngles(N, good_prime_gens, angles); cond := Conductor(chi);
//     // So now we have <M_inv, M, mult> instead of <M_inv, M, [diamond_matrices]>.
//     decomp[i][3] := NumberOfColumns(decomp[i][2]) / Order(chi);
//     // So now we have <M_inv, M, mult, chi, {a bunch of newspaces}>.
//     decomp[i] cat:= <AssociatedCharacter(cond, chi)>;
//     decomp[i] cat:= <{NewSubspace(CuspidalSubspace(ModularSymbols(chi0,2))) : chi0 in chi0s}> where chi0s := [AssociatedCharacter(dd*cond,chi) : dd in Divisors(N^2/cond)];
// end for;
// // Now we are going to apply Hecke operators.
// // We have decomp = [<M_inv, M, mult, {newspaces kernels}>]. This will be depopulated until it is empty.
// p := 0; 
// irreducible_pieces := []; // This is what we are going to fill up.
// while #decomp gt 0 do 
//     p := NextPrime(p);
//     if (N mod p) eq 0 then continue; end if;
//     Tpmat := Hecke_mat(p);
//     new_decomp := [];
//     // We now see what "Tpmat" does to each Hecke submodule "dat".
//     for dat in decomp do
//         M_inv, M, mult, chi, kers := Explode(dat);
//         Tpdat := M_inv*Tpmat*M; // This gives the Tp matrix on the piece "dat".
//         f_p := CharacteristicPolynomial(Tpdat); f_p_factors := Factorization(f_p);
//         // Now let us consider each distinct irreducible factor.
//         for f_pi in f_p_factors do 
//             if #f_p_factors gt 1 then
//                 piece := Transpose(Matrix(Basis(Kernel(Transpose(eval_mat_poly(f_pi[1], Tpdat)))))); // This is the kernel of f_pi on "dat" with respect to the basis of "dat".
//                 new_M_inv := pseudoinv(piece)*M_inv; new_M := M*piece; // This is the kernel of f_pi with respect to basis of everything.
//             else 
//                 new_M_inv := M_inv; new_M := M;
//             end if;
//             // The new multiplicity of our isotypic component.
//             new_mult := GCD(f_pi[2], ZZ!(mult*NumberOfColumns(new_M)/NumberOfColumns(M)));
//             // We cut down our kernels by T_p, and remove any of the spaces that are dimension 0.
//             new_kers := {Kernel([<p,f_p_factors[1]>],S) : S in kers}; new_kers := {S : S in new_kers | Dimension(S) gt 0};
//             // We check to see if we got a unique irreducible thing in new_kers. This is true if and only if new_kers has size 1, and its unique space S has dimension exactly equal to new_dim/new_mult. 
//             // Oh, wait -- S, as a space of modular symbols, contains cusp forms with multiplicity 2, and S is a newspace for chi and NOT its Galois orbit, so instead we have to do (2*new_dim)/(Order(chi)*new_mult).
//             if #new_kers eq 1 and Dimension(Random(new_kers)) eq (2*NumberOfColumns(new_M))/(Order(chi)*new_mult) then 
//                 Append(~irreducible_pieces, <new_M_inv, new_M, Random(new_kers)>); 
//             else
//                 Append(~new_decomp, <new_M_inv, new_M, new_mult, chi, new_kers>);
//             end if;
//         end for;
//     end for;
//     decomp := new_decomp;
// end while;
// // OK. Now irreducible_pieces is a sequence [<M_inv, M, S>] where M_inv and M give the subspace of Makdisi symbols, and S gives the corresponding newspace in ordinary modular symbols.
// // The map RationalMapping, when applied to an irreducible Hecke module, maps everything to zero if and only if the module is of analytic rank at least 1.
// rzq_pieces := [<dat[1], dat[2]> : dat in irreducible_pieces | Dimension(Kernel(RationalMapping(dat[3]))) ne Dimension(dat[3])];
// rzq_pieces_sanity_check := [<dat[1], dat[2]> : dat in irreducible_pieces | Dimension(Kernel(RationalMapping(dat[3]))) eq 0];
// printf "We should have #rzq_pieces = %o equal to #rzq_pieces_sanity_check = %o\n", #rzq_pieces, #rzq_pieces_sanity_check;
// assert #rzq_pieces eq #rzq_pieces_sanity_check;


// if #rzq_pieces eq 0 then print("Your curve does not have a rank zero quotient. Save it for quadratic Chabauty!"); 
// elif #rzq_pieces eq 1 then print("The optimal rank zero quotient has dimension 1, which means that the Chabauty-Coleman locus will not necessarily be algebraic. Use the recent software of Mayle-Rouse!");
// else printf "The optimal rank zero quotient has dimension %o, which means X(Qp)1 will be algebraic.\n", #rzq_pieces; end if; 

function saturation_transformation(W)
    // Given a matrix W of row vectors of rational numbers, find the matrix T such that T*W is saturated.
    _,P,__ := SmithForm(W); //S,P,Q : Then PWQ = S.
    return ChangeRing(DiagonalMatrix(ElementaryDivisors(W)),Rationals())^(-1) * P;
end function;

// We're now going to determine the "bad" formal immersion primes. This is so that we can avoid having to compute ungodly amounts of q-expansion coefficients.
// Recall that cusp_qexps[g] gives me the q-expansion matrix at the cusp g, whose rows are indexed by the indices of io_makdisi.
// rzq_lin_combs := VerticalJoin([Transpose(dat[2]) : dat in rzq_pieces]); 
// joined_qexps_mat := rzq_lin_combs * HorizontalJoin([cusp_qexps[g] : g in Keys(cusp_qexps)]);
joined_qexps_mat_rat := Matrix([ &cat[ Eltseq(joined_qexps_mat[i,j]) : j in [1..NumberOfColumns(joined_qexps_mat)]] : i in [1..NumberOfRows(joined_qexps_mat)]]);
den_bd := LCM([LCM([Denominator(joined_qexps_mat[i,j]) : j in [1..NumberOfColumns(joined_qexps_mat)]]) : i in [1..NumberOfRows(joined_qexps_mat)]]);
AA := ChangeRing(den_bd * joined_qexps_mat_rat, ZZ);
TT := saturation_transformation(AA)*den_bd;
printf "The saturation matrix is:\n%o\n",TT;
TT := ChangeRing(TT, QzN); // So TT * cusp_qexps[g] gives a basis of integral q-expansions at all cusps.
// At each cusp, we compute the GCD of the absolute norm of the leading terms. The primes that divide these are "bad".
bad_primes := {};
bad_res_classes := {};
printf "GEOMETRICALLY AND AT THE CUSPS:\n";
for dat in infoCNG do 
    g,w,H := Explode(dat);
    // So, if I'm p, then I'm "bad", if I divide all the leading terms, and if g corresponds to an F_p point on X_G. The latter occurs if and only if p mod N lies in H.
    gcd := AbsoluteNorm(ideal<MaximalOrder(QzN) | [ (TT * cusp_qexps[g])[i,ZZ!(N/w) + 1] : i in [1..#io_makdisi] ]>);
    if gcd eq 0 then
        printf "The bad formal immersion primes at cusp %o are everything.\n", Eltseq(g); 
        bad_res_classes join:= {io(x) : x in H};
    else
        printf "The bad formal immersion primes at cusp %o are %o.\n", Eltseq(g), {pe[1] : pe in Factorization(gcd)};
        bad_primes join:= {pe[1] : pe in Factorization(gcd) | (N mod pe[1] ne 0) and oi(Integers(N)!pe[1]) in H};
    end if;
end for;

if #bad_res_classes eq EulerPhi(N) then 
    Error("There is cusp that is never a formal immersion!!"); bad1 := 0; bad2 := 1/bad1;
end if;
bad_primes := {pe[1] : pe in Factorization(N)} join {p : p in bad_primes | not Integers(N)!p in bad_res_classes};
printf "IN TOTAL AND OVER THE RATIONALS:\nThe bad formal immersion primes are the mod %o residue classes %o along with the set %o.\n", N, bad_res_classes, bad_primes;  
// SO THE IMPORTANT STUFF IS:
// rGxys, decomp, rzq_pieces, rzq_lin_combs, bad_primes, bad_res_classes.