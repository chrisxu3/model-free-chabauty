CC := ComplexField();

function ee(x)
    return Exp(2*Pi(CC)*CC.1*x);
end function;

procedure memoize(~f)
    // Precomputes the map f.
    X := Domain(f); Y := Codomain(f);
    f := map<X -> Y | [<x,f(x)> : x in X]>;
end procedure;

// Newton-Girard formulae
function newton_girard_arr(P, k)
    // Input: Polynomial P(x) and positive integer k. 
    // Output: sequence of power sums \sum_{(x-r)|P} r^i, for i=1..k.
    n := Degree(P);
    e := AssociativeArray();
    for i in [0..n] do e[i] := (-1)^i * Coefficient(P,n-i)/Coefficient(P,n); end for;

    ret := [];
    for i in [1..k] do 
        if i eq 1 then 
            asdf := (-1)^(i-1) * i*e[i];
        elif i le n then 
            asdf := (-1)^(i-1) * i*e[i] + &+[(-1)^(i-1+j) * e[i-j]*ret[j] : j in [1..i-1]];
        else 
            asdf := &+[(-1)^(i-1+j) * e[i-j]*ret[j] : j in [i-n..i-1]];
        end if;
        Append(~ret, asdf);
    end for;
    return ret;
end function;

function LeftTransversal(G,H)
    /* 
        Input: Group G, subgroup H.
        Output: A left coset transversal. A tuple (T,phi) where T is a subset of G giving reps t*H, and phi: G -> T satisfies g in phi(g)*H. 
    */
    T, sec := Transversal(G,H); T := [g^(-1) : g in T]; sec := map<G->T | g :-> (sec(g^(-1)))^(-1)>; return T,sec;
end function;

function K0(N)
    /*
        Input:
            N, a positive integer.
        Output: 
            K0(N), the subgroup of GL(2,N) consisting of upper triangular matrices.
    */
    A, io := UnitGroup(Integers(N));
    gens := [[io(a),0,0,1] : a in Generators(A)] cat [[1,0,0,io(a)] : a in Generators(A)] cat [[1,1,0,1]];
    return sub<GL(2,Integers(N))|gens>;
end function;

function K1(N)
    /*
        Input:
            N, a positive integer.
        Output: 
            K1(N), the subgroup of GL(2,N) consisting of upper triangular matrices whose first entry is 1.
    */
    A, io := UnitGroup(Integers(N));
    gens := [[io(a),0,0,1] : a in Generators(A)] cat [[1,1,0,1]];
    return sub<GL(2,Integers(N))|gens>;
end function;

function diamond_ops(N)
    A, io := UnitGroup(Integers(N));
    gens := [[1,0,0,io(a)] : a in Generators(A)];
    return sub<GL(2,Integers(N))|gens>;
end function;

function Gamma1(N)
    /*
        Input:
            N, a positive integer.
        Output: 
            Gamma1(N), the subgroup of SL(2,N) consisting of unipotent matrices.
    */
    gens := [[1,1,0,1]];
    return sub<SL(2,Integers(N))|gens>;
end function;

function scalars(N)
    /*
        Input: N, a positive integer.
        Output: The scalar matrices of GL2(N).
    */
    A, io := UnitGroup(Integers(N));
    gens := [[io(a),0,0,io(a)] : a in Generators(A)];
    return sub<GL(2,Integers(N))|gens>;
end function;

function add_pm(G,N)
    GL2 := GL(2,Integers(N));
    return sub<GL2|Setseq(Generators(G)) cat [GL2![-1,0,0,-1]]>;
end function;

function GammaSb(G,N)
    return G meet SL(2,Integers(N));
end function;

function real_type_conjugate(G)
    GL2 := GL(2,BaseRing(G));
    eta := GL2![1,0,0,-1];
    if eta in G then return G; end if;
    NN := Normalizer(GL2,G);
    if eta in NN then return G; end if;
    for h in Transversal(GL2, NN) do
        if eta in NN^h then return G^h; end if; 
    end for;
    print("The group you have chosen has no real type conjugate! Bad!");
    bad1 := 0;
    return 1/bad1;
end function;

function dbl_coset(H,G,K)
    // This function computes reps, sec, stabs, where:
    // "reps" is coset representatives of H\G/K.
    // "sec" gives the map from G -> "reps".
    // "stabs" is a dictionary with keys in "reps", so that stabs[g] = K cap g^{-1}Hg, the stabilizer of the right action of K on Hg.
    idx := #G/#H;
    HbG, secH := Transversal(G,H);
    table := CosetTable(G,H);
    pi := CosetAction(G,H);

    cst_enum := [Identity(G) : i in [1..idx]];
    cst_enum_inv := AssociativeArray();
    // In cst_enum, we'll assign each number in CosetTable to the corresponding coset representative.
    // In cst_enum_inv, we'll do the opposite.
    for g in HbG do cst_enum[table(<1,g>)] := g; cst_enum_inv[g] := table(<1,g>); end for;

    // O is a list of sets, each set containing some numbers in CosetTable.
    // cst_to_dblcst is supposed to assign, to each Hg, a representative in HgK.
    O := Orbits(pi(K));
    cst_to_dblcst := [0 : i in [1..idx]];
    for i in [1..#O] do 
        for n in O[i] do cst_to_dblcst[n] := O[i][1]; end for;
    end for;
    
    HbGbK := {cst_enum[O[i][1]] : i in [1..#O]};
    secHK := map<G -> HbGbK | g :-> cst_enum[cst_to_dblcst[cst_enum_inv[secH(g)]]]>;
    stabs := AssociativeArray(); 
    for g in HbGbK do stabs[g] := (K meet Conjugate(H,g)); end for;
    return HbGbK, secHK, stabs;
end function;

function zet(r,N)
    return ee(r/N);
end function;

function fft(A, f : exact := false, bottom_N := 0)
    /* 
        Input: 
            A, a finite "framed" abelian group with generators A.1,..., A.n, satisfying diagonal relation.
            f, a function on A.
            exact, true if we are to use cyclotomic numbers (default is false).
        (Don't use this, this is only used for recursion purposes.)
            bottom_N, the exponent of N at the bottom of the recursion.
        Output: 
            The discrete Fourier transform of f, with respect to the natural pairing on the generators of A:
            <e_i, e_j> := \delta_{ij}/ord(e) mod 1.
    */
    ZZ := Integers();
    QQ := Rationals();
    CC := ComplexField();
    if Order(A) eq 1 then return f; end if;
    // Find a subgroup B of small index.
    B := CompositionSeries(A)[2];
    repts := SetToSequence(Transversal(A,B)); // So A = {B+rep : rep in repts}.
    N := Exponent(A); // In the comments, I am always referring to everything mod 1, i.e. in (1/N)Z/Z. But the code refers via Z/NZ.
    b_N := (bottom_N eq 0) select N else bottom_N; 
    ddiff := ZZ!(b_N/N);
    
    divv := map<Integers(N) -> QQ | n :-> (ZZ!n)/N>;
    m := NumberOfGenerators(B); n := NumberOfGenerators(A);
    _, pair := Dual(A); // So "pair" does what <e_i, e_j> does, except it identifies (1/N)Z/Z with Z/NZ by the usual mapping.
    
    // Do note that a \in A, does induce an element of B^\vee via b :-> <b,a>.
    // Concretely, this means that B.j :-> <A!B.j, a> for all j. The isomorphism B to B^\vee sends B.j to (B.i :-> \delta_{ij}/Order(B.j) mod 1), 
    // therefore the element "a" induces \sum_j <A!B.j, a>*Order(B.j)*B.j as an element of B. We denote this by the mapping X.
    X := (Order(B) eq 1) select hom<A -> B | a :-> B!0> 
        else hom<A -> B | [&+[ZZ!( divv(pair(A!B.j,A.i))*Order(B.j) )* B.j : j in [1..m]] : i in [1..n]]>;
    // We have fhat(a) = \sum_{k \in A/B} \sum_{b \in B} f(b+s(k)) <b,a><s(k),a> = \sum_{k \in A/B} fkhat(X(a)) * <s(k),a>,
    // where fk(b) := f(b+s(k)).
    if not exact then 
        f_ks := [fft(B, map<B -> CC | [<b,f(b+repts[i])>: b in B]>) : i in [1..#repts]];
        return map<A -> CC | [<a, &+[f_ks[i](X(a)) * ee(divv(pair(repts[i],a))) : i in [1..#repts]]> : a in A]>;
    else
        QzN<zet> := CyclotomicField(b_N);
        f_ks := [fft(B, map<B -> QzN | [<b,f(b+repts[i])>: b in B]> : exact := exact, bottom_N := b_N) : i in [1..#repts]];
        return map<A -> QzN | [<a, &+[f_ks[i](X(a)) * zet^(ddiff*ZZ!pair(repts[i],a)) : i in [1..#repts]]> : a in A]>;
    end if;
end function;

function ifft(A, f : exact := false)
    // Returns the inverse Fourier transform of f, which is simply given by a :-> 1/#A * FFT(f)(-a). 
    fhat := fft(A,f : exact := exact);
    CC := Codomain(fhat);
    return map<A -> CC | [<a, 1/#A * fhat(-a)> : a in A]>;
end function;

function fftify(seq)
    // Given a sequence (array) of length N, return the corresponding map from AbelianGroup([N]) to values.
    N := #seq;
    A := AbelianGroup([N]);
    Y := Parent(seq[1]);
    return map<A -> Y | [<r*A.1, seq[r+1]> : r in [0..N-1]]>;
end function;

function defftify(f)
    // Given a map from AbelianGroup([N]) to Y, return the corresponding list.
    A := Domain(f); assert IsCyclic(A);
    N := Exponent(A);
    return [f(r*A.1) : r in [0..N-1]];
end function;

function ptws_op(f,g,op)
    X := Domain(f); Y := Codomain(f); assert X eq Domain(g);
    return map<X -> Y | [<x, op(f(x),g(x))> : x in X]>;
end function; 

ptws_add := func<f,g | ptws_op(f,g, func<x,y|x+y>)>;
ptws_sub := func<f,g | ptws_op(f,g, func<x,y|x-y>)>;
ptws_mult := func<f,g | ptws_op(f,g, func<x,y|x*y>)>;
ptws_div := func<f,g | ptws_op(f,g, func<x,y|x/y>)>;

poly_add := ptws_add;
poly_sub := ptws_sub;
poly_mult := func<f,g | ifft(A, ptws_mult(fft(A,f),fft(A,g))) where A := Domain(f)>; 
poly_div := func<f,g | ifft(A, ptws_div(fft(A,f),fft(A,g))) where A := Domain(f)>; 

function strict_round(x : prec := 1E-10)
    // This rounds "x" to the nearest integer, but we are assuming that "x" is a good approximation to the integer.
    ret := Round(x);
    aa := Abs(x - ComplexField()!ret);
    if aa gt prec then 
        
        Error("Error! Need more precision... or more likely your Bernoulli denominator isn't quite enough... Here's the continued fraction expansion for the offending term..."); 
        temp := ContinuedFraction(Re(x));
        print(temp);
        truncate := [temp[i] : i in [1..#temp-1]]; 
        val := ContinuedFractionValue(truncate);
        printf "Would you like to change the continued fraction to %o? ", truncate;
        while true do 
            read yn, "(y/n) (or k to keep)";
            if yn eq "y" then break; elif yn eq "k" then val := ContinuedFractionValue(temp); break;
            elif yn eq "n" then bad := 0; bad2 := 1/bad; else continue; end if;
        end while;
        printf "OK! You have determined the value to be %o. Have fun!\n", val;
        return val;
    end if;
    // try printf "Yay! Rounded with an error of 10 to the %o...\n", Ceiling(Log(aa)/Log(10)); catch e print("Yay! Rounded with an error of 10 to the high power..."); end try;
    return ret;
end function;

procedure print_assoc(D)
    // Prints the associative array.
    print([<k, D[k]> : k in Keys(D)]);
    return;
end procedure;

function col_vector(arr)
    return Transpose(Matrix(Vector(arr)));
end function;

function assoc_to_tup(D)
    return [<k, D[k]> : k in Keys(D)];
end function;