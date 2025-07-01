load "zywina/GL2GroupTheory.m";
load "zywina/ModularCurves.m";

I:=Open("zywina/agreeable.dat", "r");
X:=AssociativeArray();
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		X[y`key]:=y;
	end if;
until not b;

keys := [k: k in Keys(X) | X[k]`is_agreeable and X[k]`genus ge 2];
Sort(~keys, func<a,b|X[a]`level - X[b]`level>);

function OptimalConjugate(X)
	G := X`G;
	N := X`level;
	gens := Generators(G);
	ret_r := 0; ret_h := 0;
	for h in GL(2,Integers(N)) do 
		curr := {g^h : g in gens};
		r := Generator(sub<Integers(N)|[M[2,1] : M in curr]>);
		if r gt ret_r then
			ret_h := curr;
			ret_r := r; 
		end if;
	end for;
	return ret_r, CreateModularCurveRec(N, curr);
end function;

function SL2Genus(H)
	N := Characteristic(BaseRing(H));
	SL2:=SL(2,Integers(N));
    // To compute many of our quantities, there is no harm in adjoining -I to H.
    H0:=sub<SL2|Generators(H) join {SL2![-1,0,0,-1]}>;

    // We first find a set of representatives T of the cosets H0 \ SL2.
    // We construct the map  f: SL2 -> T  for which f(A) and A lie in the same coset.

    T,phi:=RightTransversal(SL2, H0);  
    psi:=map<T->[1..#T] | {<T[i],i>: i in [1..#T]} >;
    f:=phi*psi;  
    
    degree:=#T;  // The index of H0 in SL2.

    // Compute the cusps and their widths
    B:=SL2![1,1,0,1];
    sigma:=Sym(#T)![f(t*B): t in T];   // permutation that describes how B acts on the set H0\SL2 via right multiplication  
    C:=CycleDecomposition(sigma);
    cusps0:=[Rep(c): c in C];
    cusps :=[T[i]: i in cusps0];  
	vinf:=#cusps; // number of cusps

    // Compute number of elliptic points of order 2
    B:=SL2![0,1,-1,0];
    C:=CycleDecomposition(Sym(#T)![f(t*B): t in T]);
    v2:=#[c: c in C | #c eq 1];

    // Compute number of elliptic points of order 3
    B:=SL2![0,-1,1,1];
    C:=CycleDecomposition(Sym(#T)![f(t*B): t in T]);
    v3:=#[c: c in C | #c eq 1];
	return Integers()!( 1 + degree/12 - v2/4 - v3/3 - vinf/2 );
end function;

function Gamma0G(N)
	G := GL(2,Integers(N));
	x,m := MultiplicativeGroup(Integers(N));
	gens := [m(k) : k in Generators(x)];
	return sub<G | [[1,0,0,a] : a in gens] cat [[a,0,0,1] : a in gens] cat [[1,1,0,1]]>;
end function;