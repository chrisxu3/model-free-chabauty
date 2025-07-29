// determining annihilating differentials from cusp forms

// defining cusp forms and precision
M := 200;
level := 37;
R<q>:=LaurentSeriesRing(Rationals(),M);
C2 := CuspForms(level, 2);
C2 := BaseExtend(C2, Rationals()); 
SetPrecision(C2, M);

// recovering newforms from LMFDB
N2 := Newforms(C2); 
f_37_LMFDB := N2[2][1]; // defined over Q so don't need complex embeddings etc

// writing newforms as a linear combination of eisenstein series 
sturm_bound := Floor((level+1)/6);
eisenstein_series := ;
newform_mat := Matrix(Rationals(), 1, sturm_bound+1, [Coefficient(f_37_LMFDB[i], j): j in [0..sturm_bound]]);
eisensten_mat := Matrix(Rationals(), #, sturm_bound+1, [[Coefficient(C2.i, j): j in [0..sturm_bound]]: i in [1..#]]);
newform_solutions := Solution(eisensten_mat, newform_mat);
newform_from_eisenstein := &+[newform_solutions[i][j]*C2.j: j in [1..#]];
