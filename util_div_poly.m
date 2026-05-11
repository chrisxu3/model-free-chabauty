ZZ := Integers();

// Now we're going to build up division polynomials, whatever that means.
procedure div_poly_populate(A,B,x,y,m,twowhyinv,~table,~grad_table)
    R := Parent(x);
    if (m in Keys(table) and m in Keys(grad_table)) then return; end if;
    if m eq 0 then table[m] := R!0; grad_table[m] := Vector([R!0,R!0]); return; end if;
    if m eq 1 then table[m] := R!1; grad_table[m] := Vector([R!0,R!0]); return; end if;
    if m eq 2 then table[m] := 2*y; grad_table[m] := Vector([R!0,R!2]); return; end if;
    if m eq 3 then table[m] := 3*x^4 + 6*A*x^2 + 12*B*x - A^2; grad_table[m] := Vector([12*y^2, 0]); return; end if;
    if m eq 4 then
        table[m] := 4*y*(x^6 + 5*A*x^4 + 20*B*x^3 - 5*A^2*x^2 - 4*A*B*x - 8*B^2 - A^3);
        grad_table[m] := Vector([4*y*(6*x^5 + 20*A*x^3 + 60*B*x^2 - 10*A^2*x - 4*A*B), 2*table[4]*twowhyinv]);
        return;
    end if;
    // Now let's handle the cases when m is greater than 4.
    if (m mod 2) eq 0 then 
        n := ZZ!(m/2); for k in [n-2,n-1,n,n+1,n+2] do div_poly_populate(A,B,x,y,k,twowhyinv,~table,~grad_table); end for;
        blah := twowhyinv * (table[n+2]*table[n-1]^2 - table[n-2]*table[n+1]^2);
        table[m] := table[n]* blah;
        grad_table[m] := grad_table[n] * blah + table[n]*twowhyinv * 
                        (grad_table[n+2] * table[n-1]^2 + 2*table[n+2]*table[n-1]*grad_table[n-1] - grad_table[n-2] * table[n+1]^2 - 2*table[n-2]*table[n+1]*grad_table[n+1])
                        - Vector([0,2*table[m]*twowhyinv]);
        return;
    else 
        n := ZZ!((m-1)/2); for k in [n-1,n,n+1,n+2] do div_poly_populate(A,B,x,y,k,twowhyinv,~table,~grad_table); end for;
        table[m] := table[n+2]*table[n]^3 - table[n-1]*table[n+1]^3;
        grad_table[m] := grad_table[n+2] * table[n]^3 + 3*table[n+2]*table[n]^2*grad_table[n] - grad_table[n-1]*table[n+1]^3 - 3*table[n-1]*table[n+1]^2*grad_table[n+1];
    end if;
end procedure;

procedure newton_iterate_once(A,B,N,~v)
    // Given column vector v = (x,y)^T, and numbers A and B, perform one step of the iteration
    // v :-> v - (DF)(v)^(-1) * F(v), where we have
    // F(v) := (y^2-x^3-A*x-B, Psi_N(x,y)).
    x := v[1][1]; y := v[2][1];
    table := AssociativeArray(); grad_table := AssociativeArray();
    twowhyinv := 1/(2*y);
    div_poly_populate(A,B,x,y,N,twowhyinv,~table,~grad_table);
    Fv := Vector([y^2 - x^3 - A*x - B, table[N]]);
    grad := grad_table[N];
    DF := Matrix(2,2,[-3*x^2-A, 2*y, grad[1], grad[2]]);
    w := Solution(Transpose(DF), Fv);
    v -:= Transpose(Matrix(w));
    return;
end procedure;

procedure newton_iterate(A,B,N,~v)
    C := Precision(Parent(v[1][1]));
    err := 0;
    while err lt C do 
        old_v := v;
        newton_iterate_once(A,B,N,~v);
        old_x := old_v[1][1]; old_y := old_v[2][1];
        x := v[1][1]; y := v[2][1];
        err := Min(Valuation(old_x-x), Valuation(old_y-y));
        printf "The current precision is %o and the target precision is %o.\n", err, C;
    end while;
end procedure;