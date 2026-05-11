function divisor_add(D1, D2)
    ret := AssociativeArray();
    primes := Keys(D1) join Keys(D2);
    for p in primes do 
        e1 := (p in Keys(D1)) select D1[p] else 0; e2 := (p in Keys(D2)) select D2[p] else 0;
        e := e1 + e2; 
        if e ne 0 then ret[p] := e; end if;
    end for;
    return ret;
end function;

function divisor_mult(lam, D)
    ret := AssociativeArray();
    for p in Keys(D) do ret[p] := lam*D[p]; end for;
    return ret;
end function;

function divisor_positive_part(D)
    ret := AssociativeArray();
    for p in Keys(D) do 
        if D[p] gt 0 then ret[p] := D[p]; end if;
    end for;
    return ret;
end function;

function divisor_ceil(D)
    ret := AssociativeArray();
    for p in Keys(D) do
        e := Ceiling(D[p]); if e ne 0 then ret[p] := e; end if; 
    end for;
    return ret;
end function;

function divisor_floor(D)
    ret := AssociativeArray();
    for p in Keys(D) do
        e := Floor(D[p]); if e ne 0 then ret[p] := e; end if; 
    end for;
    return ret;
end function;

function divisor(r)
    ret := AssociativeArray();
    for dat in Factorization(r) do ret[dat[1]] := dat[2]; end for;
    return ret;
end function;

function divisor_to_num(D)
    return &*[p^(D[p]) : p in Keys(D)];
end function;

function divisor_lcm(divisor_list)
    ret := AssociativeArray();
    for p in (&join [Keys(D) : D in divisor_list]) do 
        e := Max([((p in Keys(D)) select D[p] else 0 ): D in divisor_list]);
        if e ne 0 then ret[p] := e; end if;
    end for;
    return ret;
end function;

function gauss_sum(chi)
    // Given chi primitive of conductor N, output sum_r chi(r)zeta_N^r.
    CC := ComplexField();
    N := Conductor(chi);
    return &+[CC!chi(r)*zet(r,N) : r in [0..N-1]];
end function;

function bernoulli_2(chi)
    CC := ComplexField();
    r_chi := Conductor(chi); if r_chi eq 1 then return divisor(1/6); end if;
    K_2_chi := r_chi^2;
    B_norm := 1;
    for chi_conj in Conjugates(chi) do 
        // This is the determination of the value of d for what's below.
        if r_chi eq 4 then d := 2;
        elif IsPrime(r_chi) and r_chi gt 2 then d := 2*r_chi;
        elif IsPrimePower(r_chi) and ((r_chi mod 2) eq 1) then _,p,__ := IsPrimePower(r_chi); d := 1 - (chi_conj^(-1))(1+p);
        else d := 1;
        end if;
        // We have that d/2 * B_{2,chi} is an algebraic integer.
        B_2chiconj := K_2_chi / (Pi(CC)^2 * gauss_sum(chi_conj)) * Evaluate(LSeries(chi_conj),2) * CC!d/2;
        B_norm := B_norm * B_2chiconj;
    end for;
    d_norm := (not assigned p) select d else AbsoluteNorm(Minimise(d));
    B_norm := strict_round(B_norm); 
    return divisor(Rationals()!(2/d_norm * B_norm));
end function;

function cycl_poly_divisor(m, x)
    return divisor(Evaluate(CyclotomicPolynomial(m), x));
end function;

procedure print_div(D)
    [<p,D[p]> : p in Keys(D)];
end procedure;

function den(N)
    // 1/4 * EulerPhi(N) * N^2 * lcm_{[chi] : chi even, r(chi) divides N} B_{2,chi} * N^2/r(chi) * \prod_{p|N, p\nmid r(chi)} Phi_m(p^2)/p^2
    ret := divisor(1/4 * EulerPhi(N) * N^2);
    blah := Factorization(N);
    div_list := [**];
    for chi0 in CharacterOrbitReps(N) do 
        if IsOdd(chi0) then continue; end if;
        r_chi := Conductor(chi0);
        chi := AssociatedCharacter(r_chi, chi0);
        temp_ret := bernoulli_2(chi);
        temp_ret := divisor_add(temp_ret, divisor(N^2));
        temp_ret := divisor_add(temp_ret, divisor_mult(-1, divisor(r_chi)));

        blahh := Set([dat[1] : dat in Factorization(r_chi)]);

        qn := SplitCharacterLabel(ConreyLabel(chi));

        for p in [dat[1] : dat in blah | not dat[1] in blahh] do 
            m := Denominator(ConreyCharacterAngle(qn[1],qn[2],p));
            temp_ret := divisor_add(temp_ret, cycl_poly_divisor(m, p^2));
            temp_ret := divisor_add(temp_ret, divisor(1/p^2));
        end for;
        Append(~div_list, temp_ret);
    end for;
    ret := divisor_add(ret, divisor_lcm(div_list));
    ret := divisor_positive_part(ret);
    ret := divisor_floor(ret);
    return divisor_to_num(ret);
end function;