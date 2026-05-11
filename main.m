G := 0; N := 0; ind := 0; genus := 0; p := 0;

procedure load_crv(l, ~G, ~N, ~ind, ~genus)
    flag := false;
    for X in XX do 
        if l eq X`label or l eq X`name then
            flag := true; 
            G := X`subgroup; crv := X; break;
        end if;
    end for;
    if not flag then
        if l in XX_zyw then 
            Error("This curve has local obstructions, already handled by LMFDB, and thus has no rational points.");
        else 
            Error("No subgroup found!"); 
        end if;
        bad1 := 0; bad2 := 1/bad1; 
    end if;
    try assert crv`genus gt 1; catch e Error(Sprintf("Your curve %o has genus equal to %o and is hence invalid...", l, crv`genus)); end try;
    N := crv`level; ind := crv`index; genus := crv`genus;
end procedure;

procedure load_prime(prime, ~p)
    try 
        assert IsPrime(prime) and prime gt 3 and (N eq 0 or (N mod prime) ne 0);
        p := prime;
    catch e 
        Error(Sprintf("Your prime %o is invalid!", p));
    end try;
end procedure;

procedure set_prec(prec)
    SetDefaultRealField(RealField(prec));
end procedure;

while true do 
    read l, "Enter a curve name: ";
    try load_crv(l, ~G, ~N, ~ind, ~genus); break; catch e continue; end try;
end while;

load "main1_mak_syms.m";
assert assigned bad_primes; assert assigned bad_res_classes;
while true do 
    read pr, "Pick a prime: ";
    try pr := StringToInteger(pr); catch e continue; end try;
    if (not IsPrime(pr)) or (pr in bad_primes) or (oi(pr) in bad_res_classes) or (pr le 3) then print("Bad!"); continue; end if;
    load_prime(pr,~p);
    break;
end while;
load "main2_evaluation.m";