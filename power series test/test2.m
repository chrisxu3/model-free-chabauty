load "fft.m";

mfprec := 3000;
cfprec := 5000;
SetDefaultRealField(RealField(cfprec));
CF := ComplexField();
M := CuspForms(Gamma0(43), 2);
SetPrecision(M, mfprec);
bas := Basis(M);

tau := (43+Sqrt(-43))/2;
q0 := Exp(2*Pi(CF)*CF.1*tau);

// try N = 200
N := 200;
R<q> := PowerSeriesRing(Rationals(),mfprec);
eta_1 := 1 + &+[(-1)^i*(q^(i*(3*i-1)/2)+q^(i*(3*i+1)/2)) : i in [1..N]];
eta_2 := 1 + &+[(-1)^i*(q^(i*(3*i-1))+q^(i*(3*i+1))) : i in [1..N]];
N_t := 20;

Cputime();
r := Abs(q0)/2;
N_pad := 2^(Ceiling(Log(2,N_t*48+1)));
om := Exp(2*Pi(CF)*CF.1/N_pad);
q_tcs := [q0 + r*om^(k-1) : k in [1..N_pad]];
eta_1_tcs := [Evaluate(eta_1, q0 + r*om^(k-1)) : k in [1..N_pad]];
eta_2_tcs := [Evaluate(eta_2, q0 + r*om^(k-1)) : k in [1..N_pad]];
// Cputime();
// eta_1_taylor := Evaluate(eta_1, q0);
// eta_1_dn := eta_1;
// for i in [1..N_t] do
//     eta_1_dn := Derivative(eta_1_dn);
//     eta_1_taylor := eta_1_taylor + Evaluate(eta_1_dn, q0)*(q^i)/Factorial(i);
// end for;
// eta_2_taylor := Evaluate(eta_2, q0);
// eta_2_dn := eta_2;
// for i in [1..N_t] do
//     eta_2_dn := Derivative(eta_2_dn);
//     eta_2_taylor := eta_2_taylor + Evaluate(eta_2_dn, q0)*(q^i)/Factorial(i);
// end for;
// q_taylor := q0 + q;

// Cputime();
// // N_pad := N_t*6+1;
// N_pad := N_t*48+1;
// q_tcs := dft(pad(Coefficients(q_taylor), N_pad));
// eta_1_tcs := dft(pad(Coefficients(eta_1_taylor), N_pad));
// eta_2_tcs := dft(pad(Coefficients(eta_2_taylor), N_pad));
// Cputime();
// N_pad := #q_tcs;
Cputime();
f_tcs := [q_tcs[i] * (eta_2_tcs[i]/eta_1_tcs[i])^24 : i in [1..N_pad]];
j_tcs := [2^24*f_tcs[i]^2 + 3*2^16*f_tcs[i] + 3*2^8 + 1/f_tcs[i] : i in [1..N_pad]];
Cputime();
j_taylor := ift(j_tcs);
j_taylor := [j_taylor[i]*r^(1-i) : i in [1..N_t+1]];
Cputime();
// f_taylor := q_taylor*(eta_2_taylor/eta_1_taylor)^24;
// j_taylor := 2^24*f_taylor^2 + 3*2^16*f_taylor + 3*2^8 + 1/f_taylor;
// Cputime();

