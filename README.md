# Usage.

On startup of Magma, run:

load "main_loader.m";

When you are told to pick a curve, put in a RSZB label or a modular curve label that is in "gl2data.txt" or "gl2data_zywina_a2.txt". Examples of things you can input include:
"15.90.3.a.1", "Xsp+(8)", "X0(9)" (no quotes needed)

When you are told to pick a prime, pick a prime p that is at least 5, that does not divide the level of G, that is not in "bad_primes", and that is not congruent to a number in "bad_residue_classes" mod N.

If you want to try another curve, type 

load "main.m";

and then the prompt to pick a curve will appear again.

# Primes above 60.

If you want to use primes above 60, you will need to download modular polynomials from Andrew Sutherland's website. 

# The database.

The file "gl2data_queries.py" obtains all ``relevant'' curves from the database and stores it in "gl2data.txt", which is able to be parsed by "gl2data.m". In our case, those are the curves X_G, such that:
- X_G has genus at least 2.
- det : G -> Z(N)^* is surjective.
- G contains all scalar matrices.
- X_G has no local obstructions to containing rational points.
- There is no G' containing G such that X_{G'} has genus at least 2.
 surjective determinant, containing all scalars, having no local obstructions, and have no parent curve of genus at least 2. 
 
The file "gl2_zywina_a2.txt" contains all LMFDB labels for Zywina's list of 841 congruence groups in his open images paper, except for the ones that already have local obstructions.

# Util files.

"gl2.m" is Drew's helper list of helpful GL2 functions. 
"util_bernoulli.m" contains a function "den(N)" which helps to speed up some of the computations of KM symbols.
"util_div_poly.m" contains code to Hensel lift an N-torsion point of E/F_p to \tilde{E}/Z_p.
"util_lagrange.m" contains code to find an interpolating polynomial f given known values f(1), f(2), ..., f(2^n).
"util_mod_poly.m" contains code pertaining to computing the relevant modular polynomials. In particular it contains code to compute \Phi_p^f(0,T) for the modular polynomials f=gam2=j^(1/3), and f=gam3=(j-1728)^(1/2).
"util.m" contains general utility files, some of them related to GL2, some of them related to Fourier transforms, some of them related to group theory, etc.





