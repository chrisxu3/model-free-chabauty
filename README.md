# Disclaimer.

Currently the code is a bit incomplete; if you try to run the instructions below, you will get the variable `XQp1`. To access this variable, do the following after you've performed the instructions below:

```
XXQp1 := assoc_to_tup(XQp1);
# This returns the list of keys of XQp1.
# Each key is a tuple <j00, h, is_elliptic, tw>, where j00 is the j-invariant in question, h is the matrix giving the level structure (this is w.r.t. a chosen basis), is_elliptic gives if the point is elliptic, and tw gives a number that I've "twisted" by.
[dat[1] : dat in XXQp1];
# This returns the list of entries of XQp1.
# Each entry is a matrix with g-r rows and some number of columns.
# Each row gives coefficients for the expansion of a power series with respect to a uniformizer "t", such that "t" satisfies the following relation w.r.t. the j-invariant "j":
# t = j-j00 if j00 isn't 0 or 1728, or if is_elliptic is true.
# j = tw*t^3 if j00 is 0 and is_elliptic is false.
# j = tw*t^2 + 1728 if j00 is 1728 and is_elliptic is false.
[dat[2] : dat in XXQp1];
```

# Usage.

On startup of Magma, run:

`load "main_loader.m";`

When you are told to pick a curve, put in a RSZB label or a modular curve label that is in `gl2data.txt` or `gl2data_zywina_a2.txt`. Examples of things you can input include (excluding the quotes):
"15.90.3.a.1", "Xsp+(8)", "X0(9)"

When you are told to pick a prime, type a prime `p` that is at least 5, that does not divide the level of `G`, that is not in `bad_primes`, and that is not congruent to a number in `bad_residue_classes` mod `N`.

If you want to try another curve, type 

`load "main.m";`

and then the prompt to pick a curve will appear again.

# Primes above 60.

If you want to use primes above 60, you will need to download modular polynomials from Andrew Sutherland's website. See `mod_poly/README.md` for more detail.

# The database.

The file `gl2data_queries.py` obtains all "relevant" curves from the database and stores it in `gl2data.txt`, which is able to be parsed by `gl2data.m`. In our case, those are the curves X_G, such that:
- X_G has genus at least 2.
- det : G -> Z(N)^* is surjective.
- G contains all scalar matrices.
- X_G has no local obstructions to containing rational points.
- There is no G' containing G such that X_{G'} has genus at least 2.
 surjective determinant, containing all scalars, having no local obstructions, and have no parent curve of genus at least 2. 
 
The file `gl2_zywina_a2.txt` contains all LMFDB labels for Zywina's list of 841 congruence groups in his open images paper, except for the ones that already have local obstructions.

# Main files.
`main_loader.m` loads the util files upon startup. \
`main.m` contains the main loop. \
`main1_mak_syms.m` computes a basis of weight 2 cusp forms in terms of Makdisi symbols. \
`main2_evaluation.m` computes the variable `XQp1` (see the "Disclaimer" section above). \

# Util files.

`gl2.m` is Drew's helper list of helpful GL2 functions. \
`util_bernoulli.m` contains a function `den(N)` which helps to speed up some of the computations of Makdisi symbols. \
`util_div_poly.m` contains code to Hensel lift an N-torsion point of E/F_p to \tilde{E}/Z_p. \
`util_lagrange.m` contains code to find an interpolating polynomial f given known values f(1), f(2), ..., f(2^n). It's currently unused. \
`util_mod_poly.m` contains code pertaining to computing the relevant modular polynomials. In particular it contains code to compute \Phi_p^f(0,T) for the modular polynomials f=gam2=j^(1/3), and f=gam3=(j-1728)^(1/2). \
`util.m` contains general utility files, some of them related to GL2, some of them related to Fourier transforms, some of them related to group theory, etc. \





