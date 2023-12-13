# final_Project - Legendre Symbol Algorithm

This file contains an algorithm to compute the Legendre Symbol. Fix a prime number `p` and an integer `a`. 

# Definitions

The Legendre symbol $\Bigl(\frac{a}{p}\Bigr)$ is 1 is `a` is square mod `p`, -1 if `a` is not square mod `p`, and 0 if `p` divides `a`. In Mathlib, its name is `legendreSym p a`. The Legendre Symbol can be computed using quadratic reciprocity: if `p` and `q` are distinct odd primes, then $\Bigl(\frac{p}{q}\Bigr) = (-1)^{ \frac{p-1}{2} \cdot \frac{q-1}{2}} \Bigl(\frac{p}{q}\Bigr)$. 

This project relies on the multiplicativity of the Legendre Symbol. For integers `a` and `b`, it follows that $\Bigl(\frac{ab}{p}\Bigr) = \Bigl(\frac{a}{p}\Bigr) * \Bigl(\frac{b}{p}\Bigr)$. If `a` is positive, then `legendreSym p a` is the same as multiplying all Legendre Symbols $\Bigl(\frac{q}{p}\Bigr)$ where `q` is a prime factor of `a`. 

Below are the definitions and lemmas. Each of them are stated in the order of which the code is found.

# Supporting definitions and lemmas

A main portion of the project consists of defining `legendre_reciprocity` (which is defined below). Some lemmas and definitions are 
1. `pos_eq_natAbs` proves that a positive integer is equal to its absolute value.
2. `legendre_eq_natAbs` proves that `legendreSym p a = legendreSym p a.natAbs` for positive integers
3. `legendre_neg_mul` proves that `legendreSym p a = (legendreSym p (-1)) * (legendreSym p a.natAbs)` if `a` is negative or zero.
4. `natAbs_legendre_eq_prod_factors` proves that `legendreSym p a` for a positive integer `a` is the same as multiplying all Legendre Symbols $\Bigl(\frac{q}{p}\Bigr)$ where `q` is a prime factor of `a`.

# Important definitions
1. `legendreSym_of_factors_list` sends an integer `a` to a list of the Legendre Symbols of each factor of `a` with respect to a prime `p`. For example, `12 --> [legendreSym p 2, legendreSym p 2,  legendreSym p 3]`. 
2. `legendreSym_of_reciprocity_map` sends an integer `a` to the same list as `legendreSym_of_factors_list`. However, each factor of `a` is mapped to its Legendre Symbol using quadratic reciprocity. For example, `12 --> [χ₈ p, χ₈ p,  (-1) ^ (3 / 2 * (p / 2)) * legendreSym 3 p]`. 
3. `factors_list_eq_reciprocity_map` proves that `legendreSym_of_factors_list` is the same list as `legendreSym_of_reciprocity_map`.

# Main Definitions and Results
1. `legendre_reciprocity` is the main algorithm to compute the Legendre Symbol. `legendre_reciprocity p a` is 0 if `a = 0`. If `p=2`, then we compute the `legendreSym p (a % 2)`, where `a % 2` is 1 or 0.  

Otherwise, `legendre_reciprocity p a` multiplies every entry in `legendreSym_of_reciprocity_map`. This value is multiplied by `(χ₄ p)` if `a` is negative.

2. `legendreSym_eq_legendre_reciprocity` proves that `legendre_reciprocity` outputs the same value `legendreSym`. 