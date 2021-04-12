#include "mathfp.h"

/*@

    lemma abs_exponent: ∀ ℝ x; exponent(x) ≡ exponent(\abs(x));

    lemma abs_mantissa: ∀ ℝ x; mantissa_64bit(x) ≡ mantissa_64bit(\abs(x));

    lemma abs_signbit: ∀ ℝ x; signbit(\abs(x)) ≡ 0;

    // if x is double =>
    // abs_real((ℝ) x) == (ℝ) ((double) abs_real((ℝ) x))
    lemma abs_is_double: ∀ double x; \is_finite(x) ⇒ 
        \abs(x) ≡ (double) \abs(x);
*/

/*@
    requires finite_arg: \is_finite(x);
    assigns \nothing;

    ensures \abs(x) ≡ \result;

    // ensures signbit(\result) ≡ 0;
    // ensures mantissa(\result) ≡ mantissa(\old(x));
    // ensures exponent(\result) ≡ exponent(\old(x));
*/
double fabs(double x)
{
    signed long long e = signed_exponent(x);
    unsigned long long m = mantissa(x);
    return make_double(0, e, m);
}
