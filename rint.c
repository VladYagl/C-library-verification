#include "mathfp.h"

#define DBL_EPSILON 2.22044604925031308085e-16
#define EPS DBL_EPSILON

static const double toint = 1/EPS;

/*@
    lemma abs_eps: \abs(EPS) ≡ EPS;
    
    lemma log_eps: \log(\abs(EPS)) < -10;

    lemma toint_exponent: exponent(EPS) ≡ -52;

    lemma toint_mantissa: mantissa_64bit(EPS) ≡ 0;
*/

/*@
    requires \is_finite(x);

    assigns \nothing;
    ensures (ℤ) \result ≡ \result;
*/
double rint(double x)
{
    // /*@
    //     assert toint_const: mantissa_64bit(toint) ≡ 0;
    // */


    // union {double f; uint64_t i;} u = {x};
	// int e = u.i>>52 & 0x7ff;
	// int s = u.i>>63;
    unsigned long long e = exponent(x);
    unsigned long long s = signbit(x);

	double y;

	if (e >= 0x3ff+52)
		return x;
	if (s)
		y = x - toint + toint;
	else
		y = x + toint - toint;
	if (y == 0)
		return s ? -0.0 : 0;
	return y;
}
