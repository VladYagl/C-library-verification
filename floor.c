#include "mathfp.h"

#define DBL_EPSILON 2.22044604925031308085e-16
#define EPS DBL_EPSILON

static const double toint = 1/EPS;

double floor(double x)
{
	// union {double f; uint64_t i;} u = {x};
	// int e = u.i >> 52 & 0x7ff;
    unsigned long long e = exponent(x);
    unsigned long long s = signbit(x);

	double y;

	if (e >= 0x3ff+52 || x == 0)
		return x;
	/* y = int(x) - x, where int(x) is an integer neighbor of x */
	if (s)
		y = x - toint + toint - x;
	else
		y = x + toint - toint - x;
	/* special case because of non-nearest rounding modes */
	if (e <= 0x3ff-1) {
		// FORCE_EVAL(y);
		return s ? -1 : 0;
	}
	if (y > 0)
		return x + y - 1;
	return x + y;
}
