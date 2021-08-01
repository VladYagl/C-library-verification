#include "mathfp.h"

typedef unsigned long long uint64_t;
typedef unsigned int uint32_t;

#define UINT64_MAX 18446744073709551615ULL

/*@
    lemma exp_bounds:
        ∀ double x; x ≢ 0 ⇒ -0x3ff ≤ exponent(x) ≤ 0x400;

    lemma mantissa_bounds:
        ∀ double x; x ≢ 0 ⇒ 0 ≤ mantissa_64bit(x) < (1 << 52);


    // --- LSL Lemmas ---

    lemma lsl_zero_then_less:
        ∀ ℤ x, y; y ≥ 0 ⇒ (x >> y) ≡ 0 ⇒ x < (1 << y);

    lemma lsl_less_then_zero:
        ∀ ℤ x, y; y ≥ 0 ⇒ x < (1 << y) ⇒ (x >> y) ≡ 0;

    lemma lsl_lsl:
        ∀ ℤ x, y, z; 0 ≤ y ⇒ 0 ≤ z ⇒ ((x << y) << z) ≡ (x << (y + z));

    lemma value_1_lsl_64:
        ∀ ℤ x; x ≡ 64 ⇒ (1 << x) ≡ 1 << 64;

    lemma touint64:
        ∀ ℤ x; (uint64_t)x ≡ (x & ((1 << 64) - 1));

    lemma lsl_touint64:
        ∀ ℤ x, y; 0 ≤ y ⇒ (uint64_t)(((uint64_t)x) << y) ≡ (uint64_t)(x << y);

    lemma lsl_touint64_lsl:
        ∀ ℤ x, y, z; 0 ≤ y ⇒ 0 ≤ z ⇒ (uint64_t)(((uint64_t)(x << y)) << z) ≡ (uint64_t)(x << (y + z));

    // This one is wrong, missing x<2^52
    lemma lsl_non_zero_exists:
        ∀ uint64_t x; x > 0 ⇒ (∃ ℤ i; 0 ≤ i ≤ 52 ∧ ((uint64_t)(x << i))>>52 ≢ 0);


    // --- LAND Lemmas ---

    lemma land_commutativity:
        ∀ ℤ x, y, a, b; a ≡ y ⇒ b ≡ x ⇒ ((x & y) ≡ (a & b));

    lemma land_zero:
        ∀ ℤ x, y, n, p; (x ≥ 0 ∧ y ≥ 0 ∧ n > 0 ∧ p > 0) ⇒ y ≡ (p << n) ⇒ x < (1 << n) ⇒ (x & y) ≡ 0;

    lemma land_zero_1:
        ∀ ℤ x, y, n; (x ≥ 0 ∧ y ≥ 0 ∧ n > 0) ⇒ y ≡ (1 << n) ⇒ x < (1 << n) ⇒ (x & y) ≡ 0;


    lemma land_big:
        ∀ ℤ x; 0 ≤ x ⇒ (x & (1 << 62)) ≡ 0 ⇒ (x < (1 << 62));

    lemma land_very_big:
        ∀ ℤ x; 0 ≤ x < (1 << 64) ⇒ (x & (1 << 64)) ≡ 0;

    // lemma ax_conversion:
        // ∀ ℤ i, ℤ uxi; (uxi ≥ 0 ∧ uxi < (1 << 64)) ⇒ (1 << 64) > (uxi * (1 << i)) ≥ (1 << 52) ⇒ ((uint64_t)(uxi << i))>>52 ≢ 0;

    lemma ax_conversion_32bit:
        ∀ uint32_t i, uint32_t uxi; (i ≥ 0 ∧ uxi ≥ 0) ⇒ ((uint32_t)(uxi * (1 << i))) ≡ ((uint32_t)(uxi << i));

    lemma ax_conversion_32bit_hard:
        ∀ ℤ i, ℤ uxi; (i ≥ 0 ∧ uxi ≥ 0 ∧ uxi < (1 << 32)) ⇒ (1 << 32) > ((uint32_t)(uxi * (1 << i))) ≥ (1 << 20) ⇒ ((uint32_t)(uxi << i))>>20 ≢ 0;

    lemma ax_conversion_easy:
        ∀ uint64_t i, uint64_t uxi; (i ≥ 0 ∧ uxi ≥ 0) ⇒ ((uint64_t)(uxi * (1 << i))) ≡ ((uint64_t)(uxi << i));

    lemma ax_conversion_2:
        ∀ ℤ i, ℤ uxi; (i ≥ 0 ∧ uxi ≥ 0 ∧ uxi < (1 << 62)) ⇒ (1 << 62) > ((uint64_t)(uxi * (1 << i))) ≥ (1 << 52) ⇒ ((uint64_t)(uxi << i))>>52 ≢ 0;

    // --- Value Lemmas ---

    lemma value_1_lsl_52:
        ∀ ℤ x; x ≡ 52 ⇒ (1 << x) ≡ 1 << 52;
*/

/*@
    requires finite_arg_x: \is_finite(x);
    requires finite_arg_x: \is_finite(y);
    requires not_zero_x: x ≢ 0;
    requires not_zero_y: y ≢ 0;
    requires not_subnormal_x: exponent(x) + 0x3ff ≢ 0;
    requires not_subnormal_y: exponent(y) + 0x3ff ≢ 0;


    requires finite_arg_x: \is_finite(y);
    requires \valid(quo);
    assigns *quo;

    ensures \result ≡ 0;
*/
double remquo(double x, double y, int *quo)
{
	// union {double f; uint64_t i;} ux = {x}, uy = {y};
	// int ex = ux.i>>52 & 0x7ff;
	// int ey = uy.i>>52 & 0x7ff;
	// int sx = ux.i>>63;
	// int sy = uy.i>>63;

    int ex = exponent(x);
    int ey = exponent(y);
    int sx = signbit(x);
    int sy = signbit(y);
    uint64_t mx = mantissa(x);
    uint64_t my = mantissa(y);

    /*@ assert 0 ≤ ex < 0x800; */
    /*@ assert 0 ≤ ey < 0x800; */


	uint32_t q;
	uint64_t i;
	uint64_t uxi = mx | ((uint64_t)ex << 52) | ((uint64_t)sx << 63);
	uint64_t uyi = my | ((uint64_t)ey << 52) | ((uint64_t)sy << 63);

	*quo = 0;

    // **** SPECIAL CASES ****
	// if (uyi<<1 == 0 || isnan(y) || ex == 0x7ff)
	// 	return (x*y)/(x*y);
	// if (uxi<<1 == 0)
	// 	return x;
    // ***********************

	/* normalize x and y */
	// if (!ex) {
        // // **** SPECIAL CASE :: x.exp == 0 (SUBNORMAL VALUES)

        // /*@ assert ex ≡ 0; */

        // /*@
            // loop invariant 0 ≤ \at(ex, LoopEntry) - ex ≤ 52;
            // loop invariant (uint64_t)(uxi << (\at(ex, LoopEntry) - ex + 12)) ≡ i;
            // loop assigns i, ex;
        // */
	// 	for (i = uxi<<12; i>>63 == 0; ex--, i <<= 1);
	// 	uxi <<= -ex + 1;
	// } else {
        /*@ assert ex ≢ 0; */
		uxi &= -1ULL >> 12;
        uxi = mx;
        /*@ assert uxi ≡ mantissa_64bit(x); */
        /*@ assert uxi < (1 << 52); */
		uxi |= 1ULL << 52;
        /*@ assert just_doit: uxi ≡ mantissa_64bit(x) + (1 << 52); */ // uses: land_zero
	// }
	// if (!ey) {
        // // // **** SPECIAL CASE :: y.exp == 0 (SUBNORMAL VALUES)
        // /*@
            // loop invariant i>>63 == 0;
            // loop assigns i, ey;
        // */
	// 	for (i = uyi<<12; i>>63 == 0; ey--, i <<= 1);
	// 	uyi <<= -ey + 1;
	// } else {
        /*@ assert ey ≢ 0; */
		uyi &= -1ULL >> 12;
		uyi |= 1ULL << 52;
	// }

	q = 0;
	if (ex < ey) {
		if (ex+1 == ey)
			goto end;
		// return x;
		return 0;
	}

	/* x mod y */
    /*@
        loop invariant \at(ex, LoopEntry) ≥ ex ≥ ey;
        loop assigns ex, i, uxi, q;
        loop variant ex - ey;
    */
	for (; ex > ey; ex--) {
		i = uxi - uyi;
		if (i >> 63 == 0) {
			uxi = i;
			q++;
		}
		uxi <<= 1;
		q <<= 1;
	}
    /*@ assert ex ≡ ey; */
	i = uxi - uyi;
	if (i >> 63 == 0) {
		uxi = i;
		q++;
	}
	if (uxi == 0)
		ex = -60;
	else
        /*@ assert 0 ≤ ex < 0x800; */
        /*@ assert uxi > 0; */
        // /*@ assert uxi ≤ (1 << 52); */
        // /*@ assert exists: ∃ ℤ i; 0 ≤ i ≤ 52 ∧ (1 << 64) > (uxi * (1 << i)) ≥ (1 << 52); */ // uses: lsl_non_zero_exists
        // /*@ assert exists: ∃ ℤ i; 0 ≤ i ≤ 64 ∧ ((uint64_t)(uxi << i))>>64 ≢ 0; */ // uses: lsl_non_zero_exists
        /*@ assert exists: ∃ ℤ i; 0 ≤ i ≤ 52 ∧ ((uint64_t)(uxi << i))>>52 ≢ 0; */ // uses: lsl_non_zero_exists
        /*@
            loop invariant uxi ≡ (uint64_t)(\at(uxi, LoopEntry) << (\at(ex, LoopEntry) - ex)); // uses: lsl_touint64_lsl
            // loop invariant ∀ ℤ i; 0 ≤ i ≤ 52 ⇒ (1 << 64) > (uxi * (1 << i)) ≥ (1 << 52) ⇒ \at(ex, LoopEntry) - ex ≤ i; 
            loop invariant ∀ ℤ i; 0 ≤ i ≤ 52 ⇒ ((uint64_t)(\at(uxi, LoopEntry) << i))>>52 ≢ 0 ⇒ \at(ex, LoopEntry) - ex ≤ i; 
            loop invariant 0 ≤ \at(ex, LoopEntry) - ex ≤ 52;
            loop assigns uxi, ex;
        */
		for (; uxi>>52 == 0; uxi <<= 1, ex--);

end:
	/* scale result and decide between |x| and |x|-|y| */
	if (ex > 0) {
		uxi -= 1ULL << 52;
		uxi |= (uint64_t)ex << 52;
	} else {
		uxi >>= -ex + 1;
	}

    // **** FINAL PACK ****
	// ux.i = uxi;
	// x = ux.f;
	// if (sy)
	// 	y = -y;
	// if (ex == ey || (ex+1 == ey && (2*x > y || (2*x == y && q%2)))) {
	// 	x -= y;
	// 	q++;
	// }
	// q &= 0x7fffffff;
	// *quo = sx^sy ? -(int)q : (int)q;
	// return sx ? -x : x;
    return 0;
}
