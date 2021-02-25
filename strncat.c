#include "string.h"

char *strncat(char *restrict d, const char *restrict s, size_t n)
{
	char *a = d;
	d += strlen(d);

    //@ assert strlen: d == \at(d + strlen(d), Pre);

    /*@ 
        loop invariant based{Pre, Here}(&d);
        loop invariant stupid_s: \at(s, Pre) + (d - a - \at(strlen(d), Pre)) ≡ s;

        loop invariant n_eq: \at(n, Pre) - n ≡ d - a - \at(strlen(d), Pre);

        loop invariant limits_pos:  0 ≤ (d - a) - \at(strlen(d), Pre);

        // loop invariant d_same: ∀ ℤ j; 0 ≤ j < \at(strlen(d), Pre) ⇒
            // \at(d, Pre)[j] ≡ \at(d[j], Pre);

        loop invariant s_same: ∀ ℤ j; 0 ≤ j < \at(strlen(s), Pre) ⇒
            \at(s, Pre)[j] ≡ \at(s[j], Pre);

        loop invariant copied: ∀ ℤ j; 0 ≤ j < d - a - \at(strlen(d), Pre) ⇒
            \at(d, Pre)[j + \at(strlen(d), Pre)] ≡ \at(s, Pre)[j];

        loop assigns n, d, s;
        loop assigns dest: (\at(d, Pre) + \at(strlen(d), Pre))[0 .. \at(n, Pre)];
    */
	while (n && *s) n--, *d++ = *s++;
	*d++ = 0;
    
    /*@ assert a[\at(strlen(d), Pre) + \at(n, Pre)] ≡ 0; */
    /*@ assert ∀ ℤ j; 0 ≤ j < \at(strlen(d), Pre) + \at(n, Pre) ⇒ 
            a[j] ≢ 0; */
	return a;
}
