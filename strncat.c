#include "string.h"

char *strncat(char *restrict d, const char *restrict s, size_t n)
{
	char *a = d;
	d += strlen(d);

    /*@ 
        loop invariant based{Pre, Here}(&d);
        loop invariant based{Pre, Here}(&s);
        loop invariant s_mem: based_ptr{Pre, Here}(&s);

        loop invariant n_eq:  \at(n, Pre) - n ≡ d - a - \at(strlen(d), Pre);
        loop invariant s_eq:  s - \at(s, Pre) ≡ d - a - \at(strlen(d), Pre);

        loop invariant limits:
            0 ≤ (d - a) - \at(strlen(d), Pre) ≤ \at(len(s, n), Pre);

        loop invariant copied: ∀ ℤ j; 0 ≤ j < d - a - \at(strlen(d), Pre) ⇒
            \at(d, Pre)[j + \at(strlen(d), Pre)] ≡ \at(s, Pre)[j];

        loop assigns n, d, s;
        loop assigns dest:
            (\at(d, Pre) + \at(strlen(d), Pre))
                [0 .. \at(len(s, n), Pre)];
    */
	while (n && *s) n--, *d++ = *s++;
	*d++ = 0;
    
    /*@ assert a[\at(strlen(d) + len(s, n), Pre)] ≡ 0; */

    /*@ assert ∀ ℤ j; 0 ≤ j < \at(strlen(d) + len(s, n), Pre) ⇒ 
                    a[j] ≢ 0; */
	return a;
}
