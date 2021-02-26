#include "string.h"

char *strncat(char *restrict d, const char *restrict s, size_t n)
{
	char *a = d;
	d += strlen(d);

    //@ assert strlen: d == \at(d + strlen(d), Pre);

    /*@ 
        loop invariant based{Pre, Here}(&d);
        loop invariant based{Pre, Here}(&s);
        loop invariant stupid_s: \at(s, Pre) + (d - a - \at(strlen(d), Pre)) ≡ s;

        loop invariant n_eq: \at(n, Pre) - n ≡ d - a - \at(strlen(d), Pre);

        loop invariant limits_pos_lower:  0 ≤ (d - a) - \at(strlen(d), Pre);

        loop invariant s - \at(s, Pre) ≡ d - a - \at(strlen(d), Pre);
        loop invariant *s ≡ \at(s, Pre)[s - \at(s, Pre)];

        loop invariant limits_s_lower: 0 ≤ s - \at(s, Pre);
        loop invariant limits_s_upper: \at(0 ≤ strlen(s) < n, Pre) ⇒ 
            s - \at(s, Pre) ≤ \at(strlen(s), Pre);

        loop invariant s_same_small: \at(0 ≤ strlen(s) < n, Pre) ⇒
            ∀ ℤ j; 0 ≤ j < \at(strlen(s), Pre) ⇒
                \at(s, Pre)[j] ≡ \at(s[j], Pre);

        loop invariant s_same_big: \at(strlen(s) < 0 ∨ n ≤ strlen(s), Pre) ⇒
            ∀ ℤ j; 0 ≤ j < \at(n, Pre) ⇒
                \at(s, Pre)[j] ≡ \at(s[j], Pre);

        loop invariant copied: ∀ ℤ j; 0 ≤ j < d - a - \at(strlen(d), Pre) ⇒
            \at(d, Pre)[j + \at(strlen(d), Pre)] ≡ \at(s, Pre)[j];

        loop assigns n, d, s;
        loop assigns dest:
            (\at(d, Pre) + \at(strlen(d), Pre))
                [0 .. \at(min_len(strlen(s), n), Pre)];
    */
	while (n && *s) n--, *d++ = *s++;
	*d++ = 0;
    
    /*@ assert \at(strlen(s) < 0 ∨ n ≤ strlen(s), Pre) ⇒ n ≡ 0; */
    /*@ assert \at(strlen(s) < 0 ∨ n ≤ strlen(s), Pre) ⇒
            a[\at(strlen(d), Pre) + \at(n, Pre)] ≡ 0; */
    /*@ assert \at(strlen(s) < 0 ∨ n ≤ strlen(s), Pre) ⇒
                ∀ ℤ j; 0 ≤ j < \at(strlen(d), Pre) + \at(n, Pre) ⇒ 
                    a[j] ≢ 0; */

    /*@ assert \at(0 ≤ strlen(s) < n, Pre) ⇒ *s ≡ 0; */
    /*@ assert \at(0 ≤ strlen(s) < n, Pre) ⇒
            a[\at(strlen(d), Pre) + \at(strlen(s), Pre)] ≡ 0; */
    /*@ assert \at(0 ≤ strlen(s) < n, Pre) ⇒
                ∀ ℤ j; 0 ≤ j < \at(strlen(d), Pre) + \at(strlen(s), Pre) ⇒ 
                    a[j] ≢ 0; */
	return a;
}
