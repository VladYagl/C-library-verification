#include "string.h"

char *__stpcpy(char *d, const char *s) /*@ ghost (size_t n) */
{
    /*@ 
        loop invariant based_full{Pre, Here}(&s);
        loop invariant based_full{Pre, Here}(&d);
        loop invariant s_idx: 
            s - \at(s, Pre) ≡ d - \at(d, Pre);

        loop invariant limits_pos_lower: 0 ≤ d - \at(d, Pre);
        loop invariant limits_pos_upper: d - \at(d, Pre) ≤ \at(strlen(s), Pre);

        loop invariant s_same:
            ∀ ℤ j; 0 ≤ j < \at(strlen(s), Pre) ⇒
                \at(s, Pre)[j] ≡ \at(s[j], Pre);

        loop invariant copied: ∀ ℤ j; 0 ≤ j < d - \at(d, Pre) ⇒
            \at(d, Pre)[j] ≡ \at(s, Pre)[j];

        loop assigns d, s;
        loop assigns dest: \at(d, Pre)[0 .. \at(strlen(s), Pre)];
    */
	for (; (*d=*s); s++, d++);

    /*@ assert \at(d, Pre)[\at(strlen(s), Pre)] ≡ 0; */
    /*@ assert \at(s, Pre)[\at(strlen(s), Pre)] ≡ 0; */
	return d;
}

// weak_alias(__stpcpy, stpcpy);
