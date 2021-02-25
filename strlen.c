#include "string.h"

size_t strlen(const char *s)
{
	const char *a = s;

    /*@ 
        loop invariant based: based{Pre, Here}(&s);
        // loop invariant based_ptr: based_ptr{Pre, Here}(&s);
        loop invariant under_len: 0 ≤ s - \at(s, Pre) ≤ \at(strlen(s), Pre); 

        loop assigns s;
        loop variant \at(strlen(s), Pre) - (s - a);
    */
	for (; *s; s++);

    // //@ assert *(a + (s - a)) ≡ *s;
    // //@ assert a[s - a] ≡ 0;
	return s-a;
}
