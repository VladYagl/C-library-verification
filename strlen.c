#include "string.h"

size_t strlen(const char *s)
{
	const char *a = s;

    /*@ 
        loop invariant based: based{Pre, Here}(&s);
        loop invariant based_ptr: based_ptr{Pre, Here}(&s);
        loop invariant under_len: 0 ≤ s - \at(s, Pre) ≤ \at(strlen(s), Pre); 

        loop assigns s;
        loop variant \at(strlen(s), Pre) - (s - a);
    */
	for (; *s; s++);

    // @ assert based_ptr{Pre, Here}(&a);
    // // @ assert (\at(s, Pre))[s - a] ≡ *s;
    // @ assert 0 ≤ s - a ≤ \at(strlen(s), Pre);
    // @ assert s - \at(s, Pre) ≥ \at(strlen(s), Pre);
    // @ assert s - a ≡ \at(strlen(s), Pre);
	return s-a;
}
