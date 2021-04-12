#include "string.h"

char *strcat(char *dest, const char *src)
{
	// stpcpy(dest + strlen(dest), src);
    size_t tmp = strlen(dest);
    // size_t tmp2 = strlen(src);
    /*@ assert strlen(src) ≡ \at(strlen(src), Pre); */
	__stpcpy(dest + tmp, src); //  /*@ ghost (tmp2) */;
    
    /*@ assert s_same:
            ∀ ℤ j; 0 ≤ j ≤ \at(strlen(src), Pre) ⇒
                \at(src, Pre)[j] ≡ \at(src[j], Pre); */

    /*@ assert strlen(src) ≡ \at(strlen(src), Pre); */
    /*@ assert strlen(dest + \at(strlen(dest), Pre)) ≡ strlen(src); */
    /*@ assert ∀ ℤ j; 0 ≤ j < \at(strlen(dest), Pre) ⇒ 
                    dest[j] ≡ \at(dest[j], Pre); */
    /*@ assert ∀ ℤ j; 0 ≤ j ≤ \at(strlen(src), Pre) ⇒ 
                    dest[j + \at(strlen(dest), Pre)] ≡ src[j]; */
    /*@ assert (dest + \at(strlen(dest), Pre))[\at(strlen(src), Pre)] ≡ 0; */

    /*@ assert dest[\at(strlen(dest) + strlen(src), Pre)] ≡ 0; */
    /*@ assert ∀ ℤ j; 0 ≤ j < \at(strlen(dest) + strlen(src), Pre) ⇒ 
                    dest[j] ≢ 0; */
	return dest;
}
