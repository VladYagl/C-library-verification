#include "string.h"

void *memset(void *dest, int c, size_t n)
{
    //@ assert n ≥ 0;
	unsigned char *s = dest;
    /*@ ghost before: ; */
	size_t k;

	/* Fill head and tail with minimal branching. Each
	 * conditional ensures that all the subsequently used
	 * offsets are well-defined and in the dest region. */

	if (!n) return dest;

    //@ assert based(s, (unsigned char*)dest);
	s[0] = c;
	s[n-1] = c;
	if (n <= 2) return dest;
	s[1] = c;
	s[2] = c;
	s[n-2] = c;
	s[n-3] = c;
	if (n <= 6) return dest;
	s[3] = c;
	s[n-4] = c;
	if (n <= 8) return dest;

	/* Advance pointer to align it at a 4-byte boundary,
	 * and truncate n to a multiple of 4. The previous code
	 * already took care of any head/tail that get cut off
	 * by the alignment. */

	k = -(uintptr_t)s & 3;
    /*@ assert 0 ≤ k ≤ 3; */
	s += k;
    /*@ assert 0 ≤ s - \at(s, before) ≤ 3; */
	n -= k;
    /*@ assert 0 ≤ \at(n, Pre) - n ≤ 3; */
    /*@ ghost test: ; */
	n &= -4;
    /*@ assert 0 ≤ n ≤ \at(n, test) - 3; */
    /*@ assert 0 ≤ n ≤ \at(n, Pre) - 6; */

    /*@ assert 0 ≤ \at(n, Pre) - n ≤ 6; */
    /*@ assert \at(n, Pre) - n ≥ s - \at(s, before); */

    /*@ assert  ∀ ℤ i; 0 ≤ i < (s - \at(s, before)) ⇒
            \at(s, before)[i] ≡ (unsigned char)c;  */

    /*@ assert  ∀ ℤ i; \at(n, Pre) - 4 ≤ i < \at(n, Pre) ⇒
            \at(s, before)[i] ≡ (unsigned char)c;  */

	/* Pure C fallback with no aliasing violations. */
    /*@
        loop invariant \at(n, Pre) ≥ n ≥ 0;
        loop invariant \at(n, Pre) ≥ \at(n, LoopEntry) - n ≥ 0;
        loop invariant \at(s, LoopEntry) + (s - \at(s, LoopEntry)) ≡ s;
        loop invariant *(\at(s, LoopEntry) + (s - \at(s, LoopEntry))) ≡ *s;
        loop invariant s - \at(s, LoopEntry) ≡ \at(n, LoopEntry) - n;

        loop invariant ∀ ℤ i; 0 ≤ i < (s - \at(s, before)) ⇒
            \at(s, before)[i] ≡ (unsigned char)c;

        loop invariant  ∀ ℤ i; \at(n, Pre) - 4 ≤ i < \at(n, Pre) ⇒
            \at(s, before)[i] ≡ (unsigned char)c;

        loop invariant (unsigned char *)dest + (s - \at(s, before)) ≡ s;

        loop assigns n, s;
        loop assigns \at(s, before)[0 .. \at(n - 1, Pre)];
    */
	for (; n; n--, s++) *s = c;
    
    /*@ assert s - \at(s, before) ≥ \at(n, Pre) - 3; */
    /*@ assert s - \at(s, before) ≥ \at(n, Pre) - 4; */
    /*@ assert  ∀ ℤ i; 0 ≤ i < \at(n, Pre) ⇒
            \at(s, before)[i] ≡ (unsigned char)c;  */

	return dest;
}
