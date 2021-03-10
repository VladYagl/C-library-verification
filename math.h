/*@
    ensures (__f ^ \result) ≡ 0;
    assigns \nothing;
*/
static __inline unsigned long long __DOUBLE_BITS(double __f)
{
	union {double __f; unsigned long long __i;} __u;
	__u.__f = __f;
	return __u.__i;
}

#define isnan(x) ((__DOUBLE_BITS(x) & -1ULL>>1) > 0x7ffULL<<52)

/*@
    requires finite_arg: \is_finite(x);
    assigns \nothing;
    // ensures \result ≥ 0;
    // ensures x ≥ 0 ⇒ x ≡ \result;
    // ensures x < 0 ⇒ -x ≡ \result;
    ensures x ≡ \result;
*/
double fabs(double x)
{
	union {double f; unsigned long long i;} u = {x};
	u.i &= -1ULL/2;
	return u.f;
}


/*@
    assigns \nothing;
    ensures \is_NaN(x) ⇒ \result ≡ 1;
    ensures !\is_NaN(x) ⇒ \result ≡ 0;
*/
int nan_test(double x) {
    return isnan(x);
} 


/*@
    assigns \nothing;
    ensures \is_NaN(x) ⇒ \result ≡ 1;
    ensures !\is_NaN(x) ⇒ \result ≡ 0;
*/
int nan_test2(double x) {
	union {double __f; unsigned long long __i;} __u;
	__u.__f = x;
	return (__u.__i & -1ULL>>1) > 0x7ffULL<<52;
} 
