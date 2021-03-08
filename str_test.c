#include "string.h"

/*@
    requires valid_string(s);
    assigns s[0..(strlen(s) - 2)];
    ensures strlen(s) ≡ \old(strlen(s));
    ensures s ≡ \old(s);
*/
void a(char* s);

/*@
    requires valid_string(s);
    assigns s[0..strlen(\old(s))];
    ensures strlen(s) ≡ strlen(s);
    ensures s ≡ \old(s);
*/
void b(char *s) {
    int x = 0;
    a(s);
    //@ assert x ≡ 0;
}



/*@
    requires valid_string(s);
    assigns s[0..n];
*/
void an(char* s, int n);

/*@
    requires valid_string(s);
    assigns s[0..n];
*/
void bn(char *s, int n) {
    an(s, n);
}
