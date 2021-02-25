typedef long unsigned int size_t;
#define SIZE_T_MAX 4294967295UL

/*@
    predicate based(char* a, char* b) = a + (b - a) ≡ b;

    predicate based_ptr(char *a, char* b) = *(a + (b - a)) ≡ *b;

    lemma always_based: ∀ char *a, char *b; based(a, b) ⇒ based_ptr(a, b);

    predicate based{L1, L2}(char** a) = based(\at(*a, L1), \at(*a, L2));

    predicate based_ptr{L1, L2}(char** a) = 
        based_ptr{L2}(\at(*a, L1), \at(*a, L2));
*/

/*@
    logic ℤ min(ℤ a, ℤ b) = (a < b) ? a : b;


    axiomatic StrLen {
        logic ℤ strlen(char* s) reads s[0 .. ];

        axiom pos_or_nul:
            ∀ char* s, ℤ i;
                (0 ≤ i ∧ (∀ ℤ j; 0 ≤ j < i ⇒ s[j] ≢ '\0') ∧ s[i] ≡ '\0') ⇒
                    strlen(s) ≡ i;

        axiom no_end:
            ∀ char* s; (∀ ℤ i; 0 ≤ i ⇒ s[i] ≢ '\0') ⇒ strlen(s) < 0;

        axiom index_of_strlen:
            ∀ char* s; strlen(s) ≥ 0 ⇒ s[strlen(s)] ≡ '\0';

        axiom before_strlen:
            ∀ char* s; strlen(s) ≥ 0 ⇒ (∀ ℤ i; 0 ≤ i < strlen(s) ⇒ s[i] ≢ '\0');

        axiom less_then_size_t:
            ∀ char* s; strlen(s) ≤ SIZE_T_MAX;
    }
*/

/*@
    predicate valid_read_string(char* s) =
        strlen(s) ≥ 0 ∧ \valid_read(s + (0 .. strlen(s)));

    predicate valid_string(char* s) =
        strlen(s) ≥ 0 ∧ \valid(s + (0 .. strlen(s)));

    predicate array_equal{L1, L2}(char* a, ℤ a_begin, char* b, ℤ b_begin, ℤ len) =
        ∀ ℤ i; 0 ≤ i < len ⇒ \at(a[a_begin + i], L1) ≡ \at(b[b_begin + i], L2);

    predicate array_equal{L1, L2}(char* a, char* b, ℤ len) =
        array_equal{L1, L2}(a, 0, b, 0, len);

    predicate string_equal{L1, L2}(char* a, char *b) =
        \at(strlen(a), L1) ≡ \at(strlen(b), L2) ∧ array_equal{L1, L2}(a, b, strlen{L1}(a));
*/

/*@
    requires valid: valid_read_string(s);
    assigns \nothing;
    ensures \result ≡ strlen(s);
*/
size_t strlen(const char *s);

/*@
    // Only case if n ≤ strlen(s)
    requires big_enough: n ≤ strlen(s);

    requires valid:         valid_read_string(d);
    requires valid_src:     \valid_read(s + (0 .. (n - 1)));
    requires valid_dest:    \valid(d + strlen(d) + (0 .. n));

    requires separation: 
        \separated(&d[0 .. (strlen(d) + n)], &s[0 .. strlen(s)]);

    assigns dest: d[strlen(d) .. strlen(d) + n];
    assigns res: \result \from d;

    ensures result_ptr: \result ≡ d;
    ensures sum: strlen(d) ≡ \old(strlen(d)) + n;
    ensures d_same:   array_equal{Post, Pre}(d, d, \old(strlen(d)));
    ensures s_copied: array_equal{Post, Pre}(d, \old(strlen(d)), s, 0, n);
*/
char *strncat(char *restrict d, const char *restrict s, size_t n);