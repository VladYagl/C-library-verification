typedef long unsigned int size_t;
typedef unsigned long int uintptr_t;

#define SIZE_T_MAX 4294967295UL
#define UCHAR_MAX 255

/*@
    // weird predicate that means: a.base = b.base
    predicate based(unsigned char* a, unsigned char* b) = a + (b - a) ≡ b;

    predicate based(char* a, char* b) = a + (b - a) ≡ b;

    // I think this one means pointers are in the same memmory chunk or smth
    predicate based_ptr(char *a, char* b) = *(a + (b - a)) ≡ *b;

    predicate based_full(char *a, char* b) = based(a, b) ∧ based_ptr(a, b);

    // proved automatically
    lemma always_based: ∀ char *a, char *b; based(a, b) ⇒ based_ptr(a, b);

    lemma always_based_2: ∀ char *a, char *b; based(a, b);

    predicate based{L1, L2}(char** a) = based(\at(*a, L1), \at(*a, L2));

    predicate based_ptr{L1, L2}(char** a) = 
        based_ptr{L2}(\at(*a, L1), \at(*a, L2));

    predicate based_full{L1, L2}(char** a) = 
        based_full{L2}(\at(*a, L1), \at(*a, L2));
*/

/*@
    axiomatic StrLen {
        logic ℤ strlen(char* s) reads s[0 .. ];

        axiom pos_or_nul:
            ∀ char* s, ℤ i;
                (0 ≤ i ∧ (∀ ℤ j; 0 ≤ j < i ⇒ s[j] ≢ '\0') ∧ s[i] ≡ '\0') ⇒
                    strlen(s) ≡ i;

        axiom no_end:
            ∀ char* s; (∀ ℤ i; 0 ≤ i ⇒ s[i] ≢ '\0') ⇒ strlen(s) < 0;

        //-------
        // I think axioms below can be proved as lemmas

        axiom index_of_strlen:
            ∀ char* s; strlen(s) ≥ 0 ⇒ s[strlen(s)] ≡ '\0';

        axiom before_strlen:
            ∀ char* s; strlen(s) ≥ 0 ⇒ (∀ ℤ i; 0 ≤ i < strlen(s) ⇒ s[i] ≢ '\0');

        axiom less_then_size_t:
            ∀ char* s; strlen(s) ≤ SIZE_T_MAX;

        axiom neg_len:
            ∀ char* s; strlen(s) < 0 ⇒ (∀ ℤ i; 0 ≤ i ⇒ s[i] ≢ '\0');

        //----
        axiom same:
            ∀ char *s, *d; strlen(s) ≥ 0 ⇒ (∀ ℤ i; 0 ≤ i ≤ strlen(s) ⇒ s[i] ≡ d[i]) ⇒ strlen(s) ≡ strlen(d);
    }
        // lemma same:
            // ∀ char *s, *d; strlen(s) ≥ 0 ⇒ (∀ ℤ i; 0 ≤ i ≤ strlen(s) ⇒ s[i] ≡ d[i]) ⇒ strlen(s) ≡ strlen(d);
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
        \at(strlen(a), L1) ≡ \at(strlen(b), L2) ∧ array_equal{L1, L2}(a, b, strlen{L1}(a) + 1);


    // logic functions to model strncat standard behaviour

    logic ℤ min_len(ℤ len, ℤ n) = (0 ≤ len < n) ? len : n;

    logic ℤ len(char* s, ℤ n) = min_len(strlen(s), n);
*/

/*@
    requires valid: valid_read_string(s);
    assigns \nothing;
    ensures \result ≡ strlen(s);
*/
size_t strlen(const char *s);

/*@
    requires valid_d: valid_read_string(d);
    requires valid_src: \valid_read(s + (0 .. (len(s, n - 1)) ));
    requires valid_dest: \valid(d + strlen(d) + (0 .. len(s, n)));
    requires separation: \separated(
            &d[0 .. (strlen(d) + len(s, n))],
            &s[0 .. len(s, n - 1)]
        );

    assigns dest: d[\old(strlen(d)) .. \old(strlen(d) + len(s, n))];
    assigns \result \from d;

    ensures sum: strlen(d) ≡ \old(strlen(d) + len(s, n));
    ensures result_ptr: \result ≡ d;
    ensures d_same: array_equal{Post, Pre}(d, d, \old(strlen(d)));
    ensures s_copied: array_equal{Post, Pre}(
            d, \old(strlen(d)), 
            s, 0, 
            \old(len(s, n))
        );
*/
char *strncat(char *restrict d, const char *restrict s, size_t n);

/*@
    requires valid_s: valid_read_string(s);
    requires valid_dest: \valid(d + (0 .. strlen(s)));
    requires separation: \separated(
            &d[0 .. strlen(s)],
            &s[0 .. strlen(s)]
        );

    // Due to a bug I can't use strlen in assigns
    // so strlen is passed as an extra argument in ghost
    // requires cheat: strlen(s) ≡ n;

    assigns dest: d[0 .. strlen(s)];
    assigns \result \from d;

    ensures len: strlen(d) ≡ \old(strlen(s));
    ensures len_same: strlen(s) ≡ \old(strlen(s));
    ensures result_ptr: \result ≡ d + \old(strlen(s));
    ensures s_copied: string_equal{Pre, Post}(s, d);
    ensures s_same:
        ∀ ℤ j; 0 ≤ j ≤ \at(strlen(s), Pre) ⇒
            s[j] ≡ \old(s[j]);
*/
char *__stpcpy(char *d, const char *s);

/*@
    requires valid_s: valid_read_string(dest);
    requires valid_s: valid_read_string(src);
    requires valid_dest: \valid(dest + strlen(dest) + (0 .. strlen(src)));
    requires separation: \separated(
            &dest[0 .. (strlen(dest) + strlen(src))],
            &src[0 .. strlen(src)]
        );

    assigns dest: (dest + strlen(dest))[0 .. \old(strlen(src))];
    assigns \result \from dest;

    ensures len: strlen(dest) ≡ \old(strlen(dest) + strlen(src));
    ensures result_ptr: \result ≡ dest;
    ensures s_copied: string_equal{Pre, Post}(src, (dest + strlen(dest)));
*/
char *strcat(char *dest, const char *src);


/*@
    // unsafe casts! standtard says: (unsigned char)
    // frama-c can't cast from (void*) to (unsigned char*) sint8 <> uint8
    requires valid_dest: \valid((char *)dest + (0 .. n - 1));

    assigns dest: ((char *)dest)[0 .. (n - 1)];
    assigns \result \from dest;

    ensures set: ∀ ℤ i; 0 ≤ i < n ⇒
        ((char *)dest)[i] ≡ (char)c;
*/
void *memset(void *dest, int c, size_t n);
