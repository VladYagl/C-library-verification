#define SIZE_T_MAX 4294967295UL

/*@
    axiomatic StrLen {
        logic ℤ strlen(char* s) reads s[0 .. ];

        axiom pos_or_nul:
            ∀ char* s, ℤ i;
                (0 ≤ i ∧ (∀ ℤ j; 0 ≤ j < i ⇒ s[j] ≢ '\0') ∧ s[i] ≡ '\0') ⇒
                    strlen(s) ≡ i;

        axiom no_end:
            ∀ char* s; (∀ ℤ i; 0 ≤ i ⇒ s[i] ≢ '\0') ⇒ strlen(s) < 0;

        axiom less_then_size_t:
           ∀ char* s; strlen(s) ≤ SIZE_T_MAX;

        // axiom index_of_strlen:
        //     ∀ char* s; strlen(s) ≥ 0 ⇒ s[strlen(s)] ≡ '\0';

        //axiom before_strlen:
        //    ∀ char* s; strlen(s) ≥ 0 ⇒ (∀ ℤ i; 0 ≤ i < strlen(s) ⇒ s[i] ≢ '\0');

        //axiom neg_len:
        //    ∀ char* s; strlen(s) < 0 ⇒ (∀ ℤ i; 0 ≤ i ⇒ s[i] ≢ '\0');

        ////-------
        //// I think axiom below can be proved as lemmas

        //axiom same:
        //    ∀ char *s, *d; strlen(s) ≥ 0 ⇒ (∀ ℤ i; 0 ≤ i ≤ strlen(s) ⇒ s[i] ≡ d[i]) ⇒ strlen(s) ≡ strlen(d);
    }

//-----------HELPERS-----------------

    lemma exists_first_2:
        ∀ char* s; ∀ ℤ i; 0 ≤ i ⇒ ((∃ ℤ i1; (0 ≤ i1 ≤ i ∧ (∀ ℤ j; 0 ≤ j < i1 ⇒ s[j] ≢ '\0') ∧ s[i1] ≡ '\0')) ∨ (∀ ℤ j; 0 ≤ j ≤ i ⇒ s[j] ≢ '\0'));

    lemma exists_first:
        ∀ char* s; (∃ ℤ i; 0 ≤ i ∧ s[i] ≡ '\0') ⇒ (∃ ℤ i; (0 ≤ i ∧ (∀ ℤ j; 0 ≤ j < i ⇒ s[j] ≢ '\0') ∧ s[i] ≡ '\0'));

//-----------*AXIOMS*----------------

    lemma index_of_strlen:
        ∀ char* s; strlen(s) ≥ 0 ⇒ s[strlen(s)] ≡ '\0';

    lemma before_strlen:
       ∀ char* s; strlen(s) ≥ 0 ⇒ (∀ ℤ i; 0 ≤ i < strlen(s) ⇒ s[i] ≢ '\0');

    lemma neg_len:
       ∀ char* s; strlen(s) < 0 ⇒ (∀ ℤ i; 0 ≤ i ⇒ s[i] ≢ '\0');

    lemma same:
        ∀ char *s, *d; strlen(s) ≥ 0 ⇒ (∀ ℤ i; 0 ≤ i ≤ strlen(s) ⇒ s[i] ≡ d[i]) ⇒ strlen(s) ≡ strlen(d);
*/
