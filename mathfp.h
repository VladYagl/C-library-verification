/*@
    logic ℤ signbit(ℝ x) = x ≥ 0 ? 0 : 1;

    logic ℤ exponent(ℝ x) =
        \floor(\log(\abs(x)) / \log(2));

    logic ℤ mantissa_64bit(ℝ x) =
        \floor((\abs(x) / \pow(2, exponent(x)) - 1) * (1 << 52));

    logic ℝ make_double(ℤ s, ℤ e, ℤ m) =
        (m + (1 << 52)) /
        \pow(2, \floor(\log(m + (1 << 52)) / \log(2)) - e) *
        \pow(-1, s);

    lemma mantissa_hidden_bit:
        ∀ ℝ x; mantissa_64bit(x) + (1 << 52) ≡ 
            \floor(\abs(x) / \pow(2, exponent(x)) * (1 << 52));

    lemma exponent_signbit_independent:
        ∀ ℝ x; exponent(x) ≡ exponent(\abs(x));

    lemma mantissa_signbit_independent:
        ∀ ℝ x; mantissa_64bit(x) ≡ mantissa_64bit(\abs(x));

    lemma floor_eq:
        ∀ ℝ x, y; x ≡ y ⇒ \floor(x) ≡ \floor(y);

    lemma floor_sum:
        ∀ ℝ x, ℤ y; \floor(x + y) ≡ \floor(x) + y;

    lemma floor_zero:
        ∀ ℝ x; 0 ≤ x < 1 ⇒ \floor(x) ≡ 0;

    predicate is_double(ℝ x) = x ≡ (double) x;

    // axiomatic make_double {

        // // // explicit casts:
        // axiom make_double_from_parts:
        //     ∀ double x; \is_finite(x) ⇒
        //         make_double(signbit((ℝ) x), exponent((ℝ) x), mantissa_64bit((ℝ) x)) ≡ (ℝ) x;

        // // old version
        // axiom make_double_from_parts:
        //     ∀ double x; \is_finite(x) ⇒
        //         make_double(signbit(x), exponent(x), mantissa_64bit(x)) ≡ x;

        // axiom make_double_from_parts:
        //     ∀ ℝ x; x ≡ (double) x ⇒
        //         make_double(signbit(x), exponent(x), mantissa_64bit(x)) ≡ x;
    // } 

    lemma real_ln_nonneg:
        ∀ ℝ x; x ≥ 1 ⇒ \log(x) ≥ 0;

    lemma real_ln_pos:
        ∀ ℝ x; x > 1 ⇒ \log(x) > 0;

    lemma real_log_mono:
        ∀ ℝ x, ℝ y; 0 < x < y ⇒ \log(x) < \log(y);

    lemma real_log_pos:
        ∀ ℝ x, ℝ y; y > 1 ⇒ x ≥ 1 ⇒ \log(x) / \log(y) ≥ 0;

    lemma real_log_less:
        ∀ ℝ x, ℝ y; y > 1 ⇒ 1 ≤ x < y ⇒ \log(x) / \log(y) < 1;

    lemma real_leq_geq:
        ∀ ℝ x, ℝ y; x ≤ y ⇒ x ≥ y ⇒ y ≡ x;

    lemma real_0_lt_2:
        ∀ ℝ x, ℝ y; x ≡ 2 ⇒ y ≡ 0 ⇒ y < x;

    lemma real_1_lt_2:
        ∀ ℝ x, ℝ y; x ≡ 2 ⇒ y ≡ 1 ⇒ y < x;

    lemma real_2_power_1:
        ∀ ℝ x, ℝ y; x ≡ 2 ⇒ y ≡ 1 ⇒ \pow(x, y) ≡ 2;

    lemma real_2_power_52:
        \pow(2, 52) ≡ 1 << 52;

    lemma real_2_ln_52:
        \log(1 << 52) / \log(2) ≡ 52;

    lemma real_2_power_ln:
        ∀ ℝ x; x ≢ 0 ⇒ \pow(2, \floor(\log(\abs(x)) / \log(2))) ≢ 0;

    lemma real_2__ln:
        ∀ ℝ x; x ≡ 2 ⇒ \log(x) ≢ 0;

    lemma real_abs_div:
        ∀ ℝ x, ℝ y; y > 0 ⇒ \abs(x) / y ≡ \abs(x / y);

    // lemma mantissa_exponent_independent:
        // ∀ ℝ x; x ≢ 0 ⇒ mantissa_64bit(x) ≡ mantissa_64bit(x * 2);


    // --------- WRONG ------------------
    // lemma mantissa_is_int:
    //     ∀ ℝ x; x ≡ (double) x ⇒ 
    //         mantissa_64bit(x) + (1 << 52) ≡ 
    //             \abs(x) / \pow(2, exponent(x)) * (1 << 52);

    // lemma make_double_help2:
        // ∀ ℝ x; 1 ≤ \abs(x) / \pow(2, exponent(x)) < 2;

    // lemma make_double_help:
    //     ∀ ℝ x; x ≡ (double) x ⇒
    //         \floor(\log(mantissa_64bit(x) + (1 << 52)) / \log(2)) ≡ 52;

    // lemma make_double_from_parts:
    //     ∀ ℝ x; x ≡ (double) x ⇒
    //         make_double(signbit(x), exponent(x), mantissa_64bit(x)) ≡ x;

    // --------- CORRECT ----------------
    lemma make_double_signbit:
        ∀ ℝ x; x ≡ (double) x ⇒ x ≢ 0 ⇒ 
            \abs(x) * \pow(-1, signbit(x)) ≡ x;

    axiomatic make_double {
        axiom mantissa_is_int:
            ∀ ℝ x; x ≡ (double) x ⇒ x ≢ 0 ⇒ 
                mantissa_64bit(x) + (1 << 52) ≡ 
                    \abs(x) / \pow(2, exponent(x)) * (1 << 52);
    }

    lemma make_double_help2:
        ∀ ℝ x; x ≢ 0 ⇒ 1 ≤ \abs(x) / \pow(2, exponent(x)) < 2;

    lemma make_double_help:
        ∀ ℝ x; x ≡ (double) x ⇒ x ≢ 0 ⇒ 
            \floor(\log(mantissa_64bit(x) + (1 << 52)) / \log(2)) ≡ 52;

    lemma make_double_from_parts:
        ∀ ℝ x; x ≡ (double) x ⇒ x ≢ 0 ⇒ 
            make_double(signbit(x), exponent(x), mantissa_64bit(x)) ≡ x;
*/

/*@
    assigns \nothing;
    ensures x > 0 ⇒ \result ≡ 0;
    ensures x < 0 ⇒ \result ≡ 1;
*/
unsigned long long signbit(double x);

/*@
    assigns \nothing;
    ensures \result ≡ exponent(x);
*/
signed long long signed_exponent(double x);

/*@
    assigns \nothing;
    ensures \result ≡ exponent(x) + 0x3ff;
*/
unsigned long long exponent(double x);


/*@
    assigns \nothing;
    ensures \result ≡ mantissa_64bit(x);
*/
unsigned long long mantissa(double x);


/*@
    assigns \nothing;
    ensures \result ≡ make_double(sign, exponent, mantissa);
*/
double make_double(
        unsigned long long sign,
        signed long long exponent, 
        unsigned long long mantissa
    );



