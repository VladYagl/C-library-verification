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

    lemma exponent_signbit_independent:
        ∀ ℝ x; exponent(x) ≡ exponent(\abs(x));

    lemma mantissa_signbit_independent:
        ∀ ℝ x; mantissa_64bit(x) ≡ mantissa_64bit(\abs(x));

    axiomatic Floor {

        axiom floor_eq:
            ∀ ℝ x, y; x ≡ y ⇒ \floor(x) ≡ \floor(y);

        axiom floor_sum:
            ∀ ℝ x, ℤ y; \floor(x + y) ≡ \floor(x) + y;

    }

    axiomatic make_double {

        // // explicit casts:
        // axiom make_double_from_parts:
        //     ∀ double x; \is_finite(x) ⇒
        //         make_double(signbit((ℝ) x), exponent((ℝ) x), mantissa_64bit((ℝ) x)) ≡ (ℝ) x;

        // // old version
        // axiom make_double_from_parts:
        //     ∀ double x; \is_finite(x) ⇒
        //         make_double(signbit(x), exponent(x), mantissa_64bit(x)) ≡ x;

        axiom make_double_from_parts:
            ∀ ℝ x; x ≡ (double) x ⇒
                make_double(signbit(x), exponent(x), mantissa_64bit(x)) ≡ x;
    } 

    lemma real_leq_geq:
        ∀ ℝ x, ℝ y; x ≤ y ⇒ x ≥ y ⇒ y ≡ x;

    lemma real_0_lt_2:
        ∀ ℝ x, ℝ y; x ≡ 2 ⇒ y ≡ 0 ⇒ y < x;

    lemma real_1_lt_2:
        ∀ ℝ x, ℝ y; x ≡ 2 ⇒ y ≡ 1 ⇒ y < x;

    lemma real_2_power_1:
        ∀ ℝ x, ℝ y; x ≡ 2 ⇒ y ≡ 1 ⇒ \pow(x, y) ≡ 2;

    lemma real_2_power_ln:
        ∀ ℝ x; x ≢ 0 ⇒ \pow(2, \floor(\log(\abs(x)) / \log(2))) ≢ 0;

    lemma real_abs_div:
        ∀ ℝ x, ℝ y; y > 0 ⇒ \abs(x) / y ≡ \abs(x / y);

    lemma mantissa_exponent_independent:
        ∀ ℝ x; x ≢ 0 ⇒ mantissa_64bit(x) ≡ mantissa_64bit(x * 2);
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



