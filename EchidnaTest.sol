// SPDX-License-Identifier: BSD-4-Clause
pragma solidity ^0.8.1;

import "ABDKMath64x64.sol";

contract Test {
    int128 internal zero = ABDKMath64x64.fromInt(0);
    int128 internal one = ABDKMath64x64.fromInt(1);

    // One in decimal 2^64
    int128 private constant ONE = 18446744073709551616;

    //  -2^127
    int128 private constant MIN_64x64 = -0x80000000000000000000000000000000;

    /*
     * Maximum value signed 64.64-bit fixed point number may have.
     */
    //  2^ 127 - 1
    int128 private constant MAX_64x64 = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

    event Value(string, int128);
    event Value256(string, int256);

    function debug(string calldata x, int128 y) public {
        emit Value(x, ABDKMath64x64.toInt(y));
    }

    // -------------------------------------------
    // WRAPPER FUNCTIONS
    // -------------------------------------------

    function toIntRoundToZero(int128 x) public returns (int64) {
        if (x >= 0) return ABDKMath64x64.toInt(x);
        else return -ABDKMath64x64.toInt(neg(x));
    }

    function add(int128 x, int128 y) public returns (int128) {
        return ABDKMath64x64.add(x, y);
    }

    function sub(int128 x, int128 y) public returns (int128) {
        return ABDKMath64x64.sub(x, y);
    }

    function mul(int128 x, int128 y) public returns (int128) {
        return ABDKMath64x64.mul(x, y);
    }

    function muli(int128 x, int256 y) public returns (int256) {
        return ABDKMath64x64.muli(x, y);
    }

    function mulu(int128 x, uint256 y) public returns (uint256) {
        return ABDKMath64x64.mulu(x, y);
    }

    function div(int128 x, int128 y) public returns (int128) {
        return ABDKMath64x64.div(x, y);
    }

    function divi(int256 x, int256 y) public returns (int128) {
        return ABDKMath64x64.divi(x, y);
    }

    function divu(uint256 x, uint256 y) public returns (int128) {
        return ABDKMath64x64.divu(x, y);
    }

    function fromInt(int256 x) public returns (int128) {
        return ABDKMath64x64.fromInt(x);
    }

    function pow(int128 x, uint256 y) public returns (int128) {
        return ABDKMath64x64.pow(x, y);
    }

    function neg(int128 x) public returns (int128) {
        return ABDKMath64x64.neg(x);
    }

    function abs(int128 x) public returns (int128) {
        return ABDKMath64x64.abs(x);
    }

    function inv(int128 x) public returns (int128) {
        return ABDKMath64x64.inv(x);
    }

    function sqrt(int128 x) public returns (int128) {
        return ABDKMath64x64.sqrt(x);
    }

    function toInt(int128 x) public returns (int64) {
        return ABDKMath64x64.toInt(x);
    }

    function fromUInt(uint256 x) public returns (int128) {
        return ABDKMath64x64.fromUInt(x);
    }

    function toUInt(int128 x) public returns (uint64) {
        return ABDKMath64x64.toUInt(x);
    }

    function from128x128(int256 x) public returns (int128) {
        return ABDKMath64x64.from128x128(x);
    }

    function to128x128(int128 x) public returns (int256) {
        return ABDKMath64x64.to128x128(x);
    }

    function avg(int128 x, int128 y) public returns (int128) {
        return ABDKMath64x64.avg(x, y);
    }

    function gavg(int128 x, int128 y) public returns (int128) {
        return ABDKMath64x64.gavg(x, y);
    }

    function log_2(int128 x) public returns (int128) {
        return ABDKMath64x64.log_2(x);
    }

    function ln(int128 x) public returns (int128) {
        return ABDKMath64x64.ln(x);
    }

    function exp_2(int128 x) public returns (int128) {
        return ABDKMath64x64.exp_2(x);
    }

    function exp(int128 x) public returns (int128) {
        return ABDKMath64x64.exp(x);
    }

    // -------------------------------------------
    // Heler Functions
    // -------------------------------------------
    function within_tolerance(
        int128 x,
        int128 y,
        int128 tol
    ) public returns (bool) {
        int256 diff = int256(x) - y;
        return diff > 0 ? diff <= tol : diff >= -tol;
    }

    function abs_greater_than(int128 x, int128 limit) public returns (bool) {
        return x > 0 ? x >= limit : x <= -limit;
    }

    // Ensures that |x| >= limit
    function make_outside_lim(int128 x, int128 limit) public returns (int128) {
        require(limit >= MIN_64x64 && limit <= MAX_64x64);

        // Handle edge case of -MAX
        if (x == MIN_64x64) return MIN_64x64;

        bool isNegative = x < 0;
        if (isNegative) x = -x;

        int128 result = (x % (MAX_64x64 - limit)) + limit;
        assert(result >= limit);
        if (isNegative) result = -result;

        assert(result >= MIN_64x64 && result <= MAX_64x64);
        return result;
    }

    // -------------------------------------------
    // Test Functions
    // -------------------------------------------

    function test_add_math_prop(
        int128 x,
        int128 y,
        int128 z
    ) public {
        int128 addRes = add(x, y);
        /**
         * If y > 0, x + y > x
         * If y < 0, x + y < x
         * If y = 0, x + y = x
         */
        if (y > 0) {
            assert(addRes > x);
        } else if (y < 0) {
            assert(addRes < x);
        } else {
            assert(addRes == x);
        }

        // Communicative: x + y = y + x
        assert(addRes == add(y, x));

        // Associative: (x + y) + z = x + (y + z)
        assert(add(add(x, y), z) == add(x, add(y, z)));
    }

    function test_add_revert(int128 x, int128 y) public {
        try this.add(x, y) {} catch {
            // Overflow / Underflow check

            // x and y have to have the same signs to overflow.
            assert((x < 0 && y < 0) || (x > 0 && y > 0));

            if (y > 0) {
                // x + y <= MAX_64x64  -> x <= MAX_64x64 - y
                assert(x >= sub(MAX_64x64, y));
            } else {
                // x and y are both negative
                // x + y <= MIN_64x64
                // x- abs(y) <= MIN_64x64
                assert(sub(x, -y) <= MIN_64x64);
            }
        }
    }

    function test_sub_revert(int128 x, int128 y) public {
        try this.sub(x, y) {} catch {
            // Overflow / Underflow check

            // x and y cannot have the same signs to overflow.
            assert((x < 0 && y > 0) || (x > 0 && y < 0));

            if (y > 0) {
                // y is positive, x is negative
                // x - y <= MIN
                assert(x <= add(MIN_64x64, y));
            } else {
                // y is neg, x is positive
                // x - y >= MAX
                // x >= MAX + y
                assert(x >= add(MAX_64x64, y));
            }
        }
    }

    function test_sub_math_properties(int128 x, int128 y) public {
        /**
         * If y > 0, x - y < x
         * If y < 0, x - y > x
         * If y = 0, x - y = x
         */
        int128 subRes = sub(x, y);
        if (y > 0) {
            assert(subRes < x);
        } else if (y < 0) {
            assert(subRes > x);
        } else {
            assert(subRes == x);
        }

        // Identity Property x - x = 0
        assert(sub(x, x) == 0);
    }

    function test_mul_associative(
        int128 x,
        int128 y,
        int128 z
    ) public {
        // Associative: (x * y) * z = x * (y * z)
        int128 xy = mul(x, y);
        int128 yz = mul(y, z);
        if (abs_greater_than(xy, ONE) && abs_greater_than(yz, ONE)) {
            assert(within_tolerance(mul(mul(x, y), z), mul(x, mul(y, z)), ONE));
        } else {
            // |x| < ONE || |y| < ONE || |z| < ONE
            assert(
                !abs_greater_than(x, ONE) ||
                    !abs_greater_than(y, ONE) ||
                    !abs_greater_than(z, ONE)
            );
        }
    }

    function test_multiply_two_neg(int128 x, int128 y) public {
        if (x > 0) x = -x;
        if (y > 0) y = -y;

        // Should be positive
        assert(mul(x, y) >= 0);
    }

    function test_mul_communicative(int128 x, int128 y) public {
        // Communicative: x * y = y * x
        assert(mul(x, y) == mul(y, x));
    }

    /**
     * |    | +x                  | -x                   |
     * |----|---------------------|----------------------|
     * | +y | x < xy if y > ONE   | x > xy if y > ONE    |
     * | -y | x > xy always       | x < xy always        |
     */
    function test_mul_outputs(int128 x, int128 y) public {
        int128 mulRes = mul(x, y);

        emit Value("mulRes", mulRes);

        if (y == 0 || x == 0) {
            // Zero property
            assert(mulRes == 0);
        } else if (y == ONE) {
            // Identity Property
            assert(mulRes == x);
        } else if (x > 0 && y < 0) {
            assert(x > mulRes);
        } else if (x < 0 && y < 0) {
            assert(x < mulRes);
        } else if (x > 0 && y > 0) {
            if (y >= ONE) {
                assert(x <= mulRes);
            } else {
                assert(x >= mulRes);
            }
        } else if (x < 0 && y > 0) {
            // x > xy if x,y > ONE
            if (y >= ONE) {
                assert(x >= mulRes);
            } else {
                assert(x <= mulRes);
            }
        }
    }

    function test_mul_reverts(int128 x, int128 y) public {
        try this.mul(x, y) {} catch {
            if (y > 0) {
                // x <= MAX/y when y is positive
                // x >= MIN/y when y is positive
                assert(x <= div(MAX_64x64, y) || x >= div(MIN_64x64, y));
            } else {
                // x >= MAX/y when y is negative
                // x <= MIN/y when y is negative
                assert(x >= div(MAX_64x64, y) || x <= div(MIN_64x64, y));
            }
        }
    }

    /**
     * |    | +x                 | -x                 |
     * |----|--------------------|--------------------|
     * | +y | x < x/y if y < ONE | x > x/y if y < ONE |
     * | -y | x > x/y always     | x < x/y always     |
     */
    function test_div_outputs(int128 x, int128 y) public {
        int128 divRes = div(x, y);
        emit Value("x", x);
        emit Value("y", y);
        emit Value("divRes", divRes);
        if (y == ONE) {
            assert(x == divRes);
        } else if (x > 0 && y < 0) {
            assert(x > divRes);
        } else if (x < 0 && y < 0) {
            assert(x < divRes);
        } else if (x > 0 && y > 0) {
            if (y <= ONE) {
                assert(x <= divRes);
            } else {
                assert(x >= divRes);
            }
        } else if (x < 0 && y > 0) {
            if (y <= ONE) {
                assert(x >= divRes);
            } else {
                assert(x <= divRes);
            }
        }
    }

    function test_div_errors(int128 x, int128 y) public {
        try this.div(x, y) {} catch {
            // Divide by zero error
            bool divideByZero = y == 0;

            // y is guaranteed to be < ONE, thus multiplying will not cause overflow
            bool overflow = x > mul(MAX_64x64, y);
            bool underflow = x < mul(MIN_64x64, y);

            assert(divideByZero || overflow || underflow);
        }
    }

    function test_double_neg(int128 x) public {
        assert(neg(neg(x)) == x);
    }

    function test_neg(int128 x) public {
        try this.neg(x) returns (int128 negRes) {
            assert(
                (negRes > 0 && x < 0) ||
                    (negRes < 0 && x > 0) ||
                    (negRes == 0 && x == 0)
            );
        } catch {
            assert(x == MIN_64x64);
        }
    }

    function test_abs(int128 x) public {
        try this.abs(x) returns (int128 absRes) {
            assert(absRes >= 0);
            assert(
                (absRes == x && x > 0) ||
                    (absRes == -x && x < 0) ||
                    (absRes == 0 && x == 0)
            );
        } catch {
            assert(x == MIN_64x64);
        }
    }

    function test_double_inv(int128 x) public {
        // Inner inv can truncate which results in smaller number
        // thus second inv will make the absolute value bigger
        if (x > 0) {
            assert(x <= inv(inv(x)));
        } else {
            assert(x >= inv(inv(x)));
        }
    }

    function test_inv(int128 x) public {
        try this.inv(x) returns (int128 invRes) {
            if (x == ONE) {
                assert(invRes == ONE);
            }
        } catch {
            emit Value("mul(MAX_64x64, x)", mul(MAX_64x64, x));
            emit Value("x", x);
            assert(
                // 1/x > MAX -> 1 > MAX * x
                // TODO: Figure out how to express this with all the overflows
                x == 0 || (x > 0 && x < ONE) || (x < 0 && x > -ONE)
            );
        }
    }

    function test_avg(int128 x, int128 y) public {
        assert(avg(x, x) == x);
        assert(avg(x, y) == avg(y, x));
        assert(avg(x, -x) == 0);

        int128 avgRes = avg(x, y);
        int128 low = x < y ? x : y;
        int128 high = x > y ? x : y;

        // Average of x,y should be between x,y min(x,y) <= avg(x,y) <= max(x,y)
        assert(low <= avgRes && avgRes <= high);
    }

    function test_gavg(int128 x, int128 y) public {
        x = abs(x);
        y = abs(y);

        assert(gavg(x, y) == gavg(y, x));
        assert(gavg(x, x) == x);
        assert(gavg(x, y) <= avg(x, y));
    }

    function test_gavg_err(int128 x, int128 y) public {
        try this.gavg(x, y) {} catch {
            // Throws an error if x*y < 0 which can only happen if
            // x < 0 or y < 0
            assert(x < 0 || y < 0);
        }
    }

    function test_muli_mulu_eq(int128 x, int256 y) public {
        uint256 yPos = y > 0 ? uint256(y) : uint256(-y);

        if (y < 0) {
            assert(muli(x, y) == -int256(mulu(x, yPos)));
        } else {
            assert(muli(x, y) == int256(mulu(x, yPos)));
        }
    }

    function test_pow_identities(int128 x) public {
        assert(pow(x, 0) == ONE);
        assert(pow(x, 1) == x);
    }

    function test_pow_gt_one(int128 x, uint256 y) public {
        int128 powRes = pow(x, y);
        emit Value("powRes", powRes);
        emit Value("x", x);

        // 0^0 is 1
        if (x == 0 && y == 0) {
            assert(powRes == ONE);
        }
        // 0 ^ y = 0
        else if (x == 0) {
            assert(pow(0, y) == 0);
        }
        // x ^ 0 == 1
        else if (y == 0) {
            assert(pow(x, y) == ONE);
        }
        // x ^ 1 == x
        else if (y == 1) {
            assert(pow(x, y) == x);
        }
        //  x is positive
        else if (x > 0) {
            // pow(x, n) > x if x is >= ONE
            if (x < ONE) assert(powRes <= x);
            else if (x == ONE) assert(powRes == x);
            else assert(powRes >= x);
        }
        // x is negative
        else if (x < 0) {
            bool yEven = y % 2 == 0;
            if (yEven) {
                // TODO: This is an incomplete test.. Checking if > -ONE limits the test
                // x ^ (even) > x where x is negative
                assert(powRes > x || x > -ONE);
            } else {
                if (x > -ONE) assert(powRes >= x);
                else if (x == ONE) assert(powRes == x);
                else assert(powRes <= x);
            }
        }
    }

    function test_pow_math_props(
        int128 x,
        uint256 y,
        uint256 z
    ) public {
        // Law of Product: a^m × a^n = a^(m+n)
        assert(mul(pow(x, y), pow(x, z)) == pow(x, y + z));

        // Law of Quotient: a^m/a^n = a^(m-n)
        assert(div(pow(x, y), pow(x, z)) == pow(x, y - z));

        // Law of Power of a Power: (a^m)^n = a^(mn)
        assert(pow(pow(x, y), z) == pow(x, y * z));
    }

    function test_pow_math_props2(
        int128 a,
        int128 b,
        uint256 m
    ) public {
        // Law of Power of a Product: (ab)^m = a^m b^m
        assert(pow(mul(a, b), m) == mul(pow(a, m), pow(b, m)));

        // Law of Power of a Quotient: (a/b)^m = a^m/b^m
        assert(pow(div(a, b), m) == div(pow(a, m), pow(b, m)));
    }

    function test_pow(int128 x, uint256 y) public {
        try this.pow(x, y) {} catch {
            // TODO: Check either it is less than zero or overflows
            // assert(x < 0);
        }
    }

    function test_sqrt_math(int128 x, int128 y) public {
        emit Value("x", x);
        emit Value("sqrt(mul(x, x))", sqrt(mul(x, x)));
        emit Value("mul(sqrt(x), sqrt(x))", mul(sqrt(x), sqrt(x)));
        emit Value("sqrt(mul(x, y))", sqrt(mul(x, y)));
        emit Value("mul(sqrt(x), sqrt(y))", mul(sqrt(x), sqrt(y)));

        // sqrt(x * x) <= x because x * x can truncate
        assert(sqrt(mul(x, x)) <= x);
        // // sqrt(x) * sqrt(x) <= x with some margin
        assert(mul(sqrt(x), sqrt(x)) <= x);
    }

    function test_from_int(int256 x) public {
        assert(-fromInt(-x) == fromInt(x));

        assert(toInt(fromInt(x)) == x);
    }

    function test_toInt(int128 x) public {
        int64 res = toInt(x);
        emit Value("toInt(x)", int128(res));
        if (x < -ONE) {
            assert(res < 0);
        } else if (x > ONE) {
            assert(res > 0);
        }

        emit Value("toInt(-x)", int128(toInt(-x)));
        assert(toInt(x) + toInt(-x) <= 1);

        // toInt loses precision but rounds down
        assert(fromInt(toInt(x)) <= x);
    }

    function test_toUint(int128 x) public {
        emit Value("toUInt(x)", int128(uint128(toUInt(x))));
        try this.toUInt(x) returns (uint64 ret) {
            assert(ret >= 1 == x >= ONE);
        } catch {
            assert(x < 0);
        }
    }

    function test_from128x128(int256 x) public {
        assert(to128x128(from128x128(x)) <= x);
    }

    function test_to128x128(int128 x) public {
        assert(from128x128(to128x128(x)) == x);
    }

    function test_muli_one_y(int256 y) public {
        assert(muli(ONE, y) == y);
    }

    function test_mulu_one_y(uint256 y) public {
        assert(mulu(ONE, y) == y);
    }

    function test_divi_one(int256 x) public {
        assert(divi(x, 1) == fromInt(x));
    }

    function test_divu_one(uint256 x) public {
        assert(divu(x, 1) == fromUInt(x));
    }

    function test_muli_gt(int128 x, int256 y) public {
        int256 res = muli(x, y);
        emit Value256("muli", res);
        emit Value("toInt", toIntRoundToZero(x));
        if (x >= 0) {
            if (y > 0) {
                assert(toIntRoundToZero(x) <= res);
            } else {
                assert(res <= toIntRoundToZero(x));
            }
        } else {
            if (y > 0) {
                assert(res <= toIntRoundToZero(x));
            } else {
                assert(toIntRoundToZero(x) <= res);
            }
        }
    }

    function test_muli_mulu_one_zero(int128 x) public {
        // muli(x, 1) = x with some tolerance
        emit Value("muli(x, 1)", int128(muli(x, 1)));
        emit Value("toInt(x)", toIntRoundToZero(x));
        emit Value("x", x);
        if (x >= ONE || x <= -ONE) {
            assert(muli(x, 1) <= toIntRoundToZero(x));
            assert(mulu(x, 1) == toUInt(x));
        } else {
            assert(muli(x, 1) == 0);
            assert(mulu(x, 1) == 0);
        }
        assert(muli(x, 0) == 0);
        assert(mulu(x, 0) == 0);
    }

    // TODO: FIgure out how to do this for muli
    function mulu_divu(uint256 x, uint256 y) public {
        // can truncate which makes this not strict equality
        uint256 res = mulu(divu(x, y), y) - x;
        assert(res < (1 << 128));
        int256 diff = int256(res);

        int256 tol = ONE;

        assert(-tol <= diff && diff <= tol);
    }

    function test_exp_taylor(int128 x) public {
        // 1 - x <= e^-x <= 1 - x + x^2/2 for all x >= 0
        // Note that we put tolerances of 1 bec neg range is wider

        x = abs(x);
        int128 expRes = exp(-x);
        emit Value("x ", x);
        emit Value("sub(ONE, x) ", sub(ONE, x));
        emit Value("exp(-x)", expRes);
        emit Value(
            "ONE - x + div(mul(x, x), fromInt(2) ",
            ONE - x + div(mul(x, x), fromInt(2))
        );

        assert(
            (sub(ONE, x) <= expRes + 1 &&
                expRes - 1 <= ONE - x + div(mul(x, x), fromInt(2)))
        );
    }

    function test_exp_2x_3x(int128 x) public {
        // 2^x < e^x < 3^x
        // Can only check when x > 0 because of pow limitation
        // Check when x > ONE bec of truncation
        x = abs(make_outside_lim(x, ONE));
        uint256 xPos = uint256(uint128(x));

        emit Value("x", x);
        emit Value256("x", int256(xPos));
        emit Value("pow(ONE * 2, xPos)", pow(ONE * 2, xPos));
        emit Value("exp(x)", exp(x));
        emit Value("pow(ONE * 3, xPos)", pow(ONE * 3, xPos));

        assert(pow(ONE * 2, xPos) <= exp(x) && exp(x) <= pow(ONE * 3, xPos));

        // 2^-x < e^-x < 3^-x
        assert(
            inv(pow(ONE * 2, xPos)) <= inv(exp(x)) &&
                inv(exp(x)) <= inv(pow(ONE * 3, xPos))
        );
    }

    function test_exp_2_pow_2(int128 x) public {
        x = abs(x);
        uint256 xPos = uint256(int256(x));
        emit Value("exp_2(x)", exp_2(x));
        emit Value("pow(ONE * 2, xPos)", pow(ONE * 2, xPos));
        assert(exp_2(fromInt(x)) == pow(ONE * 2, xPos));
    }

    function test_log_2_exp_2(int128 x) public {
        emit Value("exp_2(fromInt(x))", exp_2(fromInt(x)));
        emit Value("log_2(exp_2(fromInt(x)))", log_2(exp_2(fromInt(x))));
        assert(fromInt(x) - log_2(exp_2(fromInt(x))) < ONE);
    }

    function test_ln_exp(int128 x) public {
        emit Value("exp(fromInt(x))", exp(fromInt(x)));
        emit Value("ln(exp(fromInt(x)))", ln(exp(fromInt(x))));
        emit Value("fromInt(x)", fromInt(x));
        assert(fromInt(x) - ln(exp(fromInt(x))) < ONE);
    }
}
