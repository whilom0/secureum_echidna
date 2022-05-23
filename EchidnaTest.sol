// SPDX-License-Identifier: BSD-4-Clause
pragma solidity ^0.8.1;

import "ABDKMath64x64.sol";

contract Test {
    int128 internal zero = ABDKMath64x64.fromInt(0);
    int128 internal one = ABDKMath64x64.fromInt(1);

    // (2^127-1) / 2 rounded down
    int128 private constant maxFixedAdd =
        85070591730234615865843651857942052863;

    // (-2^127-1) / 2 rounded down
    int128 private constant maxFixedSub =
        -85070591730234615865843651857942052863;

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

    function debug(string calldata x, int128 y) public {
        emit Value(x, ABDKMath64x64.toInt(y));
    }

    // -------------------------------------------
    // WRAPPER FUNCTIONS
    // -------------------------------------------

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

    // TODO:
    // function test_inv(int128 x) public {
    //     x = 1;
    //     try this.inv(x) returns (int128 invRes) {
    //         if (x == ONE) {
    //             assert(invRes == ONE);
    //         }
    //     } catch {
    //         emit Value("mul(MAX_64x64, x)", mul(MAX_64x64, x));
    //         emit Value("x", x);
    //         assert(
    //             // 1/x > MAX -> 1 > MAX * x
    //             x == 0 ||
    //                 (x > 0 && 1 > mul(MAX_64x64, x) && x < ONE) ||
    //                 (x < 0 && 1 < mul(MIN_64x64, x) && x > -ONE)
    //         );
    //     }
    // }

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

    function test_muli_mulu_eq(int128 x, int256 y) public {
        uint256 yPos = y > 0 ? uint256(y) : uint256(-y);

        if (y < 0) {
            assert(muli(x, y) == -int256(mulu(x, yPos)));
        } else {
            assert(muli(x, y) == int256(mulu(x, yPos)));
        }
    }

    // TODO: Figure out how to do this
    // function test_muli_one(int128 x) public {
    //     emit Value("muli(x, 1)", int128(muli(x, 1)));
    //     emit Value("toInt(x)", toInt(x));
    //     emit Value("x", x);
    //     if (x >= ONE || x <= -ONE) {
    //         assert(muli(x, 1) == toInt(x));
    //     } else {
    //         assert(muli(x, 1) == 0);
    //     }
    // }
}
