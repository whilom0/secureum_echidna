
// Want to catch if an F is missing in 0x7FFF....

// Strategy: Each function to test the function itself
// Tests between functions to verify that the math is correct
// Setup one time tests to check the hand-defined edge cases


// ----------- Constants -------------
function test() {
  // (2^127-1) / 2 rounded down
  int128 private constant maxFixedAdd = 85070591730234615865843651857942052863;

  // (-2^127-1) / 2 rounded down
  int128 private constant maxFixedSub = -85070591730234615865843651857942052863;

  // One in decimal (1 << 64)
  int128 private constant ONE = 18446744073709551616;


  // ------- One-time custom Solidity based checks ----------------
  // Check that maxFixedAdd + maxFixedAdd results in MAX
  // Check that MIN + (-1) reverts
  // Check that MAX + 1 reverts 
  // Check that MAX + -MAX = 0
  // Check that maxFixedSub + maxFixedSub = MIN
  // Check that (maxFixedSub - 1) reverts


  // ---------------- Combined Tests ---------------
  // Distributive property: a(b + c) = ab + ac 
  // Distributive property: a(b - c) = ab - ac 
  // ONE (x) = toInt(x)
}


// function add_subtract (int128 x, int128 y) internal pure returns (int128) {
//   // If y > 0, x + y >= x
//   // If y < 0, x + y <= x
//   // If y = 0, x + y = x

//   // Communicative: x + y = y + x
//   // Associative: (x + y) + z = x + (y + z)
//   // Identity: x + y = x
// }

// TODO:
function mul_div (int128 x, int128 y) internal pure returns (int128) {
  // ------------- DONE ---------------
  // Identity: x * ONE = x
  // Zero: x * ZERO = 0
  // Associative: (x * y) * z = x * (y * z)
  // Communicative: x * y = y * x
  // Multitplying two negative numbers = postiive
  // Check for overflow when x*y is too big
  // If y > ONE then mul(x,y) > x when x is positive...
  // If y < ONE then mul(x,y) < x
  
  // Identity: x / ONE = x
  // Zero: x / 0 throws an error
  // If y > ONE then div(x,y) < x
  // If y < ONE then div(x,y) > x
  // Check for overflow when x/y is too big

}

// TODO:
function muli_mulu_divi_divu (int128 x, int128 y) internal pure returns (int128) {

  //  muli(x,y) =- mulu(x,y) * -1 if y < 0, else equal
  //  mulu(x, 1) = 0 if x < ONE else > 0
  //  mulu(ONE, y) = y -- same with mulu
  //  mulu(x, 0) = 0 -- same with mulu
  //  mulu(x, y) > y (always) -- negative option for muli

  // Special edge case handling for negative because range is bigger
  // muli and mulu have these special cases

  // divi(x,1) = x
  // divu(x,1) = x

}
// TODO:
function neg_abs_inv () {
  // neg(x) < x if x is posiive
  // neg(x) > x if x is negative
  // neg(neg(x)) = x
  // Check that it reverts on MIN_64x64 or greater

  // abs(x) = x if x is positive
  // abs(x) = neg(x) otherwise
  // Check that it reverts on MIN_64x64 or greater

  // inv(inv(x)) = x
  // inv(ONE) = ONE
  // Check 0 reverts
  // If x > 2^64, then should 

}
// TODO:
function avg_gavg () {

  // avg(x. x) = x
  // avg(x,y) = avg(y,x)
  // avg(x, -x) = 0
  // Average of x,y should be between x,y min(x,y) <= avg(x,y) <= max(x,y)

  // gavg(x,y) = gavg(y,x)
  // gavg(x,x) = x
  // gavg(x,y) <= avg(x,y)
  // Should throw an error if x*y < 0
}
// TODO:
function pow_sqrt () {

  // pow(x, 0) = 1
  // pow(x, 1) = x
  // Check for infinite loop / if it terminates
  // pov(x,y) if x is negative, y is evem, results in x positive, else negative
  // pow(x, n) > x if x is >= ONE else <= ONE

  // Law of Product: am × an = am+n
  // Law of Quotient: am/an = am-n
  // Law of Zero Exponent: a0 = 1
  // Law of Negative Exponent: a-m = 1/am
  // Law of Power of a Power: (am)n = amn
  // Law of Power of a Product: (ab)m = ambm
  // Law of Power of a Quotient: (a/b)m = am/bm

  // sqrt(x) should throw error if x <= 0
  // sqrt(x * x) = x
  // sqrt(a *b) = sqrt(a) * sqrt(b) 
  // sqrt(x) * sqrt(x) <= x with some margin

}
// TODO:
function log_2_ln_exp_2_exp () {
// TODO:

  // exp(x) follows all the checks of pow(x)
  // exp_2(x) follows the same rules as pow(x)
  // 2^x < exp(x) < 3^x
  // 1-x <= e^x <= 1-x + x^2/2 where x < 0 
  
  // Insert the logarithm math rules here

  // log_2(pow(2, x)) <= x -- with some allocation for error
  // ln(exp(x)) = x
}
// TODO:
function conversions () {
  // fromInt/fromUint (x) -- essentially x * 256 
  // - fromInt(-x) = -fromInt(x)

  // toInt / toUint(x) 
  // - toInt(ONE) = 1
  // - If less than zero, rounds to zero: x < 2^64 = 0
  
  // toInt(fromInt(x)) = x -- Should have no loss in precision
  // fromInt(toInt(x)) <= x -- toInt loses precision but rounds down
  // fromInt(toInt(x)) <= 2^64 -- Bound the loss of precision to ONE
  // toUint reverts on negative number

  // from128x128, to128x128
  // to128x128(from128x128(x)) <= x -- Potential loss of precision
  // from128x128(to128x128(x)) = x -- No loss in precision
  // TODO: Bounded loss of precision 

  //  ------------------ One time checks -----------------
  // - Basic sanity checks (fromInt(0) = 0)
  // - if outside range, it should revert 
  // - Check the losses in precision to make sure it is within range

  // ----------------- Combined Checks --------------------
  // - dividing x by 2^64 is the same as to128x128
  // - toInt/toUInt is the same as dividing by ONE
}