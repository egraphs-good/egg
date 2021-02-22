#[path = "../tests/math.rs"]
mod math;
use math::*;

#[path = "../tests/lambda.rs"]
mod lambda;
use lambda::*;

iai::main!(
    diff_power_harder,
    diff_power_simple,
    integ_one,
    integ_part1,
    integ_part2,
    integ_part3,
    integ_sin,
    integ_x,
    math_associate_adds,
    math_diff_different,
    math_diff_ln,
    math_diff_same,
    math_diff_simple1,
    math_diff_simple2,
    math_powers,
    math_simplify_add,
    math_simplify_const,
    math_simplify_factor,
    math_simplify_root,
    lambda_compose,
    lambda_compose_many,
    lambda_fib,
    // lambda_function_repeat,
    lambda_if,
    lambda_if_elim,
    lambda_if_simple,
    lambda_let_simple,
    lambda_under,
);
