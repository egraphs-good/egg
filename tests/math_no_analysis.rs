//! Since existence proofs don't support analysis,
//! we test egg without analysis here.

use egg::{rewrite as rw, *};
use ordered_float::NotNan;

pub type EGraph = egg::EGraph<Math, ()>;
pub type Rewrite = egg::Rewrite<Math, ()>;

pub type Constant = NotNan<f64>;

define_language! {
    pub enum Math {
        "d" = Diff([Id; 2]),
        "i" = Integral([Id; 2]),

        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "pow" = Pow([Id; 2]),
        "ln" = Ln(Id),
        "sqrt" = Sqrt(Id),

        "sin" = Sin(Id),
        "cos" = Cos(Id),

        Constant(Constant),
        Symbol(Symbol),
    }
}

// You could use egg::AstSize, but this is useful for debugging, since
// it will really try to get rid of the Diff operator
pub struct MathCostFn;
impl egg::CostFunction<Math> for MathCostFn {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &Math, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            Math::Diff(..) => 100,
            Math::Integral(..) => 100,
            _ => 1,
        };
        enode.fold(op_cost, |sum, i| sum + costs(i))
    }
}

#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite> { vec![
  rw!("add-1-1"; "(+ 1 1)" => "2"),
  rw!("add-0-r"; "(+ ?a 0)" => "?a"),
  rw!("add-0-l"; "(+ 0 ?a)" => "?a"),
  rw!("add-2-2"; "(+ 2 2)" => "4"),
  rw!("add-3-1"; "(+ 3 1)" => "4"),
  rw!("sub-0-r"; "(- ?a 0)" => "?a"),
  rw!("sub-0-1"; "(- 0 1)" => "-1"),
  rw!("sub-1-0"; "(- 1 0)" => "1"),
  rw!("sub-1-1"; "(- 1 1)" => "0"),
  rw!("add-2-neg1"; "(+ 2 -1)" => "1"),
  rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
  rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
  rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
  rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),

  rw!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
  rw!("div-canon"; "(/ ?a ?b)" => "(* ?a (pow ?b -1))"),
  // rw!("canon-sub"; "(+ ?a (* -1 ?b))"   => "(- ?a ?b)"),
  // rw!("canon-div"; "(* ?a (pow ?b -1))" => "(/ ?a ?b)" if is_not_zero("?b")),

  rw!("zero-add"; "(+ ?a 0)" => "?a"),
  rw!("zero-mul"; "(* ?a 0)" => "0"),
  rw!("one-mul";  "(* ?a 1)" => "?a"),

  rw!("add-zero"; "?a" => "(+ ?a 0)"),
  rw!("mul-one";  "?a" => "(* ?a 1)"),

  rw!("cancel-sub"; "(- ?a ?a)" => "0"),
  rw!("cancel-div"; "(/ ?a ?a)" => "1"),

  rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
  rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),

  rw!("pow-mul"; "(* (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (+ ?b ?c))"),
  rw!("pow0"; "(pow ?x 0)" => "1"),
  rw!("pow1"; "(pow ?x 1)" => "?x"),
  rw!("pow2"; "(pow ?x 2)" => "(* ?x ?x)"),
  rw!("pow-recip"; "(pow ?x -1)" => "(/ 1 ?x)"),
  rw!("recip-mul-div"; "(* ?x (/ 1 ?x))" => "1"),

  rw!("d-variable"; "(d ?x ?x)" => "1"),
  rw!("d-constant"; "(d ?x ?c)" => "0"),

  rw!("d-add"; "(d ?x (+ ?a ?b))" => "(+ (d ?x ?a) (d ?x ?b))"),
  rw!("d-mul"; "(d ?x (* ?a ?b))" => "(+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a)))"),

  rw!("d-sin"; "(d ?x (sin ?x))" => "(cos ?x)"),
  rw!("d-cos"; "(d ?x (cos ?x))" => "(* -1 (sin ?x))"),

  rw!("d-ln"; "(d ?x (ln ?x))" => "(/ 1 ?x)"),

  rw!("d-power";
      "(d ?x (pow ?f ?g))" =>
      "(* (pow ?f ?g)
          (+ (* (d ?x ?f)
                (/ ?g ?f))
             (* (d ?x ?g)
                (ln ?f))))"
  ),

  rw!("i-one"; "(i 1 ?x)" => "?x"),
  rw!("i-power-const"; "(i (pow ?x ?c) ?x)" =>
      "(/ (pow ?x (+ ?c 1)) (+ ?c 1))"),
  rw!("i-cos"; "(i (cos ?x) ?x)" => "(sin ?x)"),
  rw!("i-sin"; "(i (sin ?x) ?x)" => "(* -1 (cos ?x))"),
  rw!("i-sum"; "(i (+ ?f ?g) ?x)" => "(+ (i ?f ?x) (i ?g ?x))"),
  rw!("i-dif"; "(i (- ?f ?g) ?x)" => "(- (i ?f ?x) (i ?g ?x))"),
  rw!("i-parts"; "(i (* ?a ?b) ?x)" =>
      "(- (* ?a (i ?b ?x)) (i (* (d ?x ?a) (i ?b ?x)) ?x))"),
]}

egg::test_fn! {
    existence_associate_adds, [
        rw!("comm-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    ],
    runner = Runner::default()
        .with_iter_limit(7)
        .with_scheduler(SimpleScheduler),
    "(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))"
    =>
    "(+ 7 (+ 6 (+ 5 (+ 4 (+ 3 (+ 2 1))))))"
    @check |r: Runner<Math, ()>| assert_eq!(r.egraph.number_of_classes(), 127),
    @existence true
}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    existence_fail, rules(),
    "(+ x y)" => "(/ x y)",
    @existence true
}

egg::test_fn! {existence_simplify_add, rules(), "(+ x (+ x (+ x x)))" => "(* 4 x)", @existence true }
egg::test_fn! {existence_powers, rules(), "(* (pow 2 x) (pow 2 y))" => "(pow 2 (+ x y))", @existence true}

egg::test_fn! {
    existence_simplify_const, rules(),
    "(+ 1 (- a (* (- 2 1) a)))" => "1",
    @existence true
}

egg::test_fn! {
    existence_simplify_factor, rules(),
    "(* (+ x 3) (+ x 1))"
    =>
    "(+ (+ (* x x) (* 4 x)) 3)"
    @existence true
}

egg::test_fn! {existence_diff_same, rules(), "(d x x)" => "1", @existence true}
egg::test_fn! {existence_diff_different, rules(), "(d x y)" => "0", @existence true}
egg::test_fn! {existence_diff_simple2,   rules(), "(d x (+ 1 (* y x)))" => "y", @existence true}
egg::test_fn! {existence_diff_ln,        rules(), "(d x (ln x))" => "(/ 1 x)", @existence true}

egg::test_fn! {
    existence_diff_power_simple, rules(),
    "(d x (pow x 3))" => "(* 3 (pow x 2))",
    @existence true
}

egg::test_fn! {
    existence_integ_one, rules(), "(i 1 x)" => "x",
    @existence true
}

egg::test_fn! {
    existence_integ_sin, rules(), "(i (cos x) x)" => "(sin x)", @existence true
}

egg::test_fn! {
    existence_integ_x, rules(), "(i (pow x 1) x)" => "(/ (pow x 2) 2)", @existence true
}

egg::test_fn! {
    existence_integ_part1, rules(), "(i (* x (cos x)) x)" => "(+ (* x (sin x)) (cos x))", @existence true
}
