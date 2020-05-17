/** A macro to easily create a [`Language`].

Example use:
```
# use egg::*;
define_language! {
    enum SimpleLanguage {
        Num(i32),
        Add = "+",
        Mul = "*",
        // language items are parsed in order, and we want symbol to
        // be a fallback, so we put it last
        Symbol(String),
    }
}
```

`define_language` derives `Debug`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`,
`Hash`, and `Clone` on the given `enum` so it can implement [`Language`].
The macro also implements [`FromStr`] and [`Display`] for the `enum`
based on either the data of variants or the provided strings.

Enum variants must be of one of two forms:
- `Variant = "name"`

   This form's [`FromStr`] and [`Display`] parse and print the given
   string, in this case ```"name"```.

- `Variant(Data)`

   This form uses the [`FromStr`] and [`Display`] implementations of
   the given type `Data`.
   So `Data` needs to implement those as well as all of the trait
   bounds of [`Language`].

   Since the parser will not consider the name of the variant, your
   language cannot have two variants with the same data type;
   the second will never get parsed.
   Likewise, you must order your variants from most
   specific to most general; the parser will try to parse the variants
   from top to bottom.

Variants not in one of the two above forms will fail to compile:
```compile_fail
# use egg::*;
define_language! {
    enum SimpleLanguage {
        Num,
    }
}
```

Note that you can always implement [`Language`] yourself,
and that [`Language`] does not require [`FromStr`] or [`Display`].
But they are pretty handy.


[`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
[`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
[`Language`]: trait.Language.html
**/
#[macro_export]
macro_rules! define_language {
    (
        $(#[$meta:meta])*
        $vis:vis enum $name:ident {
            $($variant:ident $(( $($t:ty),* ))? $(= $str:literal)? ),*
                $(,)?
        }
    ) => {
        $(#[$meta])*
        #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
        $vis enum $name {
            $( $variant $(( $($t),* ))? ),*
        }

        impl std::str::FromStr for $name {
            type Err = ();
            fn from_str(s: &str) -> Result<Self, Self::Err> {
                $( define_language!(
                    @parse_arm s,
                    $name $variant
                    $(( $($t),* ))?
                        $(= $str)?
                ); )*
                Err(())
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                $( define_language!(
                    @print_arm self, f,
                    $name $variant
                        $(( $($t),* ))?
                        $(= $str)?
                ); )*
                unreachable!()
            }
        }

        impl $crate::Language for $name {}

    };
    (@parse_arm $e:expr, $name:ident $variant:ident = $str:literal) => {
        if $e == $str {
            return Ok($name :: $variant);
        }
    };
    (@parse_arm $e:expr, $name:ident $variant:ident) => {
        compile_error!(r#"Variants without data must have a name specified: `Variant = "vrnt"`"#);
    };
    (@parse_arm $e:expr, $name:ident $variant:ident ( $t:ty ) ) => {
        if let Ok(inner) = $e.parse::<$t>() {
            return Ok($name :: $variant (inner));
        }
    };
    (@parse_arm $e:expr, $name:ident $variant:ident ( $($t:ty),* ) ) => {
        compile_error!("We only support variants with a single field");
    };
    (@print_arm $e:expr, $f:expr, $name:ident $variant:ident = $str:literal) => {
        if let $name::$variant = $e {
            return write!($f, $str)
        }
    };
    (@print_arm $e:expr, $f:expr, $name:ident $variant:ident ( $t:ty ) ) => {
        if let $name::$variant(inner) = $e {
            return write!($f, "{}", inner)
        }
    };
    (@print_arm $e:expr, $f:expr, $name:ident $variant:ident ( $($t:ty),* ) ) => {
        compile_error!("We only support variants with a single field");
    };
}

#[macro_export]
macro_rules! impl_enode {
    ($(#[$meta:meta])* $vis:vis enum $name:ident $variants:tt) => {
        impl_enode!($(#[$meta])* $vis enum $name $variants -> {} {} {} {} {} {});
    };

    ($(#[$meta:meta])* $vis:vis enum $name:ident {} ->
     $decl:tt {$($matches:tt)*} $for_each:tt $for_each_mut:tt
     $write_op:tt {$($from_op_str:tt)*}
    ) => {
        $(#[$meta])*
        #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
        $vis enum $name $decl

        impl $crate::ENode for $name {
            fn matches(&self, other: &Self) -> bool {
                use $name::*;
                match (self, other) { $($matches)* _ => false }
            }
            fn for_each<F: FnMut(Id)>(&self, mut f: F)  {
                todo!()
                // use $name::*;
                // match self $for_each
            }
            fn for_each_mut<F: FnMut(Id) -> Id>(&mut self, mut f: F)  {
                todo!()
                // use $name::*;
                // match self $for_each_mut
            }
        }

        impl $crate::ENodeDisplay for $name {
            fn write_op(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                use $name::*;
                match (f, self) $write_op
            }
        }

        impl $crate::ENodeFromStr for $name {
            fn from_op_str(op_str: &str, children: Vec<$crate::Id>) -> ::std::result::Result<Self, String> {
                use $name::*;
                match (op_str, children) {
                    $($from_op_str)*
                    (s, c) => Err(::std::format!("Failed to parse '{}' with children {:?}", s, c)),
                }
            }
        }
    };

    ($(#[$meta:meta])* $vis:vis enum $name:ident
     {
         $string:literal = $variant:ident,
         $($variants:tt)*
     } ->
     { $($decl:tt)* } { $($matches:tt)* } { $($for_each:tt)* } { $($for_each_mut:tt)* }
     { $($write_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        impl_enode!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant, }
            { $($matches)*       ($variant, $variant) => true, }
            { $($for_each)*      $variant => (), }
            { $($for_each_mut)*  $variant => (), }
            { $($write_op)*      (f, $variant) => ::std::fmt::Display::fmt($string, f), }
            { $($from_op_str)*   ($string, v) if v.is_empty() => Ok($variant), }
        );
    };


    ($(#[$meta:meta])* $vis:vis enum $name:ident
     {
         $string:literal = $variant:ident ([Id; $n:expr]),
         $($variants:tt)*
     } ->
     { $($decl:tt)* } { $($matches:tt)* } { $($for_each:tt)* } { $($for_each_mut:tt)* }
     { $($write_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        impl_enode!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant( [Id; $n] ), }
            { $($matches)*       ($variant(..), $variant(..)) => true, }
            { $($for_each)*      (f, $variant(ids)) => ids.iter().copied().for_each(f), }
            { $($for_each_mut)*  (f, $variant(ids)) => ids.iter_mut().for_each(|i| *i = f(*i)), }
            { $($write_op)*      (f, $variant(..)) => ::std::fmt::Display::fmt($string, f), }
            { $($from_op_str)*   (s, v) if v.len() == $n => {
                let mut ids = <[Id; $n]>::default();
                ids.copy_from_slice(&v);
                Ok($variant(ids))
            }, }
        );
    };

    ($(#[$meta:meta])* $vis:vis enum $name:ident
     {
         $string:literal = $variant:ident(Id),
         $($variants:tt)*
     } ->
     { $($decl:tt)* } { $($matches:tt)* } { $($for_each:tt)* } { $($for_each_mut:tt)* }
     { $($write_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        impl_enode!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant(Id), }
            { $($matches)*       ($variant(..), $variant(..)) => true, }
            { $($for_each)*      (f, $variant(id)) => f(*id), }
            { $($for_each_mut)*  (f, $variant(id)) => f(*id), }
            { $($write_op)*      (f, $variant(..)) => ::std::fmt::Display::fmt($string, f), }
            { $($from_op_str)*   ($string, v) if v.len() == 1 => Ok($variant(v[0])), }
        );
    };

    ($(#[$meta:meta])* $vis:vis enum $name:ident
     {
         $string:literal = $variant:ident(Id, Id),
         $($variants:tt)*
     } ->
     { $($decl:tt)* } { $($matches:tt)* } { $($for_each:tt)* } { $($for_each_mut:tt)* }
     { $($write_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        impl_enode!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant(Id, Id), }
            { $($matches)*       ($variant(..), $variant(..)) => true, }
            { $($for_each)*      (f, $variant(a, b)) => { f(*a), f(*b) }, }
            { $($for_each_mut)*  (f, $variant(a, b)) => { f(*a), f(*b) }, }
            { $($write_op)*      (f, $variant(..)) => ::std::fmt::Display::fmt($string, f), }
            { $($from_op_str)*   ($string, v) if v.len() == 2 => Ok($variant(v[0], v[1])), }
        );
    };

    ($(#[$meta:meta])* $vis:vis enum $name:ident
     {
         $variant:ident ($data:ty),
         $($variants:tt)*
     } ->
     { $($decl:tt)* } { $($matches:tt)* } { $($for_each:tt)* } { $($for_each_mut:tt)* }
     { $($write_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        impl_enode!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant($data), }
            { $($matches)*       ($variant(data1), $variant(data2)) => data1 == data2, }
            { $($for_each)*      $variant(_data) => (), }
            { $($for_each_mut)*  $variant(_data) => (), }
            { $($write_op)*      (ref mut f, $variant(data)) => ::std::fmt::Display::fmt(data, f), }
            { $($from_op_str)*   (s, v) if s.parse::<$data>().is_ok() && v.is_empty() => Ok($variant(s.parse().unwrap())), }
        );
    };
}

/** Utility macro to create an [`ENode`].

Basically `enode!(op, arg1, arg2, ...)`
desugars to
`ENode::new(op.into(), vec![arg1, arg2, ...])`.
Note the conversion on `op`.

```
# use egg::*;
define_language! {
    enum SimpleLanguage {
        Num(i32),
        Add = "+",
        Mul = "*",
    }
}

use SimpleLanguage::*;

let mut egraph: EGraph<SimpleLanguage, ()> = Default::default();
let one = egraph.add(enode!(Num(1)));
let two = egraph.add(enode!(Num(2)));

let three = egraph.add(enode!(Add, one, two));
let three_manual = egraph.add(ENode::new(Add, vec![one, two]));
assert_eq!(three, three_manual);
```

[`ENode`]: struct.ENode.html
**/
#[macro_export]
macro_rules! enode {
    ($e:expr) => {
        $crate::ENode::leaf($e.into())
    };
    ($e:expr, $($child:expr),*$(,)?) => {
        $crate::ENode::new($e.into(), vec![$($child),*])
    };
}

/** Utility macro to create an [`RecExpr`].

Just a wrapper around [`enode!`].

`recexpr!(op, arg1, arg2, ...)`
desugars to
`RecExpr::from(enode!(op, arg1, arg2, ...))`.

```
use egg::{*, recexpr as r};

define_language! {
    enum SimpleLanguage {
        Num(i32),
        Add = "+",
        Mul = "*",
    }
}

use SimpleLanguage::*;

let mut egraph: EGraph<SimpleLanguage, ()> = Default::default();

let one = egraph.add(enode!(Num(1)));
let two = egraph.add(enode!(Num(2)));
let three = egraph.add(enode!(Add, one, two));

let three_recexpr = r!(Add, r!(Num(1)), r!(Num(2)));
assert_eq!(three, egraph.add_expr(&three_recexpr));
```

[`enode!`]: macro.enode.html
[`RecExpr`]: struct.RecExpr.html
**/
#[macro_export]
macro_rules! recexpr {
    ($e:expr) => {
        $crate::RecExpr::from($crate::enode!($e))
    };
    ($e:expr, $($child:expr),*$(,)?) => {
        $crate::RecExpr::from($crate::enode!($e, $($child),*))
    };
}

/** A macro to easily make [`Rewrite`]s.

The `rewrite!` macro greatly simplifies creating simple, purely
syntactic rewrites while also allowing more complex ones.

The simplest form `rewrite!(a; b => c)` creates a [`Rewrite`]
with name `a`, [`Searcher`] `b`, and [`Applier`] `c`.
Note that in the `b` and `c` position, the macro only accepts a single
token tree (see the [macros reference][macros] for more info).
In short, that means you should pass in an identifier, literal, or
something surrounded by parentheses or braces.

If you pass in a literal to the `b` or `c` position, the macro will
try to parse it as a [`Pattern`] which implements both [`Searcher`]
and [`Applier`].

The macro also accepts any number of `if <expr>` forms at the end,
where the given expression should implement [`Condition`].
For each of these, the macro will wrap the given applier in a
[`ConditionalApplier`] with the given condition.

```
# use egg::*;
define_language! {
    enum SimpleLanguage {
        Num(i32),
        Add = "+",
        Sub = "-",
        Mul = "*",
        Div = "/",
    }
}

type EGraph = egg::EGraph<SimpleLanguage, ()>;

let rules: &[Rewrite<SimpleLanguage, ()>] = &[
    rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
    rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),

    rewrite!("add-0"; "(+ ?a 0)" => "?a"),
    rewrite!("mul-0"; "(* ?a 0)" => "0"),
    rewrite!("mul-1"; "(* ?a 1)" => "?a"),

    rewrite!("silly"; "(* ?a 1)" => { MySillyApplier("foo") }),

    rewrite!("something_conditional";
             "(/ ?a ?b)" => "(* ?a (/ 1 ?b))"
             if is_not_zero("?b")),
];

#[derive(Debug)]
struct MySillyApplier(&'static str);
impl Applier<SimpleLanguage, ()> for MySillyApplier {
    fn apply_one(&self, _: &mut EGraph, _: Id, _: &Subst) -> Vec<Id> {
        panic!()
    }
}

// This returns a function that implements Condition
fn is_not_zero(var: &'static str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    let zero = enode!(SimpleLanguage::Num(0));
    move |egraph, _, subst| !egraph[subst[&var]].nodes.contains(&zero)
}
```

[`Searcher`]: trait.Searcher.html
[`Applier`]: trait.Applier.html
[`Condition`]: trait.Condition.html
[`ConditionalApplier`]: struct.ConditionalApplier.html
[`Rewrite`]: struct.Rewrite.html
[`Pattern`]: struct.Pattern.html
[macro]: https://doc.rust-lang.org/stable/reference/macros-by-example.html#metavariables
**/
#[macro_export]
macro_rules! rewrite {
    (
        $name:expr;
        $lhs:tt => $rhs:tt
        $(if $cond:expr)*
    )  => {{
        let long_name = format!("{} => {}", stringify!($lhs), stringify!($rhs));
        let searcher = $crate::rewrite!(@parse $lhs);
        let applier = $crate::rewrite!(@parse $rhs);
        $( let applier = $crate::ConditionalApplier {applier, condition: $cond}; )*
        $crate::Rewrite::new($name, long_name, searcher, applier)
    }};
    (@parse $rhs:literal) => {
        $rhs.parse::<$crate::Pattern<_>>().unwrap()
    };
    (@parse $rhs:expr) => { $rhs };
}

#[cfg(test)]
mod tests {

    use crate::*;

    impl_enode! {
        enum Simple {
            "++" = Add2(Id, Id),
            "+" = Add([Id; 2]),
            "-" = Sub([Id; 2]),
            "*" = Mul([Id; 2]),
            // "-" = Neg(Id),
            "pi" = Pi,
            Int(i32),
            // Var(String),
        }
    }

    // FIXME
    // #[test]
    // fn some_rewrites() {
    //     use crate::{PatternAst, Rewrite};

    //     let pat = PatternAst::ENode(Box::new(enode!(Term::Num(3)))).compile();
    //     let _: Vec<Rewrite<Term, ()>> = vec![
    //         // here it should parse the rhs
    //         rewrite!("rule"; "cons" => "f"),
    //         // here it should just accept the rhs without trying to parse
    //         rewrite!("rule"; "f" => { pat }),
    //     ];
    // }
}
