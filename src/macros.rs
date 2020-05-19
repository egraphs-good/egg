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
macro_rules! impl_enode {
    ($(#[$meta:meta])* $vis:vis enum $name:ident $variants:tt) => {
        impl_enode!($(#[$meta])* $vis enum $name $variants -> {} {} {} {} {} {});
    };

    ($(#[$meta:meta])* $vis:vis enum $name:ident {} ->
     $decl:tt {$($matches:tt)*} $for_each:tt $for_each_mut:tt
     $display_op:tt {$($from_op_str:tt)*}
    ) => {
        $(#[$meta])*
        #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
        $vis enum $name $decl

        impl $crate::ENode for $name {
            #[inline(always)]
            fn matches(&self, other: &Self) -> bool {
                ::std::mem::discriminant(self) == ::std::mem::discriminant(other) &&
                match (self, other) { $($matches)* _ => false }
            }
            #[inline]
            fn for_each<F: FnMut(Id)>(&self, mut f: F)  {
                match (f, self) $for_each
            }
            #[inline]
            fn for_each_mut<F: FnMut(&mut Id)>(&mut self, mut f: F)  {
                match (f, self) $for_each_mut
            }
        }

        impl $crate::ENodeDisplay for $name {
            fn display_op(&self) -> &dyn ::std::fmt::Display {
                match self $display_op
            }
        }

        impl $crate::ENodeFromStr for $name {
            fn from_op_str(op_str: &str, children: Vec<$crate::Id>) -> ::std::result::Result<Self, String> {
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
     { $($display_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        impl_enode!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant, }
            { $($matches)*       ($name::$variant, $name::$variant) => true, }
            { $($for_each)*      (_, $name::$variant) => (), }
            { $($for_each_mut)*  (_, $name::$variant) => (), }
            { $($display_op)*    $name::$variant => &$string, }
            { $($from_op_str)*   ($string, v) if v.is_empty() => Ok($name::$variant), }
        );
    };


    ($(#[$meta:meta])* $vis:vis enum $name:ident
     {
         $string:literal = $variant:ident ([Id; $n:expr]),
         $($variants:tt)*
     } ->
     { $($decl:tt)* } { $($matches:tt)* } { $($for_each:tt)* } { $($for_each_mut:tt)* }
     { $($display_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        impl_enode!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant( [Id; $n] ), }
            { $($matches)*       ($name::$variant(..), $name::$variant(..)) => true, }
            { $($for_each)*      (ref mut f, $name::$variant(ids)) => ids.iter().copied().for_each(f), }
            { $($for_each_mut)*  (ref mut f, $name::$variant(ids)) => ids.iter_mut().for_each(f), }
            { $($display_op)*    $name::$variant(..) => &$string, }
            { $($from_op_str)*   (s, v) if v.len() == $n => {
                let mut ids = <[Id; $n]>::default();
                ids.copy_from_slice(&v);
                Ok($name::$variant(ids))
            }, }
        );
    };

    ($(#[$meta:meta])* $vis:vis enum $name:ident
     {
         $string:literal = $variant:ident(Id),
         $($variants:tt)*
     } ->
     { $($decl:tt)* } { $($matches:tt)* } { $($for_each:tt)* } { $($for_each_mut:tt)* }
     { $($display_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        impl_enode!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant(Id), }
            { $($matches)*       ($name::$variant(..), $name::$variant(..)) => true, }
            { $($for_each)*      (ref mut f, $name::$variant(id)) => { f(*id); }, }
            { $($for_each_mut)*  (ref mut f, $name::$variant(id)) => { f(id); }, }
            { $($display_op)*    $name::$variant(..) => &$string, }
            { $($from_op_str)*   ($string, v) if v.len() == 1 => Ok($name::$variant(v[0])), }

        );
    };

    ($(#[$meta:meta])* $vis:vis enum $name:ident
     {
         $string:literal = $variant:ident(Id, Id),
         $($variants:tt)*
     } ->
     { $($decl:tt)* } { $($matches:tt)* } { $($for_each:tt)* } { $($for_each_mut:tt)* }
     { $($display_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        impl_enode!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant(Id, Id), }
            { $($matches)*       ($name::$variant(..), $name::$variant(..)) => true, }
            { $($for_each)*      (ref mut f, $name::$variant(a, b)) => { f(*a); f(*b); }, }
            { $($for_each_mut)*  (ref mut f, $name::$variant(a, b)) => { f(a); f(b); }, }
            { $($display_op)*    $name::$variant(..) => &$string, }
            { $($from_op_str)*   ($string, v) if v.len() == 2 => Ok($name::$variant(v[0], v[1])), }
        );
    };

    ($(#[$meta:meta])* $vis:vis enum $name:ident
     {
         $string:literal = $variant:ident(Id, Id, Id),
         $($variants:tt)*
     } ->
     { $($decl:tt)* } { $($matches:tt)* } { $($for_each:tt)* } { $($for_each_mut:tt)* }
     { $($display_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        impl_enode!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant(Id, Id, Id), }
            { $($matches)*       ($name::$variant(..), $name::$variant(..)) => true, }
            { $($for_each)*      (ref mut f, $name::$variant(a, b, c)) => { f(*a); f(*b); f(*c); }, }
            { $($for_each_mut)*  (ref mut f, $name::$variant(a, b, c)) => { f(a); f(b); f(c); }, }
            { $($display_op)*    $name::$variant(..) => &$string, }
            { $($from_op_str)*   ($string, v) if v.len() == 3 => Ok($name::$variant(v[0], v[1], v[2])), }

        );
    };

    ($(#[$meta:meta])* $vis:vis enum $name:ident
     {
         $variant:ident ($data:ty),
         $($variants:tt)*
     } ->
     { $($decl:tt)* } { $($matches:tt)* } { $($for_each:tt)* } { $($for_each_mut:tt)* }
     { $($display_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        impl_enode!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant($data), }
            { $($matches)*       ($name::$variant(data1), $name::$variant(data2)) => data1 == data2, }
            { $($for_each)*      (_, $name::$variant(_data)) => (), }
            { $($for_each_mut)*  (_, $name::$variant(_data)) => (), }
            { $($display_op)*    $name::$variant(data) => data, }
            { $($from_op_str)*   (s, v) if s.parse::<$data>().is_ok() && v.is_empty() => Ok($name::$variant(s.parse().unwrap())), }
        );
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
