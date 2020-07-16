/** A macro to easily create a [`Language`].

`define_language` derives `Debug`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`,
`Hash`, and `Clone` on the given `enum` so it can implement [`Language`].
The macro also implements
[`Language::from_op_str`](trait.Language.html#method.from_op_str) and
[`Language::display_op`](trait.Language.html#method.display_op) for the `enum`
based on either the data of variants or the provided strings.

The final variant **must have a trailing comma**; this is due to limitations in
macro parsing.

See [`LanguageChildren`](trait.LanguageChildren.html) for acceptable types of children `Id`s.

Note that you can always implement [`Language`] yourself by just not using this
macro.

Presently, the macro does not support data variant with children, but that may
be added later.

# Example

The following macro invocation shows the the accepted forms of variants:
```
# use egg::*;
define_language! {
    enum SimpleLanguage {
        // string variant with no children
        "pi" = Pi,

        // string variants with an array of child `Id`s (any static size)
        // any type that implements LanguageChildren may be used here
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),

        // can also do a variable number of children in a boxed slice
        // this will only match if the lengths are the same
        "list" = List(Box<[Id]>),

        // string variants with a single child `Id`
        // note that this is distinct from `Sub`, even though it has the same
        // string, because it has a different number of children
        "-"  = Neg(Id),

        // data variants with a single field
        // this field must implement `FromStr` and `Display`
        Num(i32),
        // language items are parsed in order, and we want symbol to
        // be a fallback, so we put it last
        Symbol(Symbol),
        // This is the ultimate fallback, it will parse any operator (as a string)
        // and any number of children.
        // Note that if there were 0 children, the previous branch would have succeeded
        Other(Symbol, Vec<Id>),
    }
}
```

[`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
[`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
[`Language`]: trait.Language.html
**/
#[macro_export]
macro_rules! define_language {
    ($(#[$meta:meta])* $vis:vis enum $name:ident $variants:tt) => {
        $crate::__define_language!($(#[$meta])* $vis enum $name $variants -> {} {} {} {} {} {});
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __define_language {
    ($(#[$meta:meta])* $vis:vis enum $name:ident {} ->
     $decl:tt {$($matches:tt)*} $children:tt $children_mut:tt
     $display_op:tt {$($from_op_str:tt)*}
    ) => {
        $(#[$meta])*
        #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
        $vis enum $name $decl

        impl $crate::Language for $name {
            #[inline(always)]
            fn matches(&self, other: &Self) -> bool {
                ::std::mem::discriminant(self) == ::std::mem::discriminant(other) &&
                match (self, other) { $($matches)* _ => false }
            }

            #[inline]
            fn children(&self) -> &[Id] {
                match self $children
            }

            #[inline]
            fn children_mut(&mut self) -> &mut [Id] {
                match self $children_mut
            }

            fn display_op(&self) -> &dyn ::std::fmt::Display {
                match self $display_op
            }

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
     { $($decl:tt)* } { $($matches:tt)* } { $($children:tt)* } { $($children_mut:tt)* }
     { $($display_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        $crate::__define_language!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant, }
            { $($matches)*       ($name::$variant, $name::$variant) => true, }
            { $($children)*      $name::$variant => &[], }
            { $($children_mut)*  $name::$variant => &mut [], }
            { $($display_op)*    $name::$variant => &$string, }
            { $($from_op_str)*   ($string, v) if v.is_empty() => Ok($name::$variant), }
        );
    };

    ($(#[$meta:meta])* $vis:vis enum $name:ident
     {
         $string:literal = $variant:ident ($ids:ty),
         $($variants:tt)*
     } ->
     { $($decl:tt)* } { $($matches:tt)* } { $($children:tt)* } { $($children_mut:tt)* }
     { $($display_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        $crate::__define_language!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant($ids), }
            { $($matches)*       ($name::$variant(l), $name::$variant(r)) => $crate::LanguageChildren::len(l) == $crate::LanguageChildren::len(r), }
            { $($children)*      $name::$variant(ids) => $crate::LanguageChildren::as_slice(ids), }
            { $($children_mut)*  $name::$variant(ids) => $crate::LanguageChildren::as_mut_slice(ids), }
            { $($display_op)*    $name::$variant(..) => &$string, }
            { $($from_op_str)*   (s, v) if s == $string && <$ids as $crate::LanguageChildren>::can_be_length(v.len()) => {
                let ids = <$ids as $crate::LanguageChildren>::from_vec(v);
                Ok($name::$variant(ids))
            }, }
        );
    };

    ($(#[$meta:meta])* $vis:vis enum $name:ident
     {
         $variant:ident ($data:ty),
         $($variants:tt)*
     } ->
     { $($decl:tt)* } { $($matches:tt)* } { $($children:tt)* } { $($children_mut:tt)* }
     { $($display_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        $crate::__define_language!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant($data), }
            { $($matches)*       ($name::$variant(data1), $name::$variant(data2)) => data1 == data2, }
            { $($children)*      $name::$variant(_data) => &[], }
            { $($children_mut)*  $name::$variant(_data) => &mut [], }
            { $($display_op)*    $name::$variant(data) => data, }
            { $($from_op_str)*   (s, v) if s.parse::<$data>().is_ok() && v.is_empty() => Ok($name::$variant(s.parse().unwrap())), }
        );
    };

    ($(#[$meta:meta])* $vis:vis enum $name:ident
     {
         $variant:ident ($data:ty, $ids:ty),
         $($variants:tt)*
     } ->
     { $($decl:tt)* } { $($matches:tt)* } { $($children:tt)* } { $($children_mut:tt)* }
     { $($display_op:tt)* } { $($from_op_str:tt)* }
    ) => {
        $crate::__define_language!(
            $(#[$meta])* $vis enum $name
            { $($variants)* } ->
            { $($decl)*          $variant($data, $ids), }
            { $($matches)*       ($name::$variant(d1, l), $name::$variant(d2, r)) => d1 == d2 && $crate::LanguageChildren::len(l) == $crate::LanguageChildren::len(r), }
            { $($children)*      $name::$variant(_, ids) => $crate::LanguageChildren::as_slice(ids), }
            { $($children_mut)*  $name::$variant(_, ids) => $crate::LanguageChildren::as_mut_slice(ids), }
            { $($display_op)*    $name::$variant(data, _) => data, }
            { $($from_op_str)*   (s, v) if s.parse::<$data>().is_ok() && <$ids as $crate::LanguageChildren>::can_be_length(v.len()) => {
                let data = s.parse::<$data>().unwrap();
                let ids = <$ids as $crate::LanguageChildren>::from_vec(v);
                Ok($name::$variant(data, ids))
            }, }
        );
    };
}

/** A macro to easily make [`Rewrite`]s.

The `rewrite!` macro greatly simplifies creating simple, purely
syntactic rewrites while also allowing more complex ones.

This panics if [`Rewrite::new`](struct.Rewrite.html#method.new) fails.

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
[`ConditionalApplier`] with the given condition, with the first condition being
the outermost, and the last condition being the innermost.

# Example
```
# use egg::*;
define_language! {
    enum SimpleLanguage {
        Num(i32),
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
    }
}

type EGraph = egg::EGraph<SimpleLanguage, ()>;

let mut rules: Vec<Rewrite<SimpleLanguage, ()>> = vec![
    rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
    rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),

    rewrite!("mul-0"; "(* ?a 0)" => "0"),

    rewrite!("silly"; "(* ?a 1)" => { MySillyApplier("foo") }),

    rewrite!("something_conditional";
             "(/ ?a ?b)" => "(* ?a (/ 1 ?b))"
             if is_not_zero("?b")),
];

// rewrite! supports bidirectional rules too
// it returns a Vec of length 2, so you need to concat
rules.extend(vec![
    rewrite!("add-0"; "(+ ?a 0)" <=> "?a"),
    rewrite!("mul-1"; "(* ?a 1)" <=> "?a"),
].concat());

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
    let zero = SimpleLanguage::Num(0);
    move |egraph, _, subst| !egraph[subst[var]].nodes.contains(&zero)
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
        let searcher = $crate::__rewrite!(@parse $lhs);
        let core_applier = $crate::__rewrite!(@parse $rhs);
        let applier = $crate::__rewrite!(@applier core_applier; $($cond,)*);
        $crate::Rewrite::new($name, long_name, searcher, applier).unwrap()
    }};
    (
        $name:expr;
        $lhs:tt <=> $rhs:tt
        $(if $cond:expr)*
    )  => {{
        let name = $name;
        let name2 = String::from(name.clone()) + "-rev";
        vec![
            $crate::rewrite!(name;  $lhs => $rhs $(if $cond)*),
            $crate::rewrite!(name2; $rhs => $lhs $(if $cond)*)
        ]
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __rewrite {
    (@parse $rhs:literal) => {
        $rhs.parse::<$crate::Pattern<_>>().unwrap()
    };
    (@parse $rhs:expr) => { $rhs };
    (@applier $applier:expr;) => { $applier };
    (@applier $applier:expr; $cond:expr, $($conds:expr,)*) => {
        $crate::ConditionalApplier {
            condition: $cond,
            applier: $crate::__rewrite!(@applier $applier; $($conds,)*)
        }
    };
}

#[cfg(test)]
mod tests {

    use crate::*;

    define_language! {
        enum Simple {
            "+" = Add([Id; 2]),
            "-" = Sub([Id; 2]),
            "*" = Mul([Id; 2]),
            "-" = Neg(Id),
            "list" = List(Box<[Id]>),
            "pi" = Pi,
            Int(i32),
            Var(Symbol),
        }
    }

    #[test]
    fn modify_children() {
        let mut add = Simple::Add([0.into(), 0.into()]);
        add.for_each_mut(|id| *id = 1.into());
        assert_eq!(add, Simple::Add([1.into(), 1.into()]));
    }

    #[test]
    fn some_rewrites() {
        let mut rws: Vec<Rewrite<Simple, ()>> = vec![
            // here it should parse the rhs
            rewrite!("rule"; "cons" => "f"),
            // here it should just accept the rhs without trying to parse
            rewrite!("rule"; "f" => { "pat".parse::<Pattern<_>>().unwrap() }),
        ];
        rws.extend(rewrite!("two-way"; "foo" <=> "bar"));
    }

    #[test]
    #[should_panic(expected = "refers to unbound var ?x")]
    fn rewrite_simple_panic() {
        let _: Rewrite<Simple, ()> = rewrite!("bad"; "?a" => "?x");
    }

    #[test]
    #[should_panic(expected = "refers to unbound var ?x")]
    fn rewrite_conditional_panic() {
        let x: Pattern<Simple> = "?x".parse().unwrap();
        let _: Rewrite<Simple, ()> = rewrite!(
            "bad"; "?a" => "?a" if ConditionEqual(x.clone(), x)
        );
    }
}
