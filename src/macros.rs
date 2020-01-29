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
        #[derive(Debug, PartialEq, Eq, Hash, Clone)]
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

        impl $crate::expr::Language for $name {}

    };
    (@parse_arm $e:expr, $name:ident $variant:ident = $str:literal) => {
        if $e == $str {
            return Ok($name :: $variant);
        }
    };
    (@parse_arm $e:expr, $name:ident $variant:ident ( $t:ty ) ) => {
        if let Ok(inner) = $e.parse::<$t>() {
            return Ok($name :: $variant (inner));
        }
    };
    (@parse_arm $e:expr, $name:ident $variant:ident ( $($t:ty),* ) ) => {
        compile_error!("We only support enums with a single field");
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
        compile_error!("We only support enums with a single field");
    };
}

#[cfg(test)]
mod tests {
    define_language! { enum Term {
        Nil = "nil",
        Cons = "cons",
        Foo = "f",
        Num(i32),
    }}
}
