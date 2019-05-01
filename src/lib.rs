mod unionfind;

pub mod dot;
pub mod egraph;
pub mod expr;
pub mod extract;
pub mod pattern;

#[cfg(test)]
pub mod parse;

#[cfg(test)]
fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}
