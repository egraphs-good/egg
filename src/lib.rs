mod unionfind;

pub mod dot;
pub mod egraph;
pub mod expr;
pub mod parse;
pub mod pattern;

#[cfg(test)]
fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}
