pub use crate::*;
pub use generic_analysis::Analysis as RawAnalysis;
pub use LatticeAnalysis as Analysis;

pub type EGraph<L, N> = EMGraph<L, WrapLatticeAnalysis<N>>;
pub type EClass<L, N> = EMClass<L, WrapLatticeAnalysis<N>>;
pub type Runner<L, N, I = ()> = run::Runner<L, WrapLatticeAnalysis<N>, I>;
pub type Rewrite<L, N> = rewrite::Rewrite<L, WrapLatticeAnalysis<N>>;
