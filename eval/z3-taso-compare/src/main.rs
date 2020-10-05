use std::time::Instant;
use tamago::{parse::*, verify::*};

fn main() {
    env_logger::init();
    prove_taso_rules(true);
    // optimize();
}

fn optimize() {
    use egg::*;
    use tamago::model::*;
    use tamago::rewrites::*;

    let start = "(input 0 0)".parse().unwrap();
    let runner = Runner::<Mdl, (), ()>::default()
        .with_expr(&start)
        .run(&rules()[..]);
    runner.egraph.dot().to_svg("target/tamago.svg").unwrap();
}

fn prove_taso_rules(batch: bool) {
    use std::env::*;
    use std::fs::*;

    let file = args().nth(1).expect("Pls supply taso rules file.");
    let taso_rules = read_to_string(file).expect("Something went wrong reading the file");

    println!("Parsing rules...");
    let initial = parse_rules(&taso_rules);
    println!("Parsed rules!");

    let start = Instant::now();
    if batch {
        let mut to_prove = initial.clone();
        while !to_prove.is_empty() {
            let n_before = to_prove.len();
            to_prove = verify(&to_prove);
            let n_proved = n_before - to_prove.len();
            println!("Proved {} on this trip", n_proved);
            if n_proved == 0 {
                println!("\nCouldn't prove {} rule(s)", to_prove.len());
                for pair in &to_prove {
                    let i = initial.iter().position(|p| p == pair).unwrap();
                    println!("  {}: {} => {}", i, pair.0, pair.1);
                }
                break;
            }
        }
    } else {
        verify_nb(&initial);
    }
    let duration = start.elapsed();

    println!(
        "DONE {} in {}",
        if batch { "batched" } else { "one-at-a-time" },
        duration.as_secs_f64(),
    );
}
