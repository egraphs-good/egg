#![recursion_limit = "128"]

use stdweb::traits::IEvent;
use stdweb::web::Date;
use yew::services::ConsoleService;
use yew::{html, Component, ComponentLink, Html, Renderable, ShouldRender};

mod math;

use egg::{
    egraph::EClass,
    expr::{Id, RecExpr},
    parse::{pat_to_expr, ParsableLanguage},
    pattern::{Pattern, PatternMatches, Rewrite},
};
use math::*;

struct Queried {
    pattern: Pattern<Math>,
    matches: Vec<PatternMatches<Math>>,
}

struct Model {
    console: ConsoleService,
    egraph: MathEGraph,
    query: Result<Queried, String>,
    added: Vec<Added>,
    examples: Vec<&'static str>,
    rewrite_groups: Vec<RewriteGroup>,
}

struct RewriteGroup {
    name: String,
    enabled: bool,
    rewrites: Vec<OptionalRewrite>,
}

impl Renderable<Model> for RewriteGroup {
    fn view(&self) -> Html<Model> {
        html! {
            <div class="rewrite-group",>
                <input type="checkbox", checked=self.enabled,></input>
                <details>
                    <summary> {&self.name} </summary>
                    { for self.rewrites.iter().map(Renderable::view) }
                </details>
            </div>
        }
    }
}

struct OptionalRewrite {
    enabled: bool,
    rewrite: Rewrite<Math>,
}

impl Renderable<Model> for OptionalRewrite {
    fn view(&self) -> Html<Model> {
        html! {
            <div class="rewrite",>
                <input type="checkbox", checked=self.enabled,></input>
                <details>
                    <summary> {&self.rewrite.name} </summary>
                    <div class="lhs",> {self.rewrite.lhs.to_sexp()} </div>
                    <div class="rhs",> {self.rewrite.rhs.to_sexp()} </div>
                </details>
            </div>
        }
    }
}

struct Added {
    id: Id,
    expr: RecExpr<Math>,
}

impl Renderable<Model> for Added {
    fn view(&self) -> Html<Model> {
        html! { <tr> <td> {self.expr.to_sexp()} </td> <td> {self.id} </td> </tr> }
    }
}

enum Msg {
    AddExpr(String),
    AddQuery,
    RunRewrites,
    UpdateQuery(String),
}

impl Component for Model {
    type Message = Msg;
    type Properties = ();

    fn create(_: Self::Properties, _: ComponentLink<Self>) -> Self {
        Model {
            console: ConsoleService::new(),
            egraph: MathEGraph::default(),
            query: Err("enter a pattern or expression".into()),
            added: vec![],
            examples: vec!["(+ 1 2)", "(* x (+ y z))", "(+ x (+ x (+ x x)))"],
            rewrite_groups: math::rules(),
        }
    }

    fn update(&mut self, msg: Self::Message) -> ShouldRender {
        match msg {
            Msg::UpdateQuery(s) => {
                self.query = Math
                    .parse_pattern(&s)
                    .map(|pattern| {
                        let matches = pattern.search(&self.egraph);
                        Queried { pattern, matches }
                    })
                    .map_err(|e| e.to_string());
            }
            Msg::AddQuery => {
                if let Ok(pat) = &self.query {
                    match pat_to_expr(pat.pattern.clone()) {
                        Ok(expr) => {
                            let id = self.egraph.add_expr(&expr);
                            self.update(Msg::UpdateQuery(expr.to_sexp().to_string()));
                            self.added.push(Added { expr, id });
                        }
                        Err(err) => {
                            self.query = Err(err.to_string());
                        }
                    }
                }
            }
            Msg::AddExpr(s) => {
                self.update(Msg::UpdateQuery(s.clone()));
                self.update(Msg::AddQuery);
            }
            Msg::RunRewrites => {
                let start_time = Date::now();

                let mut applied = 0;
                let mut total_matches = 0;
                let mut last_total_matches = 0;
                let mut matches = Vec::new();

                for group in &self.rewrite_groups {
                    if !group.enabled {
                        continue;
                    }

                    for rule in &group.rewrites {
                        if rule.enabled {
                            let ms = rule.rewrite.lhs.search(&self.egraph);
                            if !ms.is_empty() {
                                matches.push((&rule.rewrite, ms));
                            }
                        }
                    }
                }

                let match_time = Date::now();

                for (rule, ms) in matches {
                    for m in ms {
                        let actually_matched = m.apply(&rule.rhs, &mut self.egraph);
                        self.console.log(&format!(
                            "Applied {} {} times",
                            rule.name,
                            actually_matched.len()
                        ));

                        applied += actually_matched.len();
                        total_matches += m.mappings.len();

                        // log the growth of the egraph
                        if total_matches - last_total_matches > 1000 {
                            last_total_matches = total_matches;
                            let elapsed = Date::now() - match_time;
                            self.console.log(&format!(
                                "nodes: {}, eclasses: {}, actual: {}, total: {}, us per match: {}",
                                self.egraph.total_size(),
                                self.egraph.number_of_classes(),
                                applied,
                                total_matches,
                                elapsed * 1.0e9
                            ));
                        }
                    }
                }
                self.egraph.rebuild();
                self.egraph.fold_constants();
                self.egraph.prune();

                let elapsed = Date::now() - start_time;
                self.console
                    .log(&format!("Applied {} in {}s", applied, elapsed,));
            }
        };
        true
    }
}

fn view_example(s: &'static str) -> Html<Model> {
    html! { <div onclick=|_| Msg::AddExpr(s.to_string()),> {s} </div> }
}

fn view_eclass(eclass: &EClass<Math, BestExpr>) -> Html<Model> {
    html! {
        <details class="eclass",>
            <summary> {eclass.id} </summary>
            <p>{format!("Size: {}", eclass.len())}</p>
            <p>{format!("Best: {}", eclass.metadata.expr.to_sexp())}</p>
            <p>{format!("Cost: {}", eclass.metadata.cost)}</p>
        </details>
    }
}

impl Renderable<Model> for Model {
    fn view(&self) -> Html<Self> {
        let query_message = match &self.query {
            Ok(q) => {
                let found: Vec<Id> = q.matches.iter().map(|m| m.eclass).collect();
                format!("Found at {:?}", found)
            }
            Err(s) => s.clone(),
        };

        html! {
        <main>
            <section id="add",>
                <form onsubmit=|e| {e.prevent_default(); Msg::AddQuery},>
                    <input oninput=|e| Msg::UpdateQuery(e.value),></input>
                </form>
                <p> {query_message} </p>
                <table>
                    <tr>
                        <th> {"expr"} </th>
                        <th> {"eclass"} </th>
                    </tr>
                    { for self.added.iter().map(Renderable::view) }
                </table>
            </section>
            <section id="examples",>
                <h3> {"Examples"} </h3>
                <div>
                    { for self.examples.iter().cloned().map(view_example) }
                </div>
            </section>
            <section id="eclasses",>
                <h3> {"EClasses"} </h3>
                <div>
                    { for self.egraph.classes().map(view_eclass) }
                </div>
            </section>
            <section id="rewrites",>
                <h3> {"Rewrites"} </h3>
                <button onclick=|_| Msg::RunRewrites,>{"Run"}</button>
                <div>
                    { for self.rewrite_groups.iter().map(Renderable::view) }
                </div>
            </section>
        </main>
        }
    }
}

fn main() {
    yew::start_app::<Model>();
}
