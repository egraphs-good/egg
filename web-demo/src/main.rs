use stdweb::traits::IEvent;
use stdweb::web::Date;
use yew::services::ConsoleService;
use yew::{html, Component, ComponentLink, Html, Renderable, ShouldRender};

mod math;

use egg::{
    egraph::{AddResult, EClass},
    expr::{Id, RecExpr},
    parse::{pat_to_expr, ParsableLanguage, ParseError},
    pattern::{Pattern, PatternMatches, Rewrite},
};
use math::*;

struct Queried {
    pattern: Pattern<Math>,
    matches: Vec<PatternMatches<Math>>,
}

pub struct Model {
    console: ConsoleService,
    egraph: MathEGraph,
    query: Result<Queried, String>,
    added: Vec<Added>,
    examples: Vec<&'static str>,
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

pub enum Msg {
    AddExpr(String),
    AddQuery,
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
            examples: vec!["(+ 1 2)", "(* x (+ y z))"],
        }
    }

    fn update(&mut self, msg: Self::Message) -> ShouldRender {
        match msg {
            Msg::UpdateQuery(s) => {
                self.console.log(&s);

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
        };
        true
    }
}

fn view_example(s: &'static str) -> Html<Model> {
    html! { <div onclick=|e| Msg::AddExpr(s.to_string()),> {s} </div> }
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
                    { for self.added.iter().map(|a| a.view()) }
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
        </main>
        }
    }
}

fn main() {
    yew::start_app::<Model>();
}
