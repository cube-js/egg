use egg::*;
use std::collections::HashMap;

type Cost = i32;

struct TopDownExtract<'a, L, A>
where
    L: Language,
    A: Analysis<L>,
{
    egraph: &'a EGraph<L, A>,
    extract_map: HashMap<Id, (usize, Cost)>,
}

impl<'a, L, A> TopDownExtract<'a, L, A>
where
    L: Language,
    A: Analysis<L>,
{
    fn new(egraph: &'a EGraph<L, A>) -> Self {
        Self {
            egraph,
            extract_map: Default::default(),
        }
    }

    fn extract(&mut self, eclass: Id, limit: Cost) -> (usize, Cost) {
        if limit <= 0 {
            return (usize::MAX, Cost::MAX);
        }
        if let Some((i, cost)) = self.extract_map.get(&eclass).copied() {
            return (i, cost);
        }
        // mark this e-class as in progress with big cost
        self.extract_map.insert(eclass, (usize::MAX, Cost::MAX));

        // compute the cost of each node, take the min
        let mut min_cost = limit;
        let mut min_i = usize::MAX;
        'nodes: for (i, node) in self.egraph[eclass].nodes.iter().enumerate() {
            // compute the cost of this node, recursing into children
            let mut total_node_cost = 1;
            let mut remaining = min_cost.saturating_sub(total_node_cost);
            for &child in node.children() {
                if remaining <= 0 {
                    continue 'nodes;
                }
                let (_, cost) = self.extract(child, remaining);
                total_node_cost = total_node_cost.saturating_add(cost);
                remaining = min_cost.saturating_sub(total_node_cost);
            }
            // if we made it out of this loop, we have a valid cost
            dbg!((i, node, remaining));
            min_cost = min_cost - remaining;
            min_i = i;
        }

        self.extract_map.insert(eclass, (min_i, min_cost));
        (min_i, min_cost)
    }

    pub fn build_term(&mut self, root: Id) -> (Cost, RecExpr<L>) {
        let (_, cost) = self.extract(root, Cost::MAX);
        let mut choose_node = |id: Id| {
            let (i, _) = self.extract(id, Cost::MAX);
            self.egraph[id].nodes[i].clone()
        };
        (cost, choose_node(root).build_recexpr(choose_node))
    }
}

define_language! {
    enum SimpleLanguage {
        Num(i32),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        Symbol(Symbol),
    }
}

fn make_rules() -> Vec<Rewrite<SimpleLanguage, ()>> {
    vec![
        rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("add-0"; "(+ ?a 0)" => "?a"),
        rewrite!("mul-0"; "(* ?a 0)" => "0"),
        rewrite!("mul-1"; "(* ?a 1)" => "?a"),
    ]
}

/// parse an expression, simplify it using egg, and pretty print it back out
fn simplify(s: &str) -> String {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<SimpleLanguage> = s.parse().unwrap();

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let runner = Runner::default().with_expr(&expr).run(&make_rules());

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let mut extractor = TopDownExtract::new(&runner.egraph);
    let (best_cost, best) = extractor.build_term(root);
    println!("Simplified {} to {} with cost {}", expr, best, best_cost);
    best.to_string()
}

#[test]
fn simple_tests() {
    assert_eq!(simplify("(* 0 42)"), "0");
    assert_eq!(simplify("(+ 0 (* 1 foo))"), "foo");
}
