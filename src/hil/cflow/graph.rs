/// A read-only view of a SESE graph.
pub trait GraphView {
    fn entry(&self) -> usize;
    fn exit(&self) -> usize;
    fn len(&self) -> usize;
    fn successors(&self, node: usize) -> &[usize];
    fn predecessors(&self, node: usize) -> &[usize];
    fn contains_node(&self, node: usize) -> bool;
}

pub struct Reversed<G: GraphView>(G);

impl<G: GraphView> GraphView for Reversed<G> {
    fn entry(&self) -> usize {
        self.0.exit()
    }

    fn exit(&self) -> usize {
        self.0.entry()
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn successors(&self, node: usize) -> &[usize] {
        self.0.predecessors(node)
    }

    fn predecessors(&self, node: usize) -> &[usize] {
        self.0.successors(node)
    }

    fn contains_node(&self, node: usize) -> bool {
        self.0.contains_node(node)
    }
}

/// Builds forward/backward adjacency lists based on the given block exits.
pub fn build_graph<I>(exits_iter: I) -> (Vec<Vec<usize>>, Vec<Vec<usize>>)
where
    I: IntoIterator<Item = [Option<usize>; 2]>,
    I::IntoIter: ExactSizeIterator,
{
    let iter = exits_iter.into_iter();
    let len = iter.len();

    let successors: Vec<Vec<_>> = iter
        .map(|targets| targets.into_iter().flatten().filter(|&t| t < len).collect())
        .collect();

    let mut predecessors = vec![Vec::new(); len];

    for (src, targets) in successors.iter().enumerate() {
        for &target in targets {
            predecessors[target].push(src);
        }
    }

    (successors, predecessors)
}

use std::collections::HashSet;

pub fn compute_rpo<G: GraphView>(graph: &G) -> Vec<usize> {
    let mut visited = HashSet::with_capacity(graph.len());
    let mut post_order = Vec::with_capacity(graph.len());

    fn dfs<G: GraphView>(
        graph: &G,
        block: usize,
        visited: &mut HashSet<usize>,
        post_order: &mut Vec<usize>,
    ) {
        visited.insert(block);

        for &succ in graph.successors(block) {
            if !visited.contains(&succ) {
                dfs(graph, succ, visited, post_order);
            }
        }

        post_order.push(block);
    }

    dfs(graph, graph.entry(), &mut visited, &mut post_order);

    post_order.reverse();
    post_order
}

/// Computes immediate dominators for all reachable blocks using the
/// Cooper-Harvey-Kennedy algorithm.
pub fn build_idoms<G: GraphView>(graph: &G) -> Vec<Option<usize>> {
    let rpo_nodes = compute_rpo(graph);

    let mut doms = vec![None; graph.len()];
    doms[graph.entry()] = Some(graph.entry());

    let mut rpo_number = vec![usize::MAX; graph.len()];
    for (index, &block) in rpo_nodes.iter().enumerate() {
        rpo_number[block] = index;
    }

    let mut changed = true;
    while changed {
        changed = false;
        for &block in &rpo_nodes {
            if block == graph.entry() {
                continue;
            }

            let Some(mut new_idom) = graph
                .predecessors(block)
                .iter()
                .copied()
                .find(|&p| doms[p].is_some())
            else {
                continue;
            };

            for &p in graph.predecessors(block) {
                if p != new_idom && doms[p].is_some() {
                    new_idom = intersect(p, new_idom, &doms, &rpo_number);
                }
            }

            if doms[block] != Some(new_idom) {
                doms[block] = Some(new_idom);
                changed = true;
            }
        }
    }
    doms[graph.entry()] = None;

    doms
}

fn intersect(mut b1: usize, mut b2: usize, doms: &[Option<usize>], rpo_number: &[usize]) -> usize {
    while b1 != b2 {
        while rpo_number[b1] > rpo_number[b2] {
            b1 = doms[b1].unwrap();
        }
        while rpo_number[b2] > rpo_number[b1] {
            b2 = doms[b2].unwrap();
        }
    }
    b1
}
