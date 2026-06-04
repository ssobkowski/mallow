use std::collections::{HashMap, HashSet};

/// A read-only view of a directed graph.
pub trait GraphView {
    fn entry(&self) -> usize;
    fn successors(&self, node: usize) -> &[usize];
    fn predecessors(&self, node: usize) -> &[usize];
    fn contains_node(&self, node: usize) -> bool;
    fn iter(&self) -> impl Iterator<Item = usize> + '_;
    fn len(&self) -> usize;

    #[cfg(feature = "visualize")]
    fn is_reachable(&self, node: usize) -> bool {
        self.contains_node(node) && (node == self.entry() || !self.predecessors(node).is_empty())
    }

    fn post_order(&self) -> Vec<usize> {
        fn dfs<G: GraphView + ?Sized>(
            graph: &G,
            node: usize,
            visited: &mut HashSet<usize>,
            order: &mut Vec<usize>,
        ) {
            if !graph.contains_node(node) {
                return;
            }

            if !visited.insert(node) {
                return;
            }

            for &succ in graph.successors(node) {
                dfs(graph, succ, visited, order);
            }

            order.push(node);
        }

        let mut visited = HashSet::new();
        let mut order = Vec::new();

        dfs(self, self.entry(), &mut visited, &mut order);

        order
    }

    fn reverse_post_order(&self) -> Vec<usize> {
        let mut order = self.post_order();
        order.reverse();
        order
    }

    /// Computes immediate dominators for all reachable blocks using the
    /// Cooper-Harvey-Kennedy algorithm.
    fn build_idoms(&self) -> DominatorTree {
        let rpo_nodes = self.reverse_post_order();

        let mut idoms = HashMap::new();
        idoms.insert(self.entry(), self.entry());

        let mut rpo_number = HashMap::new();
        for (index, &block) in rpo_nodes.iter().enumerate() {
            rpo_number.insert(block, index);
        }

        let mut changed = true;
        while changed {
            changed = false;
            for &block in &rpo_nodes {
                if block == self.entry() {
                    continue;
                }

                let Some(mut new_idom) = self
                    .predecessors(block)
                    .iter()
                    .copied()
                    .find(|p| rpo_number.contains_key(p) && idoms.contains_key(p))
                else {
                    continue;
                };

                for &p in self.predecessors(block) {
                    if p != new_idom && rpo_number.contains_key(&p) && idoms.contains_key(&p) {
                        new_idom = DominatorTree::intersect(p, new_idom, &idoms, &rpo_number);
                    }
                }

                if idoms.get(&block).copied() != Some(new_idom) {
                    idoms.insert(block, new_idom);
                    changed = true;
                }
            }
        }
        idoms.remove(&self.entry());

        DominatorTree { idoms }
    }
}

impl<G: GraphView + ?Sized> GraphView for &G {
    fn entry(&self) -> usize {
        (**self).entry()
    }

    fn successors(&self, node: usize) -> &[usize] {
        (**self).successors(node)
    }

    fn predecessors(&self, node: usize) -> &[usize] {
        (**self).predecessors(node)
    }

    fn contains_node(&self, node: usize) -> bool {
        (**self).contains_node(node)
    }

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        (**self).iter()
    }

    fn len(&self) -> usize {
        (**self).len()
    }
}

#[derive(Debug, Clone)]
pub struct DominatorTree {
    idoms: HashMap<usize, usize>,
}

impl DominatorTree {
    pub fn idom(&self, node: usize) -> Option<usize> {
        self.idoms.get(&node).copied()
    }

    pub fn dominates(&self, dom: usize, node: usize) -> bool {
        if dom == node {
            return true;
        }

        let mut current = node;
        loop {
            match self.idom(current) {
                Some(idom) if idom == dom => return true,
                Some(idom) => current = idom,
                None => return false,
            }
        }
    }

    fn intersect(
        mut b1: usize,
        mut b2: usize,
        idoms: &HashMap<usize, usize>,
        rpo_number: &HashMap<usize, usize>,
    ) -> usize {
        while b1 != b2 {
            while rpo_number
                .get(&b1)
                .expect("intersect node must have an RPO number")
                > rpo_number
                    .get(&b2)
                    .expect("intersect node must have an RPO number")
            {
                b1 = *idoms
                    .get(&b1)
                    .expect("intersect node must have an immediate dominator");
            }
            while rpo_number
                .get(&b2)
                .expect("intersect node must have an RPO number")
                > rpo_number
                    .get(&b1)
                    .expect("intersect node must have an RPO number")
            {
                b2 = *idoms
                    .get(&b2)
                    .expect("intersect node must have an immediate dominator");
            }
        }
        b1
    }
}

/// A graph with a single distinguished entry and exit.
pub trait SeseGraphView: GraphView {
    fn exit(&self) -> usize;
}

impl<G: SeseGraphView + ?Sized> SeseGraphView for &G {
    fn exit(&self) -> usize {
        (**self).exit()
    }
}

pub struct Reversed<G: SeseGraphView>(G);

impl<G: SeseGraphView> Reversed<G> {
    pub fn new(graph: G) -> Self {
        Self(graph)
    }
}

impl<G: SeseGraphView> GraphView for Reversed<G> {
    fn entry(&self) -> usize {
        self.0.exit()
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

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.0.iter()
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<G: SeseGraphView> SeseGraphView for Reversed<G> {
    fn exit(&self) -> usize {
        self.0.entry()
    }
}

pub struct AdjGraph<'a> {
    entry: usize,
    successors: &'a [Vec<usize>],
    predecessors: &'a [Vec<usize>],
}

impl<'a> AdjGraph<'a> {
    pub fn new(entry: usize, successors: &'a [Vec<usize>], predecessors: &'a [Vec<usize>]) -> Self {
        assert_eq!(successors.len(), predecessors.len());

        Self {
            entry,
            successors,
            predecessors,
        }
    }
}

impl GraphView for AdjGraph<'_> {
    fn entry(&self) -> usize {
        self.entry
    }

    fn successors(&self, node: usize) -> &[usize] {
        &self.successors[node]
    }

    fn predecessors(&self, node: usize) -> &[usize] {
        &self.predecessors[node]
    }

    fn contains_node(&self, node: usize) -> bool {
        node < self.successors.len()
    }

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        0..self.successors.len()
    }

    fn len(&self) -> usize {
        self.successors.len()
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

#[cfg(test)]
mod tests {
    use super::{AdjGraph, GraphView, Reversed, SeseGraphView};
    use std::collections::HashMap;

    struct SparseGraph {
        entry: usize,
        exit: usize,
        nodes: HashMap<usize, ()>,
        successors: HashMap<usize, Vec<usize>>,
        predecessors: HashMap<usize, Vec<usize>>,
    }

    impl SparseGraph {
        fn new(entry: usize, exit: usize, edges: &[(usize, usize)], nodes: &[usize]) -> Self {
            let nodes = nodes.iter().copied().map(|node| (node, ())).collect();
            let mut successors: HashMap<usize, Vec<usize>> = HashMap::new();
            let mut predecessors: HashMap<usize, Vec<usize>> = HashMap::new();

            for &(src, dst) in edges {
                successors.entry(src).or_default().push(dst);
                predecessors.entry(dst).or_default().push(src);
            }

            Self {
                entry,
                exit,
                nodes,
                successors,
                predecessors,
            }
        }
    }

    impl GraphView for SparseGraph {
        fn entry(&self) -> usize {
            self.entry
        }

        fn successors(&self, node: usize) -> &[usize] {
            self.successors.get(&node).map_or(&[], Vec::as_slice)
        }

        fn predecessors(&self, node: usize) -> &[usize] {
            self.predecessors.get(&node).map_or(&[], Vec::as_slice)
        }

        fn contains_node(&self, node: usize) -> bool {
            self.nodes.contains_key(&node)
        }

        fn iter(&self) -> impl Iterator<Item = usize> + '_ {
            self.nodes.keys().copied()
        }

        fn len(&self) -> usize {
            self.nodes.len()
        }
    }

    impl SeseGraphView for SparseGraph {
        fn exit(&self) -> usize {
            self.exit
        }
    }

    #[test]
    fn dense_adj_graph_rpo_and_idoms() {
        let successors = vec![vec![1, 2], vec![3], vec![3], vec![]];
        let predecessors = vec![vec![], vec![0], vec![0], vec![1, 2]];
        let graph = AdjGraph::new(0, &successors, &predecessors);

        assert_eq!(graph.reverse_post_order(), vec![0, 2, 1, 3]);

        let idoms = graph.build_idoms();
        assert_eq!(idoms.idom(0), None);
        assert_eq!(idoms.idom(1), Some(0));
        assert_eq!(idoms.idom(2), Some(0));
        assert_eq!(idoms.idom(3), Some(0));
        assert!(idoms.dominates(0, 3));
        assert!(!idoms.dominates(1, 2));
    }

    #[test]
    fn sparse_node_ids_keep_original_ids() {
        let graph = SparseGraph::new(10, 30, &[(10, 20), (20, 30)], &[10, 20, 30]);

        assert_eq!(graph.reverse_post_order(), vec![10, 20, 30]);

        let idoms = graph.build_idoms();
        assert_eq!(idoms.idom(10), None);
        assert_eq!(idoms.idom(20), Some(10));
        assert_eq!(idoms.idom(30), Some(20));
    }

    #[test]
    fn sparse_unreachable_nodes_are_ignored() {
        let graph = SparseGraph::new(10, 30, &[(10, 20), (20, 30)], &[10, 20, 30, 99]);

        let idoms = graph.build_idoms();
        assert_eq!(idoms.idom(99), None);
        assert!(!idoms.dominates(10, 99));
    }

    #[test]
    fn reversed_sese_graph_computes_postdominator_idoms() {
        let graph = SparseGraph::new(
            10,
            40,
            &[(10, 20), (10, 30), (20, 40), (30, 40)],
            &[10, 20, 30, 40],
        );

        let postidoms = Reversed::new(&graph).build_idoms();
        assert_eq!(postidoms.idom(10), Some(40));
        assert_eq!(postidoms.idom(20), Some(40));
        assert_eq!(postidoms.idom(30), Some(40));
        assert_eq!(postidoms.idom(40), None);
    }
}
