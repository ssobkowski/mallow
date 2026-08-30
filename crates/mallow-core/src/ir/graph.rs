use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// A read-only view of a directed graph.
pub trait GraphView {
    /// The node identifier type.
    type Node: Copy + Eq + Hash;

    /// The payload/data associated with each node.
    type Item;

    /// Returns the entry node of the graph.
    fn entry(&self) -> Self::Node;

    /// Retrieves a reference to the payload associated with `node`, if it exists.
    fn get(&self, node: Self::Node) -> Option<&Self::Item>;

    /// Returns an iterator over the immediate successors of `node`.
    fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node>;

    /// Returns an iterator over the immediate predecessors of `node`.
    fn predecessors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node>;

    /// Returns an iterator over all valid node IDs in the graph.
    fn nodes(&self) -> impl Iterator<Item = Self::Node>;

    /// Checks if a node ID exists in the graph.
    fn contains_node(&self, node: Self::Node) -> bool {
        self.get(node).is_some()
    }

    /// Total number of nodes in the graph.
    fn len(&self) -> usize;

    #[cfg(feature = "visualize")]
    fn is_reachable(&self, node: Self::Node) -> bool {
        self.contains_node(node)
            && (node == self.entry() || self.predecessors(node).next().is_some())
    }

    /// Computes depth-first post-order traversal starting at the entry node.
    fn post_order(&self) -> impl Iterator<Item = Self::Node> {
        fn dfs<G: GraphView + ?Sized>(
            graph: &G,
            node: G::Node,
            visited: &mut HashSet<G::Node>,
            order: &mut Vec<G::Node>,
        ) {
            if !graph.contains_node(node) || !visited.insert(node) {
                return;
            }

            for succ in graph.successors(node) {
                dfs(graph, succ, visited, order);
            }

            order.push(node);
        }

        let mut visited = HashSet::new();
        let mut order = Vec::new();
        dfs(self, self.entry(), &mut visited, &mut order);
        order.into_iter()
    }

    /// Computes reverse post-order (RPO) traversal starting at the entry node.
    fn reverse_post_order(&self) -> impl Iterator<Item = Self::Node> {
        let mut order: Vec<_> = self.post_order().collect();
        order.reverse();
        order.into_iter()
    }

    /// Computes immediate dominators for all reachable blocks using the
    /// Cooper-Harvey-Kennedy algorithm.
    fn build_idoms(&self) -> DominatorTree<Self::Node> {
        let rpo_nodes: Vec<_> = self.reverse_post_order().collect();
        if rpo_nodes.is_empty() {
            return DominatorTree {
                idoms: HashMap::new(),
            };
        }

        let mut idoms = HashMap::with_capacity(rpo_nodes.len());
        idoms.insert(self.entry(), self.entry());

        let rpo_number: HashMap<_, _> = rpo_nodes
            .iter()
            .enumerate()
            .map(|(idx, &node)| (node, idx))
            .collect();

        let mut changed = true;
        while changed {
            changed = false;
            for &node in &rpo_nodes {
                if node == self.entry() {
                    continue;
                }

                // Pick the first already-processed predecessor
                let Some(mut new_idom) = self
                    .predecessors(node)
                    .find(|p| idoms.contains_key(p) && rpo_number.contains_key(p))
                else {
                    continue;
                };

                for p in self.predecessors(node) {
                    if p != new_idom && idoms.contains_key(&p) && rpo_number.contains_key(&p) {
                        new_idom = DominatorTree::intersect(p, new_idom, &idoms, &rpo_number);
                    }
                }

                if idoms.get(&node).copied() != Some(new_idom) {
                    idoms.insert(node, new_idom);
                    changed = true;
                }
            }
        }
        idoms.remove(&self.entry());

        DominatorTree { idoms }
    }
}

impl<G: GraphView + ?Sized> GraphView for &G {
    type Node = G::Node;
    type Item = G::Item;

    fn get(&self, node: Self::Node) -> Option<&Self::Item> {
        (**self).get(node)
    }

    fn entry(&self) -> Self::Node {
        (**self).entry()
    }

    fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        (**self).successors(node)
    }

    fn predecessors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        (**self).predecessors(node)
    }

    fn nodes(&self) -> impl Iterator<Item = Self::Node> {
        (**self).nodes()
    }

    fn contains_node(&self, node: Self::Node) -> bool {
        (**self).contains_node(node)
    }

    fn len(&self) -> usize {
        (**self).len()
    }
}

/// A graph with single-entry and single-exit guarantees.
pub trait SeseGraphView: GraphView {
    fn exit(&self) -> Self::Node;
}

impl<G: SeseGraphView + ?Sized> SeseGraphView for &G {
    fn exit(&self) -> Self::Node {
        (**self).exit()
    }
}

/// Graph adapter that reverses edge directions and swaps entry/exit nodes.
#[derive(Debug, Clone, Copy)]
pub struct Reversed<G>(G);

impl<G> Reversed<G> {
    pub fn new(graph: G) -> Self {
        Self(graph)
    }
}

impl<G: SeseGraphView> GraphView for Reversed<G> {
    type Node = G::Node;
    type Item = G::Item;

    fn get(&self, node: Self::Node) -> Option<&Self::Item> {
        self.0.get(node)
    }

    fn entry(&self) -> Self::Node {
        self.0.exit()
    }

    fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        self.0.predecessors(node)
    }

    fn predecessors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        self.0.successors(node)
    }

    fn nodes(&self) -> impl Iterator<Item = Self::Node> {
        self.0.nodes()
    }

    fn contains_node(&self, node: Self::Node) -> bool {
        self.0.contains_node(node)
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<G: SeseGraphView> SeseGraphView for Reversed<G> {
    fn exit(&self) -> Self::Node {
        self.0.entry()
    }
}

#[derive(Debug, Clone)]
pub struct DominatorTree<N> {
    idoms: HashMap<N, N>,
}

impl<N: Copy + Eq + Hash> DominatorTree<N> {
    /// Returns the immediate dominator of `node`, or `None` if `node` is the root / unreachable.
    #[inline]
    pub fn idom(&self, node: N) -> Option<N> {
        self.idoms.get(&node).copied()
    }

    /// Checks if `dom` dominates `node` (reflexive: a node dominates itself).
    #[inline]
    pub fn dominates(&self, dom: N, node: N) -> bool {
        if dom == node {
            return true;
        }

        self.strictly_dominates(dom, node)
    }

    /// Checks if `dom` strictly dominates `node` (`dom != node`).
    #[inline]
    pub fn strictly_dominates(&self, dom: N, node: N) -> bool {
        self.dominators(node).any(|ancestor| ancestor == dom)
    }

    /// Returns the Lowest Common Dominator (LCA in the dominator tree) of two nodes.
    #[inline]
    pub fn common_dominator(&self, a: N, b: N) -> Option<N> {
        if a == b || self.dominates(a, b) {
            return Some(a);
        }
        if self.dominates(b, a) {
            return Some(b);
        }

        // Walk ancestors of `a` and return the first one that also dominates `b`
        self.dominators(a).find(|&cand| self.dominates(cand, b))
    }

    /// Computes the Lowest Common Dominator for an arbitrary collection of nodes.
    #[inline]
    pub fn lowest_common_dominator<I>(&self, nodes: I) -> Option<N>
    where
        I: IntoIterator<Item = N>,
    {
        let mut iter = nodes.into_iter();
        let first = iter.next()?;
        iter.try_fold(first, |acc, node| self.common_dominator(acc, node))
    }

    /// Finds the nearest common *strict* dominator for a set of blocks.
    ///
    /// If the set is empty, falls back to `entry`.
    /// If the Lowest Common Dominator (LCD) is itself an element of `blocks`,
    /// it steps up to `idom(LCD)` so strict dominance is preserved.
    #[inline]
    pub fn common_strict_dominator(&self, entry: N, nodes: &[N]) -> N {
        let Some(lcd) = self.lowest_common_dominator(nodes.iter().copied()) else {
            return entry;
        };

        // If the LCD is one of the input blocks, it cannot strictly dominate itself.
        if nodes.contains(&lcd) {
            self.idom(lcd).unwrap_or(entry)
        } else {
            lcd
        }
    }

    /// Returns an iterator yielding all strict dominators of `node` climbing toward the entry.
    #[inline]
    pub fn dominators(&self, node: N) -> impl Iterator<Item = N> + '_ {
        std::iter::successors(self.idom(node), |&curr| self.idom(curr))
    }

    fn intersect(mut b1: N, mut b2: N, idoms: &HashMap<N, N>, rpo_number: &HashMap<N, usize>) -> N {
        while b1 != b2 {
            while rpo_number[&b1] > rpo_number[&b2] {
                b1 = idoms[&b1];
            }
            while rpo_number[&b2] > rpo_number[&b1] {
                b2 = idoms[&b2];
            }
        }
        b1
    }
}

/// Slice-backed adjacency graph with `usize` node identifiers.
#[derive(Debug, Clone, Copy)]
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
    type Node = usize;
    type Item = ();

    fn get(&self, _: usize) -> Option<&Self::Item> {
        None // AdjGraph does not store items
    }

    fn entry(&self) -> usize {
        self.entry
    }

    fn successors(&self, node: usize) -> impl Iterator<Item = usize> {
        self.successors.get(node).into_iter().flatten().copied()
    }

    fn predecessors(&self, node: usize) -> impl Iterator<Item = usize> {
        self.predecessors.get(node).into_iter().flatten().copied()
    }

    fn nodes(&self) -> impl Iterator<Item = usize> {
        0..self.successors.len()
    }

    fn contains_node(&self, node: usize) -> bool {
        node < self.successors.len()
    }

    fn len(&self) -> usize {
        self.successors.len()
    }
}

/// Builds forward/backward adjacency lists based on the given block exits.
pub fn build_graph<I, T>(exits_iter: I) -> (Vec<Vec<usize>>, Vec<Vec<usize>>)
where
    I: IntoIterator<Item = T>,
    I::IntoIter: ExactSizeIterator,
    T: IntoIterator<Item = usize>,
{
    let iter = exits_iter.into_iter();
    let len = iter.len();

    let successors: Vec<Vec<_>> = iter
        .map(|targets| targets.into_iter().filter(|&t| t < len).collect())
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
    use std::collections::HashMap;
    use std::hash::Hash;

    use super::*;

    #[derive(Debug, Clone)]
    struct SparseGraph<N, T = ()> {
        entry: N,
        exit: N,
        nodes: HashMap<N, T>,
        successors: HashMap<N, Vec<N>>,
        predecessors: HashMap<N, Vec<N>>,
    }

    impl<N: Copy + Eq + Hash, T> SparseGraph<N, T> {
        fn new(
            entry: N,
            exit: N,
            edges: &[(N, N)],
            nodes: impl IntoIterator<Item = (N, T)>,
        ) -> Self {
            let nodes: HashMap<N, T> = nodes.into_iter().collect();
            let mut successors: HashMap<N, Vec<N>> = HashMap::new();
            let mut predecessors: HashMap<N, Vec<N>> = HashMap::new();

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

    impl<N: Copy + Eq + Hash, T> GraphView for SparseGraph<N, T> {
        type Node = N;
        type Item = T;

        fn get(&self, node: N) -> Option<&Self::Item> {
            self.nodes.get(&node)
        }

        fn entry(&self) -> N {
            self.entry
        }

        fn successors(&self, node: N) -> impl Iterator<Item = N> {
            self.successors.get(&node).into_iter().flatten().copied()
        }

        fn predecessors(&self, node: N) -> impl Iterator<Item = N> {
            self.predecessors.get(&node).into_iter().flatten().copied()
        }

        fn nodes(&self) -> impl Iterator<Item = N> {
            self.nodes.keys().copied()
        }

        fn contains_node(&self, node: N) -> bool {
            self.nodes.contains_key(&node)
        }

        fn len(&self) -> usize {
            self.nodes.len()
        }
    }

    impl<N: Copy + Eq + Hash, T> SeseGraphView for SparseGraph<N, T> {
        fn exit(&self) -> N {
            self.exit
        }
    }

    #[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
    struct BlockId(u32);

    #[test]
    fn dense_adj_graph_rpo_and_idoms() {
        let successors = vec![vec![1, 2], vec![3], vec![3], vec![]];
        let predecessors = vec![vec![], vec![0], vec![0], vec![1, 2]];
        let graph = AdjGraph::new(0, &successors, &predecessors);

        assert_eq!(
            graph.reverse_post_order().collect::<Vec<_>>(),
            vec![0, 2, 1, 3]
        );

        let idoms = graph.build_idoms();
        assert_eq!(idoms.idom(0), None);
        assert_eq!(idoms.idom(1), Some(0));
        assert_eq!(idoms.idom(2), Some(0));
        assert_eq!(idoms.idom(3), Some(0));
        assert!(idoms.dominates(0, 3));
        assert!(!idoms.dominates(1, 2));
    }

    #[test]
    fn typed_custom_node_ids() {
        let b0 = BlockId(0);
        let b1 = BlockId(1);
        let b2 = BlockId(2);

        let graph = SparseGraph::new(
            b0,
            b2,
            &[(b0, b1), (b1, b2)],
            [(b0, "entry"), (b1, "body"), (b2, "exit")],
        );

        assert_eq!(graph.get(b0), Some(&"entry"));
        assert_eq!(
            graph.reverse_post_order().collect::<Vec<_>>(),
            vec![b0, b1, b2]
        );

        let idoms = graph.build_idoms();
        assert_eq!(idoms.idom(b0), None);
        assert_eq!(idoms.idom(b1), Some(b0));
        assert_eq!(idoms.idom(b2), Some(b1));
        assert!(idoms.dominates(b0, b2));
    }

    #[test]
    fn sparse_unreachable_nodes_are_ignored() {
        let graph = SparseGraph::new(
            10,
            30,
            &[(10, 20), (20, 30)],
            [(10, ()), (20, ()), (30, ()), (99, ())],
        );

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
            [(10, ()), (20, ()), (30, ()), (40, ())],
        );

        let postidoms = Reversed::new(&graph).build_idoms();
        assert_eq!(postidoms.idom(10), Some(40));
        assert_eq!(postidoms.idom(20), Some(40));
        assert_eq!(postidoms.idom(30), Some(40));
        assert_eq!(postidoms.idom(40), None);
    }
}
