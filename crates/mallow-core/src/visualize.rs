use std::path::PathBuf;

use serde_json::{Value, json};

use crate::Unit;
use crate::ir::fir::{Block, BlockExit, Edge as FirEdge, Function, ValueId};
use crate::ir::graph::{DominatorTree, GraphView};

const CHAR_W: f64 = 7.2;
const LINE_H: f64 = 16.0;
const HEADER_H: f64 = 24.0;
const H_PAD: f64 = 10.0;
const V_PAD: f64 = 8.0;
const MIN_W: f64 = 190.0;

const LAYER_H_HINT: f64 = 200.0;

struct NodeLabel {
    header: String,
    lines: Vec<(String, bool)>,
}

/// Formats a list of FIR values for the graph labels.
fn format_values(values: &[ValueId]) -> String {
    values
        .iter()
        .map(|value| format!("%v{}", value.index()))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Formats block arguments as formal-to-actual bindings.
fn format_bindings(bindings: &[(ValueId, ValueId)]) -> String {
    bindings
        .iter()
        .map(|(formal, actual)| format!("%v{} <- %v{}", formal.index(), actual.index()))
        .collect::<Vec<_>>()
        .join(", ")
}

fn build_label(idx: usize, function: &Function, block: &Block, is_entry: bool) -> NodeLabel {
    let mut header = format!("Block {idx}");
    if !block.params.is_empty() {
        header.push_str(&format!(" ({})", format_values(&block.params)));
    }
    if is_entry {
        header.push_str(" (Entry)");
    }
    if matches!(&block.exit, BlockExit::Return(_)) {
        header.push_str(" (Exit)");
    }

    let mut lines: Vec<_> = block
        .instrs
        .iter()
        .map(|instr| (function.display_instr(instr).to_string(), false))
        .collect();

    if !matches!(&block.exit, BlockExit::Jump(_) | BlockExit::Fallthrough(_)) {
        let is_return = matches!(&block.exit, BlockExit::Return(_));
        lines.push((block.exit.display().to_string(), !is_return));
    }

    NodeLabel { header, lines }
}

/// Computes the dimensions of one node label.
fn node_size(label: &NodeLabel) -> (f64, f64) {
    let max_chars = label
        .lines
        .iter()
        .map(|(line, _)| line.len())
        .chain(std::iter::once(label.header.len()))
        .max()
        .unwrap_or(0);
    let w = (max_chars as f64 * CHAR_W + H_PAD * 2.0).max(MIN_W);
    let h = HEADER_H + label.lines.len() as f64 * LINE_H + V_PAD * 2.0;
    (w, h)
}

fn dom_depths(idoms: &DominatorTree<usize>, entry: usize, node_count: usize) -> Vec<usize> {
    let mut depth = vec![usize::MAX; node_count];
    depth[entry] = 0;

    let mut changed = true;
    while changed {
        changed = false;
        for node in 0..node_count {
            if depth[node] != usize::MAX {
                continue;
            }
            if let Some(idom) = idoms.idom(node)
                && idom < node_count
                && depth[idom] != usize::MAX
            {
                depth[node] = depth[idom] + 1;
                changed = true;
            }
        }
    }

    depth
        .iter()
        .map(|&depth| if depth == usize::MAX { 0 } else { depth })
        .collect()
}

struct Edge {
    id: String,
    src: usize,
    dst: usize,
    /// Formal and actual values connected by this edge.
    bindings: Vec<(ValueId, ValueId)>,
    color: &'static str,
    is_back: bool,
    src_port_order: usize,
}

impl Edge {
    /// Formats the block-argument bindings for an ELK label.
    fn bindings_text(&self) -> Option<String> {
        (!self.bindings.is_empty()).then(|| format!("({})", format_bindings(&self.bindings)))
    }
}

struct GraphPayload {
    tag: String,
    elk_json: Value,
    label_json: Value,
    edge_color_json: Value,
}

fn graph_payload(function: &Function, tag: &str) -> GraphPayload {
    let node_count = function.cfg.len();
    let idoms = (node_count > 0).then(|| function.cfg.build_idoms());
    let depths = idoms.as_ref().map_or_else(Vec::new, |idoms| {
        dom_depths(idoms, function.cfg.entry(), node_count)
    });

    let labels: Vec<Option<NodeLabel>> = function
        .cfg
        .enumerate()
        .map(|(index, block)| {
            function
                .cfg
                .is_reachable(index)
                .then(|| build_label(index, function, block, index == function.cfg.entry()))
        })
        .collect();

    let mut edge_counter = 0usize;
    let mut edges = Vec::new();

    if let Some(idoms) = idoms.as_ref() {
        for (src, block) in function.cfg.enumerate() {
            if !function.cfg.is_reachable(src) {
                continue;
            }

            match &block.exit {
                BlockExit::Jump(edge) | BlockExit::Fallthrough(edge) => add_edge(
                    &mut edges,
                    &mut edge_counter,
                    &function.cfg,
                    idoms,
                    src,
                    edge,
                    &function.cfg[edge.target].params,
                    "#2196F3",
                    0,
                ),
                BlockExit::Branch {
                    then_edge,
                    else_edge,
                    ..
                } => {
                    // Then is green and left. Else is red and right.
                    add_edge(
                        &mut edges,
                        &mut edge_counter,
                        &function.cfg,
                        idoms,
                        src,
                        then_edge,
                        &function.cfg[then_edge.target].params,
                        "#4CAF50",
                        0,
                    );
                    add_edge(
                        &mut edges,
                        &mut edge_counter,
                        &function.cfg,
                        idoms,
                        src,
                        else_edge,
                        &function.cfg[else_edge.target].params,
                        "#f44336",
                        1,
                    );
                }
                BlockExit::NumericFor {
                    body_edge,
                    exit_edge,
                    ..
                }
                | BlockExit::NumericForLoop {
                    body_edge,
                    exit_edge,
                }
                | BlockExit::GenericForLoop {
                    body_edge,
                    exit_edge,
                    ..
                } => {
                    add_edge(
                        &mut edges,
                        &mut edge_counter,
                        &function.cfg,
                        idoms,
                        src,
                        body_edge,
                        &function.cfg[body_edge.target].params,
                        "#4CAF50",
                        0,
                    );
                    add_edge(
                        &mut edges,
                        &mut edge_counter,
                        &function.cfg,
                        idoms,
                        src,
                        exit_edge,
                        &function.cfg[exit_edge.target].params,
                        "#f44336",
                        1,
                    );
                }
                BlockExit::GenericFor { body_edge, .. } => {
                    add_edge(
                        &mut edges,
                        &mut edge_counter,
                        &function.cfg,
                        idoms,
                        src,
                        body_edge,
                        &function.cfg[body_edge.target].params,
                        "#4CAF50",
                        0,
                    );
                }
                BlockExit::Return(_) => {}
            }
        }
    }

    let mut out_edges = vec![vec![]; node_count];
    let mut in_edges = vec![vec![]; node_count];
    for edge in &edges {
        out_edges[edge.src].push(edge);
        in_edges[edge.dst].push(edge);
    }
    for outgoing in &mut out_edges {
        outgoing.sort_by_key(|edge| edge.src_port_order);
    }

    let elk_json = build_elk_json(&labels, &edges, &out_edges, &in_edges, &depths, node_count);
    let label_json = build_label_json(&labels, node_count);
    let edge_color_json = build_edge_color_json(&edges);

    GraphPayload {
        tag: tag.to_owned(),
        elk_json,
        label_json,
        edge_color_json,
    }
}

fn add_edge<G: GraphView<Node = usize>>(
    edges: &mut Vec<Edge>,
    edge_counter: &mut usize,
    graph: &G,
    idoms: &DominatorTree<usize>,
    src: usize,
    block_edge: &FirEdge,
    target_params: &[ValueId],
    color: &'static str,
    src_port_order: usize,
) {
    let dst = block_edge.target;
    if !graph.is_reachable(dst) {
        return;
    }

    *edge_counter += 1;
    edges.push(Edge {
        id: format!("e{edge_counter}"),
        src,
        dst,
        bindings: target_params
            .iter()
            .copied()
            .zip(block_edge.params.iter().copied())
            .collect(),
        color,
        is_back: idoms.dominates(dst, src),
        src_port_order,
    });
}

pub fn dump_cfgs(unit: &Unit<Function>, output: PathBuf) {
    let payloads: Vec<_> = unit
        .functions()
        .map(|function| graph_payload(&function, &format!("Proto {}", function.id.0)))
        .collect();

    let title = payloads.get(unit.entry().0 as usize).map_or_else(
        || "CFG".to_owned(),
        |payload| format!("CFG: {}", payload.tag),
    );

    let graphs_json = build_graphs_json(&payloads);
    let html = build_html(&graphs_json, unit.entry().0 as usize, &title);

    std::fs::write(&output, &html).expect("failed to write cfg html");
}

fn build_elk_json(
    labels: &[Option<NodeLabel>],
    edges: &[Edge],
    out_edges: &[Vec<&Edge>],
    in_edges: &[Vec<&Edge>],
    depths: &[usize],
    n: usize,
) -> Value {
    let children: Vec<_> = (0..n)
        .filter_map(|i| {
            let label = labels[i].as_ref()?;
            let (w, h) = node_size(label);
            let y_hint = depths[i] as f64 * LAYER_H_HINT;

            let ports: Vec<_> = out_edges[i]
                .iter()
                .map(|e| {
                    json!({
                        "id": format!("block_{i}_S_{}", e.id),
                        "properties": {
                            "port.side": "SOUTH",
                            "port.index": e.src_port_order.to_string()
                        }
                    })
                })
                .chain(in_edges[i].iter().enumerate().map(|(pi, e)| {
                    json!({
                        "id": format!("block_{i}_N_{}", e.id),
                        "properties": {
                            "port.side": "NORTH",
                            "port.index": pi.to_string()
                        }
                    })
                }))
                .collect();

            Some(json!({
                "id": format!("block_{i}"),
                "width": w,
                "height": h,
                "y": y_hint,
                "properties": { "elk.portConstraints": "FIXED_ORDER" },
                "ports": ports
            }))
        })
        .collect();

    let edges: Vec<_> = edges
        .iter()
        .map(|e| {
            let mut edge = json!({
                "id": e.id.to_string(),
                "sources": [format!("block_{}_S_{}", e.src, e.id)],
                "targets": [format!("block_{}_N_{}", e.dst, e.id)]
            });
            if let Some(text) = e.bindings_text() {
                let width = text.len() as f64 * CHAR_W + H_PAD * 2.0;
                edge["labels"] = json!([{
                    "id": format!("{}_params", e.id),
                    "text": text,
                    "width": width,
                    "height": LINE_H,
                    "layoutOptions": {
                        "elk.edgeLabels.placement": "CENTER"
                    }
                }]);
            }
            if e.is_back {
                edge["properties"] = json!({ "elk.edge.type": "BACKEDGE" });
            }
            edge
        })
        .collect();

    json!({
        "id": "root",
        "layoutOptions": {
            "elk.algorithm": "layered",
            "elk.direction": "DOWN",
            "elk.spacing.nodeNode": "50",
            "elk.layered.spacing.nodeNodeBetweenLayers": "60",
            "elk.edgeRouting": "ORTHOGONAL",
            "elk.layered.unnecessaryBendpoints": "true",
            "elk.layered.layeringStrategy": "INTERACTIVE",
            "elk.layered.crossingMinimization.strategy": "LAYER_SWEEP",
            "elk.layered.crossingMinimization.greedySwitch.type": "TWO_SIDED",
            "elk.layered.crossingMinimization.forceNodeModelOrder": "false",
            "elk.layered.nodePlacement.strategy": "NETWORK_SIMPLEX",
            "elk.layered.cycleBreaking.strategy": "GREEDY"
        },
        "children": children,
        "edges": edges
    })
}

fn build_label_json(labels: &[Option<NodeLabel>], n: usize) -> Value {
    (0..n)
        .filter_map(|i| {
            let label = labels[i].as_ref()?;
            let lines: Vec<_> = label
                .lines
                .iter()
                .map(|(text, bold)| json!({ "text": text, "bold": bold }))
                .collect();

            Some((
                format!("block_{i}"),
                json!({ "header": label.header, "lines": lines }),
            ))
        })
        .collect()
}

fn build_edge_color_json(edges: &[Edge]) -> Value {
    edges
        .iter()
        .map(|e| (e.id.to_string(), json!(e.color)))
        .collect()
}

fn build_graphs_json(graphs: &[GraphPayload]) -> Value {
    graphs
        .iter()
        .map(|graph| {
            json!({
                "tag": graph.tag,
                "elkGraph": graph.elk_json,
                "nodeLabels": graph.label_json,
                "edgeColors": graph.edge_color_json
            })
        })
        .collect()
}

fn build_html(graphs_json: &Value, selected_index: usize, title: &str) -> String {
    include_str!("../assets/cfg.html")
        .replace("__GRAPHS_JSON__", &graphs_json.to_string())
        .replace("__SELECTED_INDEX__", &selected_index.to_string())
        .replace("__BASE_TITLE__", &serde_json::to_string(title).unwrap())
}

#[cfg(test)]
mod tests {
    use id_arena::Arena;

    use super::*;
    use crate::ir::fir::Value;

    /// Verifies that block arguments survive the ELK graph conversion.
    #[test]
    fn encodes_edge_bindings_as_label() {
        let mut values = Arena::<Value>::new();
        let edges = vec![Edge {
            id: "e1".to_owned(),
            src: 0,
            dst: 1,
            bindings: {
                let formal_0 = values.alloc(Value);
                let formal_1 = values.alloc(Value);
                let actual_0 = values.alloc(Value);
                let actual_1 = values.alloc(Value);
                vec![(formal_0, actual_0), (formal_1, actual_1)]
            },
            color: "#2196F3",
            is_back: false,
            src_port_order: 0,
        }];
        let labels = vec![
            Some(NodeLabel {
                header: "Block 0".to_owned(),
                lines: Vec::new(),
            }),
            Some(NodeLabel {
                header: "Block 1 (%v0, %v1)".to_owned(),
                lines: Vec::new(),
            }),
        ];
        let out_edges = vec![vec![&edges[0]], vec![]];
        let in_edges = vec![vec![], vec![&edges[0]]];

        let graph = build_elk_json(&labels, &edges, &out_edges, &in_edges, &[0, 1], 2);

        assert_eq!(
            graph["edges"][0]["labels"][0]["text"].as_str(),
            Some("(%v0 <- %v2, %v1 <- %v3)")
        );
    }
}
