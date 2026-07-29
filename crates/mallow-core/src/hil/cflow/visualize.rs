use std::{fmt::Display, path::PathBuf};

use serde_json::{Value, json};

use crate::hil::cflow::{
    cfg::{Block, BlockExit, ControlFlowGraph},
    graph::{DominatorTree, GraphView},
};

const CHAR_W: f64 = 7.2;
const LINE_H: f64 = 16.0;
const HEADER_H: f64 = 24.0;
const H_PAD: f64 = 10.0;
const V_PAD: f64 = 8.0;
const MIN_W: f64 = 190.0;

const LAYER_H_HINT: f64 = 200.0;

struct NodeLabel {
    header: String,
    /// (text, bold)
    lines: Vec<(String, bool)>,
}

fn join_display(items: impl IntoIterator<Item = impl Display>, sep: &str) -> String {
    items
        .into_iter()
        .map(|v| v.to_string())
        .collect::<Vec<_>>()
        .join(sep)
}

fn build_label(idx: usize, block: &Block, is_entry: bool) -> NodeLabel {
    let mut header = format!("Block {idx}");
    if is_entry {
        header.push_str(" (Entry)");
    }
    if matches!(block.exit(), BlockExit::Return(_)) {
        header.push_str(" (Exit)");
    }

    let mut lines: Vec<_> = block
        .stmts()
        .iter()
        .map(|s| (format!("{}", s), false))
        .collect();

    match block.exit() {
        BlockExit::CondJump { cond, .. } => lines.push((format!("if ({})", cond), true)),
        BlockExit::FornPrep {
            var,
            start,
            end,
            step,
            ..
        } => lines.push((
            format!("for v{} = {}, {}, {}", var.index(), start, end, step),
            true,
        )),
        BlockExit::FornLoop { .. } => lines.push(("forn_loop".into(), true)),
        BlockExit::ForgPrep { exprs, .. } => lines.push((
            format!("for {}, {}, {}", exprs[0], exprs[1], exprs[2]),
            true,
        )),
        BlockExit::ForgLoop { vars, .. } => lines.push((
            format!(
                "forg_loop {}",
                join_display(vars.iter().map(|s| format!("v{}", s.index())), ", ")
            ),
            true,
        )),
        BlockExit::Return(vals) => lines.push((format!("return {}", vals), false)),
        _ => {}
    }

    NodeLabel { header, lines }
}

fn node_size(label: &NodeLabel) -> (f64, f64) {
    let max_chars = label
        .lines
        .iter()
        .map(|(l, _)| l.len())
        .chain(std::iter::once(label.header.len()))
        .max()
        .unwrap_or(0);
    let w = (max_chars as f64 * CHAR_W + H_PAD * 2.0).max(MIN_W);
    let h = HEADER_H + label.lines.len() as f64 * LINE_H + V_PAD * 2.0;
    (w, h)
}

fn dom_depths(idoms: &DominatorTree, entry: usize, node_count: usize) -> Vec<usize> {
    let n = node_count;
    let mut depth = vec![usize::MAX; n];
    depth[entry] = 0;

    let mut changed = true;
    while changed {
        changed = false;
        for i in 0..n {
            if depth[i] != usize::MAX {
                continue;
            }
            if let Some(idom) = idoms.idom(i)
                && idom < n
                && depth[idom] != usize::MAX
            {
                depth[i] = depth[idom] + 1;
                changed = true;
            }
        }
    }

    // Unreachable nodes (depth still MAX) get 0 - they're filtered out anyway.
    depth
        .iter()
        .map(|&d| if d == usize::MAX { 0 } else { d })
        .collect()
}

struct Edge {
    id: String,
    src: usize,
    dst: usize,
    /// CSS color string
    color: &'static str,
    is_back: bool,
    /// Port order on the source's south face (0 = leftmost).
    src_port_order: usize,
}

struct GraphPayload {
    tag: String,
    elk_json: Value,
    label_json: Value,
    edge_color_json: Value,
}

impl ControlFlowGraph {
    fn graph_payload(&self, tag: &str) -> GraphPayload {
        let n = self.len();

        let idoms = self.build_idoms();
        let depths = dom_depths(&idoms, self.entry(), n);
        let labels: Vec<Option<NodeLabel>> = self
            .blocks()
            .enumerate()
            .map(|(i, b)| {
                self.is_reachable(i)
                    .then(|| build_label(i, b, i == self.entry()))
            })
            .collect();

        let mut edge_counter = 0usize;
        let mut edges: Vec<Edge> = Vec::new();

        for (src, block) in self.blocks().enumerate() {
            if !self.is_reachable(src) {
                continue;
            }

            let mut push =
                |edges: &mut Vec<Edge>, dst: usize, color: &'static str, port_order: usize| {
                    if !self.is_reachable(dst) {
                        return;
                    }

                    edge_counter += 1;
                    let is_back = idoms.dominates(src, dst);
                    edges.push(Edge {
                        id: format!("e{edge_counter}"),
                        src,
                        dst,
                        color,
                        is_back,
                        src_port_order: port_order,
                    });
                };

            match block.exit() {
                BlockExit::Jump(t) | BlockExit::Fallthrough(t) => {
                    push(&mut edges, *t, "#2196F3", 0)
                }
                BlockExit::CondJump {
                    then_block,
                    else_block,
                    ..
                } => {
                    // then (green) → order 0 (left), else (red) → order 1 (right)
                    push(&mut edges, *then_block, "#4CAF50", 0);
                    push(&mut edges, *else_block, "#f44336", 1);
                }
                BlockExit::FornPrep {
                    body_block,
                    exit_block,
                    ..
                }
                | BlockExit::FornLoop {
                    body_block,
                    exit_block,
                    ..
                }
                | BlockExit::ForgLoop {
                    body_block,
                    exit_block,
                    ..
                } => {
                    push(&mut edges, *body_block, "#4CAF50", 0);
                    push(&mut edges, *exit_block, "#f44336", 1);
                }
                BlockExit::ForgPrep {
                    body_block,
                    exit_block,
                    ..
                } => {
                    push(&mut edges, *body_block, "#4CAF50", 0);
                    push(&mut edges, *exit_block, "#f44336", 1);
                }
                BlockExit::Return(_) => {}
            }
        }

        let mut out_edges = vec![vec![]; n];
        let mut in_edges = vec![vec![]; n];
        for e in &edges {
            out_edges[e.src].push(e);
            in_edges[e.dst].push(e);
        }
        for oe in &mut out_edges {
            oe.sort_by_key(|e| e.src_port_order);
        }

        let elk_json = build_elk_json(&labels, &edges, &out_edges, &in_edges, &depths, n);
        let label_json = build_label_json(&labels, n);
        let edge_color_json = build_edge_color_json(&edges);

        GraphPayload {
            tag: tag.to_owned(),
            elk_json,
            label_json,
            edge_color_json,
        }
    }
}

pub fn dump_cfgs(cfgs: &[ControlFlowGraph], selected_index: usize, output: PathBuf) {
    let payloads: Vec<_> = cfgs
        .iter()
        .enumerate()
        .map(|(i, cfg)| cfg.graph_payload(&format!("Proto {i}")))
        .collect();

    let selected_index = selected_index.min(payloads.len().saturating_sub(1));
    let title = payloads.get(selected_index).map_or_else(
        || "CFG".to_owned(),
        |payload| format!("CFG: {}", payload.tag),
    );

    let graphs_json = build_graphs_json(&payloads);
    let html = build_html(&graphs_json, selected_index, &title);

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
    include_str!("../../../assets/cfg.html")
        .replace("__GRAPHS_JSON__", &graphs_json.to_string())
        .replace("__SELECTED_INDEX__", &selected_index.to_string())
        .replace("__BASE_TITLE__", &serde_json::to_string(title).unwrap())
}
