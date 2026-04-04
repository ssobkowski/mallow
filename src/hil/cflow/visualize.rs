use std::fmt::{Display, Write as _};

use super::graph::{Block, BlockExit, ControlFlowGraph};

const ELK_JS: &str = include_str!("../../../assets/elk.bundled.js");

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
    if matches!(block.exit, BlockExit::Return(_)) {
        header.push_str(" (Exit)");
    }

    let mut lines: Vec<_> = block
        .stmts
        .iter()
        .map(|s| (format!("{}", s.inner), false))
        .collect();

    match &block.exit {
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
        BlockExit::ForgPrep { exprs, .. } => {
            lines.push((format!("for {}", join_display(exprs, ", ")), true))
        }
        BlockExit::ForgLoop { vars, .. } => lines.push((
            format!(
                "forg_loop {}",
                join_display(vars.iter().map(|s| format!("v{}", s.index())), ", ")
            ),
            true,
        )),
        BlockExit::Return(vals) => {
            lines.push((format!("return {}", join_display(vals, ", ")), false))
        }
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

fn dom_depths(idoms: &[Option<usize>], entry: usize) -> Vec<usize> {
    let n = idoms.len();
    let mut depth = vec![usize::MAX; n];
    depth[entry] = 0;

    let mut changed = true;
    while changed {
        changed = false;
        for i in 0..n {
            if depth[i] != usize::MAX {
                continue;
            }
            if let Some(idom) = idoms[i] {
                if depth[idom] != usize::MAX {
                    depth[i] = depth[idom] + 1;
                    changed = true;
                }
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

impl ControlFlowGraph {
    fn is_reachable(&self, block: usize) -> bool {
        block == self.entry_block || !self.predecessors(block).is_empty()
    }

    pub fn to_elk_html(&self, tag: &str) -> String {
        let n = self.blocks.len();

        let depths = dom_depths(&self.immediate_dominators, self.entry_block);
        let labels: Vec<Option<NodeLabel>> = self
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| {
                self.is_reachable(i)
                    .then(|| build_label(i, b, i == self.entry_block))
            })
            .collect();

        let mut edge_counter = 0usize;
        let mut edges: Vec<Edge> = Vec::new();

        for (src, block) in self.blocks.iter().enumerate() {
            if !self.is_reachable(src) {
                continue;
            }

            let mut push =
                |edges: &mut Vec<Edge>, dst: usize, color: &'static str, port_order: usize| {
                    if !self.is_reachable(dst) {
                        return;
                    }

                    edge_counter += 1;
                    let is_back = self.dominates(src, dst);
                    edges.push(Edge {
                        id: format!("e{edge_counter}"),
                        src,
                        dst,
                        color,
                        is_back,
                        src_port_order: port_order,
                    });
                };

            match &block.exit {
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

        build_html(&elk_json, &label_json, &edge_color_json, tag)
    }
}

pub fn dump_cfg(cfg: &ControlFlowGraph, tag: &str) {
    let html = cfg.to_elk_html(tag);
    let path = std::env::temp_dir().join(format!("cfg_{tag}.html"));
    std::fs::write(&path, &html).expect("failed to write cfg html");
    opener::open(&path).expect("failed to open browser");
}

fn build_elk_json(
    labels: &[Option<NodeLabel>],
    edges: &[Edge],
    out_edges: &[Vec<&Edge>],
    in_edges: &[Vec<&Edge>],
    depths: &[usize],
    n: usize,
) -> String {
    let mut s = String::new();

    s.push_str(r#"{"id":"root","layoutOptions":{"#);
    s.push_str(r#""elk.algorithm":"layered","#);
    s.push_str(r#""elk.direction":"DOWN","#);
    s.push_str(r#""elk.spacing.nodeNode":"50","#);
    s.push_str(r#""elk.layered.spacing.nodeNodeBetweenLayers":"60","#);
    s.push_str(r#""elk.edgeRouting":"ORTHOGONAL","#);
    s.push_str(r#""elk.layered.unnecessaryBendpoints":"true","#);
    s.push_str(r#""elk.layered.layeringStrategy":"INTERACTIVE","#);
    s.push_str(r#""elk.layered.crossingMinimization.strategy":"LAYER_SWEEP","#);
    s.push_str(r#""elk.layered.crossingMinimization.greedySwitch.type":"TWO_SIDED","#);
    s.push_str(r#""elk.layered.crossingMinimization.forceNodeModelOrder":"false","#);
    s.push_str(r#""elk.layered.nodePlacement.strategy":"NETWORK_SIMPLEX","#);
    s.push_str(r#""elk.layered.cycleBreaking.strategy":"GREEDY""#);
    s.push_str(r#"},"children":["#);

    let mut first_node = true;
    for i in 0..n {
        let Some(label) = &labels[i] else { continue };
        if !first_node {
            s.push(',');
        }
        first_node = false;

        let (w, h) = node_size(label);
        let y_hint = depths[i] as f64 * LAYER_H_HINT;

        write!(
            s,
            r#"{{"id":"block_{i}","width":{w:.1},"height":{h:.1},"y":{y_hint:.1},"#
        )
        .unwrap();
        s.push_str(r#""properties":{"elk.portConstraints":"FIXED_ORDER"},"ports":["#);

        let mut first_port = true;
        for e in &out_edges[i] {
            if !first_port {
                s.push(',');
            }
            first_port = false;
            write!(s,
                r#"{{"id":"block_{i}_S_{eid}","properties":{{"port.side":"SOUTH","port.index":"{order}"}}}}"#,
                eid = e.id, order = e.src_port_order
            ).unwrap();
        }

        for (pi, e) in in_edges[i].iter().enumerate() {
            if !first_port {
                s.push(',');
            }
            first_port = false;
            write!(s,
                r#"{{"id":"block_{i}_N_{eid}","properties":{{"port.side":"NORTH","port.index":"{order}"}}}}"#,
                eid = e.id, order = pi
            ).unwrap();
        }

        s.push_str("]}");
    }

    s.push_str(r#"],"edges":["#);
    for (i, e) in edges.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        write!(
            s,
            r#"{{"id":"{eid}","sources":["block_{src}_S_{eid}"],"targets":["block_{dst}_N_{eid}"]"#,
            eid = e.id,
            src = e.src,
            dst = e.dst
        )
        .unwrap();
        if e.is_back {
            s.push_str(r#","properties":{"elk.edge.type":"BACKEDGE"}"#);
        }
        s.push('}');
    }
    s.push_str("]}");
    s
}

fn build_label_json(labels: &[Option<NodeLabel>], n: usize) -> String {
    let mut s = String::from('{');
    let mut first = true;
    for i in 0..n {
        let Some(label) = &labels[i] else { continue };
        if !first {
            s.push(',');
        }
        first = false;
        write!(
            s,
            r#""block_{i}":{{"header":{},"lines":["#,
            serde_json::to_string(&label.header).unwrap()
        )
        .unwrap();
        for (li, (text, bold)) in label.lines.iter().enumerate() {
            if li > 0 {
                s.push(',');
            }
            write!(
                s,
                r#"{{"text":{},"bold":{bold}}}"#,
                serde_json::to_string(text).unwrap()
            )
            .unwrap();
        }
        s.push_str("]}");
    }
    s.push('}');
    s
}

fn build_edge_color_json(edges: &[Edge]) -> String {
    let mut s = String::from('{');
    for (i, e) in edges.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        write!(s, r#""{}":"{}""#, e.id, e.color).unwrap();
    }
    s.push('}');
    s
}

fn build_html(elk_json: &str, label_json: &str, edge_colors: &str, title: &str) -> String {
    format!(
        r#"<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <title>CFG: {title}</title>
  <script>{ELK_JS}</script>
  <style>
    body {{ margin: 0; padding: 20px; background: #f5f5f5; }}
    svg  {{ display: block; }}
  </style>
</head>
<body>
<div id="cfg" style="font-family:monospace;color:#888;padding:1rem;">computing layout...</div>
<script>
const C=7.2,LH=16,HH=24,HP=10,VP=8;
const elkGraph={elk_json};
const nodeLabels={label_json};
const edgeColors={edge_colors};
const colorName={{'#2196F3':'blue','#4CAF50':'green','#f44336':'red'}};
const NS='http://www.w3.org/2000/svg';

function el(tag,attrs,...ch){{
  const e=document.createElementNS(NS,tag);
  for(const[k,v]of Object.entries(attrs))e.setAttribute(k,v);
  for(const c of ch)c&&e.appendChild(c);
  return e;
}}
function tx(content,attrs){{
  const t=document.createElementNS(NS,'text');
  for(const[k,v]of Object.entries(attrs))t.setAttribute(k,v);
  t.textContent=content;
  return t;
}}

new ELK().layout(elkGraph).then(layout=>{{
  const M=24;
  let mx=0,my=0;
  layout.children.forEach(n=>{{mx=Math.max(mx,n.x+n.width);my=Math.max(my,n.y+n.height);}});

  const svg=el('svg',{{width:mx+M*2,height:my+M*2,xmlns:NS}});

  // arrowhead markers
  const defs=el('defs',{{}});
  for(const[nm,col]of[['blue','#2196F3'],['green','#4CAF50'],['red','#f44336']]){{
    const mk=el('marker',{{
      id:`arr-${{nm}}`,markerWidth:'8',markerHeight:'6',
      refX:'7',refY:'3',orient:'auto'
    }});
    mk.appendChild(el('path',{{d:'M0,0 L0,6 L8,3 z',fill:col}}));
    defs.appendChild(mk);
  }}
  // dashed marker variants for back edges
  for(const[nm,col]of[['blue','#2196F3'],['green','#4CAF50'],['red','#f44336']]){{
    const mk=el('marker',{{
      id:`arr-dash-${{nm}}`,markerWidth:'8',markerHeight:'6',
      refX:'7',refY:'3',orient:'auto'
    }});
    mk.appendChild(el('path',{{d:'M0,0 L0,6 L8,3 z',fill:col,opacity:'0.6'}}));
    defs.appendChild(mk);
  }}
  svg.appendChild(defs);

  const g=el('g',{{transform:`translate(${{M}},${{M}})`}});

  // edges (behind nodes)
  layout.edges.forEach(edge=>{{
    if(!edge.sections)return;
    const color=edgeColors[edge.id];
    const cn=colorName[color];
    const isBack=edge.properties&&edge.properties['elk.edge.type']==='BACKEDGE';
    edge.sections.forEach(sec=>{{
      const pts=[sec.startPoint,...(sec.bendPoints||[]),sec.endPoint];
      const d='M '+pts.map(p=>`${{p.x}} ${{p.y}}`).join(' L ');
      g.appendChild(el('path',{{
        d, fill:'none', stroke:color,
        'stroke-width':'1.5',
        'stroke-dasharray':isBack?'6,3':'none',
        'opacity':isBack?'0.6':'1',
        'marker-end':`url(#arr-${{isBack?'dash-':''}}${{cn}})`
      }}));
    }});
  }});

  // nodes
  layout.children.forEach(n=>{{
    const data=nodeLabels[n.id];
    const{{x,y,width:w,height:h}}=n;
    g.appendChild(el('rect',{{x,y,width:w,height:h,fill:'white',stroke:'#555','stroke-width':'1'}}));
    g.appendChild(el('rect',{{x,y,width:w,height:HH,fill:'#E0E0E0',stroke:'none'}}));
    g.appendChild(el('line',{{x1:x,y1:y+HH,x2:x+w,y2:y+HH,stroke:'#aaa','stroke-width':'0.5'}}));
    g.appendChild(tx(data.header,{{
      x:x+w/2,y:y+HH/2+4,
      'text-anchor':'middle',
      'font-family':'Courier,monospace','font-size':'12',
      'font-weight':'bold',fill:'#111'
    }}));
    data.lines.forEach((line,i)=>{{
      g.appendChild(tx(line.text,{{
        x:x+HP,y:y+HH+VP+i*LH+12,
        'font-family':'Courier,monospace','font-size':'12',
        'font-weight':line.bold?'bold':'normal',fill:'#111'
      }}));
    }});
  }});

  svg.appendChild(g);
  document.getElementById('cfg').replaceChildren(svg);
}}).catch(err=>{{
  document.getElementById('cfg').textContent='ELK layout error: '+err;
}});
</script>
</body>
</html>"#
    )
}
