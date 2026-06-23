//! The **view-tree model** — the Rust shape of the deos-js `deos.ui.*` element-tree.
//!
//! `deos-js` builds a *serializable* element-tree (data, NOT gpui) in real
//! SpiderMonkey: `deos.ui.{vstack,row,text,bind,button,input,list,table}`. A button's
//! `onClick` is `{turn, arg}`; a `bind(()=>expr)` is a fine-grained signal binding.
//! That JS object is `JSON.stringify`-ed by the engine and read back into Rust (see
//! [`crate::bridge`]); this module is the Rust mirror it parses into. The renderer
//! ([`crate::render`]) walks this tree into real gpui-component widgets.
//!
//! NOTE on `bind`: `JSON.stringify` drops the closure (`node.read` is a function), so
//! a serialized `bind` node carries only `kind:"bind"`. The renderer re-reads the
//! bound value off the live applet ledger directly (the binding IS `app.get(slot)`),
//! which is the same witnessed read the JS closure made — see [`ViewNode::Bind`].

use serde::Deserialize;

/// A node of the view-tree, mirroring the JS `deos.ui.*` shape exactly.
///
/// The JS shape is `{ kind, props, children? , read? }`. We deserialize via the raw
/// [`RawNode`] (a faithful JSON mirror) and lift it into this typed enum so the
/// renderer matches on real variants.
#[derive(Debug, Clone)]
pub enum ViewNode {
    /// `vstack(...children)` → a vertical column (`v_flex`).
    VStack(Vec<ViewNode>),
    /// `row(...children)` → a horizontal row (`h_flex`).
    Row(Vec<ViewNode>),
    /// `text(s)` → a `Label`.
    Text(String),
    /// `bind(() => expr)` → a signal binding. The closure does not survive
    /// serialization; the renderer re-reads the bound value off the live ledger
    /// (the model slot the JS closure read). `slot` is the model slot to re-read
    /// (the counter shape binds slot 0); `label` is an optional prefix.
    Bind { slot: usize, label: String },
    /// `button(label, aff, arg)` → a `Button` whose onClick fires affordance `turn`
    /// with `arg` (a REAL cap-gated verified turn through the applet).
    Button {
        label: String,
        turn: String,
        arg: i64,
    },
    /// `input(viewKey)` → a text input bound to ephemeral view-state `bind_view`.
    Input { bind_view: String },
    /// `list(items)` → a vertical list of child nodes.
    List(Vec<ViewNode>),
    /// `table(rows)` → a table; each row is itself a node (a `row` of cells).
    Table(Vec<ViewNode>),
}

/// The raw JSON mirror of a `deos.ui.*` node (`{ kind, props, children }`). The
/// engine's `JSON.stringify(tree)` produces exactly this; we then [`RawNode::lift`]
/// it into the typed [`ViewNode`].
#[derive(Debug, Clone, Deserialize)]
pub struct RawNode {
    pub kind: String,
    #[serde(default)]
    pub props: RawProps,
    #[serde(default)]
    pub children: Vec<RawNode>,
}

/// The raw `props` bag — every field optional (a node uses only the ones for its kind).
#[derive(Debug, Clone, Default, Deserialize)]
pub struct RawProps {
    #[serde(default)]
    pub text: Option<String>,
    #[serde(default)]
    pub label: Option<String>,
    #[serde(default)]
    pub on_click: Option<RawOnClick>,
    #[serde(default, rename = "bindView")]
    pub bind_view: Option<String>,
    /// For a `bind` node the renderer needs to know WHICH model slot to re-read.
    /// The JS closure isn't serializable, so the applet author tags the bind node's
    /// props with `slot` (the counter shape uses slot 0). Absent → slot 0.
    #[serde(default)]
    pub slot: Option<usize>,
}

/// `onClick = { turn, arg }` — the affordance a button fires.
#[derive(Debug, Clone, Deserialize)]
pub struct RawOnClick {
    pub turn: String,
    #[serde(default)]
    pub arg: i64,
}

impl RawNode {
    /// Lift a raw JSON node into the typed [`ViewNode`]. An unknown kind renders as a
    /// labelled placeholder text (honest: the renderer shows what it could not map).
    pub fn lift(&self) -> ViewNode {
        let kids = || self.children.iter().map(|c| c.lift()).collect::<Vec<_>>();
        match self.kind.as_str() {
            "vstack" => ViewNode::VStack(kids()),
            "row" => ViewNode::Row(kids()),
            "text" => ViewNode::Text(self.props.text.clone().unwrap_or_default()),
            "bind" => ViewNode::Bind {
                slot: self.props.slot.unwrap_or(0),
                label: self.props.label.clone().unwrap_or_default(),
            },
            "button" => {
                let oc = self.props.on_click.clone().unwrap_or(RawOnClick {
                    turn: String::new(),
                    arg: 0,
                });
                ViewNode::Button {
                    label: self.props.label.clone().unwrap_or_default(),
                    turn: oc.turn,
                    arg: oc.arg,
                }
            }
            "input" => ViewNode::Input {
                bind_view: self.props.bind_view.clone().unwrap_or_default(),
            },
            "list" => ViewNode::List(kids()),
            "table" => ViewNode::Table(kids()),
            other => ViewNode::Text(format!("‹unmapped node: {other}›")),
        }
    }
}

/// Parse the engine's `JSON.stringify(viewTree)` string into a typed [`ViewNode`].
pub fn parse_view_tree(json: &str) -> Result<ViewNode, String> {
    let raw: RawNode = serde_json::from_str(json).map_err(|e| format!("view-tree JSON: {e}"))?;
    Ok(raw.lift())
}
