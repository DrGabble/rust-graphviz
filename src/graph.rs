use std::ffi::{c_void, CStr};
use std::marker::PhantomData;
use std::ptr::NonNull;

use super::discipline;
use super::raw;

// Nice pdf doc: http://www.graphviz.org/pdf/cgraph.pdf
// Manpage: https://man.archlinux.org/man/cgraph.3.en
// Source: https://gitlab.com/graphviz/graphviz/-/tree/main/lib/cgraph

///
/// Root graph
///
pub struct Root {
    // NOTE this IS an owning pointer
    inner: NonNull<raw::Agraph_t>,
}

impl Root {
    pub fn new(graph_type: GraphType) -> Self {
        let name = std::ptr::null_mut();
        let mut string_discipline = discipline::string_io();
        let graph_ptr = unsafe {
            // UNSAFE passing cont as mut (library doesn't mark it as const but doesn't actually mutate)
            // UNSAFE must make sure to free pointer in drop
            raw::agopen(name, graph_type.into(), &mut string_discipline)
        };
        let inner = NonNull::new(graph_ptr).expect("Couldnt create empty graph");
        Self { inner }
    }
}

impl From<String> for Root {
    fn from(string: String) -> Self {
        let c_string = to_c_str!(string);
        let graph_ptr = unsafe { raw::agmemread(c_string.as_ptr()) };
        let mut inner = NonNull::new(graph_ptr).expect("Couldnt create graph from string");
        // UNSAFE set pointer to string writing io disciplines for Into<String>
        let callbacks = unsafe { &mut *inner.as_mut().clos };
        callbacks.disc.io = discipline::string_io().io;
        Self { inner }
    }
}

impl<'r> GraphInner<'r, 'r> for Root {
    fn inner_mut(&self) -> *mut raw::Agraph_t {
        self.inner.as_ptr()
    }

    fn root(&'r self) -> &'r Root {
        self
    }
}

impl<'r> Graph<'r, 'r> for Root {}

impl Root {
    pub fn is_directed(&self) -> bool {
        unsafe { raw::agisdirected(self.inner_mut()) != 0 }
    }

    pub fn is_strict(&self) -> bool {
        unsafe { raw::agisstrict(self.inner_mut()) != 0 }
    }
}

impl<'a> From<&'a Root> for String {
    fn from(graph: &'a Root) -> String {
        let mut string = String::new();
        let string_ptr = &mut string as *mut String as *mut c_void;
        // UNSAFE io discipline MUST be set to `disipline::string_write` in constructor of Graph
        let result = unsafe { raw::agwrite(graph.inner_mut(), string_ptr) };
        assert_eq!(result, 0, "Could not write to string");
        string
    }
}

impl Drop for Root {
    fn drop(&mut self) {
        let result = unsafe { raw::agclose(self.inner_mut()) };
        assert_eq!(result, 0, "Failed to free graph");
    }
}

///
/// Graph Type specifies if the graph is directed or strict.
///
pub enum GraphType {
    Directed,
    StrictDirected,
    Undirected,
    StrictUndirected,
}

impl From<GraphType> for raw::Agdesc_t {
    fn from(graph_type: GraphType) -> raw::Agdesc_t {
        unsafe {
            // UNSAFE using mutable statics here (but in a const fashion)
            match graph_type {
                GraphType::Directed => raw::Agdirected,
                GraphType::StrictDirected => raw::Agstrictdirected,
                GraphType::Undirected => raw::Agundirected,
                GraphType::StrictUndirected => raw::Agstrictundirected,
            }
        }
    }
}

///
/// Handle to a Subgraph
///
pub struct Subgraph<'r> {
    // NOTE this is NOT an owning pointer
    inner: NonNull<raw::Agraph_t>,
    // all data is actual stored in Root, so this ensures it outlives the Node
    root: &'r Root,
}

impl<'s, 'r: 's> GraphInner<'s, 'r> for Subgraph<'r> {
    fn inner_mut(&self) -> *mut raw::Agraph_t {
        self.inner.as_ptr()
    }

    fn root(&'s self) -> &'r Root {
        self.root
    }
}

impl<'s, 'r: 's> Graph<'s, 'r> for Subgraph<'r> {}

// Trait to enable Graph trait: seperate so that iterators can be generic over it
// (cant be generic over Graph because it has generic functions)
//
// The two lifetimes is for some shennagians so that Root can return itself with root(),
// while Subgraph can return a reference to another Root. The end result is that Node<'r>
// can outlive its parent Subgraph but NOT its arch-parent Root.
//
// TODO could be better named
pub trait GraphInner<'s, 'r: 's> {
    fn inner_mut(&self) -> *mut raw::Agraph_t;
    fn root(&'s self) -> &'r Root;
}

///
/// Traits for functions which are generic over Root and Subgraph
///
pub trait Graph<'s, 'r: 's>: GraphInner<'s, 'r> + Sized {
    /// Adds a new subgraph with the given name if it doesn't already exist. If it does already exist,
    /// will just return a handle to that already existing subgraph.
    fn add_subgraph<N: Into<Vec<u8>>>(&'s self, name: N) -> Subgraph<'r> {
        let name = to_c_str!(name);
        let name_ptr = name.as_ptr() as *mut i8;
        // UNSAFE name_ptr must be valid for function call, hence name as seperate variable to keep it alive
        // UNSAFE passing cont as mut (library doesn't mark it as const but doesn't actually mutate)
        let subgraph_ptr = unsafe { raw::agsubg(self.inner_mut(), name_ptr, true as i32) };
        let inner = NonNull::new(subgraph_ptr).expect("Couldnt create subgraph");
        Subgraph {
            inner,
            root: self.root(),
        }
    }

    /// Returns a handle to an already existing subgraph if it exists, else returns `None`.
    fn get_subgraph<N: Into<Vec<u8>>>(&'s self, name: N) -> Option<Subgraph<'r>> {
        let name = to_c_str!(name);
        let name_ptr = name.as_ptr() as *mut i8;
        // UNSAFE name_ptr must be valid for function call, hence name as seperate variable to keep it alive
        // UNSAFE passing cont as mut (library doesn't mark it as const but doesn't actually mutate)
        let subgraph_ptr = unsafe { raw::agsubg(self.inner_mut(), name_ptr, false as i32) };
        NonNull::new(subgraph_ptr).map(|inner| Subgraph {
            inner,
            root: self.root(),
        })
    }

    /// Adds a new anonymous node with with a generated name, and returns a handle to it.
    fn add_node_auto(&self) -> Node<'_> {
        let name = std::ptr::null_mut();
        let node_ptr = unsafe { raw::agnode(self.inner_mut(), name, true as i32) };
        let inner = NonNull::new(node_ptr).expect("Couldnt create anonymous node");
        Node {
            inner,
            root: PhantomData,
        }
    }

    /// Adds a new node with the given name if it doesn't already exist. If it does already exist,
    /// will just return a handle to that already existing node.
    fn add_node_named<N: Into<Vec<u8>>>(&self, name: N) -> Node<'r> {
        let name = to_c_str!(name);
        // UNSAFE name_ptr must be valid for function call, hence name as seperate variable to keep it alive
        // UNSAFE passing cont as mut (library doesn't mark it as const but doesn't actually mutate)
        let name_ptr = name.as_ptr() as *mut i8;
        let node_ptr = unsafe { raw::agnode(self.inner_mut(), name_ptr, true as i32) };
        let inner = NonNull::new(node_ptr).expect("Could not create named node");
        Node {
            inner,
            root: PhantomData,
        }
    }

    /// Returns a handle to an already existing node if it exists, else returns `None`.
    fn get_node<N: Into<Vec<u8>>>(&self, name: N) -> Option<Node<'r>> {
        let name = to_c_str!(name);
        // UNSAFE name_ptr must be valid for function call, hence name as seperate variable to keep it alive
        // UNSAFE passing cont as mut (library doesn't mark it as const but doesn't actually mutate)
        let name_ptr = name.as_ptr() as *mut i8;
        let node_ptr = unsafe { raw::agnode(self.inner_mut(), name_ptr, false as i32) };
        NonNull::new(node_ptr).map(|inner| Node {
            inner,
            root: PhantomData,
        })
    }

    /// Adds a new anonymous edge with with a generated name, and returns a handle to it.
    /// (In an undirected graph the order of the Nodes is not important).
    fn add_edge_auto(&self, head: Node, tail: Node) -> Edge<'r> {
        let head = head.inner.as_ptr();
        let tail = tail.inner.as_ptr();
        let name = std::ptr::null_mut();
        let edge_ptr = unsafe { raw::agedge(self.inner_mut(), head, tail, name, true as i32) };
        let inner = NonNull::new(edge_ptr).expect("Couldnt create anonymous edge");
        Edge {
            inner,
            root: PhantomData,
        }
    }

    /// Adds a new edge with the given name between these nodes if it doesn't already exist.
    /// If it does already exist, will just return a handle to that already existing edge.
    /// (In an undirected graph the order of the Nodes is not important).
    fn add_edge_named<N: Into<Vec<u8>>>(&self, head: Node, tail: Node, name: N) -> Edge<'r> {
        let head = head.inner.as_ptr();
        let tail = tail.inner.as_ptr();
        let name = to_c_str!(name);
        // UNSAFE name_ptr must be valid for function call, hence name as seperate variable to keep it alive
        // UNSAFE passing cont as mut (library doesn't mark it as const but doesn't actually mutate)
        let name_ptr = name.as_ptr() as *mut i8;
        let node_ptr = unsafe { raw::agedge(self.inner_mut(), head, tail, name_ptr, true as i32) };
        let inner = NonNull::new(node_ptr).expect("Could not create named edge");
        Edge {
            inner,
            root: PhantomData,
        }
    }

    /// Returns a handle to an already existing edge between these nodes if it exists, else returns `None`.
    /// (In an undirected graph the order of the Nodes is not important).
    fn get_edge<N: Into<Vec<u8>>>(&self, head: Node, tail: Node, name: N) -> Option<Edge<'r>> {
        let head = head.inner.as_ptr();
        let tail = tail.inner.as_ptr();
        let name = to_c_str!(name);
        // UNSAFE name_ptr must be valid for function call, hence name as seperate variable to keep it alive
        // UNSAFE passing cont as mut (library doesn't mark it as const but doesn't actually mutate)
        let name_ptr = name.as_ptr() as *mut i8;
        let node_ptr = unsafe { raw::agedge(self.inner_mut(), head, tail, name_ptr, false as i32) };
        NonNull::new(node_ptr).map(|inner| Edge {
            inner,
            root: PhantomData,
        })
    }

    fn nodes(&'s self) -> NodeIter<'r> {
        NodeIter::new(self.root())
    }

    fn edges(&'s self, node: Node<'r>) -> EdgeIter<'r> {
        EdgeIter::new(self.root(), node)
    }
}

///
/// Node
///
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Node<'r> {
    // NOTE: this is NOT an owning pointer
    inner: NonNull<raw::Agnode_t>,
    // all data is actual stored in Root, so this ensures it outlives the Node
    root: PhantomData<&'r Root>,
}

impl<'r> Node<'r> {
    pub fn name(&self) -> &str {
        let node_ptr = self.inner.as_ptr() as *mut c_void;
        let string_ptr = unsafe { raw::agnameof(node_ptr) };
        assert!(!string_ptr.is_null(), "Couldnt get name of node");
        let c_string = unsafe { CStr::from_ptr(string_ptr) };
        c_string.to_str().unwrap()
    }
}

///
/// Iterator for traversing all Nodes in a Graph
///
pub struct NodeIter<'r> {
    root: &'r Root,
    next_node: *mut raw::Agnode_t,
}

impl<'r> NodeIter<'r> {
    fn new(root: &'r Root) -> Self {
        let next_node = unsafe { raw::agfstnode(root.inner_mut()) };
        Self { root, next_node }
    }
}

impl<'r> Iterator for NodeIter<'r> {
    type Item = Node<'r>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(inner) = NonNull::new(self.next_node) {
            self.next_node = unsafe { raw::agnxtnode(self.root.inner_mut(), self.next_node) };
            Some(Node {
                inner,
                root: PhantomData,
            })
        } else {
            None
        }
    }
}

///
/// Edge
///
#[derive(Copy, Clone)]
pub struct Edge<'r> {
    // NOTE: this is NOT an owning pointer
    inner: NonNull<raw::Agedge_t>,
    // all data is actual stored in Root, so this ensures it outlives the Edge
    root: PhantomData<&'r Root>,
}

impl<'r> Edge<'r> {
    pub fn name(&self) -> &str {
        let edge_ptr = self.inner.as_ptr() as *mut c_void;
        let string_ptr = unsafe { raw::agnameof(edge_ptr) };
        assert!(!string_ptr.is_null(), "Couldnt get name of edge");
        let c_string = unsafe { CStr::from_ptr(string_ptr) };
        c_string.to_str().unwrap()
    }
}

///
/// Iterator for traversing the Edges of a Node
///
pub struct EdgeIter<'r> {
    root: &'r Root,
    node: Node<'r>,
    next_edge: *mut raw::Agedge_t,
}

impl<'r> EdgeIter<'r> {
    fn new(root: &'r Root, node: Node<'r>) -> Self {
        let next_edge = unsafe { raw::agfstedge(root.inner_mut(), node.inner.as_ptr()) };
        Self {
            root,
            node,
            next_edge,
        }
    }
}

impl<'r> Iterator for EdgeIter<'r> {
    type Item = Edge<'r>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(inner) = NonNull::new(self.next_edge) {
            self.next_edge = unsafe {
                raw::agnxtedge(
                    self.root.inner_mut(),
                    self.next_edge,
                    self.node.inner.as_ptr(),
                )
            };
            Some(Edge {
                inner,
                root: PhantomData,
            })
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // non-deterministic tabs for some reason...
    // also remove newlines for conciseness of tests
    fn to_output(graph: &Root) -> String {
        String::from(graph).replace("\n", "").replace("\t", "")
    }

    #[test]
    fn test_simple_graph_string_roundtrip() {
        let source = "graph {}";
        let graph = Root::from(source.to_string());
        assert_eq!(source, &to_output(&graph));
        assert!(!graph.is_directed());
        assert!(!graph.is_strict());
    }

    #[test]
    fn test_simple_graph_to_string() {
        let graph = Root::new(GraphType::StrictDirected);
        assert_eq!("strict digraph {}", &to_output(&graph));
        assert!(graph.is_directed());
        assert!(graph.is_strict());
    }

    #[test]
    fn test_adding_named_nodes() {
        let graph = Root::new(GraphType::Undirected);
        assert!(graph.get_node("bob").is_none());
        let node = graph.add_node_named("bob");
        assert_eq!(node.name(), "bob");
        assert!(graph.get_node("bob").is_some());
        assert_eq!("graph {bob;}", &to_output(&graph));
    }

    #[test]
    fn test_subgraphs() {
        let graph = Root::new(GraphType::Undirected);
        assert!(graph.get_subgraph("alpha").is_none());
        assert!(graph.get_subgraph("beta").is_none());

        let subgraph = graph.add_subgraph("alpha");
        assert!(graph.get_subgraph("alpha").is_some());
        assert!(graph.get_subgraph("beta").is_none());
        assert!(subgraph.get_subgraph("alpha").is_none());
        assert!(subgraph.get_subgraph("beta").is_none());

        let subsubgraph = subgraph.add_subgraph("beta");
        subsubgraph.add_node_named("node");
        assert_eq!(
            "graph {subgraph alpha {subgraph beta {\"node\";}}}",
            &to_output(&graph)
        );
    }

    #[test]
    fn test_edges() {
        let graph = Root::new(GraphType::Undirected);
        let head = graph.add_node_named("head");
        let tail = graph.add_node_named("tail");
        graph.add_edge_named(head, tail, "edge");
        assert_eq!("graph {head -- tail[key=\"edge\"];}", to_output(&graph));
    }

    #[test]
    fn test_node_and_edge_iterator() {
        let graph = Root::new(GraphType::Directed);
        let sub = graph.add_subgraph("sub");

        let alpha = sub.add_node_named("alpha");
        let beta = sub.add_node_named("beta");
        let gamma = sub.add_node_named("gamma");
        let mut nodes = graph.nodes();
        assert_eq!(nodes.next().unwrap().name(), "alpha");
        assert_eq!(nodes.next().unwrap().name(), "beta");
        assert_eq!(nodes.next().unwrap().name(), "gamma");

        sub.add_edge_named(alpha, beta, "one");
        sub.add_edge_named(beta, alpha, "two");
        sub.add_edge_named(alpha, gamma, "three");
        let mut edges = graph.edges(alpha);
        assert_eq!(edges.next().unwrap().name(), "one");
        assert_eq!(edges.next().unwrap().name(), "three");
        assert_eq!(edges.next().unwrap().name(), "two");
    }
}
