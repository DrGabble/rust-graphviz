use std::ffi::c_void;
use std::ptr::NonNull;

use super::discipline;
use super::raw;

// Noce pdf doc: http://www.graphviz.org/pdf/cgraph.pdf
// Manpage: https://man.archlinux.org/man/cgraph.3.en
// Source: https://gitlab.com/graphviz/graphviz/-/tree/main/lib/cgraph

pub struct Graph {
    inner: NonNull<raw::Agraph_t>,
}

impl Graph {
    pub fn new(graph_type: GraphType) -> Self {
        let label = std::ptr::null_mut();
        let mut string_discipline = discipline::string_io();
        let graph_ptr = unsafe {
            // UNSAFE passing cont as mut (library doesn't mark it as const but doesn't actually mutate)
            // UNSAFE must make sure to free pointer in drop
            raw::agopen(label, graph_type.into(), &mut string_discipline)
        };
        let inner = NonNull::new(graph_ptr).expect("Couldnt create empty graph");
        Self { inner }
    }
}

impl From<String> for Graph {
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

impl<'a> From<&'a Graph> for String {
    fn from(graph: &'a Graph) -> String {
        let mut string = String::new();
        let string_ptr = &mut string as *mut String as *mut c_void;
        let result = unsafe { raw::agwrite(graph.inner.as_ptr(), string_ptr) };
        assert_eq!(result, 0, "Could not write to string");
        string
    }
}

impl Drop for Graph {
    fn drop(&mut self) {
        let result = unsafe { raw::agclose(self.inner.as_ptr()) };
        assert_eq!(result, 0, "Failed to free graph");
    }
}

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
