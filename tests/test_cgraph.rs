use graphviz_ffi::*;

#[test]
fn test_simple_graph_string_roundtrip() {
    let source = "graph {\n}\n";
    let graph = Graph::from(source.to_string());
    let output = String::from(&graph);
    assert_eq!(source, &output);
}

#[test]
fn test_simple_graph_to_string() {
    let graph = Graph::new(GraphType::StrictDirected);
    let output = String::from(&graph);
    assert_eq!("strict digraph {\n}\n", &output);
}
