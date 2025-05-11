use crate::graph::{EdgeIndex, NodeIndex, UnGraph};
use crate::visit::{VisitMap, Visitable};
use std::cmp::max;
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

pub fn truss_decomposition<N, E: core::fmt::Debug>(
    graph: UnGraph<N, E>,
    h: usize,
) -> HashMap<(NodeIndex, NodeIndex), usize> {
    let mut graph = graph;
    let mut bin = HashMap::<usize, HashSet<(NodeIndex, NodeIndex)>>::new();
    let mut upper_trussness = 2;
    let mut trussness = HashMap::new();
    let mut sup = h_support(&graph, h);
    for (e, sup) in sup.iter() {
        let edge_upper_trussness = sup + 2;
        bin.entry(edge_upper_trussness)
            .or_insert(HashSet::new())
            .insert(*e);
        upper_trussness = max(upper_trussness, edge_upper_trussness);
    }

    for k in 2..=upper_trussness {
        while !bin.get(&k).unwrap_or(&HashSet::new()).is_empty() {
            let uv @ (u, v) = pick(bin.get_mut(&k).unwrap()).unwrap();
            let e = graph.find_edge(u, v).unwrap();
            trussness.insert(uv, k);

            let (u, v) = graph.edge_endpoints(e).unwrap();
            graph.remove_edge(e);
            let u_affected_edges = h_hop_edges_node(&graph, &u, h);
            let v_affected_edges = h_hop_edges_node(&graph, &v, h);

            for _e in u_affected_edges.union(&v_affected_edges).copied() {
                let _uv @ (_u, _v) = graph.edge_endpoints(_e).unwrap();
                let old_edge_upper_trussness = sup.get(&_uv).unwrap() + 2;
                bin.get_mut(&old_edge_upper_trussness).unwrap().remove(&_uv);

                let new_sup = h_support_edge(&graph, _e, h);
                sup.insert(_uv, new_sup);
                bin.entry(max(new_sup + 2, k))
                    .or_insert(HashSet::new())
                    .insert(_uv);
            }
        }
    }

    trussness
}

fn h_hop_neighbors_node<N, E>(
    graph: &UnGraph<N, E>,
    start: &NodeIndex,
    h: usize,
) -> HashSet<NodeIndex> {
    let mut visited = graph.visit_map();
    let mut h_hop_neighbors = HashSet::new();
    let mut bfs_q = VecDeque::new();

    visited.visit(*start);
    bfs_q.push_back((*start, 0));

    while let Some((node, depth)) = bfs_q.pop_front() {
        if depth == h {
            continue;
        }
        for neighbor in graph.neighbors(node) {
            if visited.visit(neighbor) {
                h_hop_neighbors.insert(neighbor);
                bfs_q.push_back((neighbor, depth + 1));
            }
        }
    }

    h_hop_neighbors
}

fn h_hop_neighbors<N, E>(
    graph: &UnGraph<N, E>,
    h: usize,
) -> HashMap<NodeIndex, HashSet<NodeIndex>> {
    graph
        .node_indices()
        .map(|node| (node, h_hop_neighbors_node(graph, &node, h)))
        .collect()
}

fn h_hop_edges_node<N, E>(
    graph: &UnGraph<N, E>,
    start: &NodeIndex,
    h: usize,
) -> HashSet<EdgeIndex> {
    let mut h_hop_edges = HashSet::new();
    let mut bfs_q = VecDeque::new();

    bfs_q.push_back((*start, 0));

    while let Some((node, depth)) = bfs_q.pop_front() {
        if depth == h {
            continue;
        }
        for neighbor in graph.neighbors(node) {
            h_hop_edges.insert(graph.find_edge(node, neighbor).unwrap());
            bfs_q.push_back((neighbor, depth + 1));
        }
    }

    h_hop_edges
}

fn h_support_edge<N, E>(graph: &UnGraph<N, E>, edge: EdgeIndex, h: usize) -> usize {
    let (u, v) = graph.edge_endpoints(edge).unwrap();
    let neighbors_u = h_hop_neighbors_node(graph, &u, h);
    let neighbors_v = h_hop_neighbors_node(graph, &v, h);
    neighbors_u.intersection(&neighbors_v).count()
}

fn h_support<N, E>(graph: &UnGraph<N, E>, h: usize) -> HashMap<(NodeIndex, NodeIndex), usize> {
    let h_neighbors = h_hop_neighbors(graph, h);
    let mut sup_map = HashMap::new();

    for e in graph.raw_edges() {
        let (u, v) = (e.source(), e.target());
        let neighbors_u = h_neighbors.get(&u).unwrap();
        let neighbors_v = h_neighbors.get(&v).unwrap();
        let sup = neighbors_u.intersection(neighbors_v).count();
        sup_map.insert((u, v), sup);
    }

    sup_map
}

fn pick<T>(set: &mut HashSet<T>) -> Option<T>
where
    T: Eq + Hash + Copy,
{
    let item = *set.iter().next()?;
    set.take(&item)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::graph::UnGraph;
    use std::prelude::v1::Vec;

    fn sample_graph() -> UnGraph<u32, ()> {
        UnGraph::<u32, ()>::from_edges(&[
            (1, 2),
            (1, 4),
            (2, 4),
            (2, 5),
            (3, 6),
            (4, 7),
            (5, 6),
            (5, 7),
            (6, 8),
            (7, 8),
            (7, 9),
            (8, 9),
            (8, 11),
            (9, 10),
            (9, 13),
            (10, 11),
            (11, 12),
            (11, 14),
            (12, 14),
            (13, 14),
        ])
    }

    #[test]
    fn should_compute_h_hop_neighbors_node() {
        let g = sample_graph();
        let actual = h_hop_neighbors_node(&g, &NodeIndex::new(1), 2);

        let expected = HashSet::from([
            NodeIndex::new(2),
            NodeIndex::new(4),
            NodeIndex::new(5),
            NodeIndex::new(7),
        ]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn should_compute_h_hop_neighbors() {
        let g = sample_graph();
        let actual = h_hop_neighbors(&g, 2);

        let v_1 = NodeIndex::new(1);
        assert_eq!(
            *actual.get(&v_1).unwrap(),
            HashSet::from([
                NodeIndex::new(2),
                NodeIndex::new(4),
                NodeIndex::new(5),
                NodeIndex::new(7),
            ]),
        );
        let v_2 = NodeIndex::new(2);
        assert_eq!(
            *actual.get(&v_2).unwrap(),
            HashSet::from([
                NodeIndex::new(1),
                NodeIndex::new(4),
                NodeIndex::new(7),
                NodeIndex::new(5),
                NodeIndex::new(6),
            ]),
        );
    }

    #[test]
    fn should_compute_h_hop_edges_node() {
        let g = sample_graph();
        let actual = h_hop_edges_node(&g, &NodeIndex::new(1), 2)
            .iter()
            .filter_map(|e| g.edge_endpoints(*e))
            .collect::<HashSet<_>>();

        let expected = HashSet::from([
            (NodeIndex::new(1), NodeIndex::new(2)),
            (NodeIndex::new(1), NodeIndex::new(4)),
            (NodeIndex::new(2), NodeIndex::new(4)),
            (NodeIndex::new(2), NodeIndex::new(5)),
            (NodeIndex::new(4), NodeIndex::new(7)),
        ]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn should_compute_h_support_edge() {
        let g = sample_graph();
        let actual = h_support_edge(
            &g,
            g.find_edge(NodeIndex::new(3), NodeIndex::new(6)).unwrap(),
            3,
        );

        assert_eq!(actual, 6);
    }

    #[test]
    fn should_compute_h_support() {
        let g = sample_graph();
        let actual = h_support(&g, 2).into_iter().collect::<HashSet<_>>();

        let expected = HashSet::from([
            ((NodeIndex::new(1), NodeIndex::new(2)), 3),
            ((NodeIndex::new(1), NodeIndex::new(4)), 3),
            ((NodeIndex::new(2), NodeIndex::new(4)), 3),
            ((NodeIndex::new(2), NodeIndex::new(5)), 4),
            ((NodeIndex::new(3), NodeIndex::new(6)), 2),
            ((NodeIndex::new(4), NodeIndex::new(7)), 5),
            ((NodeIndex::new(5), NodeIndex::new(6)), 5),
            ((NodeIndex::new(5), NodeIndex::new(7)), 6),
            ((NodeIndex::new(6), NodeIndex::new(8)), 5),
            ((NodeIndex::new(7), NodeIndex::new(8)), 7),
            ((NodeIndex::new(7), NodeIndex::new(9)), 7),
            ((NodeIndex::new(8), NodeIndex::new(9)), 8),
            ((NodeIndex::new(8), NodeIndex::new(11)), 7),
            ((NodeIndex::new(9), NodeIndex::new(10)), 5),
            ((NodeIndex::new(9), NodeIndex::new(13)), 5),
            ((NodeIndex::new(10), NodeIndex::new(11)), 6),
            ((NodeIndex::new(11), NodeIndex::new(12)), 4),
            ((NodeIndex::new(11), NodeIndex::new(14)), 5),
            ((NodeIndex::new(12), NodeIndex::new(14)), 4),
            ((NodeIndex::new(13), NodeIndex::new(14)), 5),
        ]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn should_compute_trussness_1_hop() {
        let g = sample_graph();
        let actual = truss_decomposition(g.clone(), 1);
        let expected = HashSet::from([
            ((NodeIndex::new(1), NodeIndex::new(2)), 3),
            ((NodeIndex::new(1), NodeIndex::new(4)), 3),
            ((NodeIndex::new(2), NodeIndex::new(4)), 3),
            ((NodeIndex::new(2), NodeIndex::new(5)), 2),
            ((NodeIndex::new(3), NodeIndex::new(6)), 2),
            ((NodeIndex::new(4), NodeIndex::new(7)), 2),
            ((NodeIndex::new(5), NodeIndex::new(6)), 2),
            ((NodeIndex::new(5), NodeIndex::new(7)), 2),
            ((NodeIndex::new(6), NodeIndex::new(8)), 2),
            ((NodeIndex::new(7), NodeIndex::new(8)), 3),
            ((NodeIndex::new(7), NodeIndex::new(9)), 3),
            ((NodeIndex::new(8), NodeIndex::new(9)), 3),
            ((NodeIndex::new(8), NodeIndex::new(11)), 2),
            ((NodeIndex::new(9), NodeIndex::new(10)), 2),
            ((NodeIndex::new(9), NodeIndex::new(13)), 2),
            ((NodeIndex::new(10), NodeIndex::new(11)), 2),
            ((NodeIndex::new(11), NodeIndex::new(12)), 3),
            ((NodeIndex::new(11), NodeIndex::new(14)), 3),
            ((NodeIndex::new(12), NodeIndex::new(14)), 3),
            ((NodeIndex::new(13), NodeIndex::new(14)), 2),
        ]);

        let mut actual_sorted: Vec<_> = actual.into_iter().collect();
        let mut expected_sorted: Vec<_> = expected.into_iter().collect();

        actual_sorted.sort();
        expected_sorted.sort();

        assert_eq!(actual_sorted, expected_sorted);
    }
}
