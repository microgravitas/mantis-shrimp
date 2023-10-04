use graphbench::graph::*;
use graphbench::degengraph::DegenGraph;

use std::collections::BTreeSet;
use fxhash::FxHashMap;

use itertools::*;

use crate::{setfunc::{SetFunc, SmallSetFunc}, vecset::{difference, union, intersection}};

pub struct NQuery<'a> {
    R:SetFunc,
    max_query_size: usize,
    degeneracy: usize,
    graph:&'a DegenGraph
}

impl<'a> NQuery<'a> {
    pub fn new(graph:&'a DegenGraph) -> Self {  
        let mut R = SetFunc::default();
        let degeneracy = *graph.left_degrees().values().max().unwrap() as usize;

        NQuery { R, graph, max_query_size: 0, degeneracy }
    }

    pub fn query_R(&self, X: &Vec<Vertex>) -> i32 {
        if X.is_empty() {
            return 0
        }

        let res = self.R[X];
        res
    }

    fn query_uncor(&self, X: &Vec<Vertex>, S: &Vec<Vertex>) -> i32 {
        if X.is_empty() {
            return 0
        }

        let S_minus_X:Vec<_> = difference(S, X);
        let mut res:i32 = 0;

        for subset in S_minus_X.into_iter().powerset() {
            let Y = union(X, &subset);

            if subset.len() % 2 == 0 {
                res += self.R[&Y];
            } else {
                res -= self.R[&Y];
            }
        }
        res
    }

    fn left_neighbour_set(&self, S: &Vec<Vertex>) -> Vec<Vertex> {
        let mut res: BTreeSet<Vertex> = BTreeSet::default();

        for u in S {
            let l_neigh = self.graph.left_neighbours(u);
            res.extend(l_neigh.into_iter())
        }
    
        res.into_iter().collect()
    }

    pub fn ensure_size(&mut self, size:usize) {
        if size <= self.max_query_size || self.max_query_size == self.degeneracy {
            return;
        }

        println!("Recomputing R for query size {size}...");

        for s in (self.max_query_size+1)..=size {
            for u in self.graph.vertices() {
                let mut N = self.graph.left_neighbours(u);
                N.sort_unstable();
    
                for subset in N.into_iter().combinations(s) {
                    self.R[&subset] += 1;
                }
            }
        }

        self.max_query_size = size;
    }

    pub fn ensure_size_exact(&mut self, size:usize) {
        if size <= self.max_query_size || self.max_query_size == self.degeneracy {
            return;
        } 

        println!("Recomputing R for exact query size {size}...");

        for u in self.graph.vertices() {
            let mut N = self.graph.left_neighbours(u);
            N.sort_unstable();
    
            for subset in N.into_iter().combinations(size) {
                self.R[&subset] += 1;
            }
        }
    }

    pub fn ensure_size_restricted(&mut self, size:usize, query_candidates:&VertexSet) {
        if size <= self.max_query_size || self.max_query_size == self.degeneracy {
            return;
        }

        println!("Recomputing R for query size {size}...");

        for s in (self.max_query_size+1)..=size {
            for u in self.graph.vertices() {
                let mut N = self.graph.left_neighbours(u);
                N.retain(|x| query_candidates.contains(x));
                N.sort_unstable();
    
                for subset in N.into_iter().combinations(s) {
                    self.R[&subset] += 1;
                }
            }
        }

        self.max_query_size = size;
    }

    fn prepare(&self,  S: &[Vertex]) -> SmallSetFunc {
        let mut S:Vec<u32> = S.iter().cloned().collect();
        S.sort_unstable();
        assert!(S.len() <= self.max_query_size || self.max_query_size == self.degeneracy);

        let mut I = self.R.subfunc(&S); // Copies R into I on S
        I.mobius_trans_down();

        let res_sum:i32 = I.values_nonzero().sum();

        // Insert correct value for the empty set manually
        I[&vec![]] = self.graph.num_vertices() as i32 - res_sum;

        // Left-neighbour correction
        let left_neighs = self.left_neighbour_set(&S);

        for v in left_neighs {   
            // Collect v's left and right neighbourhoods 
            let N: Vec<Vertex> = self.graph.neighbours(&v).cloned().sorted_unstable().collect();
            let N_left: Vec<Vertex> = self.graph.left_neighbours(&v).into_iter().sorted_unstable().collect();
            let N_right = difference(&N, &N_left);
            
            // Take the intersections of the neighbourhoods with S
            let N_left = intersection(&S, &N_left);
            let N_right = intersection(&S, &N_right);

            let N = union(&N_left, &N_right);

            assert!(I[&N_left] > 0);
            I[&N_left] -= 1;
            I[&N] += 1;
        }
        I
    }

    pub fn is_shattered(&self, S: &[Vertex]) -> bool {
        let I = self.prepare(S);
        if I.count_nonzero() != 2_usize.pow(S.len() as u32) {
            return false
        }
        true
    }

    pub fn contains_ladder(&self, S: &[Vertex]) -> bool {
        let I = self.prepare(S);
        I.is_ladder()
    }

    pub fn contains_crown(&self, S: &[Vertex]) -> bool {
        let I = self.prepare(S);
        I.contains_crown()
    }

    pub fn contains_biclique(&self, S: &[Vertex]) -> bool {
        let I = self.prepare(S);
        I.contains_biclique()
    }    

    pub fn degree_profile(&self, v:&Vertex) -> Vec<usize> {
        let mut degrees = Vec::default();
        for u in self.graph.neighbours(v) {
            degrees.push(self.graph.degree(u) as usize);
        }
        degrees.sort_unstable();
        degrees.reverse();
        degrees
    }
}


#[cfg(test)]
mod  tests {
    use super::*;    
    use graphbench::{editgraph::EditGraph, graph::MutableGraph};
    use rand::prelude::*;
    use std::collections::BTreeSet;

    #[test]
    fn shattered_test1 () {
        let mut graph = EditGraph::from_txt("test1_shattered.txt").expect("File not found.");
        let graph = DegenGraph::with_ordering(&graph, vec![1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16].iter());  

        let mut nquery = NQuery::new(&graph);
        nquery.ensure_size_restricted(4, &graph.vertices().cloned().collect());

        let sh_set = vec![1, 2, 3, 4];
        let result = nquery.is_shattered(&sh_set);
        assert_eq!(result, true);
    }

    #[test]
    fn shattered_test2 () {
        let mut graph = EditGraph::from_txt("test1_shattered.txt").expect("File not found.");
        let graph = DegenGraph::from_graph(&graph);  

        let mut nquery = NQuery::new(&graph);
        nquery.ensure_size_restricted(4, &graph.vertices().cloned().collect());

        let unsh_set = vec![1, 2, 3, 16];
        let result = nquery.is_shattered(&unsh_set);
        assert_eq!(result, false);
    }

    #[test]
    fn shattered_test_small() {
        let mut rng = rand::thread_rng();
        for k in 2..=5 {
            let mut G = EditGraph::new();
            G.add_vertices((0..k).into_iter());
            
            let mut v = k;
            let mut order = (0..k).into_iter().collect_vec();
            for set in (0..k).into_iter().powerset() {
                G.add_vertex(&v);
                for u in set {
                    G.add_edge(&u, &v);
                }
                order.push(v);
                v += 1;
            }

            let D = DegenGraph::with_ordering(&G, order.iter());
            let mut nquery = NQuery::new(&D);
            nquery.ensure_size_restricted(k as usize, &D.vertices().cloned().collect());

            let result = nquery.is_shattered(&(0..k).into_iter().collect_vec());
            assert_eq!(result, true);

            order.shuffle(&mut rng);
            let D = DegenGraph::with_ordering(&G, order.iter());
            let mut nquery = NQuery::new(&D);
            nquery.ensure_size_restricted(k as usize, &D.vertices().cloned().collect());

            let result = nquery.is_shattered(&(0..k).into_iter().collect_vec());
            assert_eq!(result, true);            
        }
    }

    #[test]
    fn bad() {
        let k = 3;
        let mut G = EditGraph::new();
        G.add_vertices((0..k).into_iter());
        
        let mut v = k;
        for set in (0..k).into_iter().powerset() {
            println!("{v} -> {set:?}");
            G.add_vertex(&v);
            for u in set {
                G.add_edge(&u, &v);
            }
            v += 1;
        }

        let order = vec![1,3,9,0,6,7,10,2,5,4,8];
        let D = DegenGraph::with_ordering(&G, order.iter());
        let mut nquery = NQuery::new(&D);
        nquery.ensure_size_restricted(k as usize, &D.vertices().cloned().collect());

        let result = nquery.is_shattered(&(0..k).into_iter().collect_vec());
        assert_eq!(result, true);
    }    
}