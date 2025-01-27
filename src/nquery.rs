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

    pub fn query_uncor(&self, X: &Vec<Vertex>, S: &Vec<Vertex>) -> i32 {
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

    fn left_neighbour_set(&self, S: &[Vertex]) -> Vec<Vertex> {
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

    /// Preparse the internal neighbourhood-data structure for queries of size `size`
    /// restricted to vertices in the set `query_candidates`.
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

    /// Prepares the vertex set S for neighbourhood-queries, e.g. for each subset X of S
    /// we obtain the number of vertices in G which have all of X as neighbours an none of S\X.
    fn prepare(&self,  S: &[Vertex]) -> SmallSetFunc {
        let mut S:Vec<u32> = S.iter().cloned().collect();
        S.sort_unstable();
        assert!(S.len() <= self.max_query_size || self.max_query_size == self.degeneracy);

        // Copies R into I on S. At this point, I[X] with X nonempty tells us how many vertices in G exist which
        // a) Are to the right of X in the ordering
        // b) Have all of X as neighbours (but might also have further neighbours in S)
        let mut I = self.R.subfunc(&S); // Copies R into I on S

        // Compute downward Mobius inveres of I. At this point, I[X] with X nonempty tells us how many vertices in G exist which
        // a) Are to the right of X in the ordering
        // b) Have all of X as neighbours and none of S/X
        I.mobius_trans_down();

        // We now insert the correct value for the empty set manually. Note that this
        // has to happend before we apply the 'left correction'.
        let res_sum:i32 = I.values_nonzero().sum();
        I[&vec![]] = self.graph.num_vertices() as i32 - res_sum;

        // Apply left-neighbour correction. Afterwards, I[X] tells us how many vertices in G exist
        // which have all of X as neigbhours and none of S/X
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
        assert_eq!(I.values_nonzero().sum::<i32>(), self.graph.num_vertices() as i32);
        I
    }

    pub fn is_shattered(&self, S: &[Vertex]) -> bool {
        assert!(!S.is_empty());
        
        // Some early-outs since the Mobius inversion is expensive for larger sets.
        if S.len() > 4 {
            // 1. The set S must have at least one apex.
            if self.R[S] == 0 { 
                // S has not 'right' apex, so we search for a 'left' apex. If it exists,
                // it must be in the left neighbourhood of the rightmost vertex of S.
                let rightmost = self.graph.rightmost(S).unwrap();
                let cands = self.graph.left_neighbours(&rightmost);
                let mut found_apex = false;
                for a in cands {
                    let mut is_apex = true;
                    for x in S {
                        if !self.graph.adjacent(&a, x) {
                            is_apex = false;
                            break;
                        }
                    }
                    if is_apex {
                        found_apex = true;
                        break;
                    }
                }

                if !found_apex {
                    return false
                }
            }
        }

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
    use graphbench::{editgraph::EditGraph, graph::MutableGraph, io::*};
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