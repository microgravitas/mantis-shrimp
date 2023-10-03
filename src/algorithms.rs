use std::collections::BTreeSet;

use graphbench::graph::*;
use graphbench::degengraph::DegenGraph;

use crate::nquery::NQuery;

use itertools::*;
use crate::skipcombs::{SkippableCombinations, SkippableCombinationsIter};

fn binom(n: usize, k: usize) -> usize {
    let mut res = 1;
    for i in 0..k {
        res = (res * (n - i)) / (i + 1);
    }
    res
}

fn generate_degree_profile(k:usize) -> Vec<usize> {
    let mut res = Vec::default();
    for d in (1..=k).rev() {
        for _ in 0..binom(k, d) {
            res.push(d);
        }
    }
    res
}

fn dominates_profile(degA:&Vec<usize>, degB:&Vec<usize>) -> bool {
    if degA.len() < degB.len() {
        return false;
    }

    for (dA,dB) in degA.iter().zip(degB.iter()) {
        if dA < dB {
            return false;
        }
    }

    true
}

pub struct VCAlgorithm<'a> {
    graph: &'a DegenGraph,
    nquery: NQuery<'a>,
    local_lower_bound:VertexMap<u8>,
    local_upper_bound:VertexMap<u8>,
    shatter_candidates:VertexSet,
    cover_candidates:VertexSet,
    vc_dim:usize,
    d: usize,
    logd: f32
}

impl<'a> VCAlgorithm<'a> {
    pub fn new(graph: &'a DegenGraph) -> Self {
        let d = *graph.left_degrees().values().max().unwrap() as usize;
        let logd = (d as f32).log2();    

        let shatter_candidates:VertexSet = graph.vertices().cloned().collect();
        let mut cover_candidates:VertexSet = shatter_candidates.iter().cloned().collect(); 

        let local_lower_bound = VertexMap::default();
        let local_upper_bound = graph.left_degrees().iter().map(|(k,v)| (*k,1 + *v as u8)).collect();

        let vc_dim = 1;
        let mut nquery = NQuery::new(graph);
        VCAlgorithm{ graph, d, logd, shatter_candidates, cover_candidates, nquery, local_lower_bound, local_upper_bound, vc_dim}
    }

    pub fn run(&mut self) {
        let mut improved = true;
        let mut cover_size = 1;

        // Main loop: try to find larger and larger shattered sets
        while improved && self.vc_dim <= self.d+1 {
            improved = false;

            let brute_force_estimate = binom(self.shatter_candidates.len(), self.vc_dim+1);
            let cover_estimate = binom(self.cover_candidates.len(), cover_size) * binom(cover_size * self.d, self.vc_dim+1);

            self.nquery.ensure_size(self.vc_dim+1, &self.shatter_candidates);

            if brute_force_estimate < cover_estimate {
                println!("Brute-force: ({} choose {}) candidates", self.shatter_candidates.len(), self.vc_dim+1 );        
                // Test each subset of size vc_dim+1 whether it is shattered
                let mut it = self.shatter_candidates.iter().combinations_skippable(self.vc_dim+1);
                while let Some(S) = it.next()  {                    
                    let S:Vec<u32> = S.into_iter().cloned().collect(); // TODO: Better way of converting Vec<&u32> to Vec<u32>?
                    
                    if self.nquery.is_shattered(&S) {
                        self.vc_dim += 1;
                        println!("Found shattered set of size {}: {:?}", self.vc_dim, S);
                                          
                        improved = true;
                        break;
                    }


                    // Figure out what prefix of the current set is not shattered
                    // and skip all subsequent combinations with the same prefix.
                    if self.vc_dim+1 > 3 {
                        let mut k = 2;
                        while self.nquery.is_shattered(&S[..k]) && k < self.vc_dim-1 {
                            k += 1;
                        }
                        if k < self.vc_dim-1 {
                            it.skip_prefix(k);
                        }
                    }                         
                }

                if !improved {
                    break; // No further improvement possible
                }
            } else if cover_size == 1 {
                println!("Covering: {} cover candidates", self.cover_candidates.len() );
                'outer: for c in self.cover_candidates.iter() {
                    if self.local_upper_bound[c] as usize <= self.vc_dim {
                        continue;
                    }

                    // Collect candidate set
                    let mut N:VertexSet = VertexSet::default();
                    N.insert(*c);
                    N.extend( self.graph.left_neighbours_slice(c));

                    // Retain only those elements that are witness candidates
                    N.retain(|x| self.shatter_candidates.contains(x) );

                    if N.len() <= self.vc_dim {
                        continue;
                    }

                    // Test each subset of size vc_dim+1 whether it is shattered
                    // println!("  Checking ({} choose {}) subsets for cover {:?}", N.len(), self.vc_dim+1, C);
                    let mut it = N.into_iter().combinations_skippable(self.vc_dim+1);
                    while let Some(S) = it.next() {
                        if self.nquery.is_shattered(&S) {
                            self.vc_dim += 1;
                            println!("Found shattered set of size {}: {:?}", self.vc_dim, S);

                            // Update local lower bound on vc dimension
                            self.local_lower_bound.insert(*c, self.vc_dim as u8);

                            improved = true;
                            break 'outer;
                        }

                        // Figure out what prefix of the current set is not shattered
                        // and skip all subsequent combinations with the same prefix.
                        if self.vc_dim+1 > 3 {
                            let mut k = 2;
                            while self.nquery.is_shattered(&S[..k]) && k < self.vc_dim-1 {
                                k += 1;
                            }
                            if k < self.vc_dim-1 {
                                it.skip_prefix(k);
                            }
                        }                        
                    }

                    // We exhaustively searched this vertex' neighbourhood, so we know
                    // it does not contain shattered sets of size vc_dim+1.
                    self.local_upper_bound.entry(*c).and_modify(|e| *e = std::cmp::min(*e, self.vc_dim as u8));
                }                    
            } else {
                // We proved that if the shattered set has size at least $p:= \ceil{\log d + 1}$, then 
                // there exists a left-cover in which every vertex sees at least a $1 / p$ fraction of the solution.
                // Therefore, we can exclude vertices whose local upper bound is less than $\ceil{(vc_dim + 1) / p}$.
                let p = f32::ceil(self.logd + 1f32) as usize;
                let candidates = if (self.vc_dim+1) >= p {
                    let k = self.vc_dim + 1;
                    let limit = (k / p) as u8 + u8::from( k / p != 0 ); // This is equal to ceil( k / p)
                    self.cover_candidates.iter().filter(|v| self.local_upper_bound[v] >= limit).cloned().collect_vec()
                } else {
                    self.cover_candidates.iter().cloned().collect_vec()
                };


                println!("Covering: ({} choose {}) candidates", self.cover_candidates.len(), cover_size );
                'outer: for C in candidates.into_iter().combinations(cover_size) {
                    let joint_upper_bound:usize = C.iter().map(|u| self.local_upper_bound[u] as usize).sum(); 
                    if joint_upper_bound <= self.vc_dim {
                        continue;
                    }

                    // Collect candidate set
                    let mut N:VertexSet = C.iter().map(|u| *u).collect();
                    for &u in &C {
                        N.extend( self.graph.left_neighbours_slice(&u));
                    }

                    // Retain only those elements that are witness candidates
                    N.retain(|x| self.shatter_candidates.contains(x) );

                    if N.len() <= self.vc_dim {
                        continue;
                    }

                    // Test each subset of size vc_dim+1 whether it is shattered
                    // println!("  Checking ({} choose {}) subsets for cover {:?}", N.len(), self.vc_dim+1, C);
                    let mut it = N.into_iter().combinations_skippable(self.vc_dim+1);
                    while let Some(S) = it.next() {
                        if self.nquery.is_shattered(&S) {
                            self.vc_dim += 1;
                            println!("Found shattered set of size {}: {:?}", self.vc_dim, S);
                            improved = true;
                            break 'outer;
                        }

                        // Figure out what prefix of the current set is not shattered
                        // and skip all subsequent combinations with the same prefix.
                        if self.vc_dim+1 > 3 {
                            let mut k = 2;
                            while self.nquery.is_shattered(&S[..k]) && k < self.vc_dim-1 {
                                k += 1;
                            }
                            if k < self.vc_dim-1 {
                                it.skip_prefix(k);
                            }
                        }      
                    }
                }                
            } 

            if improved {
                println!("Found larger set, recomputing ");
                self.recompute_candidates();

                if self.shatter_candidates.len() <= self.vc_dim {
                    break;  // No further improvement possible
                }
            } else if cover_size < self.logd.ceil() as usize {
                improved = true;
                cover_size += 1;
                println!("No improvement, increasing cover size to {cover_size}");
            }
        }

        println!("Largest shattered set: {:?}", self.vc_dim);
    }

    fn recompute_candidates(&mut self) {
        println!("  > Recomputing candidates");
        let degree_profile = generate_degree_profile(self.vc_dim+1);
        let n = self.graph.num_vertices();
        println!("  > Degree profile is {degree_profile:?}");
        self.shatter_candidates.retain(|v| {
            let degrees = self.nquery.degree_profile(v);
            dominates_profile(&degrees, &degree_profile)
        });

        println!("  > Found {} out of {n} as candidates for {}-shattered set", self.shatter_candidates.len(), self.vc_dim);

        self.cover_candidates.retain(|v| {
            let mut covers = false;

            let mut num_cands = self.graph.left_neighbours_slice(v).iter()
                .filter(|u| self.shatter_candidates.contains(u)).count();
            num_cands += self.shatter_candidates.contains(v) as usize;

            // Update local upper bound
            self.local_upper_bound.entry(*v).and_modify(|e| *e = std::cmp::min(*e, num_cands as u8));

            // v only remains a cover candidate if it sees at least one 
            // candiate vertex
            num_cands > 0
        });

        println!("  > Found {} out of {n} as cover candidates for {}-shattered set", self.cover_candidates.len(), self.vc_dim);
    }
}   

