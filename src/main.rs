#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(unused_imports)]

mod io;
mod nquery;
mod algorithms;
mod setfunc;
mod vecset;
mod skipcombs;

// use std::backtrace::Backtrace;
use std::collections::BTreeSet;
use std::default;
use io::load_graph;
use nquery::*;
use algorithms::*;

use graphbench::editgraph::EditGraph;
use graphbench::graph::*;
use graphbench::io::*;
use graphbench::degengraph::*;
use graphbench::algorithms::lineargraph::LinearGraphAlgorithms;
use itertools::*;

use fxhash::FxHashMap;

use clap::{Parser, ValueEnum};
use std::path::Path;



#[derive(Parser, Debug)]
#[clap(author, version="1.0", about, long_about = None)]
struct Args {
    #[clap(short, long)]
    help: bool,

    /// The statistic to compute
    #[clap(value_enum)]
    statistic:StatisticArg,

    /// The network file
    file:String,    

    ///  (VC only) restrict search of shattered set to these vertices
    shattered_candidates:Option<String>,

    /// (VC only) 
    #[clap(short, long)]
    no_brute_force: bool
}

#[derive(Clone, Debug, ValueEnum)]
enum StatisticArg {
    VC, 
    Ladder,
    Crown,
    Biclique
}

fn main() -> Result<(), &'static str> {
    let args = Args::parse();
    let filename = args.file;

    // Load graph
    let path = Path::new(&filename);
    let mut graph = match load_graph(path) {
        Ok(G) => G,
        Err(msg) => {
            println!("{msg}");
            return Err("Parsing error");
        }
    };

    println!("Loaded graph with n={} and m={}", graph.num_vertices(), graph.num_edges());
    
    graph.remove_loops();
    let graph = DegenGraph::from_graph(&graph);  

    let d = *graph.left_degrees().values().max().unwrap() as usize;
    let logd = (d as f32).log2();    
    println!("Computed degeneracy ordering with d={} (log d = {:.2})", d, logd);

    match args.statistic {
        StatisticArg::VC => {
            println!("Computing VC dimension");
            let mut alg = VCAlgorithm::new(&graph);          

            if let Some(filename) = args.shattered_candidates {
                let cand_set = match VertexSet::from_file(&filename) {
                    Ok(cand_set) => cand_set,
                    Err(error) => {
                        println!("{:?}", error);
                        return Err("Could not parse candidate vertex set");
                    }
                };
                let cand_size = cand_set.len();
                println!("Restricting VC search to {cand_size} vertices contained in `{filename}`");
                alg.set_shatter_candidates(&cand_set);
            }

            if args.no_brute_force {
                println!("Disabled brute force (--no-brute-force was set");
                alg.set_brute_force(false)
            }

            alg.run();            
        },
        StatisticArg::Ladder => {
            println!("Approximating ladder index");
            let mut alg = LadderAlgorithm::new(&graph);
            alg.run();   
        },
        StatisticArg::Crown => {
            println!("Approximating crown size");
            let mut alg = CrownAlgorithm::new(&graph);
            alg.run();               
        },
        StatisticArg::Biclique => {
            println!("Computing biclique size");
            let mut alg = BicliqueAlgorithm::new(&graph);
            alg.run();               
        }        
    }


    Ok(())
}