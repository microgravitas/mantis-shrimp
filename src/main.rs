#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(unused_imports)]
#![allow(warnings)]

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

use graphbench::degengraph::*;
use itertools::*;

use fxhash::FxHashMap;

use clap::{Parser, ValueEnum};
use std::path::Path;



/// Counts 'butterflies' (4-cycles) in sparse bipartite networks.
#[derive(Parser, Debug)]
#[clap(author, version="1.0", about, long_about = None)]
struct Args {
    #[clap(short, long)]
    help: bool,

    /// The network file
    file:String,    
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


    let mut alg = VCAlgorithm::new(&graph);
    alg.run();

    Ok(())
}