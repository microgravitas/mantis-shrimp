use std::path::Path;
use std::ffi::OsStr;

use graphbench::editgraph::EditGraph;
use graphbench::io::*;
use graphbench::graph::VertexSet;

pub fn load_graph(file:&Path) -> Result<EditGraph, String> {
    if !(file.exists() && file.is_file()) {
        return Err(format!("The provided file `{file:?}` does not exist or is a directory."));
    }

    let extension = file.extension().and_then(OsStr::to_str);

    match extension {
        Some("txt") => {
            Ok(EditGraph::from_txt(file.to_str().unwrap()).unwrap())
        }
        Some("gz") => {
            Ok(EditGraph::from_gzipped(file.to_str().unwrap()).unwrap())
        }
        Some(_) => {
            Err(format!("Invalid file `{file:?}`. The supported formats are `.txt.gz` and `.txt`."))
        }        
        None => {
            Err(format!("Invalid file `{file:?}`. The supported formats are `.txt.gz` and `.txt`."))
        }
    }
}