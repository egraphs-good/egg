// #![allow(non_upper_case_globals)]
// #![allow(non_camel_case_types)]
// #![allow(non_snake_case)]

// include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
//
// use rand::prelude::*;
// use root::taso::*;

use egg::*;

define_language! {
    pub enum Mdl {
        "input"     = Inpt([Id; 2]),
        "ewadd"     = Ewadd([Id; 2]),
        "ewmul"     = Ewmul([Id; 2]),
        "smul"      = Smul([Id; 2]),
        "transpose" = Transpose(Id),
        "matmul"    = Matmul([Id; 2]),
        "conv2d"    = Conv2d([Id; 6]),
        "enlarge"   = Enlarge([Id; 3]),
        "relu"      = Relu(Id),
        "poolavg"   = Poolavg([Id; 6]),
        "poolmax"   = Poolmax([Id; 6]),
        "concat"    = Concat([Id; 3]),
        "split_0"   = Split0([Id; 2]),
        "split_1"   = Split1([Id; 2]),
        "Cpool"     = Cpool([Id; 2]),
        "Iconv"     = Iconv([Id; 2]),
        // NOTE refer to TASO for the const values
        // Anone = 0
        // Arelu = 2
        // Psame = 0
        "Imatmul"   = Imatmul,
        "Iewmul"    = Iewmul,
        Num(i32),
        Var(Symbol),
    }
}

//pub struct TensorAnalysis {
//  graph: std::cell::RefCell<Box<Graph>>
//}
//
//impl Default for TensorAnalysis {
//  fn default() -> Self {
//    unsafe {
//      // NOTE Box heap-allocates, otherwise any pointer from
//      // C++ may be dangling
//      let mut graph = Box::new(Graph::new());
//      Graph_Graph(&mut *graph);
//      TensorAnalysis { graph: std::cell::RefCell::new(graph) }
//    }
//  }
//}
//
//#[derive(Debug)]
//pub struct Tnsr {
//  cost: f32,
//  meta: TensorHandle,
//}
//
//impl Analysis<Mdl> for TensorAnalysis {
//  type Data = Tnsr;
//
//  fn merge(&self, to: &mut Self::Data, from: Self::Data) -> bool {
//    if to.cost > from.cost {
//      *to = from;
//      true
//    } else { false }
//  }
//
//  fn make(egraph: &EGraph<Mdl, Self>, enode: &Mdl) -> Self::Data {
//    let x = |i: &Id| &egraph[*i].data;
//    let mut g = egraph.analysis.graph.borrow_mut();
//    match enode {
//      // Mdl::Matmul([a, b]) => {
//      //     let t_a = x(a).meta;
//      //     let t_b = x(b).meta;
//
//      //     unsafe { // very unsafe sketchy
//      //       let mm = g.matmul(t_a, t_b, ActiMode_AC_MODE_NONE);
//      //       Tnsr {cost : (*(*mm).op.ptr).runtime, meta : mm}
//      //     }
//      //   },
//      // Mdl::Relu(a) => {
//      //     let t_a = x(a).meta;
//
//      //     unsafe { // very unsafe sketchy
//      //       let relu = g.relu(t_a, true);
//      //       Tnsr {cost : (*(*relu).op.ptr).runtime, meta : relu}
//      //     }
//      //   },
//      // HACK this is so to get an example working
//      Mdl::Inpt([a, b]) => {
//          // let t_a = x(a).meta;
//          // TODO deal with non tensors e.g. scalars
//
//          unsafe { // very unsafe sketchy
//            // NOTE all this just to pass ownership
//            // to C++, not sure if necessary
//            let mut dims = vec![64, 1024];
//            dims.shrink_to_fit();
//            assert!(dims.len() == dims.capacity());
//            let ptr = dims.as_mut_ptr();
//            std::mem::forget(ptr);
//
//            let inp = g.new_input(2, ptr);
//            Tnsr {cost : 0.0, meta : inp}
//          }
//        },
//      //Mdl::Concat([a, b, c]) => {
//      //    // let t_a = x(a).meta;
//      //    let t_b = x(b).meta;
//      //    let t_c = x(c).meta;
//
//      //    unsafe { // very unsafe sketchy
//      //      let cat = g.concat(1, 2, vec![t_b, t_c].as_ptr());
//      //      Tnsr {cost : (*(*cat).op.ptr).runtime, meta : cat}
//      //    }
//      //  },
//      // HACK this is here to get an example working
//      Mdl::Num(_n) => {
//          unsafe { // very unsafe sketchy
//            Tnsr { cost : 0.0, meta : std::ptr::null_mut() }
//          }
//        },
//      other => {println!("{:?}", other); todo!()}
//    }
//  }
//
//  // TODO may not need modify to do anything?
//  fn modify(egraph: &mut EGraph<Mdl, Self>, id: Id) {
//  }
//}
