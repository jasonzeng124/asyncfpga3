module {
  func.func @get_tanh(%arg0: memref<1000xf32> {handshake.arg_name = "A"}, %arg1: memref<1000xi32> {handshake.arg_name = "addr"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %cst = arith.constant {handshake.name = "constant6"} 1.000000e+00 : f32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg1[%2] {handshake.name = "load0"} : memref<1000xi32>
    %4 = arith.index_cast %3 {handshake.name = "index_cast1"} : i32 to index
    %5 = memref.load %arg0[%4] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : memref<1000xf32>
    %6 = arith.cmpf ult, %5, %cst {handshake.name = "cmpf0"} : f32
    cf.cond_br %6, ^bb2, ^bb3(%cst : f32) {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    %cst_0 = arith.constant {handshake.name = "constant7"} 3.70476198 : f32
    %cst_1 = arith.constant {handshake.name = "constant8"} 19.5238094 : f32
    %7 = arith.mulf %5, %5 {handshake.name = "mulf0"} : f32
    %8 = arith.addf %7, %cst_1 {handshake.name = "addf0"} : f32
    %9 = arith.mulf %8, %5 {handshake.name = "mulf1"} : f32
    %10 = arith.mulf %9, %5 {handshake.name = "mulf2"} : f32
    %11 = arith.addf %10, %cst_0 {handshake.name = "addf1"} : f32
    %12 = arith.mulf %11, %5 {handshake.name = "mulf3"} : f32
    cf.br ^bb3(%12 : f32) {handshake.name = "br1"}
  ^bb3(%13: f32):  // 2 preds: ^bb1, ^bb2
    %c1000_i32 = arith.constant {handshake.name = "constant9"} 1000 : i32
    %c1_i32 = arith.constant {handshake.name = "constant10"} 1 : i32
    %14 = arith.index_cast %3 {handshake.name = "index_cast2"} : i32 to index
    memref.store %13, %arg0[%14] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<1000xf32>
    %15 = arith.addi %0, %c1_i32 {handshake.name = "addi0"} : i32
    %16 = arith.cmpi ult, %15, %c1000_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %16, ^bb1(%15 : i32), ^bb4 {handshake.name = "cond_br1"}
  ^bb4:  // pred: ^bb3
    return {handshake.name = "return0"}
  }
}

