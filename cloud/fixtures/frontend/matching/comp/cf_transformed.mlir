module {
  func.func @matching(%arg0: memref<1000xi32> {handshake.arg_name = "edges"}, %arg1: memref<1000xi32> {handshake.arg_name = "vertices"}, %arg2: i32 {handshake.arg_name = "num_edges"}) -> f32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %cst = arith.constant {handshake.name = "constant1"} 0.000000e+00 : f32
    %0 = arith.cmpi sgt, %arg2, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%cst, %c0_i32 : f32, i32), ^bb5(%cst : f32) {handshake.name = "cond_br0"}
  ^bb1(%1: f32, %2: i32):  // 2 preds: ^bb0, ^bb4
    %c1_i32 = arith.constant {handshake.name = "constant4"} 1 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant5"} 0 : i32
    %3 = arith.shli %2, %c1_i32 {handshake.name = "shli0"} : i32
    %4 = arith.extui %3 {handshake.name = "extui0"} : i32 to i64
    %5 = arith.index_cast %4 {handshake.name = "index_cast0"} : i64 to index
    %6 = memref.load %arg0[%5] {handshake.name = "load0"} : memref<1000xi32>
    %7 = arith.index_cast %6 {handshake.name = "index_cast1"} : i32 to index
    %8 = memref.load %arg1[%7] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : memref<1000xi32>
    %9 = arith.cmpi slt, %8, %c0_i32_0 {handshake.name = "cmpi1"} : i32
    cf.cond_br %9, ^bb2, ^bb4(%1 : f32) {handshake.name = "cond_br1"}
  ^bb2:  // pred: ^bb1
    %c1_i32_1 = arith.constant {handshake.name = "constant6"} 1 : i32
    %c0_i32_2 = arith.constant {handshake.name = "constant7"} 0 : i32
    %10 = arith.ori %3, %c1_i32_1 {handshake.name = "ori0"} : i32
    %11 = arith.extui %10 {handshake.name = "extui1"} : i32 to i64
    %12 = arith.index_cast %11 {handshake.name = "index_cast2"} : i64 to index
    %13 = memref.load %arg0[%12] {handshake.name = "load2"} : memref<1000xi32>
    %14 = arith.index_cast %13 {handshake.name = "index_cast3"} : i32 to index
    %15 = memref.load %arg1[%14] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load3"} : memref<1000xi32>
    %16 = arith.cmpi slt, %15, %c0_i32_2 {handshake.name = "cmpi2"} : i32
    cf.cond_br %16, ^bb3, ^bb4(%1 : f32) {handshake.name = "cond_br2"}
  ^bb3:  // pred: ^bb2
    %cst_3 = arith.constant {handshake.name = "constant8"} 1.000000e+00 : f32
    %17 = arith.index_cast %6 {handshake.name = "index_cast4"} : i32 to index
    memref.store %13, %arg1[%17] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<1000xi32>
    %18 = arith.index_cast %13 {handshake.name = "index_cast5"} : i32 to index
    memref.store %6, %arg1[%18] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<1000xi32>
    %19 = arith.addf %1, %cst_3 {handshake.name = "addf0"} : f32
    cf.br ^bb4(%19 : f32) {handshake.name = "br0"}
  ^bb4(%20: f32):  // 3 preds: ^bb1, ^bb2, ^bb3
    %c1_i32_4 = arith.constant {handshake.name = "constant9"} 1 : i32
    %21 = arith.addi %2, %c1_i32_4 {handshake.name = "addi0"} : i32
    %22 = arith.cmpi slt, %21, %arg2 {handshake.name = "cmpi3"} : i32
    cf.cond_br %22, ^bb1(%20, %21 : f32, i32), ^bb5(%20 : f32) {handshake.name = "cond_br3"}
  ^bb5(%23: f32):  // 2 preds: ^bb0, ^bb4
    return {handshake.name = "return0"} %23 : f32
  }
}

