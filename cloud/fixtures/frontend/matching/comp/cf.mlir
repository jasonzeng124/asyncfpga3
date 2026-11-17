module {
  func.func @matching(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: i32) -> f32 {
    %c0_i32 = arith.constant 0 : i32
    %cst = arith.constant 0.000000e+00 : f32
    %c1_i32 = arith.constant 1 : i32
    %cst_0 = arith.constant 1.000000e+00 : f32
    %0 = arith.cmpi slt, %c0_i32, %arg2 : i32
    cf.cond_br %0, ^bb1(%cst, %c0_i32 : f32, i32), ^bb5(%cst : f32)
  ^bb1(%1: f32, %2: i32):  // 2 preds: ^bb0, ^bb4
    %3 = arith.shli %2, %c1_i32 : i32
    %4 = arith.extui %3 : i32 to i64
    %5 = arith.index_cast %4 : i64 to index
    %6 = memref.load %arg0[%5] {handshake.name = "load0"} : memref<1000xi32>
    %7 = arith.extsi %6 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg1[%8] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : memref<1000xi32>
    %10 = arith.cmpi slt, %9, %c0_i32 : i32
    cf.cond_br %10, ^bb2, ^bb4(%1 : f32)
  ^bb2:  // pred: ^bb1
    %11 = arith.ori %3, %c1_i32 : i32
    %12 = arith.extui %11 : i32 to i64
    %13 = arith.index_cast %12 : i64 to index
    %14 = memref.load %arg0[%13] {handshake.name = "load2"} : memref<1000xi32>
    %15 = arith.extsi %14 : i32 to i64
    %16 = arith.index_cast %15 : i64 to index
    %17 = memref.load %arg1[%16] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load3"} : memref<1000xi32>
    %18 = arith.cmpi slt, %17, %c0_i32 : i32
    cf.cond_br %18, ^bb3, ^bb4(%1 : f32)
  ^bb3:  // pred: ^bb2
    %19 = arith.extsi %6 : i32 to i64
    %20 = arith.index_cast %19 : i64 to index
    memref.store %14, %arg1[%20] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<1000xi32>
    %21 = arith.extsi %14 : i32 to i64
    %22 = arith.index_cast %21 : i64 to index
    memref.store %6, %arg1[%22] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<1000xi32>
    %23 = arith.addf %1, %cst_0 : f32
    cf.br ^bb4(%23 : f32)
  ^bb4(%24: f32):  // 3 preds: ^bb1, ^bb2, ^bb3
    %25 = arith.addi %2, %c1_i32 : i32
    %26 = arith.cmpi slt, %25, %arg2 : i32
    cf.cond_br %26, ^bb1(%24, %25 : f32, i32), ^bb5(%24 : f32)
  ^bb5(%27: f32):  // 2 preds: ^bb0, ^bb4
    return %27 : f32
  }
}
