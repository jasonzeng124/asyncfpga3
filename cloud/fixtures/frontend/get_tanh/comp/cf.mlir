module {
  func.func @get_tanh(%arg0: memref<1000xf32>, %arg1: memref<1000xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %cst = arith.constant 1.000000e+00 : f32
    %cst_0 = arith.constant 19.5238094 : f32
    %cst_1 = arith.constant 3.70476198 : f32
    %c1_i32 = arith.constant 1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg1[%2] {handshake.name = "load0"} : memref<1000xi32>
    %4 = arith.extsi %3 : i32 to i64
    %5 = arith.index_cast %4 : i64 to index
    %6 = memref.load %arg0[%5] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : memref<1000xf32>
    %7 = arith.cmpf ult, %6, %cst : f32
    cf.cond_br %7, ^bb2, ^bb3(%cst : f32)
  ^bb2:  // pred: ^bb1
    %8 = arith.mulf %6, %6 : f32
    %9 = arith.addf %8, %cst_0 : f32
    %10 = arith.mulf %9, %6 : f32
    %11 = arith.mulf %10, %6 : f32
    %12 = arith.addf %11, %cst_1 : f32
    %13 = arith.mulf %12, %6 : f32
    cf.br ^bb3(%13 : f32)
  ^bb3(%14: f32):  // 2 preds: ^bb1, ^bb2
    %15 = arith.extsi %3 : i32 to i64
    %16 = arith.index_cast %15 : i64 to index
    memref.store %14, %arg0[%16] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<1000xf32>
    %17 = arith.addi %0, %c1_i32 : i32
    %18 = arith.cmpi ult, %17, %c1000_i32 : i32
    cf.cond_br %18, ^bb1(%17 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    return
  }
}
