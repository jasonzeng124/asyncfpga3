module {
  func.func @matching_2(%arg0: memref<1000xi32>, %arg1: memref<1000xf32>, %arg2: i32) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %cst = arith.constant 0.000000e+00 : f32
    %0 = arith.cmpi slt, %c0_i32, %arg2 : i32
    cf.cond_br %0, ^bb1(%c0_i32 : i32), ^bb5
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb4
    %2 = arith.shli %1, %c1_i32 : i32
    %3 = arith.extui %2 : i32 to i64
    %4 = arith.index_cast %3 : i64 to index
    %5 = memref.load %arg0[%4] {handshake.name = "load0"} : memref<1000xi32>
    %6 = arith.extsi %5 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg1[%7] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : memref<1000xf32>
    %9 = arith.cmpf olt, %8, %cst : f32
    cf.cond_br %9, ^bb2, ^bb4
  ^bb2:  // pred: ^bb1
    %10 = arith.ori %2, %c1_i32 : i32
    %11 = arith.extui %10 : i32 to i64
    %12 = arith.index_cast %11 : i64 to index
    %13 = memref.load %arg0[%12] {handshake.name = "load2"} : memref<1000xi32>
    %14 = arith.extsi %13 : i32 to i64
    %15 = arith.index_cast %14 : i64 to index
    %16 = memref.load %arg1[%15] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load3"} : memref<1000xf32>
    %17 = arith.cmpf olt, %16, %cst : f32
    cf.cond_br %17, ^bb3, ^bb4
  ^bb3:  // pred: ^bb2
    %18 = arith.sitofp %13 : i32 to f32
    %19 = arith.extsi %5 : i32 to i64
    %20 = arith.index_cast %19 : i64 to index
    memref.store %18, %arg1[%20] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<1000xf32>
    %21 = arith.sitofp %5 : i32 to f32
    %22 = arith.extsi %13 : i32 to i64
    %23 = arith.index_cast %22 : i64 to index
    memref.store %21, %arg1[%23] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<1000xf32>
    cf.br ^bb4
  ^bb4:  // 3 preds: ^bb1, ^bb2, ^bb3
    %24 = arith.addi %1, %c1_i32 : i32
    %25 = arith.cmpi slt, %24, %arg2 : i32
    cf.cond_br %25, ^bb1(%24 : i32), ^bb5
  ^bb5:  // 2 preds: ^bb0, ^bb4
    return
  }
}
