module {
  func.func @path_profiling(%arg0: memref<20xi32>, %arg1: memref<20xi32>, %arg2: memref<20xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c2_i32 = arith.constant 2 : i32
    %c3_i32 = arith.constant 3 : i32
    %c20_i32 = arith.constant 20 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb7
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg2[%2] {handshake.name = "load0"} : memref<20xi32>
    %4 = arith.andi %3, %c1_i32 : i32
    %5 = arith.cmpi eq, %4, %c0_i32 : i32
    cf.cond_br %5, ^bb2, ^bb3
  ^bb2:  // pred: ^bb1
    %6 = arith.extui %0 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    memref.store %c2_i32, %arg0[%7] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<20xi32>
    cf.br ^bb4
  ^bb3:  // pred: ^bb1
    %8 = arith.extui %0 : i32 to i64
    %9 = arith.index_cast %8 : i64 to index
    memref.store %c3_i32, %arg0[%9] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<20xi32>
    cf.br ^bb4
  ^bb4:  // 2 preds: ^bb2, ^bb3
    %10 = arith.extui %0 : i32 to i64
    %11 = arith.index_cast %10 : i64 to index
    %12 = memref.load %arg2[%11] {handshake.name = "load3"} : memref<20xi32>
    %13 = arith.remsi %12, %c3_i32 : i32
    %14 = arith.cmpi eq, %13, %c0_i32 : i32
    cf.cond_br %14, ^bb5, ^bb6
  ^bb5:  // pred: ^bb4
    %15 = arith.extui %0 : i32 to i64
    %16 = arith.index_cast %15 : i64 to index
    memref.store %c2_i32, %arg1[%16] {handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<20xi32>
    cf.br ^bb7
  ^bb6:  // pred: ^bb4
    %17 = arith.extui %0 : i32 to i64
    %18 = arith.index_cast %17 : i64 to index
    memref.store %c3_i32, %arg1[%18] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<20xi32>
    cf.br ^bb7
  ^bb7:  // 2 preds: ^bb5, ^bb6
    %19 = arith.addi %0, %c1_i32 : i32
    %20 = arith.cmpi ult, %19, %c20_i32 : i32
    cf.cond_br %20, ^bb1(%19 : i32), ^bb8
  ^bb8:  // pred: ^bb7
    return
  }
}
