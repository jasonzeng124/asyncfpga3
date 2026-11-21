module {
  func.func @test_memory_7(%arg0: memref<4xi32>, %arg1: i32) {
    %c2_i32 = arith.constant 2 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c-2_i32 = arith.constant -2 : i32
    %c5_i32 = arith.constant 5 : i32
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c2_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c2_i32 : i32), ^bb4
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb3
    %2 = arith.addi %1, %c-1_i32 : i32
    %3 = arith.extsi %2 : i32 to i64
    %4 = arith.index_cast %3 : i64 to index
    %5 = memref.load %arg0[%4] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<4xi32>
    %6 = arith.addi %1, %c-2_i32 : i32
    %7 = arith.extsi %6 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg0[%8] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : memref<4xi32>
    %10 = arith.addi %5, %9 : i32
    %11 = arith.addi %10, %c5_i32 : i32
    %12 = arith.extui %1 : i32 to i64
    %13 = arith.index_cast %12 : i64 to index
    memref.store %11, %arg0[%13] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<4xi32>
    %14 = arith.extui %1 : i32 to i64
    %15 = arith.index_cast %14 : i64 to index
    %16 = memref.load %arg0[%15] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load3"} : memref<4xi32>
    %17 = arith.cmpi sgt, %16, %c0_i32 : i32
    cf.cond_br %17, ^bb2, ^bb3
  ^bb2:  // pred: ^bb1
    %18 = arith.extui %1 : i32 to i64
    %19 = arith.index_cast %18 : i64 to index
    memref.store %c0_i32, %arg0[%19] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<4xi32>
    cf.br ^bb3
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %20 = arith.addi %1, %c1_i32 : i32
    %21 = arith.cmpi slt, %20, %arg1 : i32
    cf.cond_br %21, ^bb1(%20 : i32), ^bb4
  ^bb4:  // 2 preds: ^bb0, ^bb3
    return
  }
}
