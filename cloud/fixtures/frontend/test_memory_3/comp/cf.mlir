module {
  func.func @test_memory_3(%arg0: memref<4xi32>, %arg1: i32) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c0_i32 : i32), ^bb4
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb3
    %2 = arith.extui %1 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<4xi32>
    %5 = arith.cmpi eq, %4, %arg1 : i32
    cf.cond_br %5, ^bb2, ^bb3
  ^bb2:  // pred: ^bb1
    %6 = arith.extui %1 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    memref.store %c0_i32, %arg0[%7] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<4xi32>
    cf.br ^bb3
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %8 = arith.addi %1, %c1_i32 : i32
    %9 = arith.cmpi slt, %8, %arg1 : i32
    cf.cond_br %9, ^bb1(%8 : i32), ^bb4
  ^bb4:  // 2 preds: ^bb0, ^bb3
    return
  }
}
