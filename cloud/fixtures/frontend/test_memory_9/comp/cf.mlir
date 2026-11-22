module {
  func.func @test_memory_9(%arg0: memref<4xi32>, %arg1: i32) {
    %c1_i32 = arith.constant 1 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c5_i32 = arith.constant 5 : i32
    %0 = arith.cmpi slt, %c1_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c1_i32 : i32), ^bb2
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.addi %1, %c-1_i32 : i32
    %3 = arith.extsi %2 : i32 to i64
    %4 = arith.index_cast %3 : i64 to index
    %5 = memref.load %arg0[%4] {handshake.name = "load0"} : memref<4xi32>
    %6 = arith.muli %5, %c5_i32 : i32
    %7 = arith.extui %1 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    memref.store %6, %arg0[%8] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<4xi32>
    %9 = arith.addi %1, %c1_i32 : i32
    %10 = arith.cmpi slt, %9, %arg1 : i32
    cf.cond_br %10, ^bb1(%9 : i32), ^bb2
  ^bb2:  // 2 preds: ^bb0, ^bb1
    return
  }
}
