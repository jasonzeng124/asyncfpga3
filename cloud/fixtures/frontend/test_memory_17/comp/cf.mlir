module {
  func.func @test_memory_17(%arg0: memref<4xi32>, %arg1: memref<4xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c5_i32 = arith.constant 5 : i32
    %c1_i32 = arith.constant 1 : i32
    %c4_i32 = arith.constant 4 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg1[%2] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<4xi32>
    %4 = arith.cmpi sgt, %3, %c5_i32 : i32
    cf.cond_br %4, ^bb2, ^bb3(%c1_i32 : i32)
  ^bb2:  // pred: ^bb1
    %5 = arith.extui %0 : i32 to i64
    %6 = arith.index_cast %5 : i64 to index
    memref.store %c0_i32, %arg1[%6] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<4xi32>
    cf.br ^bb3(%c0_i32 : i32)
  ^bb3(%7: i32):  // 2 preds: ^bb1, ^bb2
    %8 = arith.extui %0 : i32 to i64
    %9 = arith.index_cast %8 : i64 to index
    memref.store %7, %arg0[%9] {handshake.name = "store2"} : memref<4xi32>
    %10 = arith.addi %0, %c1_i32 : i32
    %11 = arith.cmpi ult, %10, %c4_i32 : i32
    cf.cond_br %11, ^bb1(%10 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    return
  }
}
