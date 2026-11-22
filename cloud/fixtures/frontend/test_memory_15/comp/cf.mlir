module {
  func.func @test_memory_15(%arg0: memref<4xi32>, %arg1: memref<4xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c5_i32 = arith.constant 5 : i32
    %c1_i32 = arith.constant 1 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c4_i32 = arith.constant 4 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb4
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg0[%2] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<4xi32>
    %4 = arith.extui %0 : i32 to i64
    %5 = arith.index_cast %4 : i64 to index
    %6 = memref.load %arg1[%5] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : memref<4xi32>
    %7 = arith.cmpi sgt, %6, %c5_i32 : i32
    cf.cond_br %7, ^bb2, ^bb3
  ^bb2:  // pred: ^bb1
    %8 = arith.addi %3, %c1_i32 : i32
    %9 = arith.extui %0 : i32 to i64
    %10 = arith.index_cast %9 : i64 to index
    memref.store %c0_i32, %arg1[%10] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<4xi32>
    cf.br ^bb4(%8 : i32)
  ^bb3:  // pred: ^bb1
    %11 = arith.addi %3, %c-1_i32 : i32
    cf.br ^bb4(%11 : i32)
  ^bb4(%12: i32):  // 2 preds: ^bb2, ^bb3
    %13 = arith.extui %0 : i32 to i64
    %14 = arith.index_cast %13 : i64 to index
    memref.store %12, %arg0[%14] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<4xi32>
    %15 = arith.addi %0, %c1_i32 : i32
    %16 = arith.cmpi ult, %15, %c4_i32 : i32
    cf.cond_br %16, ^bb1(%15 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    return
  }
}
