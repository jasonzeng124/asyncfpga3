module {
  func.func @test_memory_16(%arg0: memref<4xi32>, %arg1: memref<4xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c5_i32 = arith.constant 5 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c1_i32 = arith.constant 1 : i32
    %c4_i32 = arith.constant 4 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb4
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg1[%2] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<4xi32>
    %4 = arith.cmpi sgt, %3, %c5_i32 : i32
    cf.cond_br %4, ^bb2, ^bb3
  ^bb2:  // pred: ^bb1
    %5 = arith.extui %0 : i32 to i64
    %6 = arith.index_cast %5 : i64 to index
    memref.store %c0_i32, %arg1[%6] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<4xi32>
    cf.br ^bb4(%c0_i32 : i32)
  ^bb3:  // pred: ^bb1
    %7 = arith.extui %0 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg0[%8] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load2"} : memref<4xi32>
    %10 = arith.addi %9, %c-1_i32 : i32
    cf.br ^bb4(%10 : i32)
  ^bb4(%11: i32):  // 2 preds: ^bb2, ^bb3
    %12 = arith.extui %0 : i32 to i64
    %13 = arith.index_cast %12 : i64 to index
    memref.store %11, %arg0[%13] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<4xi32>
    %14 = arith.addi %0, %c1_i32 : i32
    %15 = arith.cmpi ult, %14, %c4_i32 : i32
    cf.cond_br %15, ^bb1(%14 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    return
  }
}
