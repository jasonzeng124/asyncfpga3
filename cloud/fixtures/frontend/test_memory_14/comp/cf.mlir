module {
  func.func @test_memory_14(%arg0: memref<4xi32>, %arg1: memref<4xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c5_i32 = arith.constant 5 : i32
    %c1_i32 = arith.constant 1 : i32
    %c4_i32 = arith.constant 4 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg0[%2] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<4xi32>
    %4 = arith.extui %0 : i32 to i64
    %5 = arith.index_cast %4 : i64 to index
    %6 = memref.load %arg1[%5] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : memref<4xi32>
    %7 = arith.cmpi sgt, %6, %c5_i32 : i32
    cf.cond_br %7, ^bb2, ^bb3(%3 : i32)
  ^bb2:  // pred: ^bb1
    %8 = arith.addi %3, %c1_i32 : i32
    %9 = arith.extui %0 : i32 to i64
    %10 = arith.index_cast %9 : i64 to index
    memref.store %c0_i32, %arg1[%10] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<4xi32>
    cf.br ^bb3(%8 : i32)
  ^bb3(%11: i32):  // 2 preds: ^bb1, ^bb2
    %12 = arith.extui %0 : i32 to i64
    %13 = arith.index_cast %12 : i64 to index
    memref.store %11, %arg0[%13] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<4xi32>
    %14 = arith.addi %0, %c1_i32 : i32
    %15 = arith.cmpi ult, %14, %c4_i32 : i32
    cf.cond_br %15, ^bb1(%14 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    return
  }
}
