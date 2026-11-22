module {
  func.func @test_memory_10(%arg0: memref<4xi32>, %arg1: i32) {
    %c-1_i32 = arith.constant -1 : i32
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c5_i32 = arith.constant 5 : i32
    %0 = arith.addi %arg1, %c-1_i32 : i32
    %1 = arith.cmpi slt, %c0_i32, %0 : i32
    cf.cond_br %1, ^bb1(%c0_i32 : i32), ^bb2
  ^bb1(%2: i32):  // 2 preds: ^bb0, ^bb1
    %3 = arith.extui %2 : i32 to i64
    %4 = arith.index_cast %3 : i64 to index
    %5 = memref.load %arg0[%4] {handshake.name = "load0"} : memref<4xi32>
    %6 = arith.addi %2, %c1_i32 : i32
    %7 = arith.extui %6 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg0[%8] {handshake.name = "load1"} : memref<4xi32>
    %10 = arith.addi %5, %9 : i32
    %11 = arith.addi %10, %c5_i32 : i32
    %12 = arith.extui %2 : i32 to i64
    %13 = arith.index_cast %12 : i64 to index
    memref.store %11, %arg0[%13] {handshake.name = "store2"} : memref<4xi32>
    %14 = arith.addi %2, %c1_i32 : i32
    %15 = arith.cmpi slt, %14, %0 : i32
    cf.cond_br %15, ^bb1(%14 : i32), ^bb2
  ^bb2:  // 2 preds: ^bb0, ^bb1
    return
  }
}
