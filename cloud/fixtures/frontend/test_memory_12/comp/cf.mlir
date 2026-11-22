module {
  func.func @test_memory_12(%arg0: memref<4xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i64 = arith.constant 1 : i64
    %c1_i32 = arith.constant 1 : i32
    %c2_i64 = arith.constant 2 : i64
    %c2_i32 = arith.constant 2 : i32
    %c3_i64 = arith.constant 3 : i64
    %c3_i32 = arith.constant 3 : i32
    %c4_i32 = arith.constant 4 : i32
    %c0 = arith.constant 0 : index
    memref.store %c0_i32, %arg0[%c0] {handshake.name = "store0"} : memref<4xi32>
    %c1_i64_0 = arith.constant 1 : i64
    %0 = arith.index_cast %c1_i64_0 : i64 to index
    memref.store %c1_i32, %arg0[%0] {handshake.name = "store1"} : memref<4xi32>
    %c2_i64_1 = arith.constant 2 : i64
    %1 = arith.index_cast %c2_i64_1 : i64 to index
    memref.store %c2_i32, %arg0[%1] {handshake.name = "store2"} : memref<4xi32>
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%2: i32):  // 2 preds: ^bb0, ^bb3
    %3 = arith.andi %2, %c1_i32 : i32
    %4 = arith.cmpi eq, %3, %c0_i32 : i32
    cf.cond_br %4, ^bb3, ^bb2
  ^bb2:  // pred: ^bb1
    %c3_i64_2 = arith.constant 3 : i64
    %5 = arith.index_cast %c3_i64_2 : i64 to index
    memref.store %c3_i32, %arg0[%5] {handshake.name = "store3"} : memref<4xi32>
    cf.br ^bb3
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %6 = arith.addi %2, %c1_i32 : i32
    %7 = arith.cmpi ult, %6, %c4_i32 : i32
    cf.cond_br %7, ^bb1(%6 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    return
  }
}
