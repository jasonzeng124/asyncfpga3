module {
  func.func @test_memory_1(%arg0: memref<4xi32>, %arg1: i32) {
    %c0_i32 = arith.constant 0 : i32
    %c5_i32 = arith.constant 5 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c0_i32 : i32), ^bb2
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.extui %1 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<4xi32>
    %5 = arith.addi %4, %c5_i32 : i32
    %6 = arith.extui %1 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    memref.store %5, %arg0[%7] {handshake.name = "store1"} : memref<4xi32>
    %8 = arith.addi %1, %c1_i32 : i32
    %9 = arith.cmpi ne, %8, %arg1 : i32
    cf.cond_br %9, ^bb1(%8 : i32), ^bb2
  ^bb2:  // 2 preds: ^bb0, ^bb1
    return
  }
}
