module {
  func.func @test_memory_2(%arg0: memref<5xi32>, %arg1: i32) {
    %c-1_i32 = arith.constant -1 : i32
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c5_i32 = arith.constant 5 : i32
    %0 = arith.addi %arg1, %c-1_i32 : i32
    %1 = arith.cmpi slt, %c0_i32, %0 : i32
    cf.cond_br %1, ^bb1(%c0_i32 : i32), ^bb2
  ^bb1(%2: i32):  // 2 preds: ^bb0, ^bb1
    %3 = arith.addi %2, %c1_i32 : i32
    %4 = arith.extui %3 : i32 to i64
    %5 = arith.index_cast %4 : i64 to index
    %6 = memref.load %arg0[%5] {handshake.name = "load0"} : memref<5xi32>
    %7 = arith.addi %6, %c5_i32 : i32
    %8 = arith.extui %2 : i32 to i64
    %9 = arith.index_cast %8 : i64 to index
    memref.store %7, %arg0[%9] {handshake.name = "store1"} : memref<5xi32>
    %10 = arith.addi %2, %c1_i32 : i32
    %11 = arith.cmpi slt, %10, %0 : i32
    cf.cond_br %11, ^bb1(%10 : i32), ^bb2
  ^bb2:  // 2 preds: ^bb0, ^bb1
    return
  }
}
