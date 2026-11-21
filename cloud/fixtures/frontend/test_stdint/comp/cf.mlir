module {
  func.func @test_stdint(%arg0: memref<100xi8>, %arg1: i8) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c100_i32 = arith.constant 100 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg0[%2] {handshake.name = "load0"} : memref<100xi8>
    %4 = arith.muli %3, %3 : i8
    %5 = arith.muli %4, %3 : i8
    %6 = arith.addi %5, %arg1 : i8
    %7 = arith.extui %0 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    memref.store %6, %arg0[%8] {handshake.name = "store1"} : memref<100xi8>
    %9 = arith.addi %0, %c1_i32 : i32
    %10 = arith.cmpi ult, %9, %c100_i32 : i32
    cf.cond_br %10, ^bb1(%9 : i32), ^bb2
  ^bb2:  // pred: ^bb1
    return
  }
}
