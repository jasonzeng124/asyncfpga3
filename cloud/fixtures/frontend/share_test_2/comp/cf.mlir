module {
  func.func @share_test_2(%arg0: memref<100xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c123456_i32 = arith.constant 123456 : i32
    %c456784_i32 = arith.constant 456784 : i32
    %c444444_i32 = arith.constant 444444 : i32
    %c1_i32 = arith.constant 1 : i32
    %c100_i32 = arith.constant 100 : i32
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32)
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.extui %0 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<100xi32>
    %5 = arith.addi %1, %0 : i32
    %6 = arith.addi %5, %c123456_i32 : i32
    %7 = arith.muli %6, %0 : i32
    %8 = arith.muli %7, %c456784_i32 : i32
    %9 = arith.muli %4, %c123456_i32 : i32
    %10 = arith.muli %9, %0 : i32
    %11 = arith.addi %8, %10 : i32
    %12 = arith.muli %4, %c444444_i32 : i32
    %13 = arith.muli %12, %6 : i32
    %14 = arith.addi %11, %13 : i32
    %15 = arith.extui %0 : i32 to i64
    %16 = arith.index_cast %15 : i64 to index
    memref.store %14, %arg0[%16] {handshake.name = "store1"} : memref<100xi32>
    %17 = arith.addi %0, %c1_i32 : i32
    %18 = arith.cmpi ult, %17, %c100_i32 : i32
    cf.cond_br %18, ^bb1(%17, %6 : i32, i32), ^bb2
  ^bb2:  // pred: ^bb1
    return
  }
}
