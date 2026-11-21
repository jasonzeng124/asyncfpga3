module {
  func.func @share_test_1(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c999_i32 = arith.constant 999 : i32
    %c5_i32 = arith.constant 5 : i32
    %c1_i32 = arith.constant 1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32)
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.extui %1 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<1000xi32>
    %5 = arith.subi %c999_i32, %1 : i32
    %6 = arith.extsi %5 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg1[%7] {handshake.name = "load1"} : memref<1000xi32>
    %9 = arith.muli %4, %8 : i32
    %10 = arith.muli %9, %c5_i32 : i32
    %11 = arith.addi %0, %10 : i32
    %12 = arith.addi %1, %c1_i32 : i32
    %13 = arith.cmpi ne, %12, %c1000_i32 : i32
    cf.cond_br %13, ^bb1(%11, %12 : i32, i32), ^bb2(%11, %c0_i32 : i32, i32)
  ^bb2(%14: i32, %15: i32):  // 2 preds: ^bb1, ^bb2
    %16 = arith.subi %c999_i32, %15 : i32
    %17 = arith.extsi %16 : i32 to i64
    %18 = arith.index_cast %17 : i64 to index
    %19 = memref.load %arg0[%18] {handshake.name = "load2"} : memref<1000xi32>
    %20 = arith.extui %15 : i32 to i64
    %21 = arith.index_cast %20 : i64 to index
    %22 = memref.load %arg1[%21] {handshake.name = "load3"} : memref<1000xi32>
    %23 = arith.muli %19, %22 : i32
    %24 = arith.addi %14, %23 : i32
    %25 = arith.addi %15, %c1_i32 : i32
    %26 = arith.cmpi ne, %25, %c1000_i32 : i32
    cf.cond_br %26, ^bb2(%24, %25 : i32, i32), ^bb3(%24 : i32)
  ^bb3(%27: i32):  // pred: ^bb2
    return %27 : i32
  }
}
