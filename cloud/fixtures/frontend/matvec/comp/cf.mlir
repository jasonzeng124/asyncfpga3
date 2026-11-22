module {
  func.func @matvec(%arg0: memref<10000xi32>, %arg1: memref<100xi32>, %arg2: memref<100xi32>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c100_i32 = arith.constant 100 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32, %c0_i32 : i32, i32)
  ^bb2(%2: i32, %3: i32):  // 2 preds: ^bb1, ^bb2
    %4 = arith.extui %2 : i32 to i64
    %5 = arith.index_cast %4 : i64 to index
    %6 = memref.load %arg1[%5] {handshake.name = "load0"} : memref<100xi32>
    %7 = arith.extui %2 : i32 to i64
    %c100_i64 = arith.constant 100 : i64
    %8 = arith.muli %1, %c100_i64 : i64
    %9 = arith.addi %8, %7 : i64
    %10 = arith.index_cast %9 : i64 to index
    %11 = memref.load %arg0[%10] {handshake.name = "load1"} : memref<10000xi32>
    %12 = arith.muli %6, %11 : i32
    %13 = arith.addi %3, %12 : i32
    %14 = arith.addi %2, %c1_i32 : i32
    %15 = arith.cmpi ult, %14, %c100_i32 : i32
    cf.cond_br %15, ^bb2(%14, %13 : i32, i32), ^bb3(%13 : i32)
  ^bb3(%16: i32):  // pred: ^bb2
    %17 = arith.extui %0 : i32 to i64
    %18 = arith.index_cast %17 : i64 to index
    memref.store %16, %arg2[%18] {handshake.name = "store2"} : memref<100xi32>
    %19 = arith.addi %0, %c1_i32 : i32
    %20 = arith.cmpi ult, %19, %c100_i32 : i32
    cf.cond_br %20, ^bb1(%19 : i32), ^bb4(%16 : i32)
  ^bb4(%21: i32):  // pred: ^bb3
    return %21 : i32
  }
}
