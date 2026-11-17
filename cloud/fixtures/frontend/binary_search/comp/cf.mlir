module {
  func.func @binary_search(%arg0: i32, %arg1: memref<101xi32>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c2_i32 = arith.constant 2 : i32
    %c101_i32 = arith.constant 101 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c1_i32 = arith.constant 1 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb2
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg1[%2] {handshake.name = "load0"} : memref<101xi32>
    %4 = arith.cmpi eq, %3, %arg0 : i32
    cf.cond_br %4, ^bb3(%0 : i32), ^bb2
  ^bb2:  // pred: ^bb1
    %5 = arith.addi %0, %c2_i32 : i32
    %6 = arith.cmpi ult, %5, %c101_i32 : i32
    cf.cond_br %6, ^bb1(%5 : i32), ^bb3(%c-1_i32 : i32)
  ^bb3(%7: i32):  // 2 preds: ^bb1, ^bb2
    cf.br ^bb4(%c1_i32 : i32)
  ^bb4(%8: i32):  // 2 preds: ^bb3, ^bb5
    %9 = arith.extui %8 : i32 to i64
    %10 = arith.index_cast %9 : i64 to index
    %11 = memref.load %arg1[%10] {handshake.name = "load1"} : memref<101xi32>
    %12 = arith.cmpi eq, %11, %arg0 : i32
    cf.cond_br %12, ^bb6(%8 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    %13 = arith.addi %8, %c2_i32 : i32
    %14 = arith.cmpi ult, %13, %c101_i32 : i32
    cf.cond_br %14, ^bb4(%13 : i32), ^bb6(%c-1_i32 : i32)
  ^bb6(%15: i32):  // 2 preds: ^bb4, ^bb5
    %16 = arith.cmpi eq, %7, %c-1_i32 : i32
    %17 = arith.cmpi eq, %15, %c-1_i32 : i32
    %18 = arith.select %17, %c-1_i32, %15 : i32
    %19 = arith.select %16, %18, %7 : i32
    return %19 : i32
  }
}
