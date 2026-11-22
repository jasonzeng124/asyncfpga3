module {
  func.func @matrix(%arg0: memref<900xi32>, %arg1: memref<900xi32>, %arg2: memref<900xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c30_i32 = arith.constant 30 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%3: i32):  // 2 preds: ^bb1, ^bb4
    %4 = arith.extui %3 : i32 to i64
    cf.br ^bb3(%c0_i32, %c0_i32 : i32, i32)
  ^bb3(%5: i32, %6: i32):  // 2 preds: ^bb2, ^bb3
    %7 = arith.extui %5 : i32 to i64
    %c30_i64 = arith.constant 30 : i64
    %8 = arith.muli %1, %c30_i64 : i64
    %9 = arith.addi %8, %7 : i64
    %10 = arith.index_cast %9 : i64 to index
    %11 = memref.load %arg0[%10] {handshake.name = "load0"} : memref<900xi32>
    %12 = arith.extui %5 : i32 to i64
    %c30_i64_0 = arith.constant 30 : i64
    %13 = arith.muli %12, %c30_i64_0 : i64
    %14 = arith.addi %13, %4 : i64
    %15 = arith.index_cast %14 : i64 to index
    %16 = memref.load %arg1[%15] {handshake.name = "load1"} : memref<900xi32>
    %17 = arith.muli %11, %16 : i32
    %18 = arith.addi %6, %17 : i32
    %19 = arith.addi %5, %c1_i32 : i32
    %20 = arith.cmpi ult, %19, %c30_i32 : i32
    cf.cond_br %20, ^bb3(%19, %18 : i32, i32), ^bb4(%18 : i32)
  ^bb4(%21: i32):  // pred: ^bb3
    %22 = arith.extui %3 : i32 to i64
    %c30_i64_1 = arith.constant 30 : i64
    %23 = arith.muli %2, %c30_i64_1 : i64
    %24 = arith.addi %23, %22 : i64
    %25 = arith.index_cast %24 : i64 to index
    memref.store %21, %arg2[%25] {handshake.name = "store2"} : memref<900xi32>
    %26 = arith.addi %3, %c1_i32 : i32
    %27 = arith.cmpi ult, %26, %c30_i32 : i32
    cf.cond_br %27, ^bb2(%26 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    %28 = arith.addi %0, %c1_i32 : i32
    %29 = arith.cmpi ult, %28, %c30_i32 : i32
    cf.cond_br %29, ^bb1(%28 : i32), ^bb6
  ^bb6:  // pred: ^bb5
    return
  }
}
