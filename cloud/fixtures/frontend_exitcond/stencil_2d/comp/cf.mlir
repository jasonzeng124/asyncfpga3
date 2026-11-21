module {
  func.func @stencil_2d(%arg0: memref<900xi32>, %arg1: memref<10xi32>, %arg2: memref<900xi32>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c3_i32 = arith.constant 3 : i32
    %c30_i32 = arith.constant 30 : i32
    %c1_i32 = arith.constant 1 : i32
    %c28_i32 = arith.constant 28 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    cf.br ^bb2(%c0_i32, %c0_i32 : i32, i32)
  ^bb2(%1: i32, %2: i32):  // 2 preds: ^bb1, ^bb4
    %3 = arith.muli %1, %c3_i32 : i32
    %4 = arith.muli %1, %c30_i32 : i32
    %5 = arith.addi %4, %0 : i32
    cf.br ^bb3(%c0_i32, %2 : i32, i32)
  ^bb3(%6: i32, %7: i32):  // 2 preds: ^bb2, ^bb3
    %8 = arith.addi %3, %6 : i32
    %9 = arith.extui %8 : i32 to i64
    %10 = arith.index_cast %9 : i64 to index
    %11 = memref.load %arg1[%10] {handshake.name = "load0"} : memref<10xi32>
    %12 = arith.addi %5, %6 : i32
    %13 = arith.extui %12 : i32 to i64
    %14 = arith.index_cast %13 : i64 to index
    %15 = memref.load %arg0[%14] {handshake.name = "load1"} : memref<900xi32>
    %16 = arith.muli %11, %15 : i32
    %17 = arith.addi %7, %16 : i32
    %18 = arith.addi %6, %c1_i32 : i32
    %19 = arith.cmpi ne, %18, %c3_i32 : i32
    cf.cond_br %19, ^bb3(%18, %17 : i32, i32), ^bb4(%17 : i32)
  ^bb4(%20: i32):  // pred: ^bb3
    %21 = arith.addi %1, %c1_i32 : i32
    %22 = arith.cmpi ne, %21, %c3_i32 : i32
    cf.cond_br %22, ^bb2(%21, %20 : i32, i32), ^bb5(%20 : i32)
  ^bb5(%23: i32):  // pred: ^bb4
    %24 = arith.extui %0 : i32 to i64
    %25 = arith.index_cast %24 : i64 to index
    memref.store %23, %arg2[%25] {handshake.name = "store2"} : memref<900xi32>
    %26 = arith.addi %0, %c1_i32 : i32
    %27 = arith.cmpi ne, %26, %c28_i32 : i32
    cf.cond_br %27, ^bb1(%26 : i32), ^bb6(%23 : i32)
  ^bb6(%28: i32):  // pred: ^bb5
    return %28 : i32
  }
}
