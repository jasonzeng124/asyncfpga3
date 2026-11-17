module {
  func.func @test_flatten_array(%arg0: memref<512xi32>, %arg1: memref<512xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c7_i32 = arith.constant 7 : i32
    %c15_i32 = arith.constant 15 : i32
    %c1_i32 = arith.constant 1 : i32
    %c16_i32 = arith.constant 16 : i32
    %c8_i32 = arith.constant 8 : i32
    %c4_i32 = arith.constant 4 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%3: i32):  // 2 preds: ^bb1, ^bb4
    %4 = arith.subi %c7_i32, %3 : i32
    %5 = arith.extsi %4 : i32 to i64
    %6 = arith.extui %3 : i32 to i64
    cf.br ^bb3(%c0_i32 : i32)
  ^bb3(%7: i32):  // 2 preds: ^bb2, ^bb3
    %8 = arith.subi %c15_i32, %7 : i32
    %9 = arith.extsi %8 : i32 to i64
    %c7_i64 = arith.constant 7 : i64
    %10 = arith.shli %1, %c7_i64 : i64
    %c4_i64 = arith.constant 4 : i64
    %11 = arith.shli %5, %c4_i64 : i64
    %12 = arith.addi %11, %9 : i64
    %13 = arith.addi %10, %12 : i64
    %14 = arith.index_cast %13 : i64 to index
    %15 = memref.load %arg0[%14] {handshake.name = "load0"} : memref<512xi32>
    %16 = arith.extui %7 : i32 to i64
    %c7_i64_0 = arith.constant 7 : i64
    %17 = arith.shli %2, %c7_i64_0 : i64
    %c4_i64_1 = arith.constant 4 : i64
    %18 = arith.shli %6, %c4_i64_1 : i64
    %19 = arith.addi %18, %16 : i64
    %20 = arith.addi %17, %19 : i64
    %21 = arith.index_cast %20 : i64 to index
    memref.store %15, %arg1[%21] {handshake.name = "store1"} : memref<512xi32>
    %22 = arith.addi %7, %c1_i32 : i32
    %23 = arith.cmpi ult, %22, %c16_i32 : i32
    cf.cond_br %23, ^bb3(%22 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    %24 = arith.addi %3, %c1_i32 : i32
    %25 = arith.cmpi ult, %24, %c8_i32 : i32
    cf.cond_br %25, ^bb2(%24 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    %26 = arith.addi %0, %c1_i32 : i32
    %27 = arith.cmpi ult, %26, %c4_i32 : i32
    cf.cond_br %27, ^bb1(%26 : i32), ^bb6
  ^bb6:  // pred: ^bb5
    return
  }
}
