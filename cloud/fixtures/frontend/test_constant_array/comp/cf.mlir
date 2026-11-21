module {
  memref.global "private" constant @constant_array : memref<9xi32> = dense<[1, 2, 3, 4, 5, 6, 7, 8, 9]> {alignment = 16 : i64}
  func.func @test_constant_array(%arg0: memref<9xi32>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c0_i64 = arith.constant 0 : i64
    %c1_i32 = arith.constant 1 : i32
    %c3_i32 = arith.constant 3 : i32
    %0 = memref.get_global @constant_array : memref<9xi32>
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb3
    %3 = arith.extui %2 : i32 to i64
    %4 = arith.extui %2 : i32 to i64
    cf.br ^bb2(%c0_i32, %1 : i32, i32)
  ^bb2(%5: i32, %6: i32):  // 2 preds: ^bb1, ^bb2
    %7 = arith.extui %5 : i32 to i64
    %c3_i64 = arith.constant 3 : i64
    %8 = arith.muli %3, %c3_i64 : i64
    %9 = arith.addi %8, %7 : i64
    %10 = arith.index_cast %9 : i64 to index
    %11 = memref.load %arg0[%10] {handshake.name = "load0"} : memref<9xi32>
    %12 = arith.extui %5 : i32 to i64
    %c9_i64 = arith.constant 9 : i64
    %13 = arith.muli %c0_i64, %c9_i64 : i64
    %c3_i64_0 = arith.constant 3 : i64
    %14 = arith.muli %4, %c3_i64_0 : i64
    %15 = arith.addi %14, %12 : i64
    %16 = arith.addi %13, %15 : i64
    %17 = arith.index_cast %16 : i64 to index
    %18 = memref.load %0[%17] {handshake.name = "load1"} : memref<9xi32>
    %19 = arith.addi %11, %18 : i32
    %20 = arith.addi %6, %19 : i32
    %21 = arith.addi %5, %c1_i32 : i32
    %22 = arith.cmpi ult, %21, %c3_i32 : i32
    cf.cond_br %22, ^bb2(%21, %20 : i32, i32), ^bb3(%20 : i32)
  ^bb3(%23: i32):  // pred: ^bb2
    %24 = arith.addi %2, %c1_i32 : i32
    %25 = arith.cmpi ult, %24, %c3_i32 : i32
    cf.cond_br %25, ^bb1(%23, %24 : i32, i32), ^bb4(%23 : i32)
  ^bb4(%26: i32):  // pred: ^bb3
    return %26 : i32
  }
}
