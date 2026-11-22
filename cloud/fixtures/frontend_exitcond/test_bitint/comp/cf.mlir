module {
  memref.global "private" constant @__const.main.arr : memref<10xi16> = dense<[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]> {alignment = 16 : i64}
  memref.global "private" constant @__const.main.weight : memref<10xi5> = dense<[10, 9, 8, 7, 6, 5, 4, 3, 2, 1]> {alignment = 1 : i64}
  func.func @test_bitint(%arg0: memref<10xi16>, %arg1: memref<10xi5>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c10_i32 = arith.constant 10 : i32
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32)
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.extui %0 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<10xi16>
    %5 = arith.extui %4 : i16 to i21
    %6 = arith.extui %0 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg1[%7] {handshake.name = "load1"} : memref<10xi5>
    %9 = arith.extui %8 : i5 to i21
    %10 = arith.muli %5, %9 : i21
    %11 = arith.extui %10 : i21 to i32
    %12 = arith.addi %1, %11 : i32
    %13 = arith.addi %0, %c1_i32 : i32
    %14 = arith.cmpi ne, %13, %c10_i32 : i32
    cf.cond_br %14, ^bb1(%13, %12 : i32, i32), ^bb2(%12 : i32)
  ^bb2(%15: i32):  // pred: ^bb1
    return %15 : i32
  }
}
