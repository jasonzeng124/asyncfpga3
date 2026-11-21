module {
  func.func @sumi3_mem(%arg0: memref<1000xi32>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32)
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.extui %0 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<1000xi32>
    %5 = arith.muli %4, %4 : i32
    %6 = arith.muli %5, %4 : i32
    %7 = arith.addi %1, %6 : i32
    %8 = arith.addi %0, %c1_i32 : i32
    %9 = arith.cmpi ne, %8, %c1000_i32 : i32
    cf.cond_br %9, ^bb1(%8, %7 : i32, i32), ^bb2(%7 : i32)
  ^bb2(%10: i32):  // pred: ^bb1
    return %10 : i32
  }
}
