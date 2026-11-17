module {
  func.func @if_loop_3(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1000_i32 = arith.constant 1000 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg2 : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c1000_i32 : i32, i32), ^bb4(%c1000_i32 : i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb3
    %3 = arith.extui %1 : i32 to i64
    %4 = arith.index_cast %3 : i64 to index
    %5 = memref.load %arg0[%4] {handshake.name = "load0"} : memref<100xi32>
    %6 = arith.extui %1 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg1[%7] {handshake.name = "load1"} : memref<100xi32>
    %9 = arith.subi %5, %8 : i32
    %10 = arith.cmpi sgt, %9, %c-1_i32 : i32
    cf.cond_br %10, ^bb2, ^bb3(%2 : i32)
  ^bb2:  // pred: ^bb1
    %11 = arith.divsi %2, %9 : i32
    cf.br ^bb3(%11 : i32)
  ^bb3(%12: i32):  // 2 preds: ^bb1, ^bb2
    %13 = arith.addi %1, %c1_i32 : i32
    %14 = arith.cmpi slt, %13, %arg2 : i32
    cf.cond_br %14, ^bb1(%13, %12 : i32, i32), ^bb4(%12 : i32)
  ^bb4(%15: i32):  // 2 preds: ^bb0, ^bb3
    return %15 : i32
  }
}
